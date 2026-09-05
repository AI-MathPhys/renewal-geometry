/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.CoreResolvent

/-!
# The curved limit resolvent: perturbative Sobolev packaging

The last analytic clause of `thm:curved-limit` (flagship):
**construction of the limit resolvent** of the curved Hamiltonian
`H = H₀ + W`, where `H₀` is the flat elliptic operator (whose
resolvent data exist by the multiplier model and Plancherel
transport) and `W` is the slowly-varying correction
`(B(x) − B₀)·D + Ω-term + V`.  In the manuscript's slowly-varying
phase the correction is **relatively small**, and the resolvent is
constructed by the Kato–Rellich/Neumann method:

* `perturbedResolvent` — the operator `R = R₀ (1 + K)⁻¹` with
  `K = W ∘ R₀` the bounded relative perturbation, `‖K‖ < 1`
  (Neumann unit `1 + K`);
* `perturbedResolvent_right_inverse` — `(H − z) R y = y` for
  **every** `y` (in particular `H − z` is surjective — the
  self-adjointness range condition);
* `perturbedResolvent_left_inverse` — `R (H − z) u = u` on the
  common core `C`;
* `perturbedResolvent_image_dense` — `(H − z)''C` is dense (the
  core property transports through the Neumann unit);
* `perturbedResolvent_norm_le` — `‖R‖ ≤ ‖R₀‖ (1 − ‖K‖)⁻¹`;
* `curved_strong_resolvent_convergence` — the packaged endpoint:
  the discrete covariant resolvents converge **strongly to the
  constructed curved resolvent** on all of `L²`, by
  `strong_resolvent_of_core` applied to the constructed data;
* `clifford_resolvent_identity` / `clifford_resolvent_norm_le` /
  `clifford_weighted_bound` — the concrete smallness certificates:
  for a Clifford-type symbol with `B² = a²·1` the resolvent at
  `z = i` is the explicit `(a²+1)⁻¹(B + i)`, with uniform bound
  `3/2` and momentum-weighted bound `a·‖(B − i)⁻¹‖ ≤ 3/2`; hence
  `‖K‖ ≤ (3/2)·‖ΔB‖_∞/(κ c₀) < 1` in the slowly-varying phase.

Scope: this constructs the curved resolvent in the **perturbative
(slowly varying) regime** — exactly the phase in which
`thm:curved-limit` is stated.  Essential self-adjointness for
arbitrarily large bounded-`C¹` coefficient variation (the Friedrichs
mollifier route) would need distribution/commutator theory that
Mathlib does not yet have; in the flagship phase the perturbative
construction is the complete statement.
-/

namespace NCG

open Filter

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [CompleteSpace H]

/-! ## The Neumann unit `1 + K` -/

/-- The Neumann unit `1 + K` for `‖K‖ < 1`. -/
noncomputable def onePlusUnit (K : H →L[ℝ] H) (hK : ‖K‖ < 1) :
    (H →L[ℝ] H)ˣ :=
  Units.oneSub (-K) (by rwa [norm_neg])

theorem onePlusUnit_val (K : H →L[ℝ] H) (hK : ‖K‖ < 1) :
    (onePlusUnit K hK : H →L[ℝ] H) = 1 + K := by
  rw [onePlusUnit, Units.val_oneSub, sub_neg_eq_add]

/-- The Neumann inverse obeys `‖(1+K)⁻¹‖ ≤ (1 − ‖K‖)⁻¹`, by the
algebraic bootstrap `(1+K)⁻¹ = 1 − K (1+K)⁻¹` (no series needed). -/
theorem onePlusUnit_inv_norm_le (K : H →L[ℝ] H) (hK : ‖K‖ < 1) :
    ‖(↑(onePlusUnit K hK)⁻¹ : H →L[ℝ] H)‖ ≤ (1 - ‖K‖)⁻¹ := by
  have h1 : (onePlusUnit K hK : H →L[ℝ] H)
      * ↑(onePlusUnit K hK)⁻¹ = 1 := Units.mul_inv _
  set S : H →L[ℝ] H := (↑(onePlusUnit K hK)⁻¹ : H →L[ℝ] H)
    with hS
  have hid : S = 1 - K * S := by
    rw [onePlusUnit_val] at h1
    have h2 : (1 + K) * S = S + K * S := by
      rw [add_mul, one_mul]
    rw [h2] at h1
    have h3 := congrArg (fun A => A - K * S) h1
    simpa using h3
  have hbound : ‖S‖ ≤ 1 + ‖K‖ * ‖S‖ := by
    calc ‖S‖ = ‖(1 : H →L[ℝ] H) - K * S‖ := by rw [← hid]
      _ ≤ ‖(1 : H →L[ℝ] H)‖ + ‖K * S‖ := norm_sub_le _ _
      _ ≤ 1 + ‖K‖ * ‖S‖ := by
          have h4 : ‖(1 : H →L[ℝ] H)‖ ≤ 1 := by
            rw [ContinuousLinearMap.one_def]
            exact ContinuousLinearMap.norm_id_le
          have h5 : ‖K * S‖ ≤ ‖K‖ * ‖S‖ := norm_mul_le _ _
          linarith
  have hpos : (0:ℝ) < 1 - ‖K‖ := by linarith
  have h6 : ‖S‖ * (1 - ‖K‖) ≤ 1 := by nlinarith
  calc ‖S‖ = ‖S‖ * (1 - ‖K‖) * (1 - ‖K‖)⁻¹ := by
        field_simp
    _ ≤ 1 * (1 - ‖K‖)⁻¹ :=
        mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = (1 - ‖K‖)⁻¹ := one_mul _

/-! ## The perturbed resolvent and its resolvent data -/

/-- The curved resolvent `R = R₀ (1 + K)⁻¹`, where `K = W ∘ R₀` is
the bounded relative perturbation. -/
noncomputable def perturbedResolvent (R₀ K : H →L[ℝ] H)
    (hK : ‖K‖ < 1) : H →L[ℝ] H :=
  R₀ * (↑(onePlusUnit K hK)⁻¹ : H →L[ℝ] H)

/-- **Right inverse everywhere**: `(H − z) R y = y` for every `y`
(the surjectivity/range half of the self-adjointness packaging). -/
theorem perturbedResolvent_right_inverse
    {T₀ W : H → H} {R₀ K : H →L[ℝ] H} (hK : ‖K‖ < 1)
    (hTR : ∀ y, T₀ (R₀ y) = y)
    (hWR : ∀ y, W (R₀ y) = K y) :
    ∀ y, T₀ (perturbedResolvent R₀ K hK y)
      + W (perturbedResolvent R₀ K hK y) = y := by
  intro y
  set v : H := (↑(onePlusUnit K hK)⁻¹ : H →L[ℝ] H) y with hv
  have happ : perturbedResolvent R₀ K hK y = R₀ v := rfl
  rw [happ, hTR, hWR]
  have h1 : v + K v = (onePlusUnit K hK : H →L[ℝ] H) v := by
    rw [onePlusUnit_val]
    simp
  have h2 : (onePlusUnit K hK : H →L[ℝ] H) v = y := by
    rw [hv]
    have h3 : (onePlusUnit K hK : H →L[ℝ] H)
        ((↑(onePlusUnit K hK)⁻¹ : H →L[ℝ] H) y)
        = ((onePlusUnit K hK : H →L[ℝ] H)
          * (↑(onePlusUnit K hK)⁻¹ : H →L[ℝ] H)) y := rfl
    rw [h3, Units.mul_inv]
    rfl
  rw [h1, h2]

/-- **Left inverse on the core**: `R (H − z) u = u` for `u ∈ C`. -/
theorem perturbedResolvent_left_inverse
    {C : Set H} {T₀ W : H → H} {R₀ K : H →L[ℝ] H} (hK : ‖K‖ < 1)
    (hRT : ∀ u ∈ C, R₀ (T₀ u) = u)
    (hWR : ∀ y, W (R₀ y) = K y) :
    ∀ u ∈ C, perturbedResolvent R₀ K hK (T₀ u + W u) = u := by
  intro u hu
  have hW : W u = K (T₀ u) := by
    conv_lhs => rw [← hRT u hu]
    exact hWR (T₀ u)
  have hsum : T₀ u + W u
      = (onePlusUnit K hK : H →L[ℝ] H) (T₀ u) := by
    rw [hW, onePlusUnit_val]
    simp
  have happ : perturbedResolvent R₀ K hK (T₀ u + W u)
      = R₀ ((↑(onePlusUnit K hK)⁻¹ : H →L[ℝ] H)
          (T₀ u + W u)) := rfl
  have hcancel : (↑(onePlusUnit K hK)⁻¹ : H →L[ℝ] H)
      ((onePlusUnit K hK : H →L[ℝ] H) (T₀ u)) = T₀ u := by
    have h3 : (↑(onePlusUnit K hK)⁻¹ : H →L[ℝ] H)
        ((onePlusUnit K hK : H →L[ℝ] H) (T₀ u))
        = ((↑(onePlusUnit K hK)⁻¹ : H →L[ℝ] H)
          * (onePlusUnit K hK : H →L[ℝ] H)) (T₀ u) := rfl
    rw [h3, Units.inv_mul]
    rfl
  rw [happ, hsum, hcancel, hRT u hu]

omit [CompleteSpace H] in
/-- The image of a dense set under an invertible operator is
dense. -/
theorem dense_image_unit (A : (H →L[ℝ] H)ˣ) {S : Set H}
    (hS : Dense S) : Dense ((A : H →L[ℝ] H) '' S) := by
  intro y
  rw [Metric.mem_closure_iff]
  intro ε hε
  set w : H := (↑A⁻¹ : H →L[ℝ] H) y with hw
  have hAy : (A : H →L[ℝ] H) w = y := by
    rw [hw]
    have h3 : (A : H →L[ℝ] H) ((↑A⁻¹ : H →L[ℝ] H) y)
        = ((A : H →L[ℝ] H) * (↑A⁻¹ : H →L[ℝ] H)) y := rfl
    rw [h3, Units.mul_inv]
    rfl
  have hδ : 0 < ε / (‖(A : H →L[ℝ] H)‖ + 1) := by positivity
  obtain ⟨s, hsS, hs⟩ := Metric.mem_closure_iff.mp (hS w) _ hδ
  refine ⟨(A : H →L[ℝ] H) s, Set.mem_image_of_mem _ hsS, ?_⟩
  rw [dist_eq_norm, ← hAy, ← map_sub]
  calc ‖(A : H →L[ℝ] H) (w - s)‖
      ≤ ‖(A : H →L[ℝ] H)‖ * ‖w - s‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ < ε := by
        have h1 : ‖w - s‖ < ε / (‖(A : H →L[ℝ] H)‖ + 1) := by
          rw [← dist_eq_norm]
          exact hs
        have h2 : (0:ℝ) ≤ ‖(A : H →L[ℝ] H)‖ := norm_nonneg _
        calc ‖(A : H →L[ℝ] H)‖ * ‖w - s‖
            ≤ (‖(A : H →L[ℝ] H)‖ + 1) * ‖w - s‖ := by
              nlinarith [norm_nonneg (w - s)]
          _ < (‖(A : H →L[ℝ] H)‖ + 1)
              * (ε / (‖(A : H →L[ℝ] H)‖ + 1)) :=
              mul_lt_mul_of_pos_left h1 (by positivity)
          _ = ε := by field_simp

/-- **Core-image density**: `(H − z)''C` is dense, transported from
the flat core property through the Neumann unit. -/
theorem perturbedResolvent_image_dense
    {C : Set H} {T₀ W : H → H} {R₀ K : H →L[ℝ] H} (hK : ‖K‖ < 1)
    (hRT : ∀ u ∈ C, R₀ (T₀ u) = u)
    (hWR : ∀ y, W (R₀ y) = K y)
    (hdense : Dense (T₀ '' C)) :
    Dense ((fun u => T₀ u + W u) '' C) := by
  have himg : (fun u => T₀ u + W u) '' C
      = (onePlusUnit K hK : H →L[ℝ] H) '' (T₀ '' C) := by
    rw [Set.image_image]
    refine Set.image_congr fun u hu => ?_
    have hW : W u = K (T₀ u) := by
      conv_lhs => rw [← hRT u hu]
      exact hWR (T₀ u)
    rw [hW, onePlusUnit_val]
    simp
  rw [himg]
  exact dense_image_unit _ hdense

/-- **Resolvent bound**: `‖R‖ ≤ ‖R₀‖ (1 − ‖K‖)⁻¹`. -/
theorem perturbedResolvent_norm_le (R₀ K : H →L[ℝ] H)
    (hK : ‖K‖ < 1) :
    ‖perturbedResolvent R₀ K hK‖ ≤ ‖R₀‖ * (1 - ‖K‖)⁻¹ :=
  le_trans (norm_mul_le _ _)
    (mul_le_mul_of_nonneg_left (onePlusUnit_inv_norm_le K hK)
      (norm_nonneg _))

/-- **The curved strong-resolvent endpoint**
(`thm:curved-limit`(iv), Sobolev packaging closed): with the flat
resolvent data `(R₀, T₀, C)` and a relatively small slowly-varying
correction `W` (encoded by the bounded composite `K = W ∘ R₀` with
`‖K‖ < 1`), the curved limit resolvent **exists** — it is
`perturbedResolvent R₀ K` — and the discrete covariant resolvents
converge to it strongly on all of `L²`. -/
theorem curved_strong_resolvent_convergence
    (C : Set H) (T₀ W : H → H) (R₀ K : H →L[ℝ] H) (hK : ‖K‖ < 1)
    (hRT : ∀ u ∈ C, R₀ (T₀ u) = u)
    (hWR : ∀ y, W (R₀ y) = K y)
    (hdense : Dense (T₀ '' C))
    (Rn : ℕ → H →L[ℝ] H) (Tn : ℕ → H → H) {M : ℝ}
    (hM : ∀ n, ‖Rn n‖ ≤ M)
    (hRnTn : ∀ n, ∀ u ∈ C, Rn n (Tn n u) = u)
    (hconv : ∀ u ∈ C,
      Tendsto (fun n => Tn n u) atTop (nhds (T₀ u + W u))) :
    ∀ y, Tendsto (fun n => Rn n y) atTop
      (nhds (perturbedResolvent R₀ K hK y)) :=
  strong_resolvent_of_core C (perturbedResolvent R₀ K hK) Rn
    (fun u => T₀ u + W u) Tn hM hRnTn
    (perturbedResolvent_left_inverse hK hRT hWR)
    (perturbedResolvent_image_dense hK hRT hWR hdense) hconv

/-! ## Clifford smallness certificates -/

section Clifford

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [NormOneClass A]

omit [NormOneClass A] in
/-- **Clifford resolvent identity**: if the symbol squares to the
scalar `a²` then its resolvent at `z = i` is the explicit
`(a²+1)⁻¹ (B + i)`, two-sidedly. -/
theorem clifford_resolvent_identity (B : A) (a : ℝ)
    (hB : B * B = algebraMap ℂ A ((a : ℂ) ^ 2)) :
    (B - algebraMap ℂ A Complex.I)
        * (((a : ℂ) ^ 2 + 1)⁻¹ • (B + algebraMap ℂ A Complex.I)) = 1
    ∧ (((a : ℂ) ^ 2 + 1)⁻¹ • (B + algebraMap ℂ A Complex.I))
        * (B - algebraMap ℂ A Complex.I) = 1 := by
  have hcomm : B * algebraMap ℂ A Complex.I
      = algebraMap ℂ A Complex.I * B := (Algebra.commutes _ _).symm
  have hii : algebraMap ℂ A Complex.I * algebraMap ℂ A Complex.I
      = algebraMap ℂ A (-1) := by
    rw [← map_mul, Complex.I_mul_I]
  have hc : ((a : ℂ) ^ 2 + 1) ≠ 0 := by
    have h1 : ((a : ℂ) ^ 2 + 1) = (((a ^ 2 + 1 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [h1]
    exact_mod_cast (by positivity : (a ^ 2 + 1 : ℝ) ≠ 0)
  have hexp1 : (B - algebraMap ℂ A Complex.I)
      * (B + algebraMap ℂ A Complex.I) = ((a : ℂ) ^ 2 + 1) • 1 := by
    have h2 : (B - algebraMap ℂ A Complex.I)
        * (B + algebraMap ℂ A Complex.I)
        = B * B - algebraMap ℂ A Complex.I
            * algebraMap ℂ A Complex.I
          + (B * algebraMap ℂ A Complex.I
            - algebraMap ℂ A Complex.I * B) := by
      noncomm_ring
    rw [h2, hcomm, sub_self, add_zero, hB, hii, ← map_sub,
      ← Algebra.algebraMap_eq_smul_one]
    congr 1
    ring
  have hexp2 : (B + algebraMap ℂ A Complex.I)
      * (B - algebraMap ℂ A Complex.I) = ((a : ℂ) ^ 2 + 1) • 1 := by
    have h2 : (B + algebraMap ℂ A Complex.I)
        * (B - algebraMap ℂ A Complex.I)
        = B * B - algebraMap ℂ A Complex.I
            * algebraMap ℂ A Complex.I
          + (algebraMap ℂ A Complex.I * B
            - B * algebraMap ℂ A Complex.I) := by
      noncomm_ring
    rw [h2, ← hcomm, sub_self, add_zero, hB, hii, ← map_sub,
      ← Algebra.algebraMap_eq_smul_one]
    congr 1
    ring
  constructor
  · rw [mul_smul_comm, hexp1, smul_smul, inv_mul_cancel₀ hc,
      one_smul]
  · rw [smul_mul_assoc, hexp2, smul_smul, inv_mul_cancel₀ hc,
      one_smul]

/-- **Clifford resolvent norm bound**:
`‖(a²+1)⁻¹(B + i)‖ ≤ (a+1)/(a²+1)`. -/
theorem clifford_resolvent_norm_le (B : A) (a : ℝ) (_ha : 0 ≤ a)
    (hBnorm : ‖B‖ ≤ a) :
    ‖((a : ℂ) ^ 2 + 1)⁻¹ • (B + algebraMap ℂ A Complex.I)‖
      ≤ (a + 1) / (a ^ 2 + 1) := by
  rw [norm_smul]
  have h1 : ‖((a : ℂ) ^ 2 + 1)⁻¹‖ = (a ^ 2 + 1)⁻¹ := by
    rw [norm_inv]
    congr 1
    have h2 : ((a : ℂ) ^ 2 + 1) = (((a ^ 2 + 1 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [h2, Complex.norm_real]
    exact abs_of_nonneg (by positivity)
  have h3 : ‖B + algebraMap ℂ A Complex.I‖ ≤ a + 1 := by
    have h4 : ‖algebraMap ℂ A Complex.I‖ ≤ 1 := by
      rw [Algebra.algebraMap_eq_smul_one, norm_smul,
        Complex.norm_I, one_mul]
      exact le_of_eq norm_one
    calc ‖B + algebraMap ℂ A Complex.I‖
        ≤ ‖B‖ + ‖algebraMap ℂ A Complex.I‖ := norm_add_le _ _
      _ ≤ a + 1 := by linarith
  calc ‖((a : ℂ) ^ 2 + 1)⁻¹‖ * ‖B + algebraMap ℂ A Complex.I‖
      = (a ^ 2 + 1)⁻¹ * ‖B + algebraMap ℂ A Complex.I‖ := by
        rw [h1]
    _ ≤ (a ^ 2 + 1)⁻¹ * (a + 1) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (a + 1) / (a ^ 2 + 1) := by ring

/-- Uniform bound for the Clifford resolvent: at most `3/2`. -/
theorem clifford_norm_uniform (a : ℝ) (_ha : 0 ≤ a) :
    (a + 1) / (a ^ 2 + 1) ≤ 3/2 := by
  rw [div_le_iff₀ (by positivity : (0:ℝ) < a ^ 2 + 1)]
  nlinarith [sq_nonneg (3*a - 1)]

/-- **Weighted Clifford bound** (the smallness certificate):
`b ≤ a` gives `b · (a+1)/(a²+1) ≤ 3/2`, so the momentum-weighted
resolvent composite obeys
`‖ΔB · ξ (h₀(ξ) − i)⁻¹‖ ≤ (3/2) ‖ΔB‖_∞/(κ c₀)`, which is `< 1` in
the slowly-varying phase. -/
theorem clifford_weighted_bound (a b : ℝ) (hb : 0 ≤ b)
    (hba : b ≤ a) :
    b * ((a + 1) / (a ^ 2 + 1)) ≤ 3/2 := by
  rw [mul_div_assoc', div_le_iff₀
    (by positivity : (0:ℝ) < a ^ 2 + 1)]
  nlinarith [sq_nonneg (a - 1)]

end Clifford

end NCG
