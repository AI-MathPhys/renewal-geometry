/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Port-relative reachability forces colour (`cor:reciprocal-return-force`)

Finite-dimensional margin corollary of the reciprocal-return mass identity
`eq:reciprocal-return-mass` of `thm:reciprocal-return` in the spacetime/gauge
duality manuscript.

Setting.  A route bank with an irreducible unitary `v : G → U(V)` of dimension
`d = |V|`, a mediator `E = V ⊗ N`, an entry operator `A : T → E`, a reverse-exit
operator `B : H_priv → E`, a self-adjoint mediator Hamiltonian `h` on `N`, and
the returned words `r_{g,k} = B^* (v_g ⊗ h^k) A`.  With
`ρ_A = Tr_V(A A^*)`, `ρ_B = Tr_V(B B^*)`, `W_A = ∑_{k<n} h^k ρ_A h^k` and
`m_ret = |G|⁻¹ ∑_g ∑_{k<n} ‖r_{g,k}‖²_HS`, the corollary states that
`W_A ⪰ κ I` with `κ > 0` forces

* `m_ret ≥ (κ/d) ‖B‖²_HS`,
* `max_{g,k<n} ‖r_{g,k}‖²_HS ≥ κ/(d n) ‖B‖²_HS`,

so that `B ≠ 0` yields a strictly positive reciprocal-return mass.

The boxed mass identity `m_ret = d⁻¹ Tr(ρ_B W_A)` of `thm:reciprocal-return`
enters as an explicit hypothesis (`hmass`), exactly as the manuscript's proof
of the corollary uses it; everything else (partial-trace Gram positivity,
trace monotonicity under `W_A ⪰ κ I`, and the average-to-maximum step) is
proved here.  Scoped hypotheses: all index types are finite, `V` and `G` are
nonempty (`V` carries a nonzero irreducible representation and `G` is a group),
and the horizon `n` is positive.

## Main declarations

* `RenewalGeometry.ReciprocalReturn.hsNormSq`, `partialGram`, `returnWord`,
  `returnMass`, `returnWeight`: the manuscript's objects;
* `RenewalGeometry.ReciprocalReturn.trace_partialGram_mul_ge`: trace
  monotonicity `Tr(ρ_B W) ≥ κ Tr ρ_B` for `W ⪰ κ I`;
* `RenewalGeometry.ReciprocalReturn.reciprocalReturn_margin`: the corollary.
-/

open Matrix Kronecker
open scoped ComplexOrder

namespace RenewalGeometry
namespace ReciprocalReturn

noncomputable section

section HilbertSchmidt

variable {p q : Type*} [Fintype p] [Fintype q]

/-- Squared Hilbert–Schmidt norm `‖X‖²_HS = ∑ |X_{ij}|²` (real-valued). -/
def hsNormSq (X : Matrix p q ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (X i j)

theorem hsNormSq_nonneg (X : Matrix p q ℂ) : 0 ≤ hsNormSq X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem hsNormSq_eq_zero_iff (X : Matrix p q ℂ) : hsNormSq X = 0 ↔ X = 0 := by
  constructor
  · intro h
    unfold hsNormSq at h
    ext i j
    have hi : ∑ j, Complex.normSq (X i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)).mp h i
        (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Complex.normSq_nonneg _)).mp hi j (Finset.mem_univ j)
    simpa [Complex.normSq_eq_zero] using hij
  · rintro rfl
    simp [hsNormSq]

theorem hsNormSq_pos_of_ne_zero {X : Matrix p q ℂ} (hX : X ≠ 0) : 0 < hsNormSq X :=
  lt_of_le_of_ne (hsNormSq_nonneg X)
    (fun h => hX ((hsNormSq_eq_zero_iff X).mp h.symm))

/-- `Tr(X^* X) = ‖X‖²_HS`. -/
theorem trace_conjTranspose_mul_self_eq_hsNormSq (X : Matrix p q ℂ) :
    (Xᴴ * X).trace = (hsNormSq X : ℂ) := by
  unfold hsNormSq
  push_cast
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self]
  exact Finset.sum_comm

end HilbertSchmidt

section RouteBank

variable {V N T H G : Type*} [Fintype V] [Fintype N] [Fintype T] [Fintype H]
  [Fintype G]

/-- The `v`-th row slice of an operator into the mediator `E = V ⊗ N`. -/
def slice (v : V) (B : Matrix (V × N) H ℂ) : Matrix N H ℂ :=
  Matrix.of fun a x => B (v, a) x

/-- The partial trace `Tr_V (B B^*)` over the representation factor, written as
the sum of the slice Gram matrices `∑_v B_v B_v^*`. -/
def partialGram (B : Matrix (V × N) H ℂ) : Matrix N N ℂ :=
  ∑ v, slice v B * (slice v B)ᴴ

theorem partialGram_posSemidef (B : Matrix (V × N) H ℂ) :
    (partialGram B).PosSemidef := by
  unfold partialGram
  refine Finset.sum_induction _ (fun M : Matrix N N ℂ => M.PosSemidef)
    (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
  intro v _
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- `Tr ρ_B = ‖B‖²_HS`. -/
theorem trace_partialGram (B : Matrix (V × N) H ℂ) :
    (partialGram B).trace = (hsNormSq B : ℂ) := by
  unfold partialGram hsNormSq
  rw [Matrix.trace_sum]
  push_cast
  rw [Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, slice, Matrix.of_apply, Complex.star_def,
    Complex.mul_conj]

/-- Trace monotonicity against a partial-trace Gram: if `W ⪰ κ I` then
`Tr(ρ_B W) ≥ κ Tr ρ_B`. -/
theorem trace_partialGram_mul_ge [DecidableEq N] (B : Matrix (V × N) H ℂ) (W : Matrix N N ℂ)
    (κ : ℝ) (hW : (W - (κ : ℂ) • 1).PosSemidef) :
    (κ : ℂ) * (partialGram B).trace ≤ (partialGram B * W).trace := by
  have hkey : 0 ≤ (partialGram B * (W - (κ : ℂ) • 1)).trace := by
    unfold partialGram
    rw [Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_nonneg fun v _ => ?_
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    exact (hW.conjTranspose_mul_mul_same (slice v B)).trace_nonneg
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_eq_mul, sub_nonneg] at hkey
  exact hkey

variable [DecidableEq V] [DecidableEq N]
variable (v : G → Matrix V V ℂ) (h : Matrix N N ℂ) (A : Matrix (V × N) T ℂ)
  (B : Matrix (V × N) H ℂ)

/-- The returned word `r_{g,k} = B^* (v_g ⊗ h^k) A : T → H_priv`.  (Mathlib's `⊗ₖ`
binds tighter than `^`, so the inner parentheses around `h ^ k` are essential.) -/
def returnWord (g : G) (k : ℕ) : Matrix H T ℂ :=
  Bᴴ * (v g ⊗ₖ (h ^ k)) * A

/-- The reciprocal-return mass
`m_ret = |G|⁻¹ ∑_g ∑_{k<n} ‖r_{g,k}‖²_HS`. -/
def returnMass (n : ℕ) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g, ∑ k : Fin n, hsNormSq (returnWord v h A B g k)

/-- The cyclic return weight `W_A = ∑_{k<n} h^k ρ_A h^k`. -/
def returnWeight (n : ℕ) : Matrix N N ℂ :=
  ∑ k : Fin n, h ^ (k : ℕ) * partialGram A * h ^ (k : ℕ)

/-- **`cor:reciprocal-return-force`** (port-relative reachability forces
colour).  Given the mass identity `m_ret = d⁻¹ Tr(ρ_B W_A)` of
`thm:reciprocal-return` and `W_A ⪰ κ I` with `κ > 0`:
`m_ret ≥ (κ/d) ‖B‖²_HS`, some returned word satisfies
`‖r_{g,k}‖²_HS ≥ κ/(d n) ‖B‖²_HS` (the maximum bound), and `B ≠ 0` forces
`m_ret > 0`. -/
theorem reciprocalReturn_margin [Nonempty V] [Nonempty G] (n : ℕ) (hn : 0 < n)
    (κ : ℝ) (hκ : 0 < κ)
    (hmass : (returnMass v h A B n : ℂ) =
      (Fintype.card V : ℂ)⁻¹ * (partialGram B * returnWeight h A n).trace)
    (hW : (returnWeight h A n - (κ : ℂ) • 1).PosSemidef) :
    κ / Fintype.card V * hsNormSq B ≤ returnMass v h A B n ∧
    (∃ g : G, ∃ k : Fin n,
      κ / (Fintype.card V * n) * hsNormSq B ≤ hsNormSq (returnWord v h A B g k)) ∧
    (B ≠ 0 → 0 < returnMass v h A B n) := by
  have hd : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  have hdC : (Fintype.card V : ℂ) ≠ 0 := by
    exact_mod_cast hd.ne'
  -- the trace inequality, transported to the reals
  have htr := trace_partialGram_mul_ge B (returnWeight h A n) κ hW
  rw [trace_partialGram] at htr
  have hτ : (partialGram B * returnWeight h A n).trace =
      ((Fintype.card V * returnMass v h A B n : ℝ) : ℂ) := by
    push_cast
    rw [hmass, ← mul_assoc, mul_inv_cancel₀ hdC, one_mul]
  rw [hτ] at htr
  have hreal : κ * hsNormSq B ≤ Fintype.card V * returnMass v h A B n := by
    have := htr
    rw [show (κ : ℂ) * (hsNormSq B : ℂ) = ((κ * hsNormSq B : ℝ) : ℂ) by push_cast; rfl]
      at this
    exact Complex.real_le_real.mp this
  have hfirst : κ / Fintype.card V * hsNormSq B ≤ returnMass v h A B n := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hd, mul_comm (returnMass v h A B n)]
    exact hreal
  refine ⟨hfirst, ?_, ?_⟩
  · -- average-to-maximum
    have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsum : ∑ p : G × Fin n, returnMass v h A B n / n ≤
        ∑ p : G × Fin n, hsNormSq (returnWord v h A B p.1 p.2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Fintype.sum_prod_type]
      have hexp : ∑ g : G, ∑ k : Fin n, hsNormSq (returnWord v h A B g k) =
          Fintype.card G * returnMass v h A B n := by
        unfold returnMass
        rw [← mul_assoc, mul_inv_cancel₀ hG.ne', one_mul]
      rw [hexp]
      apply le_of_eq
      push_cast
      field_simp
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨⟨g, k⟩, -, hp⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
    refine ⟨g, k, le_trans ?_ hp⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hd hnR)]
    calc κ * hsNormSq B = (κ / Fintype.card V * hsNormSq B) * Fintype.card V := by
          field_simp
      _ ≤ returnMass v h A B n * Fintype.card V :=
          mul_le_mul_of_nonneg_right hfirst hd.le
      _ = returnMass v h A B n / n * (Fintype.card V * n) := by
          field_simp
  · intro hB
    exact lt_of_lt_of_le
      (mul_pos (div_pos hκ hd) (hsNormSq_pos_of_ne_zero hB)) hfirst

end RouteBank

end

end ReciprocalReturn
end RenewalGeometry
