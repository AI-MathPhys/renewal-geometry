/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.ReciprocalReturnMargin

/-!
# The finite reciprocal-return criterion: the mass identity

`thm:reciprocal-return` of the spacetime–gauge duality paper (boxed identity
`eq:reciprocal-return-mass`, the equivalences (ii) ⇔ (iii), and clause (iv) in
matrix form), and the unconditional form of `cor:reciprocal-return-force`.

Setting: a finite group `G` with a unitary representation `v : G → U(V)` that is
irreducible in the Schur form (every matrix commuting with all `v g` is scalar), a
mediator `E = V ⊗ N`, an entry operator `A : T → E`, a reverse-exit operator
`B : H_priv → E`, a self-adjoint mediator Hamiltonian `h` on `N`, and the returned
words `r_{g,k} = B^* (v_g ⊗ h^k) A` (`word`, definitionally equal to
`ReciprocalReturnMargin.returnWord`, see `word_eq_returnWord`; Mathlib's `⊗ₖ` binds
tighter than `^`, so the parenthesisation `v g ⊗ₖ (h ^ k)` is essential in both).

* `schur_twirl`: Schur averaging on `V`, `∑_g v_g Y v_g^* = (|G|/d) Tr(Y) · I_V`;
* `kronecker_twirl`: its `V ⊗ N` form, `∑_g (v_g ⊗ I) Z (v_g ⊗ I)^* = (|G|/d) · I ⊗ Tr_V Z`;
* `mass_eq` (**the boxed mass identity**): `m_ret = d⁻¹ Tr(ρ_B W_A)` with
  `ρ_A = Tr_V(AA^*)`, `ρ_B = Tr_V(BB^*)`, `W_A = ∑_{k<n} h^k ρ_A h^k`
  (`ReciprocalReturn.partialGram`, `ReciprocalReturn.returnWeight`);
* `mass_nonneg`, `mass_pos_iff`: `m_ret ≥ 0` and (ii) ⇔ (iii);
* `mass_eq_zero_iff`: `m_ret = 0` iff `ρ_B h^k ρ_A = 0` for all `k < n`, i.e. iff
  the range of `ρ_B` is orthogonal to `h^k Ran ρ_A` for every `k < n` (the
  finite-horizon form of clause (iv));
* `reciprocalReturn_force`: `cor:reciprocal-return-force` with the mass identity
  discharged.

Scoped hypotheses: all index types finite, `V` nonempty, `n > 0` for the
corollary; irreducibility of `v` is taken in the (equivalent, by Schur's lemma)
commutant form `hirr`.  Not formalised here: the route-bank clause (i), the
reducing projection `T ⊕ (V ⊗ Ran W_A)` for longer excursions, the Cayley–Hamilton
extension of (iv) beyond the horizon `k < n`, and the word-length bound `n + 1`.
-/

open Matrix Kronecker
open scoped ComplexOrder

namespace RenewalGeometry
namespace ReciprocalReturnMass

open ReciprocalReturn

noncomputable section

section Blocks

variable {V N : Type*} [Fintype V] [Fintype N] [DecidableEq V] [DecidableEq N]

/-- The `(a, b)` block `Z_{ab} ∈ M_V` of an operator `Z` on `V ⊗ N`. -/
def blk (Z : Matrix (V × N) (V × N) ℂ) (a b : N) : Matrix V V ℂ :=
  Matrix.of fun x y => Z (x, a) (y, b)

/-- The partial trace `Tr_V Z ∈ M_N`. -/
def partialTrace (Z : Matrix (V × N) (V × N) ℂ) : Matrix N N ℂ :=
  Matrix.of fun a b => ∑ x, Z (x, a) (x, b)

theorem partialTrace_apply (Z : Matrix (V × N) (V × N) ℂ) (a b : N) :
    partialTrace Z a b = (blk Z a b).trace := by
  simp [partialTrace, blk, Matrix.trace]

/-- `ρ_A = Tr_V (A A^*)`: the slice Gram of `ReciprocalReturnMargin` is the partial
trace of the Gram operator. -/
theorem partialGram_eq_partialTrace {T : Type*} [Fintype T] (A : Matrix (V × N) T ℂ) :
    partialGram A = partialTrace (A * Aᴴ) := by
  ext a b
  simp only [partialGram, partialTrace, slice, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.of_apply, Matrix.conjTranspose_apply]

theorem kronecker_one_mul_apply (U : Matrix V V ℂ) (Z : Matrix (V × N) (V × N) ℂ)
    (x y : V) (a b : N) :
    ((U ⊗ₖ (1 : Matrix N N ℂ)) * Z) (x, a) (y, b) = ∑ x', U x x' * Z (x', a) (y, b) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq]

theorem mul_kronecker_one_apply (U : Matrix V V ℂ) (Z : Matrix (V × N) (V × N) ℂ)
    (x y : V) (a b : N) :
    (Z * (U ⊗ₖ (1 : Matrix N N ℂ))) (x, a) (y, b) = ∑ y', Z (x, a) (y', b) * U y' y := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

theorem one_kronecker_mul_apply (M : Matrix N N ℂ) (Z : Matrix (V × N) (V × N) ℂ)
    (x y : V) (a b : N) :
    (((1 : Matrix V V ℂ) ⊗ₖ M) * Z) (x, a) (y, b) = ∑ c, M a c * Z (x, c) (y, b) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [kronecker_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq]

theorem mul_one_kronecker_apply (M : Matrix N N ℂ) (Z : Matrix (V × N) (V × N) ℂ)
    (x y : V) (a b : N) :
    (Z * ((1 : Matrix V V ℂ) ⊗ₖ M)) (x, a) (y, b) = ∑ c, Z (x, a) (y, c) * M c b := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq']

theorem blk_kronecker_mul (U : Matrix V V ℂ) (Z : Matrix (V × N) (V × N) ℂ) (a b : N) :
    blk ((U ⊗ₖ (1 : Matrix N N ℂ)) * Z) a b = U * blk Z a b := by
  ext x y
  rw [blk, Matrix.of_apply, kronecker_one_mul_apply, Matrix.mul_apply]
  simp [blk]

theorem blk_mul_kronecker (U : Matrix V V ℂ) (Z : Matrix (V × N) (V × N) ℂ) (a b : N) :
    blk (Z * (U ⊗ₖ (1 : Matrix N N ℂ))) a b = blk Z a b * U := by
  ext x y
  rw [blk, Matrix.of_apply, mul_kronecker_one_apply, Matrix.mul_apply]
  simp [blk]

theorem partialTrace_one_kronecker_mul (M : Matrix N N ℂ) (Z : Matrix (V × N) (V × N) ℂ) :
    partialTrace (((1 : Matrix V V ℂ) ⊗ₖ M) * Z) = M * partialTrace Z := by
  ext a b
  rw [Matrix.mul_apply]
  unfold partialTrace
  simp only [Matrix.of_apply]
  simp_rw [one_kronecker_mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

theorem partialTrace_mul_one_kronecker (M : Matrix N N ℂ) (Z : Matrix (V × N) (V × N) ℂ) :
    partialTrace (Z * ((1 : Matrix V V ℂ) ⊗ₖ M)) = partialTrace Z * M := by
  ext a b
  rw [Matrix.mul_apply]
  unfold partialTrace
  simp only [Matrix.of_apply]
  simp_rw [mul_one_kronecker_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul]

/-- `Tr((I ⊗ M) W) = Tr(M · Tr_V W)`. -/
theorem trace_one_kronecker_mul (M : Matrix N N ℂ) (W : Matrix (V × N) (V × N) ℂ) :
    (((1 : Matrix V V ℂ) ⊗ₖ M) * W).trace = (M * partialTrace W).trace := by
  have := congrArg Matrix.trace (partialTrace_one_kronecker_mul M W)
  rw [← this]
  simp only [Matrix.trace, Matrix.diag, partialTrace, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

end Blocks

section Twirl

variable {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] [Group G]

/-- **Schur averaging on the irreducible factor.**  For a unitary representation
`v` of the finite group `G` whose commutant is scalar,
`∑_g v_g Y v_g^* = (|G|/d) Tr(Y) · I`. -/
theorem schur_twirl [Nonempty V] (v : G → Matrix V V ℂ)
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (Y : Matrix V V ℂ) :
    ∑ g, v g * Y * (v g)ᴴ = ((Fintype.card G : ℂ) / Fintype.card V * Y.trace) • 1 := by
  have hinv : ∀ g, (v g)ᴴ = v g⁻¹ := fun g => by
    calc (v g)ᴴ = (v g)ᴴ * (v g * v g⁻¹) := by
          rw [← hmul, mul_inv_cancel, hone, Matrix.mul_one]
      _ = v g⁻¹ := by rw [← Matrix.mul_assoc, hunit, Matrix.one_mul]
  set S := ∑ g, v g * Y * (v g)ᴴ with hS
  have hcomm : ∀ g', S * v g' = v g' * S := by
    intro g'
    rw [hS, Finset.sum_mul, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft g')]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Equiv.coe_mulLeft]
    rw [Matrix.mul_assoc (v (g' * k) * Y), hinv, ← hmul,
      show (g' * k)⁻¹ * g' = k⁻¹ by group, ← hinv, hmul]
    simp only [Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := hirr S hcomm
  have htr : S.trace = (Fintype.card G : ℂ) * Y.trace := by
    rw [hS, Matrix.trace_sum]
    have : ∀ g, (v g * Y * (v g)ᴴ).trace = Y.trace := fun g => by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
    simp [this]
  rw [hc, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at htr
  have hV : (Fintype.card V : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hc]
  congr 1
  rw [div_mul_eq_mul_div, eq_div_iff hV]
  exact htr

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **Schur averaging on `V ⊗ N`**: `∑_g (v_g ⊗ I) Z (v_g ⊗ I)^* = (|G|/d) · I ⊗ Tr_V Z`. -/
theorem kronecker_twirl [Nonempty V] (v : G → Matrix V V ℂ)
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (Z : Matrix (V × N) (V × N) ℂ) :
    ∑ g, (v g ⊗ₖ (1 : Matrix N N ℂ)) * Z * (v g ⊗ₖ (1 : Matrix N N ℂ))ᴴ =
      ((Fintype.card G : ℂ) / Fintype.card V) • ((1 : Matrix V V ℂ) ⊗ₖ partialTrace Z) := by
  ext ⟨x, a⟩ ⟨y, b⟩
  have hblk : ∀ g, ((v g ⊗ₖ (1 : Matrix N N ℂ)) * Z * (v g ⊗ₖ (1 : Matrix N N ℂ))ᴴ) (x, a) (y, b)
      = (v g * blk Z a b * (v g)ᴴ) x y := by
    intro g
    have hb : blk ((v g ⊗ₖ (1 : Matrix N N ℂ)) * Z * (v g ⊗ₖ (1 : Matrix N N ℂ))ᴴ) a b =
        v g * blk Z a b * (v g)ᴴ := by
      rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, blk_mul_kronecker,
        blk_kronecker_mul]
    have := congrFun (congrFun hb x) y
    simpa [blk] using this
  rw [Matrix.sum_apply]
  simp only [hblk]
  rw [← Matrix.sum_apply, schur_twirl v hmul hone hunit hirr, Matrix.smul_apply, Matrix.smul_apply,
    kronecker_apply, ← partialTrace_apply, smul_eq_mul, smul_eq_mul]
  ring

end Twirl

section Mass

variable {V N T H G : Type*} [Fintype V] [Fintype N] [Fintype T] [Fintype H] [Fintype G]
  [DecidableEq V] [DecidableEq N] [Group G]

variable (v : G → Matrix V V ℂ) (h : Matrix N N ℂ) (A : Matrix (V × N) T ℂ)
  (B : Matrix (V × N) H ℂ)

/-- The returned word `r_{g,k} = B^* (v_g ⊗ h^k) A : T → H_priv`. -/
def word (g : G) (k : ℕ) : Matrix H T ℂ :=
  Bᴴ * (v g ⊗ₖ (h ^ k)) * A

/-- The reciprocal-return mass `m_ret = |G|⁻¹ ∑_g ∑_{k<n} ‖r_{g,k}‖²_HS`. -/
def mass (n : ℕ) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g, ∑ k : Fin n, hsNormSq (word v h A B g k)

/-- Cyclic rearrangement of the returned-word Gram trace. -/
theorem trace_word (K : Matrix (V × N) (V × N) ℂ) :
    (Aᴴ * (Kᴴ * B) * (Bᴴ * K * A)).trace = (K * (A * Aᴴ) * Kᴴ * (B * Bᴴ)).trace := by
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

/-- The per-`k` Schur average of the returned-word masses:
`∑_g ‖r_{g,k}‖²_HS = (|G|/d) Tr(ρ_B h^k ρ_A h^k)`. -/
theorem sum_hsNormSq_word [Nonempty V]
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (hh : hᴴ = h) (k : ℕ) :
    ∑ g, (hsNormSq (word v h A B g k) : ℂ) =
      (Fintype.card G : ℂ) / Fintype.card V *
        (partialGram B * (h ^ k * partialGram A * h ^ k)).trace := by
  set Zk : Matrix (V × N) (V × N) ℂ :=
    ((1 : Matrix V V ℂ) ⊗ₖ (h ^ k)) * (A * Aᴴ) * ((1 : Matrix V V ℂ) ⊗ₖ (h ^ k))ᴴ with hZk
  have hterm : ∀ g, (hsNormSq (word v h A B g k) : ℂ) =
      ((v g ⊗ₖ (1 : Matrix N N ℂ)) * Zk * (v g ⊗ₖ (1 : Matrix N N ℂ))ᴴ * (B * Bᴴ)).trace := by
    intro g
    rw [← trace_conjTranspose_mul_self_eq_hsNormSq, word, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, trace_word]
    have hK : v g ⊗ₖ (h ^ k) = (v g ⊗ₖ (1 : Matrix N N ℂ)) * ((1 : Matrix V V ℂ) ⊗ₖ (h ^ k)) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    rw [hK, Matrix.conjTranspose_mul, hZk]
    simp only [Matrix.mul_assoc]
  simp only [hterm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, kronecker_twirl v hmul hone hunit hirr,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_one_kronecker_mul, hZk,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, partialTrace_mul_one_kronecker,
    partialTrace_one_kronecker_mul, Matrix.conjTranspose_pow, hh,
    ← partialGram_eq_partialTrace, ← partialGram_eq_partialTrace, Matrix.trace_mul_comm]

/-- **The boxed mass identity `eq:reciprocal-return-mass`**:
`m_ret = d⁻¹ Tr(ρ_B W_A)`. -/
theorem mass_eq [Nonempty V]
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (hh : hᴴ = h) (n : ℕ) :
    (mass v h A B n : ℂ) =
      (Fintype.card V : ℂ)⁻¹ * (partialGram B * returnWeight h A n).trace := by
  haveI : Nonempty G := ⟨1⟩
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hV : (Fintype.card V : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold mass
  push_cast
  rw [Finset.sum_comm]
  simp only [sum_hsNormSq_word v h A B hmul hone hunit hirr hh]
  rw [← Finset.mul_sum, returnWeight, Matrix.mul_sum, Matrix.trace_sum, ← mul_assoc]
  congr 1
  field_simp

/-- `m_ret ≥ 0`. -/
theorem mass_nonneg (n : ℕ) : 0 ≤ mass v h A B n := by
  unfold mass
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hsNormSq_nonneg _

/-- **(ii) ⇔ (iii)**: `m_ret > 0` iff some returned word `r_{g,k}` (`k < n`) is
nonzero. -/
theorem mass_pos_iff (n : ℕ) :
    0 < mass v h A B n ↔ ∃ g : G, ∃ k : Fin n, word v h A B g k ≠ 0 := by
  haveI : Nonempty G := ⟨1⟩
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  unfold mass
  rw [mul_pos_iff_of_pos_left (inv_pos.mpr hG)]
  constructor
  · intro hpos
    by_contra hall
    push_neg at hall
    have : ∑ g, ∑ k : Fin n, hsNormSq (word v h A B g k) = 0 :=
      Finset.sum_eq_zero fun g _ => Finset.sum_eq_zero fun k _ => by
        rw [hall g k]; simp [hsNormSq]
    rw [this] at hpos
    exact lt_irrefl _ hpos
  · rintro ⟨g, k, hgk⟩
    refine lt_of_lt_of_le (hsNormSq_pos_of_ne_zero hgk) ?_
    refine le_trans (Finset.single_le_sum (f := fun k : Fin n => hsNormSq (word v h A B g k))
      (fun _ _ => hsNormSq_nonneg _) (Finset.mem_univ k)) ?_
    exact Finset.single_le_sum (f := fun g => ∑ k : Fin n, hsNormSq (word v h A B g k))
      (fun _ _ => Finset.sum_nonneg fun _ _ => hsNormSq_nonneg _) (Finset.mem_univ g)

/-- **`cor:reciprocal-return-force`, unconditional form.**  If `W_A ⪰ κ I` with
`κ > 0` then `m_ret ≥ (κ/d) ‖B‖²_HS`, some returned word has
`‖r_{g,k}‖²_HS ≥ κ/(d n) ‖B‖²_HS`, and `B ≠ 0` forces `m_ret > 0`. -/
theorem reciprocalReturn_force [Nonempty V]
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (hh : hᴴ = h) (n : ℕ) (hn : 0 < n) (κ : ℝ) (hκ : 0 < κ)
    (hW : (returnWeight h A n - (κ : ℂ) • 1).PosSemidef) :
    κ / Fintype.card V * hsNormSq B ≤ mass v h A B n ∧
    (∃ g : G, ∃ k : Fin n,
      κ / (Fintype.card V * n) * hsNormSq B ≤ hsNormSq (word v h A B g k)) ∧
    (B ≠ 0 → 0 < mass v h A B n) := by
  haveI : Nonempty G := ⟨1⟩
  have hmass := mass_eq v h A B hmul hone hunit hirr hh n
  have hd : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hdC : (Fintype.card V : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  -- the trace inequality, transported to the reals
  have htr := trace_partialGram_mul_ge B (returnWeight h A n) κ hW
  rw [trace_partialGram] at htr
  have hτ : (partialGram B * returnWeight h A n).trace =
      ((Fintype.card V * mass v h A B n : ℝ) : ℂ) := by
    push_cast
    rw [hmass, ← mul_assoc, mul_inv_cancel₀ hdC, one_mul]
  rw [hτ] at htr
  have hreal : κ * hsNormSq B ≤ Fintype.card V * mass v h A B n := by
    have := htr
    rw [show (κ : ℂ) * (hsNormSq B : ℂ) = ((κ * hsNormSq B : ℝ) : ℂ) by push_cast; rfl]
      at this
    exact Complex.real_le_real.mp this
  have hfirst : κ / Fintype.card V * hsNormSq B ≤ mass v h A B n := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hd, mul_comm (mass v h A B n)]
    exact hreal
  refine ⟨hfirst, ?_, ?_⟩
  · -- average-to-maximum
    have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsum : ∑ p : G × Fin n, mass v h A B n / n ≤
        ∑ p : G × Fin n, hsNormSq (word v h A B p.1 p.2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Fintype.sum_prod_type]
      have hexp : ∑ g : G, ∑ k : Fin n, hsNormSq (word v h A B g k) =
          Fintype.card G * mass v h A B n := by
        unfold mass
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
      _ ≤ mass v h A B n * Fintype.card V :=
          mul_le_mul_of_nonneg_right hfirst hd.le
      _ = mass v h A B n / n * (Fintype.card V * n) := by
          field_simp
  · intro hB
    exact lt_of_lt_of_le
      (mul_pos (div_pos hκ hd) (hsNormSq_pos_of_ne_zero hB)) hfirst

/-- Unitarity plus the group law identify `v_g^*` with `v_{g⁻¹}`. -/
theorem conjTranspose_eq_inv (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1) (g : G) : (v g)ᴴ = v g⁻¹ := by
  calc (v g)ᴴ = (v g)ᴴ * (v g * v g⁻¹) := by
        rw [← hmul, mul_inv_cancel, hone, Matrix.mul_one]
    _ = v g⁻¹ := by rw [← Matrix.mul_assoc, hunit, Matrix.one_mul]

/-- The reverse twirl `∑_g (v_g ⊗ I)^* Z (v_g ⊗ I) = (|G|/d) · I ⊗ Tr_V Z`. -/
theorem kronecker_twirl' [Nonempty V]
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (Z : Matrix (V × N) (V × N) ℂ) :
    ∑ g, (v g ⊗ₖ (1 : Matrix N N ℂ))ᴴ * Z * (v g ⊗ₖ (1 : Matrix N N ℂ)) =
      ((Fintype.card G : ℂ) / Fintype.card V) • ((1 : Matrix V V ℂ) ⊗ₖ partialTrace Z) := by
  rw [← kronecker_twirl v hmul hone hunit hirr Z, ← Equiv.sum_comp (Equiv.inv G)]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.inv_apply, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    conjTranspose_eq_inv v hmul hone hunit, inv_inv]

/-- **Clause (iv), finite-horizon matrix form.**  `m_ret = 0` iff
`ρ_B h^k ρ_A = 0` for every `k < n`, i.e. iff `Ran ρ_B ⊥ h^k Ran ρ_A` for all
`k < n` (the `h`-cyclic multiplicity spaces are orthogonal at horizon `n`). -/
theorem mass_eq_zero_iff [Nonempty V]
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (hh : hᴴ = h) (n : ℕ) :
    mass v h A B n = 0 ↔ ∀ k : Fin n, partialGram B * h ^ (k : ℕ) * partialGram A = 0 := by
  haveI : Nonempty G := ⟨1⟩
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hV : (Fintype.card V : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hzero : mass v h A B n = 0 ↔ ∀ g : G, ∀ k : Fin n, word v h A B g k = 0 := by
    have h1 := mass_pos_iff v h A B n
    have h2 := mass_nonneg v h A B n
    constructor
    · intro h0 g k
      by_contra hc
      have := h1.mpr ⟨g, k, hc⟩
      rw [h0] at this
      exact lt_irrefl _ this
    · intro hall
      by_contra hne
      obtain ⟨g, k, hgk⟩ := h1.mp (lt_of_le_of_ne h2 (Ne.symm hne))
      exact hgk (hall g k)
  constructor
  · intro h0 k
    have hall := hzero.mp h0
    -- `(I ⊗ ρ_B h^k) A = 0` from the reverse twirl of `B B^*`
    have hsum : (∑ g, (v g ⊗ₖ (1 : Matrix N N ℂ))ᴴ * (B * Bᴴ) * (v g ⊗ₖ (1 : Matrix N N ℂ))) *
        (((1 : Matrix V V ℂ) ⊗ₖ (h ^ (k : ℕ))) * A) = 0 := by
      rw [Matrix.sum_mul]
      refine Finset.sum_eq_zero fun g _ => ?_
      have hw := hall g k
      rw [word] at hw
      have hK : v g ⊗ₖ (h ^ (k : ℕ)) =
          (v g ⊗ₖ (1 : Matrix N N ℂ)) * ((1 : Matrix V V ℂ) ⊗ₖ (h ^ (k : ℕ))) := by
        rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
      rw [hK] at hw
      calc (v g ⊗ₖ (1 : Matrix N N ℂ))ᴴ * (B * Bᴴ) * (v g ⊗ₖ (1 : Matrix N N ℂ)) *
            (((1 : Matrix V V ℂ) ⊗ₖ (h ^ (k : ℕ))) * A)
          = (v g ⊗ₖ (1 : Matrix N N ℂ))ᴴ * B *
            (Bᴴ * ((v g ⊗ₖ (1 : Matrix N N ℂ)) * ((1 : Matrix V V ℂ) ⊗ₖ (h ^ (k : ℕ)))) * A) := by
              simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hw, Matrix.mul_zero]
    rw [kronecker_twirl' v hmul hone hunit hirr, Matrix.smul_mul,
      ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      ← partialGram_eq_partialTrace] at hsum
    have hdiv : (Fintype.card G : ℂ) / Fintype.card V ≠ 0 := div_ne_zero hG hV
    rw [smul_eq_zero, or_iff_right hdiv] at hsum
    -- multiply by `A^*` and take the partial trace
    have := congrArg (fun X => partialTrace (X * Aᴴ)) hsum
    simp only [Matrix.zero_mul] at this
    rw [Matrix.mul_assoc, partialTrace_one_kronecker_mul, ← partialGram_eq_partialTrace] at this
    have h0 : partialTrace (0 : Matrix (V × N) (V × N) ℂ) = 0 := by
      ext a b; simp [partialTrace]
    rw [h0] at this
    exact this
  · intro hall
    have hmass := mass_eq v h A B hmul hone hunit hirr hh n
    have htr : (partialGram B * returnWeight h A n).trace = 0 := by
      rw [returnWeight, Matrix.mul_sum, Matrix.trace_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hall k, Matrix.zero_mul, Matrix.trace_zero]
    rw [htr, mul_zero] at hmass
    exact hzero.mpr (hzero.mp (by exact_mod_cast hmass))

/-- The words of this file coincide with `ReciprocalReturnMargin.returnWord`, so the
conditional margin `ReciprocalReturn.reciprocalReturn_margin` and the unconditional
`reciprocalReturn_force` speak about the same objects. -/
theorem word_eq_returnWord (g : G) (k : ℕ) :
    word v h A B g k = returnWord v h A B g k := rfl

/-- `mass` coincides with `ReciprocalReturnMargin.returnMass`. -/
theorem mass_eq_returnMass (n : ℕ) : mass v h A B n = returnMass v h A B n := rfl

end Mass

end

end ReciprocalReturnMass
end RenewalGeometry
