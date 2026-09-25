/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.ReciprocalReturnMassExact

/-!
# All-excursion return alternative: the route-bank stopping projection

`prop:all-excursion-return` of the spacetime–gauge duality paper (the reducing
projection of `thm:reciprocal-return`).

Setting (`thm:reciprocal-return`): the carrier `T ⊕ H_priv ⊕ (V ⊗ N)` (`Carrier`), the
declared reciprocal route bank consisting of the covariant entries
`A_g = (v_g ⊗ I) A : T → V ⊗ N` (`entryGen`), the reverse exits
`B_h^* = B^* (v_h^* ⊗ I) : V ⊗ N → H_priv` (`exitGen`), the mediator dynamics
`D = I_V ⊗ h` (`mediatorGen`), and arbitrary internal operations on the type line `T`
and the private plane `H_priv` (`typeGen`, `privateGen`), together with all adjoints
(`bank`, `starClosed`); the words of the bank are the elements of the multiplicative
monoid they generate (`words`).

For a matrix `P` on `N` (the orthogonal projection onto
`𝒩_A = Span{h^k Ran ρ_A : k < n}` in the manuscript) the stopping projection is
`Q = I_T ⊕ 0_{H_priv} ⊕ (I_V ⊗ P)` (`stopProj`).  We prove:

* partial-trace positivity (`slice_fixed_of_partialGram`, `slice_zero_of_partialGram`):
  if `P` is Hermitian and `P ρ_A = ρ_A` then `(I ⊗ P) A = A` (`Ran A ⊆ V ⊗ Ran P`);
  if `P ρ_B = 0` then `(I ⊗ P) B = 0`;
* `stopProj_commute_bank`: if moreover `P h = h P`, then `Q` commutes with every
  generator of the bank and with its adjoint;
* `corner_eq_zero_of_mem_words`: consequently every word `w` of the bank has
  `p_H w p_T = 0`;
* `all_excursion_return`: the assembled statement.

The four properties of `P` used here are exactly those of the orthogonal projection
`P_{𝒩_A}` when `𝔪_ret = 0`: it is Hermitian; `𝒩_A` is `h`-invariant (Cayley–Hamilton)
and `h` is Hermitian, so `P h = h P`; `Ran ρ_A ⊆ 𝒩_A`; and `𝔪_ret = 0` gives
`Ran ρ_B ⊥ h^k Ran ρ_A` for `k < n` (`ReciprocalReturnMass.mass_eq_zero_iff`), hence
`Ran ρ_B ⊥ 𝒩_A`, i.e. `P ρ_B = 0`.  **Not formalised here**: the construction of
`P_{𝒩_A}` as a matrix, the Cayley–Hamilton invariance of `𝒩_A`, and the derived clause
`𝒩_A ⊥ 𝒩_B`; the statement is therefore conditional on `P` with these four properties.
-/

open Matrix Kronecker

namespace RenewalGeometry
namespace AllExcursion

open ReciprocalReturn

variable {V N T H G : Type*} [Fintype V] [Fintype N] [Fintype T] [Fintype H] [Fintype G]
  [DecidableEq V] [DecidableEq N] [DecidableEq T] [DecidableEq H]

/-- The full carrier `T ⊕ H_priv ⊕ (V ⊗ N)`. -/
abbrev Carrier (T H V N : Type*) := T ⊕ (H ⊕ (V × N))

/-! ### Block embeddings of the route generators -/

/-- An entry operation `T → V ⊗ N` as a block operator on the carrier. -/
def entryGen (M : Matrix (V × N) T ℂ) : Matrix (Carrier T H V N) (Carrier T H V N) ℂ :=
  fromBlocks 0 0 (fromRows 0 M) 0

/-- A reverse-exit operation `V ⊗ N → H_priv` as a block operator on the carrier. -/
def exitGen (M : Matrix H (V × N) ℂ) : Matrix (Carrier T H V N) (Carrier T H V N) ℂ :=
  fromBlocks 0 0 0 (fromBlocks 0 M 0 0)

/-- A mediator operation `V ⊗ N → V ⊗ N` as a block operator on the carrier. -/
def mediatorGen (M : Matrix (V × N) (V × N) ℂ) :
    Matrix (Carrier T H V N) (Carrier T H V N) ℂ :=
  fromBlocks 0 0 0 (fromBlocks 0 0 0 M)

/-- An internal operation on the type line `T`. -/
def typeGen (M : Matrix T T ℂ) : Matrix (Carrier T H V N) (Carrier T H V N) ℂ :=
  fromBlocks M 0 0 0

/-- An internal operation on the private plane `H_priv`. -/
def privateGen (M : Matrix H H ℂ) : Matrix (Carrier T H V N) (Carrier T H V N) ℂ :=
  fromBlocks 0 0 0 (fromBlocks M 0 0 0)

/-- The projection `p_T` onto the type line. -/
def pT : Matrix (Carrier T H V N) (Carrier T H V N) ℂ := fromBlocks 1 0 0 0

/-- The projection `p_H` onto the private plane. -/
def pH : Matrix (Carrier T H V N) (Carrier T H V N) ℂ := fromBlocks 0 0 0 (fromBlocks 1 0 0 0)

/-- The stopping projection `Q = I_T ⊕ 0_{H_priv} ⊕ (I_V ⊗ P)`. -/
def stopProj (P : Matrix N N ℂ) : Matrix (Carrier T H V N) (Carrier T H V N) ℂ :=
  fromBlocks 1 0 0 (fromBlocks 0 0 0 ((1 : Matrix V V ℂ) ⊗ₖ P))

/-- The declared reciprocal route bank: covariant entries `(v_g ⊗ I) A`, reverse exits
`B^* (v_g^* ⊗ I)`, the mediator dynamics `I ⊗ h`, and internal operations on `T` and
`H_priv`. -/
def bank (v : G → Matrix V V ℂ) (h : Matrix N N ℂ) (A : Matrix (V × N) T ℂ)
    (B : Matrix (V × N) H ℂ) : Set (Matrix (Carrier T H V N) (Carrier T H V N) ℂ) :=
  (Set.range fun g => entryGen (H := H) ((v g ⊗ₖ (1 : Matrix N N ℂ)) * A)) ∪
    (Set.range fun g => exitGen (T := T) (Bᴴ * ((v g)ᴴ ⊗ₖ (1 : Matrix N N ℂ)))) ∪
    {mediatorGen (T := T) (H := H) ((1 : Matrix V V ℂ) ⊗ₖ h)} ∪
    Set.range (typeGen (H := H) (V := V) (N := N)) ∪
    Set.range (privateGen (T := T) (V := V) (N := N))

/-- A set of generators together with their adjoints. -/
def starClosed {X : Type*} (S : Set (Matrix X X ℂ)) : Set (Matrix X X ℂ) :=
  S ∪ (fun M => Mᴴ) '' S

/-- The words of a bank: the multiplicative monoid generated by the generators and
their adjoints. -/
def words {X : Type*} [Fintype X] [DecidableEq X] (S : Set (Matrix X X ℂ)) :
    Submonoid (Matrix X X ℂ) :=
  Submonoid.closure (starClosed S)

/-! ### Elementary properties of the stopping projection -/

theorem stopProj_conjTranspose (P : Matrix N N ℂ) (hP : Pᴴ = P) :
    (stopProj (T := T) (H := H) (V := V) P)ᴴ = stopProj P := by
  simp [stopProj, fromBlocks_conjTranspose, Matrix.conjTranspose_kronecker, hP]

theorem stopProj_mul_pT (P : Matrix N N ℂ) :
    stopProj (T := T) (H := H) (V := V) P * pT = pT := by
  simp [stopProj, pT, fromBlocks_multiply]

theorem pH_mul_stopProj (P : Matrix N N ℂ) :
    pH * stopProj (T := T) (H := H) (V := V) P = 0 := by
  simp [stopProj, pH, fromBlocks_multiply]

theorem stopProj_comm_entry (P : Matrix N N ℂ) (M : Matrix (V × N) T ℂ)
    (hM : ((1 : Matrix V V ℂ) ⊗ₖ P) * M = M) :
    stopProj P * entryGen (H := H) M = entryGen M * stopProj P := by
  simp [stopProj, entryGen, fromBlocks_multiply, fromBlocks_mul_fromRows, fromRows_mul, hM]

theorem stopProj_comm_exit (P : Matrix N N ℂ) (M : Matrix H (V × N) ℂ)
    (hM : M * ((1 : Matrix V V ℂ) ⊗ₖ P) = 0) :
    stopProj P * exitGen (T := T) M = exitGen M * stopProj P := by
  simp [stopProj, exitGen, fromBlocks_multiply, hM]

theorem stopProj_comm_mediator (P : Matrix N N ℂ) (M : Matrix (V × N) (V × N) ℂ)
    (hM : ((1 : Matrix V V ℂ) ⊗ₖ P) * M = M * ((1 : Matrix V V ℂ) ⊗ₖ P)) :
    stopProj P * mediatorGen (T := T) (H := H) M = mediatorGen M * stopProj P := by
  simp [stopProj, mediatorGen, fromBlocks_multiply, hM]

theorem stopProj_comm_type (P : Matrix N N ℂ) (M : Matrix T T ℂ) :
    stopProj P * typeGen (H := H) (V := V) (N := N) M = typeGen M * stopProj P := by
  simp [stopProj, typeGen, fromBlocks_multiply]

theorem stopProj_comm_private (P : Matrix N N ℂ) (M : Matrix H H ℂ) :
    stopProj P * privateGen (T := T) (V := V) (N := N) M = privateGen M * stopProj P := by
  simp [stopProj, privateGen, fromBlocks_multiply]

/-- A Hermitian matrix commuting with `M` commutes with `Mᴴ`. -/
theorem commute_conjTranspose {X : Type*} [Fintype X] {Q M : Matrix X X ℂ} (hQ : Qᴴ = Q)
    (h : Q * M = M * Q) : Q * Mᴴ = Mᴴ * Q := by
  have := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ] at this
  exact this.symm

/-- A Hermitian matrix commuting with every generator commutes with every word. -/
theorem commute_words {X : Type*} [Fintype X] [DecidableEq X] {Q : Matrix X X ℂ}
    {S : Set (Matrix X X ℂ)} (hQ : Qᴴ = Q) (hS : ∀ M ∈ S, Q * M = M * Q) :
    ∀ w ∈ words S, Q * w = w * Q := by
  intro w hw
  induction hw using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact hS x hx
    · exact commute_conjTranspose hQ (hS y hy)
  | one => simp
  | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]

/-- A reducing projection containing `p_T` and annihilating `p_H` kills the
`H_priv ← T` corner of everything it commutes with. -/
theorem corner_eq_zero {X : Type*} [Fintype X] {Q pT pH w : Matrix X X ℂ}
    (hQpT : Q * pT = pT) (hpHQ : pH * Q = 0) (hcomm : Q * w = w * Q) :
    pH * w * pT = 0 := by
  calc pH * w * pT = pH * w * (Q * pT) := by rw [hQpT]
    _ = pH * (w * Q) * pT := by simp only [Matrix.mul_assoc]
    _ = pH * (Q * w) * pT := by rw [hcomm]
    _ = (pH * Q) * w * pT := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hpHQ, Matrix.zero_mul, Matrix.zero_mul]

/-! ### Partial-trace positivity -/

/-- `((I ⊗ P) M)_{(v,a),t} = (P M_v)_{a,t}` for the row slices `M_v`. -/
theorem one_kronecker_mul_apply' (P : Matrix N N ℂ) (M : Matrix (V × N) T ℂ) (v : V) (a : N)
    (t : T) : (((1 : Matrix V V ℂ) ⊗ₖ P) * M) (v, a) t = (P * slice v M) a t := by
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, slice,
    Matrix.of_apply, Matrix.one_apply]
  simp [Finset.sum_ite_eq]

theorem one_kronecker_mul_eq_self (P : Matrix N N ℂ) (M : Matrix (V × N) T ℂ)
    (h : ∀ v, P * slice v M = slice v M) : ((1 : Matrix V V ℂ) ⊗ₖ P) * M = M := by
  ext ⟨v, a⟩ t
  rw [one_kronecker_mul_apply', h v]
  rfl

theorem one_kronecker_mul_eq_zero (P : Matrix N N ℂ) (M : Matrix (V × N) T ℂ)
    (h : ∀ v, P * slice v M = 0) : ((1 : Matrix V V ℂ) ⊗ₖ P) * M = 0 := by
  ext ⟨v, a⟩ t
  rw [one_kronecker_mul_apply', h v]
  rfl

/-- A vanishing sum of Gram matrices `∑_v Y_v Y_v^*` forces every `Y_v = 0`. -/
theorem eq_zero_of_sum_self_mul_conjTranspose (Y : V → Matrix N T ℂ)
    (h : ∑ v, Y v * (Y v)ᴴ = 0) (v : V) : Y v = 0 := by
  ext a t
  have hdiag := congrFun (congrFun h a) a
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply,
    Complex.star_def, Complex.mul_conj] at hdiag
  have h1 : ∑ v, ∑ t, Complex.normSq (Y v a t) = 0 := by exact_mod_cast hdiag
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)).mp h1 v (Finset.mem_univ v)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Complex.normSq_nonneg _)).mp h2 t (Finset.mem_univ t)
  simpa [Complex.normSq_eq_zero] using h3

/-- **Partial-trace positivity, fixed form**: if `P` is Hermitian and `P ρ_A = ρ_A`
(`Ran ρ_A ⊆ Ran P`), then every row slice satisfies `P A_v = A_v`. -/
theorem slice_fixed_of_partialGram {P : Matrix N N ℂ} (hP : Pᴴ = P)
    {A : Matrix (V × N) T ℂ} (hPA : P * partialGram A = partialGram A) (v : V) :
    P * slice v A = slice v A := by
  have h0 : (1 - P) * partialGram A * (1 - P)ᴴ = 0 := by
    rw [sub_mul, Matrix.one_mul, hPA, sub_self, Matrix.zero_mul]
  have h1 : ∑ v, ((1 - P) * slice v A) * ((1 - P) * slice v A)ᴴ = 0 := by
    calc ∑ v, ((1 - P) * slice v A) * ((1 - P) * slice v A)ᴴ
        = (1 - P) * partialGram A * (1 - P)ᴴ := by
          rw [partialGram, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 0 := h0
  have := eq_zero_of_sum_self_mul_conjTranspose _ h1 v
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  exact this.symm

/-- **Partial-trace positivity, vanishing form**: if `P` is Hermitian and `P ρ_B = 0`
(`Ran ρ_B ⊥ Ran P`), then every row slice satisfies `P B_v = 0`. -/
theorem slice_zero_of_partialGram {P : Matrix N N ℂ} (hP : Pᴴ = P)
    {B : Matrix (V × N) H ℂ} (hPB : P * partialGram B = 0) (v : V) :
    P * slice v B = 0 := by
  have h1 : ∑ v, (P * slice v B) * (P * slice v B)ᴴ = 0 := by
    calc ∑ v, (P * slice v B) * (P * slice v B)ᴴ = P * partialGram B * Pᴴ := by
          rw [partialGram, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hPB, Matrix.zero_mul]
  exact eq_zero_of_sum_self_mul_conjTranspose _ h1 v

/-- `Ran A ⊆ V ⊗ Ran P`: `(I ⊗ P) A = A`. -/
theorem one_kronecker_mul_entry {P : Matrix N N ℂ} (hP : Pᴴ = P)
    {A : Matrix (V × N) T ℂ} (hPA : P * partialGram A = partialGram A) :
    ((1 : Matrix V V ℂ) ⊗ₖ P) * A = A :=
  one_kronecker_mul_eq_self P A (slice_fixed_of_partialGram hP hPA)

/-- `Ran B ⊥ V ⊗ Ran P`: `(I ⊗ P) B = 0`. -/
theorem one_kronecker_mul_exit {P : Matrix N N ℂ} (hP : Pᴴ = P)
    {B : Matrix (V × N) H ℂ} (hPB : P * partialGram B = 0) :
    ((1 : Matrix V V ℂ) ⊗ₖ P) * B = 0 :=
  one_kronecker_mul_eq_zero P B (slice_zero_of_partialGram hP hPB)

/-- `(I ⊗ P)` commutes with `v_g ⊗ I`. -/
theorem one_kronecker_comm_kronecker_one (P : Matrix N N ℂ) (U : Matrix V V ℂ) :
    ((1 : Matrix V V ℂ) ⊗ₖ P) * (U ⊗ₖ (1 : Matrix N N ℂ)) =
      (U ⊗ₖ (1 : Matrix N N ℂ)) * ((1 : Matrix V V ℂ) ⊗ₖ P) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_one, Matrix.one_mul]

/-! ### The proposition -/

/-- **The stopping projection reduces the bank.**  If `P` is Hermitian, commutes with
`h`, fixes `ρ_A` and annihilates `ρ_B`, then `Q = I_T ⊕ 0 ⊕ (I_V ⊗ P)` commutes with
every generator of the declared reciprocal route bank and with its adjoint. -/
theorem stopProj_commute_bank (v : G → Matrix V V ℂ) (h : Matrix N N ℂ)
    (A : Matrix (V × N) T ℂ) (B : Matrix (V × N) H ℂ) {P : Matrix N N ℂ} (hP : Pᴴ = P)
    (hPh : P * h = h * P) (hPA : P * partialGram A = partialGram A)
    (hPB : P * partialGram B = 0) :
    ∀ M ∈ bank v h A B, stopProj P * M = M * stopProj P ∧ stopProj P * Mᴴ = Mᴴ * stopProj P := by
  intro M hM
  suffices hc : stopProj P * M = M * stopProj P from
    ⟨hc, commute_conjTranspose (stopProj_conjTranspose P hP) hc⟩
  rcases hM with ((((⟨g, rfl⟩ | ⟨g, rfl⟩) | rfl) | ⟨X, rfl⟩) | ⟨Y, rfl⟩)
  · -- entry `(v_g ⊗ I) A`
    apply stopProj_comm_entry
    rw [← Matrix.mul_assoc, one_kronecker_comm_kronecker_one, Matrix.mul_assoc,
      one_kronecker_mul_entry hP hPA]
  · -- exit `B^* (v_g^* ⊗ I)`
    apply stopProj_comm_exit
    rw [Matrix.mul_assoc, ← one_kronecker_comm_kronecker_one, ← Matrix.mul_assoc]
    have h0 : Bᴴ * ((1 : Matrix V V ℂ) ⊗ₖ P) = 0 := by
      have := congrArg Matrix.conjTranspose (one_kronecker_mul_exit hP hPB)
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        hP, Matrix.conjTranspose_zero] at this
    rw [h0, Matrix.zero_mul]
  · -- mediator `I ⊗ h`
    apply stopProj_comm_mediator
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, hPh]
  · exact stopProj_comm_type P X
  · exact stopProj_comm_private P Y

/-- **Every word of the bank has zero `H_priv ← T` corner.** -/
theorem corner_eq_zero_of_mem_words (v : G → Matrix V V ℂ) (h : Matrix N N ℂ)
    (A : Matrix (V × N) T ℂ) (B : Matrix (V × N) H ℂ) {P : Matrix N N ℂ} (hP : Pᴴ = P)
    (hPh : P * h = h * P) (hPA : P * partialGram A = partialGram A)
    (hPB : P * partialGram B = 0) :
    ∀ w ∈ words (bank v h A B), pH * w * pT = 0 := by
  intro w hw
  exact corner_eq_zero (stopProj_mul_pT P) (pH_mul_stopProj P)
    (commute_words (stopProj_conjTranspose P hP)
      (fun M hM => (stopProj_commute_bank v h A B hP hPh hPA hPB M hM).1) w hw)

/-- **`prop:all-excursion-return`, conditional on the stopping projection.**  Let `P`
be the orthogonal projection onto `𝒩_A` (Hermitian, `P h = h P` by `h`-invariance of
`𝒩_A`, `P ρ_A = ρ_A`), and suppose `𝔪_ret = 0`, i.e. `Ran ρ_B ⊥ 𝒩_A` (`P ρ_B = 0`).
Then `Q = I_T ⊕ 0 ⊕ (I_V ⊗ P)` commutes with every generator of the declared reciprocal
route bank and its adjoint, and every word `w` of the bank has `p_H w p_T = 0`. -/
theorem all_excursion_return (v : G → Matrix V V ℂ) (h : Matrix N N ℂ)
    (A : Matrix (V × N) T ℂ) (B : Matrix (V × N) H ℂ) {P : Matrix N N ℂ} (hP : Pᴴ = P)
    (hPh : P * h = h * P) (hPA : P * partialGram A = partialGram A)
    (hPB : P * partialGram B = 0) :
    (∀ M ∈ bank v h A B,
      stopProj P * M = M * stopProj P ∧ stopProj P * Mᴴ = Mᴴ * stopProj P) ∧
    ∀ w ∈ words (bank v h A B), pH * w * pT = 0 :=
  ⟨stopProj_commute_bank v h A B hP hPh hPA hPB,
    corner_eq_zero_of_mem_words v h A B hP hPh hPA hPB⟩

end AllExcursion
end RenewalGeometry
