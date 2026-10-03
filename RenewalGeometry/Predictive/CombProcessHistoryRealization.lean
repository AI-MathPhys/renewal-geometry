/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.SequentialIsometricCombRealization
import RenewalGeometry.Predictive.ProcessHistoryRepresentation

/-!
# Process-history representation of a sequential comb realization

Paper `predictive_spectral_geometry`, labels `thm:ncg-comb-tomography`
(consequence clause) and `thm:ncg-process-history-representation`; paper
`emergent_spacetime`, `thm:supp-comb-tomography` (transport of retained
operators).

* `reducedChoiMap V M`: the reduced Schrödinger map on memory obtained by
  contracting a link with a fixed external intervention of Choi matrix `M`;
  `krausMap_reducedKraus`: for Kraus vectors `m ν` of the intervention it is the
  Kraus map of the reduced Kraus operators, so it depends only on the
  intervention's Choi matrix (Kraus-coordinate independence).
* `SequentialIsometricComb.combAmp`: the sequential contraction amplitude of one
  Kraus vector per slot; `combAmp_eq` identifies it with the contraction of the
  cumulative isometry with the product vector, and
  `trace_realizedChoi_mul_combProd_choi` proves that the realization reproduces
  every intervention probability: `Tr(R^(k) (M_k ⊗ ⋯ ⊗ M_1)) = ∑_ν ‖K_ν ⋯‖²`.
  Zero-probability prefixes propagate (`combAmp_eq_zero_of_trace_eq_zero`,
  `combAmp_eq_zero_of_prefix`).
* `SequentialIsometricComb.typedBranches`: the typed branch data of a
  sequential realization (boundary objects = cuts `k ≤ N`, memories `A_k`,
  primitive branches = slot interventions with their reduced maps).
* `hsBlockUnitary`, `rep_eq_hsBlockUnitary_conj`: the explicit Hilbert–Schmidt
  unitary `⊕_ξ U_ξ ⊗ Ū_ξ` conjugating the word representation, with
  `hsBlockUnitary_mulVec_block` (it transports block vectors) and
  `causalReadout_hsBlockUnitary_conj` (it preserves the causal readouts
  "prepare `1_{A_0}`, apply a history, discard the memory at cut `η`").
* `typedBranches_realization_independent`: **realization independence derived
  from the sequential covariance** — two prefix-support-minimal sequential
  realizations of the same terminal tensor (equivalently: representing the
  same intervention functional, `typedBranches_table_independent`; physical
  probe tables suffice, `typedBranches_physical_table_independent`) have
  represented process algebras related by a represented star isomorphism
  implemented by a Hilbert–Schmidt unitary preserving the causal readouts;
  `typedBranches_rep_eq_of_choi_eq`: Kraus coordinates of the interventions
  do not matter.
-/

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix
open scoped ComplexOrder Kronecker

namespace RenewalGeometry
namespace SequentialComb

open ProcessHistory

universe u

variable {O I : Type u} [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]

/-! ## Reduced Schrödinger maps of external interventions -/

section ReducedMaps

variable {A A' : Type*} [Fintype A] [Fintype A']

/-- The reduced Schrödinger map of a link `V` contracted with a fixed external
intervention of Choi matrix `M`:
`Y ↦ ∑_{x,y} M(y,x) ⟨x|V Y V^*|y⟩`. -/
def reducedChoiMap (V : Matrix (O × A') (I × A) ℂ) (M : Matrix (O × I) (O × I) ℂ) :
    Matrix A A ℂ →ₗ[ℂ] Matrix A' A' ℂ where
  toFun Y := ∑ x : O × I, ∑ y : O × I, M y x • (linkBlock V x.1 x.2 * Y * (linkBlock V y.1 y.2)ᴴ)
  map_add' Y Z := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
  map_smul' c Y := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [smul_comm]

theorem reducedKraus_eq_sum (V : Matrix (O × A') (I × A) ℂ) (m : O × I → ℂ) :
    reducedKraus V m = ∑ x : O × I, star (m x) • linkBlock V x.1 x.2 := by
  rw [Fintype.sum_prod_type]
  rfl

/-- The Choi matrix `∑_ν |m_ν⟩⟨m_ν|` of an intervention with Kraus vectors `m ν`. -/
def interventionChoi {K : Type*} [Fintype K] (m : K → O × I → ℂ) : Matrix (O × I) (O × I) ℂ :=
  ∑ ν, vecMulVec (m ν) (star (m ν))

theorem interventionChoi_posSemidef {K : Type*} [Fintype K] (m : K → O × I → ℂ) :
    (interventionChoi m).PosSemidef := by
  unfold interventionChoi
  exact Finset.sum_induction _ _ (fun A B hA hB => hA.add hB) PosSemidef.zero
    fun ν _ => posSemidef_vecMulVec_self_star (m ν)

/-- **Kraus-coordinate independence**: the Kraus map of the reduced Kraus
operators of an intervention is the reduced map of its Choi matrix. -/
theorem krausMap_reducedKraus (V : Matrix (O × A') (I × A) ℂ) {K : Type*} [Fintype K]
    (m : K → O × I → ℂ) :
    MatrixKraus.krausMap (fun ν => reducedKraus V (m ν)) = reducedChoiMap V (interventionChoi m) := by
  apply LinearMap.ext
  intro Y
  have lhs : MatrixKraus.krausMap (fun ν => reducedKraus V (m ν)) Y =
      ∑ ν, ∑ x : O × I, ∑ y : O × I, (m ν y * star (m ν x)) •
        (linkBlock V x.1 x.2 * Y * (linkBlock V y.1 y.2)ᴴ) := by
    rw [MatrixKraus.krausMap_apply]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [reducedKraus_eq_sum, conjTranspose_sum]
    simp only [Matrix.sum_mul, Matrix.mul_sum, conjTranspose_smul, star_star, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
  rw [lhs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [interventionChoi, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply, Finset.sum_smul]

end ReducedMaps

/-! ## Sequential amplitudes and intervention probabilities -/

/-- Product vector `⊗_j m_j` on the nested carrier. -/
def combVec {k : ℕ} (m : Fin k → O × I → ℂ) : CombCarrier O I k → ℂ :=
  fun x => ∏ j, m j (combSlot x j)

theorem combVec_succ {k : ℕ} (m : Fin (k + 1) → O × I → ℂ) (x : CombCarrier O I (k + 1)) :
    combVec m x = combVec (Fin.init m) x.2.2 * m (Fin.last k) (x.1, x.2.1) := by
  simp only [combVec, Fin.prod_univ_castSucc, combSlot, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.init]

theorem combProd_vecMulVec {k : ℕ} (m : Fin k → O × I → ℂ) (y x : CombCarrier O I k) :
    combProd (fun j => vecMulVec (m j) (star (m j))) y x = combVec m y * star (combVec m x) := by
  simp only [combProd, Matrix.of_apply, vecMulVec_apply, Pi.star_apply, Finset.prod_mul_distrib,
    combVec, star_prod]

theorem sum_combCarrier_succ {k : ℕ} {M : Type*} [AddCommMonoid M]
    (f : CombCarrier O I (k + 1) → M) :
    ∑ x, f x = ∑ o : O, ∑ i : I, ∑ u : CombCarrier O I k, f (o, (i, u)) := by
  let e : CombCarrier O I (k + 1) ≃ O × (I × CombCarrier O I k) := Equiv.refl _
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

namespace SequentialIsometricComb

variable {N : ℕ} (C : SequentialIsometricComb O I N)

/-- The sequential contraction amplitude `K_{m_k} ⋯ K_{m_1} |1⟩ ∈ A_k` of one
Kraus vector per slot. -/
def combAmp : ∀ k, (Fin k → O × I → ℂ) → C.Mem k → ℂ
  | 0, _ => fun _ => 1
  | k + 1, m => reducedKraus (C.link k) (m (Fin.last k)) *ᵥ combAmp k (Fin.init m)

/-- The sequential amplitude is the contraction of the cumulative isometry with
the product vector. -/
theorem combAmp_eq : ∀ k (m : Fin k → O × I → ℂ) (a : C.Mem k),
    C.combAmp k m a = ∑ x, star (combVec m x) * C.cumulative k x a
  | 0, m, a => by
      simp [combAmp, combVec, cumulative]
  | k + 1, m, a => by
      change ∑ b, reducedKraus (C.link k) (m (Fin.last k)) a b * C.combAmp k (Fin.init m) b = _
      rw [sum_combCarrier_succ]
      have hv : ∀ (o : O) (i : I) (u : CombCarrier O I k),
          combVec m ((o, (i, u)) : O × (I × CombCarrier O I k)) =
            combVec (Fin.init m) u * m (Fin.last k) (o, i) := fun o i u => combVec_succ m _
      simp only [combAmp_eq k, reducedKraus, Matrix.sum_apply, Matrix.smul_apply, linkBlock,
        Matrix.of_apply, smul_eq_mul, hv, cumulative, star_mul', Finset.sum_mul,
        Finset.mul_sum]
      -- order on the left: b, u, o, i; on the right: o, i, u, b
      rw [Finset.sum_comm]
      have step : ∀ u : CombCarrier O I k,
          (∑ b : C.Mem k, ∑ o : O, ∑ i : I,
            star (m (Fin.last k) (o, i)) * C.link k (o, a) (i, b) *
              (star (combVec (Fin.init m) u) * C.cumulative k u b)) =
          ∑ o : O, ∑ i : I, ∑ b : C.Mem k,
            star (m (Fin.last k) (o, i)) * C.link k (o, a) (i, b) *
              (star (combVec (Fin.init m) u) * C.cumulative k u b) := by
        intro u
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.sum_comm]
      simp only [step]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ =>
        Finset.sum_congr rfl fun b _ => ?_
      ring

/-- **The realization reproduces rank-one intervention probabilities**:
`Tr(R^(k) (⊗|m_j⟩⟨m_j|)) = ‖K_{m_k} ⋯ K_{m_1} |1⟩‖²`. -/
theorem trace_realizedChoi_mul_combProd_rankOne (k : ℕ) (m : Fin k → O × I → ℂ) :
    (C.realizedChoi k * combProd (fun j => vecMulVec (m j) (star (m j)))).trace =
      star (C.combAmp k m) ⬝ᵥ C.combAmp k m := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, realizedChoi, conjTranspose_apply,
    combProd_vecMulVec, dotProduct, Pi.star_apply, combAmp_eq C, star_sum, star_mul', star_star,
    Finset.sum_mul, Finset.mul_sum]
  have step : ∀ x : CombCarrier O I k,
      (∑ y : CombCarrier O I k, ∑ a : C.Mem k, C.cumulative k x a * star (C.cumulative k y a) *
        (combVec m y * star (combVec m x))) =
      ∑ a : C.Mem k, ∑ y : CombCarrier O I k, C.cumulative k x a * star (C.cumulative k y a) *
        (combVec m y * star (combVec m x)) := fun x => Finset.sum_comm
  simp only [step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **The realization reproduces every intervention probability**: for
interventions with Kraus vectors `kv j ν`,
`Tr(R^(k) (M_k ⊗ ⋯ ⊗ M_1)) = ∑_ν ‖K_{ν_k} ⋯ K_{ν_1} |1⟩‖²`. -/
theorem trace_realizedChoi_mul_combProd_choi {K : Type*} [Fintype K] (k : ℕ)
    (kv : Fin k → K → O × I → ℂ) :
    (C.realizedChoi k * combProd (fun j => interventionChoi (kv j))).trace =
      ∑ ν : Fin k → K, star (C.combAmp k (fun j => kv j (ν j))) ⬝ᵥ
        C.combAmp k (fun j => kv j (ν j)) := by
  classical
  rw [← combPairing_apply]
  unfold interventionChoi
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [combPairing_apply, trace_realizedChoi_mul_combProd_rankOne]

/-- A vanishing intervention probability forces every sequential amplitude of
the word to vanish. -/
theorem combAmp_eq_zero_of_trace_eq_zero {K : Type*} [Fintype K] (k : ℕ)
    (kv : Fin k → K → O × I → ℂ)
    (h : (C.realizedChoi k * combProd (fun j => interventionChoi (kv j))).trace = 0) :
    ∀ ν : Fin k → K, C.combAmp k (fun j => kv j (ν j)) = 0 := by
  classical
  rw [trace_realizedChoi_mul_combProd_choi] at h
  intro ν
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun ν _ => dotProduct_star_self_nonneg (C.combAmp k (fun j => kv j (ν j))))).1 h ν
    (Finset.mem_univ _)
  exact dotProduct_star_self_eq_zero.1 hall

/-- Zero amplitudes propagate to every continuation. -/
theorem combAmp_eq_zero_of_prefix : ∀ (n : ℕ) (m : Fin n → O × I → ℂ) (k : ℕ) (hk : k ≤ n),
    C.combAmp k (fun j => m (Fin.castLE hk j)) = 0 → C.combAmp n m = 0
  | 0, m, k, hk, h0 => by
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      exact h0
  | n + 1, m, k, hk, h0 => by
      by_cases hkn : k = n + 1
      · subst hkn
        have hm : (fun j => m (Fin.castLE hk j)) = m := funext fun j => by
          congr 1
        rwa [hm] at h0
      · have hk' : k ≤ n := by omega
        have hinit := combAmp_eq_zero_of_prefix n (Fin.init m) k hk' (by
          have : (fun j => Fin.init m (Fin.castLE hk' j)) = fun j => m (Fin.castLE hk j) :=
            funext fun j => by
              simp only [Fin.init]
              congr 1
          rw [this]
          exact h0)
        change reducedKraus (C.link n) (m (Fin.last n)) *ᵥ C.combAmp n (Fin.init m) = 0
        rw [hinit, mulVec_zero]

/-! ## Typed branch data of a sequential realization -/

/-- The typed branch data of a sequential realization: boundary objects are the
cuts `k ≤ N` with memories `A_k`; a primitive branch `a` is a fixed external
intervention at slot `slot a` (Kraus vectors `kv a ν`), with reduced
Schrödinger map `T_a = ∑_ν K_{a,ν} (·) K_{a,ν}^*`. -/
def typedBranches {Arr : Type*} (slot : Arr → Fin N) {K : Type*} [Fintype K]
    (kv : Arr → K → O × I → ℂ) :
    TypedBranches (Fin (N + 1)) Arr (fun a => (slot a).castSucc) (fun a => (slot a).succ)
      (fun ξ => C.Mem ξ) :=
  ⟨fun a => MatrixKraus.krausMap fun ν => reducedKraus (C.link (slot a)) (kv a ν)⟩

end SequentialIsometricComb

/-! ## The explicit Hilbert–Schmidt transport -/

section Transport

variable {Obj Arr : Type*} [Fintype Obj] [DecidableEq Obj] {src tgt : Arr → Obj}
  {D D' : Obj → Type*} [∀ ξ, Fintype (D ξ)] [∀ ξ, DecidableEq (D ξ)]
  [∀ ξ, Fintype (D' ξ)] [∀ ξ, DecidableEq (D' ξ)]

/-- The Hilbert–Schmidt unitary `⊕_ξ U_ξ ⊗ Ū_ξ` induced by memory unitaries. -/
def hsBlockUnitary (U : ∀ ξ, Matrix (D' ξ) (D ξ) ℂ) : Matrix (HSIdx D') (HSIdx D) ℂ :=
  ∑ ξ, blockIncl D' ξ * (U ξ ⊗ₖ (U ξ).map star) * (blockIncl D ξ)ᴴ

theorem hsBlockUnitary_mul_blockIncl (U : ∀ ξ, Matrix (D' ξ) (D ξ) ℂ) (ξ : Obj) :
    hsBlockUnitary U * blockIncl D ξ = blockIncl D' ξ * (U ξ ⊗ₖ (U ξ).map star) := by
  rw [hsBlockUnitary, Matrix.sum_mul, Finset.sum_eq_single ξ]
  · rw [Matrix.mul_assoc, blockIncl_isometry, Matrix.mul_one]
  · intro η _ hη
    rw [Matrix.mul_assoc, blockIncl_orth D hη, Matrix.mul_zero]
  · simp

theorem blockIncl_conjTranspose_mul_hsBlockUnitary (U : ∀ ξ, Matrix (D' ξ) (D ξ) ℂ) (ξ : Obj) :
    (blockIncl D' ξ)ᴴ * hsBlockUnitary U = (U ξ ⊗ₖ (U ξ).map star) * (blockIncl D ξ)ᴴ := by
  rw [hsBlockUnitary, Matrix.mul_sum, Finset.sum_eq_single ξ]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, blockIncl_isometry, Matrix.one_mul]
  · intro η _ hη
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, blockIncl_orth D' (Ne.symm hη), Matrix.zero_mul,
      Matrix.zero_mul]
  · simp

theorem hsBlockUnitary_conjTranspose (U : ∀ ξ, Matrix (D' ξ) (D ξ) ℂ) :
    (hsBlockUnitary U)ᴴ = ∑ ξ, blockIncl D ξ * (U ξ ⊗ₖ (U ξ).map star)ᴴ * (blockIncl D' ξ)ᴴ := by
  rw [hsBlockUnitary, conjTranspose_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem hsBlockUnitary_unitary (U : ∀ ξ, Matrix (D' ξ) (D ξ) ℂ) (hU1 : ∀ ξ, (U ξ)ᴴ * U ξ = 1)
    (hU2 : ∀ ξ, U ξ * (U ξ)ᴴ = 1) :
    (hsBlockUnitary U)ᴴ * hsBlockUnitary U = 1 ∧ hsBlockUnitary U * (hsBlockUnitary U)ᴴ = 1 := by
  have hV1 : ∀ ξ, (U ξ ⊗ₖ (U ξ).map star)ᴴ * (U ξ ⊗ₖ (U ξ).map star) = 1 :=
    fun ξ => kron_map_isometry (hU1 ξ)
  have hV2 : ∀ ξ, (U ξ ⊗ₖ (U ξ).map star) * (U ξ ⊗ₖ (U ξ).map star)ᴴ = 1 := by
    intro ξ
    have h := kron_map_isometry (W := (U ξ)ᴴ) (by rw [conjTranspose_conjTranspose, hU2])
    rw [← conjTranspose_kron_map] at h
    simpa using h
  constructor
  · rw [hsBlockUnitary_conjTranspose, Matrix.sum_mul, ← sum_objProj D]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Matrix.mul_assoc, blockIncl_conjTranspose_mul_hsBlockUnitary,
      show blockIncl D ξ * (U ξ ⊗ₖ (U ξ).map star)ᴴ * ((U ξ ⊗ₖ (U ξ).map star) *
          (blockIncl D ξ)ᴴ) = blockIncl D ξ * ((U ξ ⊗ₖ (U ξ).map star)ᴴ *
          (U ξ ⊗ₖ (U ξ).map star)) * (blockIncl D ξ)ᴴ by simp only [Matrix.mul_assoc],
      hV1, Matrix.mul_one, objProj]
  · rw [hsBlockUnitary_conjTranspose, Matrix.mul_sum, ← sum_objProj D']
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hsBlockUnitary_mul_blockIncl,
      Matrix.mul_assoc (blockIncl D' ξ), hV2, Matrix.mul_one, objProj]

/-- The explicit Hilbert–Schmidt unitary conjugates the whole word
representation when the reduced maps are related by the memory unitaries. -/
theorem rep_eq_hsBlockUnitary_conj (B : TypedBranches Obj Arr src tgt D)
    (B' : TypedBranches Obj Arr src tgt D') (U : ∀ ξ, Matrix (D' ξ) (D ξ) ℂ)
    (hU1 : ∀ ξ, (U ξ)ᴴ * U ξ = 1) (hU2 : ∀ ξ, U ξ * (U ξ)ᴴ = 1)
    (hT : ∀ a Y, B'.op a Y = U (tgt a) * B.op a ((U (src a))ᴴ * Y * U (src a)) * (U (tgt a))ᴴ)
    (f : FreePathAlg Obj Arr) :
    B'.rep f = hsBlockUnitary U * B.rep f * (hsBlockUnitary U)ᴴ := by
  classical
  obtain ⟨hu1, hu2⟩ := hsBlockUnitary_unitary U hU1 hU2
  set 𝒰 := hsBlockUnitary U
  have hιstar : ∀ ξ, (blockIncl D ξ)ᴴ * 𝒰ᴴ = (U ξ ⊗ₖ (U ξ).map star)ᴴ * (blockIncl D' ξ)ᴴ := by
    intro ξ
    have := congrArg conjTranspose (hsBlockUnitary_mul_blockIncl U ξ)
    rwa [conjTranspose_mul, conjTranspose_mul] at this
  have hV2 : ∀ ξ, (U ξ ⊗ₖ (U ξ).map star) * (U ξ ⊗ₖ (U ξ).map star)ᴴ = 1 := by
    intro ξ
    have h := kron_map_isometry (W := (U ξ)ᴴ) (by rw [conjTranspose_conjTranspose, hU2])
    rw [← conjTranspose_kron_map] at h
    simpa using h
  have hbr : ∀ a, B'.branchOp a = 𝒰 * B.branchOp a * 𝒰ᴴ := by
    intro a
    simp only [TypedBranches.branchOp]
    rw [hsMat_conj (B.op a) (B'.op a) (U (src a)) (U (tgt a)) (hT a)]
    calc blockIncl D' (tgt a) * ((U (tgt a) ⊗ₖ (U (tgt a)).map star) * hsMat (B.op a) *
          (U (src a) ⊗ₖ (U (src a)).map star)ᴴ) * (blockIncl D' (src a))ᴴ
        = (blockIncl D' (tgt a) * (U (tgt a) ⊗ₖ (U (tgt a)).map star)) * hsMat (B.op a) *
            ((U (src a) ⊗ₖ (U (src a)).map star)ᴴ * (blockIncl D' (src a))ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = (𝒰 * blockIncl D (tgt a)) * hsMat (B.op a) * ((blockIncl D (src a))ᴴ * 𝒰ᴴ) := by
          rw [hsBlockUnitary_mul_blockIncl, hιstar]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hgen : ∀ x, B'.gen x = 𝒰 * B.gen x * 𝒰ᴴ := by
    rintro (a | a | ξ)
    · exact hbr a
    · change (B'.branchOp a)ᴴ = 𝒰 * (B.branchOp a)ᴴ * 𝒰ᴴ
      rw [hbr, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    · change objProj D' ξ = 𝒰 * objProj D ξ * 𝒰ᴴ
      rw [objProj, objProj, ← Matrix.mul_assoc, hsBlockUnitary_mul_blockIncl, Matrix.mul_assoc,
        hιstar, ← Matrix.mul_assoc, Matrix.mul_assoc (blockIncl D' ξ), hV2, Matrix.mul_one]
  have hrep : B'.rep = (conjHom 𝒰 hu1 hu2).comp B.rep := by
    refine FreeStarAlg.starAlgHom_ext fun x => ?_
    rw [StarAlgHom.comp_apply]
    change FreeStarAlg.lift B'.gen B'.gen_star (FreeStarAlg.ι x) =
      conjHom 𝒰 hu1 hu2 (FreeStarAlg.lift B.gen B.gen_star (FreeStarAlg.ι x))
    rw [FreeStarAlg.lift_ι, FreeStarAlg.lift_ι, conjHom_apply, hgen]
  rw [hrep]
  rfl

/-- The block vector of a memory operator `Y` placed at object `ξ`. -/
def blockVec (ξ : Obj) (Y : Matrix (D ξ) (D ξ) ℂ) : HSIdx D → ℂ :=
  blockIncl D ξ *ᵥ hsVec Y

/-- The Hilbert–Schmidt unitary transports block vectors: `Y ↦ U_ξ Y U_ξ^*`. -/
theorem hsBlockUnitary_mulVec_blockVec (U : ∀ ξ, Matrix (D' ξ) (D ξ) ℂ) (ξ : Obj)
    (Y : Matrix (D ξ) (D ξ) ℂ) :
    hsBlockUnitary U *ᵥ blockVec ξ Y = blockVec ξ (U ξ * Y * (U ξ)ᴴ) := by
  rw [blockVec, blockVec, mulVec_mulVec, hsBlockUnitary_mul_blockIncl, ← mulVec_mulVec,
    ← hsApply_kron]
  rfl

/-- **Causal readouts**: prepare the memory operator `1` at the initial object
`ξ₀`, apply a represented history, discard the memory at object `η`. -/
def causalReadout (ξ₀ η : Obj) (x : Matrix (HSIdx D) (HSIdx D) ℂ) : ℂ :=
  star (blockVec η (1 : Matrix (D η) (D η) ℂ)) ⬝ᵥ (x *ᵥ blockVec ξ₀ (1 : Matrix (D ξ₀) (D ξ₀) ℂ))

/-- The causal readouts are invariant under the Hilbert–Schmidt transport. -/
theorem causalReadout_hsBlockUnitary_conj (U : ∀ ξ, Matrix (D' ξ) (D ξ) ℂ)
    (hU1 : ∀ ξ, (U ξ)ᴴ * U ξ = 1) (hU2 : ∀ ξ, U ξ * (U ξ)ᴴ = 1) (ξ₀ η : Obj)
    (x : Matrix (HSIdx D) (HSIdx D) ℂ) :
    causalReadout (D := D') ξ₀ η (hsBlockUnitary U * x * (hsBlockUnitary U)ᴴ) =
      causalReadout (D := D) ξ₀ η x := by
  have hone : ∀ ξ, hsBlockUnitary U *ᵥ blockVec ξ (1 : Matrix (D ξ) (D ξ) ℂ) =
      blockVec ξ (1 : Matrix (D' ξ) (D' ξ) ℂ) := by
    intro ξ
    rw [hsBlockUnitary_mulVec_blockVec, Matrix.mul_one, hU2]
  obtain ⟨hu1, -⟩ := hsBlockUnitary_unitary U hU1 hU2
  have h1 : ∀ s : HSIdx D → ℂ, (hsBlockUnitary U * x * (hsBlockUnitary U)ᴴ) *ᵥ
      (hsBlockUnitary U *ᵥ s) = hsBlockUnitary U *ᵥ (x *ᵥ s) := by
    intro s
    rw [mulVec_mulVec, Matrix.mul_assoc (hsBlockUnitary U * x), hu1, Matrix.mul_one,
      ← mulVec_mulVec]
  have h2 : ∀ t v : HSIdx D → ℂ, star (hsBlockUnitary U *ᵥ t) ⬝ᵥ (hsBlockUnitary U *ᵥ v) =
      star t ⬝ᵥ v := by
    intro t v
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hu1, one_mulVec]
  unfold causalReadout
  rw [← hone η, ← hone ξ₀, h1, h2]

end Transport

/-! ## Realization independence of the represented process algebra -/

section Independence

variable {N : ℕ} {Arr : Type*} (slot : Arr → Fin N) {K : Type*} [Fintype K]
  (kv : Arr → K → O × I → ℂ)

/-- The reduced branch maps of two realizations related by the link covariance
are Hilbert–Schmidt conjugate by the memory unitaries. -/
theorem typedBranches_op_covariant (C C' : SequentialIsometricComb O I N)
    (U : ∀ k, Matrix (C'.Mem k) (C.Mem k) ℂ)
    (hcov : ∀ k, k < N → C'.link k =
      ((1 : Matrix O O ℂ) ⊗ₖ U (k + 1)) * C.link k * ((1 : Matrix I I ℂ) ⊗ₖ U k)ᴴ)
    (a : Arr) (Y : Matrix (C'.Mem (slot a : ℕ)) (C'.Mem (slot a : ℕ)) ℂ) :
    MatrixKraus.krausMap (fun ν => reducedKraus (C'.link (slot a)) (kv a ν)) Y =
      U ((slot a : ℕ) + 1) *
        MatrixKraus.krausMap (fun ν => reducedKraus (C.link (slot a)) (kv a ν))
          ((U (slot a))ᴴ * Y * U (slot a)) * (U ((slot a : ℕ) + 1))ᴴ := by
  rw [← krausMap_conj_eq]
  have hK : (fun ν => reducedKraus (C'.link (slot a)) (kv a ν)) =
      fun ν => U ((slot a : ℕ) + 1) * reducedKraus (C.link (slot a)) (kv a ν) * (U (slot a))ᴴ := by
    funext ν
    rw [hcov _ (slot a).2, reducedKraus_covariant]
  rw [hK]

/-- **Realization independence** (`thm:ncg-process-history-representation`,
second sentence, derived).  Two prefix-support-minimal sequential isometric
realizations of the same terminal Choi tensor have represented process
algebras related by the explicit Hilbert–Schmidt unitary `𝒰 = ⊕_k U_k ⊗ Ū_k`
built from the sequential memory unitaries: `ρ' = 𝒰 ρ 𝒰^*` on the whole free
path algebra, equal kernels, a represented star isomorphism, and preserved
causal readouts. -/
theorem typedBranches_realization_independent [Nonempty I]
    (C C' : SequentialIsometricComb O I N)
    (hmin : ∀ k, k ≤ N → IsPrefixSupportMinimal (C.cumulative k))
    (hmin' : ∀ k, k ≤ N → IsPrefixSupportMinimal (C'.cumulative k))
    (hT : C.realizedChoi N = C'.realizedChoi N) :
    ∃ U : ∀ ξ : Fin (N + 1), Matrix (C'.Mem ξ) (C.Mem ξ) ℂ,
      (∀ ξ, (U ξ)ᴴ * U ξ = 1 ∧ U ξ * (U ξ)ᴴ = 1) ∧
      (∀ f, (C'.typedBranches slot kv).rep f =
        hsBlockUnitary U * (C.typedBranches slot kv).rep f * (hsBlockUnitary U)ᴴ) ∧
      (∀ ξ₀ η x, causalReadout (D := fun ξ : Fin (N + 1) => C'.Mem ξ) ξ₀ η
          (hsBlockUnitary U * x * (hsBlockUnitary U)ᴴ) =
        causalReadout (D := fun ξ : Fin (N + 1) => C.Mem ξ) ξ₀ η x) ∧
      RingHom.ker (C'.typedBranches slot kv).rep = RingHom.ker (C.typedBranches slot kv).rep ∧
      ∃ e : (C.typedBranches slot kv).rep.range ≃⋆ₐ[ℂ] (C'.typedBranches slot kv).rep.range,
        ∀ f, (e ⟨(C.typedBranches slot kv).rep f, f, rfl⟩ :
          Matrix (HSIdx fun ξ : Fin (N + 1) => C'.Mem ξ)
            (HSIdx fun ξ : Fin (N + 1) => C'.Mem ξ) ℂ) = (C'.typedBranches slot kv).rep f := by
  obtain ⟨U, hU, -, -, hcov, -⟩ := sequentialComb_unitary_covariance C C' hmin hmin' hT
  let U' : ∀ ξ : Fin (N + 1), Matrix (C'.Mem ξ) (C.Mem ξ) ℂ := fun ξ => U ξ
  have hU1 : ∀ ξ : Fin (N + 1), (U' ξ)ᴴ * U' ξ = 1 := fun ξ => (hU ξ (Nat.lt_succ_iff.mp ξ.2)).1
  have hU2 : ∀ ξ : Fin (N + 1), U' ξ * (U' ξ)ᴴ = 1 :=
    fun ξ => (hU ξ (Nat.lt_succ_iff.mp ξ.2)).2
  have hT' : ∀ a Y, (C'.typedBranches slot kv).op a Y =
      U' (slot a).succ * (C.typedBranches slot kv).op a ((U' (slot a).castSucc)ᴴ * Y *
        U' (slot a).castSucc) * (U' (slot a).succ)ᴴ :=
    fun a Y => typedBranches_op_covariant slot kv C C' U hcov a Y
  obtain ⟨𝒰, -, -, -, hker, e, he⟩ :=
    process_history_unitary_invariance (C.typedBranches slot kv) (C'.typedBranches slot kv)
      U' hU1 hU2 hT'
  exact ⟨U', fun ξ => ⟨hU1 ξ, hU2 ξ⟩,
    rep_eq_hsBlockUnitary_conj (C.typedBranches slot kv) (C'.typedBranches slot kv) U' hU1 hU2 hT',
    fun ξ₀ η x => causalReadout_hsBlockUnitary_conj U' hU1 hU2 ξ₀ η x, hker, e, he⟩

/-- **Frame/table independence**: realizations whose terminal tensors represent
the same multilinear intervention functional (e.g. reconstructed from the same
table in two different frames) give star-isomorphic represented process
algebras. -/
theorem typedBranches_table_independent [Nonempty I] (C C' : SequentialIsometricComb O I N)
    (hmin : ∀ k, k ≤ N → IsPrefixSupportMinimal (C.cumulative k))
    (hmin' : ∀ k, k ≤ N → IsPrefixSupportMinimal (C'.cumulative k))
    (p : MultilinearMap ℂ (fun _ : Fin N => Matrix (O × I) (O × I) ℂ) ℂ)
    (hp : combPairing (C.realizedChoi N) = p) (hp' : combPairing (C'.realizedChoi N) = p) :
    ∃ e : (C.typedBranches slot kv).rep.range ≃⋆ₐ[ℂ] (C'.typedBranches slot kv).rep.range,
      ∀ f, (e ⟨(C.typedBranches slot kv).rep f, f, rfl⟩ :
        Matrix (HSIdx fun ξ : Fin (N + 1) => C'.Mem ξ)
          (HSIdx fun ξ : Fin (N + 1) => C'.Mem ξ) ℂ) = (C'.typedBranches slot kv).rep f := by
  obtain ⟨-, -, -, -, -, e, he⟩ := typedBranches_realization_independent slot kv C C' hmin hmin'
    (combPairing_injective (hp.trans hp'.symm))
  exact ⟨e, he⟩

/-- **Frame independence**: realizations of the tensors reconstructed from the same
intervention table in two spanning physical frame families give star-isomorphic
represented process algebras. -/
theorem typedBranches_frame_independent [Nonempty I] (C C' : SequentialIsometricComb O I N)
    (hmin : ∀ k, k ≤ N → IsPrefixSupportMinimal (C.cumulative k))
    (hmin' : ∀ k, k ≤ N → IsPrefixSupportMinimal (C'.cumulative k))
    (F G : Fin N → PhysicalChoiTomographyFrame (O × I))
    (hF : ∀ j, Submodule.span ℂ (Set.range (F j).probe) = ⊤)
    (hG : ∀ j, Submodule.span ℂ (Set.range (G j).probe) = ⊤)
    (p : MultilinearMap ℂ (fun _ : Fin N => Matrix (O × I) (O × I) ℂ) ℂ)
    (hC : C.realizedChoi N = combFrameTensor F p) (hC' : C'.realizedChoi N = combFrameTensor G p) :
    ∃ e : (C.typedBranches slot kv).rep.range ≃⋆ₐ[ℂ] (C'.typedBranches slot kv).rep.range,
      ∀ f, (e ⟨(C.typedBranches slot kv).rep f, f, rfl⟩ :
        Matrix (HSIdx fun ξ : Fin (N + 1) => C'.Mem ξ)
          (HSIdx fun ξ : Fin (N + 1) => C'.Mem ξ) ℂ) = (C'.typedBranches slot kv).rep f :=
  typedBranches_table_independent slot kv C C' hmin hmin' p
    (by rw [hC, combPairing_combFrameTensor F hF p])
    (by rw [hC', combPairing_combFrameTensor G hG p])

/-- Physical-probe version: if the two terminal tensors give the same
probabilities on every tuple of trace-normalized positive probes, the represented
process algebras are star-isomorphic. -/
theorem typedBranches_physical_table_independent [Nonempty I]
    (C C' : SequentialIsometricComb O I N)
    (hmin : ∀ k, k ≤ N → IsPrefixSupportMinimal (C.cumulative k))
    (hmin' : ∀ k, k ≤ N → IsPrefixSupportMinimal (C'.cumulative k))
    (h : ∀ M : Fin N → Matrix (O × I) (O × I) ℂ,
      (∀ j, (M j).PosSemidef ∧ ((M j).trace).re ≤ 1) →
        (C.realizedChoi N * combProd M).trace = (C'.realizedChoi N * combProd M).trace) :
    ∃ e : (C.typedBranches slot kv).rep.range ≃⋆ₐ[ℂ] (C'.typedBranches slot kv).rep.range,
      ∀ f, (e ⟨(C.typedBranches slot kv).rep f, f, rfl⟩ :
        Matrix (HSIdx fun ξ : Fin (N + 1) => C'.Mem ξ)
          (HSIdx fun ξ : Fin (N + 1) => C'.Mem ξ) ℂ) = (C'.typedBranches slot kv).rep f := by
  obtain ⟨-, -, -, -, -, e, he⟩ := typedBranches_realization_independent slot kv C C' hmin hmin'
    (combTensor_eq_of_physical _ _ h)
  exact ⟨e, he⟩

/-- **Kraus-coordinate independence**: interventions with the same Choi matrices
give the same reduced maps and hence the same representation. -/
theorem typedBranches_rep_eq_of_choi_eq (C : SequentialIsometricComb O I N) {K' : Type*}
    [Fintype K'] (kv' : Arr → K' → O × I → ℂ)
    (h : ∀ a, interventionChoi (kv a) = interventionChoi (kv' a)) :
    (C.typedBranches slot kv).rep = (C.typedBranches slot kv').rep := by
  apply TypedBranches.rep_eq_of_op_eq
  intro a
  change MatrixKraus.krausMap (fun ν => reducedKraus (C.link (slot a)) (kv a ν)) =
    MatrixKraus.krausMap (fun ν => reducedKraus (C.link (slot a)) (kv' a ν))
  rw [krausMap_reducedKraus, krausMap_reducedKraus, h]

end Independence

end SequentialComb
end RenewalGeometry
