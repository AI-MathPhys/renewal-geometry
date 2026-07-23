/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.SemigroupLimit
import NCG.Algebra.ChoiCriterion

/-!
# Complete positivity of the Lindblad semigroup

Closes the complete-positivity clause (ii) of
`thm:stable-pointer-selection`: for the symmetric dissipator
`ℒX = −½ Σ_j [A_j, [A_j, X]]` with hermitian jumps, the semigroup
`e^{tℒ}` (`t ≥ 0`) is completely ancillary stable — every matrix
ampliation preserves positive semidefiniteness.

Route (Euler–Trotter, no unformalized inputs):

* `dissipator_split` — `ℒ = Φ + M` with the Kraus part
  `Φ(X) = Σ_j A_j X A_j` and the multiplication part
  `M(X) = −½(SX + XS)`, `S = Σ_j A_j²`;
* `exp_leftMul` / `exp_rightMul` / `exp_mulPair` — exponentials of
  multiplication generators are multiplications by matrix
  exponentials, so `e^{tM}` is the conjugation
  `X ↦ e^{−tS/2} X e^{−tS/2}`;
* conjugations and `1 + (t/n)Φ` are ampliation-stable (Kraus form +
  `Matrix.PosSemidef.mul_mul_conjTranspose_same`);
* the Euler product `(e^{tM/n}(1 + (t/n)Φ))^n` converges to
  `e^{tℒ}` (remainder bound + telescoping), and ampliation
  stability passes to limits (`PosSemidef` is closed under
  pointwise limits in the Frobenius topology).
-/

namespace NCG.Upstream

open NCG Nat Matrix
open scoped ComplexOrder

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Abbreviation for the matrix algebra carrying the dissipator. -/
local notation "𝕄" => Matrix E E ℂ

noncomputable local instance : NormedAddCommGroup 𝕄 :=
  hsCore.toNormedAddCommGroup

noncomputable local instance : TopologicalSpace 𝕄 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance : InnerProductSpace ℂ 𝕄 :=
  InnerProductSpace.ofCore hsCore.toCore

/-- Left multiplication as a continuous linear map. -/
noncomputable def leftMulL (B : 𝕄) : 𝕄 →L[ℂ] 𝕄 :=
  clm
    { toFun := fun X => B * X
      map_add' := fun X Y => by rw [mul_add]
      map_smul' := fun c X => by
        simp only [RingHom.id_apply]
        rw [mul_smul_comm] }

/-- Right multiplication as a continuous linear map. -/
noncomputable def rightMulL (B : 𝕄) : 𝕄 →L[ℂ] 𝕄 :=
  clm
    { toFun := fun X => X * B
      map_add' := fun X Y => by rw [add_mul]
      map_smul' := fun c X => by
        simp only [RingHom.id_apply]
        rw [smul_mul_assoc] }

@[simp]
theorem leftMulL_apply (B X : 𝕄) : leftMulL B X = B * X := rfl

@[simp]
theorem rightMulL_apply (B X : 𝕄) : rightMulL B X = X * B := rfl

theorem leftMulL_pow (B : 𝕄) (n : ℕ) (X : 𝕄) :
    ((leftMulL B) ^ n) X = B ^ n * X := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [_root_.pow_succ', ContinuousLinearMap.mul_apply, ih,
        leftMulL_apply, ← mul_assoc, ← _root_.pow_succ']

theorem rightMulL_pow (B : 𝕄) (n : ℕ) (X : 𝕄) :
    ((rightMulL B) ^ n) X = X * B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [_root_.pow_succ', ContinuousLinearMap.mul_apply, ih,
        rightMulL_apply, mul_assoc, ← _root_.pow_succ]

/-- The matrix exponential (via the operator exponential of left
multiplication — definitionally the entrywise exponential series). -/
noncomputable def matExp (B : 𝕄) : 𝕄 :=
  NormedSpace.exp (leftMulL B) 1

/-- `e^{L_B} X = e^B · X`: the exponential of left multiplication is
left multiplication by the matrix exponential. -/
theorem exp_leftMul (B X : 𝕄) :
    NormedSpace.exp (leftMulL B) X = matExp B * X := by
  have h1 : NormedSpace.exp (leftMulL B) X
      = ∑' n : ℕ, (n !⁻¹ : ℂ) • (B ^ n * X) := by
    rw [exp_apply_tsum]
    exact tsum_congr fun n => by rw [leftMulL_pow]
  have h2 : matExp B = ∑' n : ℕ, (n !⁻¹ : ℂ) • (B ^ n) := by
    unfold matExp
    rw [exp_apply_tsum]
    exact tsum_congr fun n => by rw [leftMulL_pow, mul_one]
  rw [h1, h2]
  -- pull the right multiplication by `X` out of the series
  have hsummable : Summable fun n : ℕ => (n !⁻¹ : ℂ) • (B ^ n) := by
    have h3 := NormedSpace.expSeries_summable' (𝕂 := ℂ) (leftMulL B)
    have h4 := h3.map
      (ContinuousLinearMap.apply ℂ 𝕄 (1 : 𝕄)).toLinearMap.toAddMonoidHom
      (ContinuousLinearMap.apply ℂ 𝕄 (1 : 𝕄)).continuous
    refine h4.congr fun n => ?_
    show ((n !⁻¹ : ℂ) • (leftMulL B) ^ n) (1 : 𝕄)
      = (n !⁻¹ : ℂ) • B ^ n
    rw [ContinuousLinearMap.smul_apply, leftMulL_pow, mul_one]
  rw [show (∑' n : ℕ, (n !⁻¹ : ℂ) • B ^ n) * X
      = rightMulL X (∑' n : ℕ, (n !⁻¹ : ℂ) • B ^ n) from rfl]
  rw [(rightMulL X).map_tsum hsummable]
  exact tsum_congr fun n => by
    rw [rightMulL_apply, smul_mul_assoc]

theorem matExp_eq_tsum (B : 𝕄) :
    matExp B = ∑' n : ℕ, (n !⁻¹ : ℂ) • (B ^ n) := by
  unfold matExp
  rw [exp_apply_tsum]
  exact tsum_congr fun n => by rw [leftMulL_pow, mul_one]

theorem matExp_summable (B : 𝕄) :
    Summable fun n : ℕ => (n !⁻¹ : ℂ) • (B ^ n) := by
  have h3 := NormedSpace.expSeries_summable' (𝕂 := ℂ) (leftMulL B)
  have h4 := h3.map
    (ContinuousLinearMap.apply ℂ 𝕄 (1 : 𝕄)).toLinearMap.toAddMonoidHom
    (ContinuousLinearMap.apply ℂ 𝕄 (1 : 𝕄)).continuous
  refine h4.congr fun n => ?_
  show ((n !⁻¹ : ℂ) • (leftMulL B) ^ n) (1 : 𝕄)
    = (n !⁻¹ : ℂ) • B ^ n
  rw [ContinuousLinearMap.smul_apply, leftMulL_pow, mul_one]

/-- `e^{R_B} X = X · e^B`. -/
theorem exp_rightMul (B X : 𝕄) :
    NormedSpace.exp (rightMulL B) X = X * matExp B := by
  have h1 : NormedSpace.exp (rightMulL B) X
      = ∑' n : ℕ, (n !⁻¹ : ℂ) • (X * B ^ n) := by
    rw [exp_apply_tsum]
    exact tsum_congr fun n => by rw [rightMulL_pow]
  rw [h1, matExp_eq_tsum]
  rw [show X * (∑' n : ℕ, (n !⁻¹ : ℂ) • B ^ n)
      = leftMulL X (∑' n : ℕ, (n !⁻¹ : ℂ) • B ^ n) from rfl]
  rw [(leftMulL X).map_tsum (matExp_summable B)]
  exact tsum_congr fun n => by
    rw [leftMulL_apply, mul_smul_comm]

theorem commute_leftMul_rightMul (B C : 𝕄) :
    Commute (leftMulL B) (rightMulL C) := by
  refine ContinuousLinearMap.ext fun X => ?_
  show leftMulL B (rightMulL C X) = rightMulL C (leftMulL B X)
  rw [rightMulL_apply, leftMulL_apply, rightMulL_apply,
    leftMulL_apply, Matrix.mul_assoc]

/-- **The conjugation exponential**: `e^{L_B + R_C} X = e^B X e^C` —
the semigroup of a two-sided multiplication generator is the
two-sided multiplication by matrix exponentials. -/
theorem exp_mulPair (B C X : 𝕄) :
    NormedSpace.exp (leftMulL B + rightMulL C) X
      = matExp B * X * matExp C := by
  letI : NormedAlgebra ℚ (𝕄 →L[ℂ] 𝕄) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  rw [NormedSpace.exp_add_of_commute (commute_leftMul_rightMul B C)]
  rw [ContinuousLinearMap.mul_apply, exp_rightMul, exp_leftMul,
    Matrix.mul_assoc]

/-- The Kraus part of the dissipator as a continuous linear map. -/
noncomputable def krausL {m : Type*} [Fintype m] (A : m → 𝕄) :
    𝕄 →L[ℂ] 𝕄 :=
  clm
    { toFun := fun X => ∑ j, A j * X * A j
      map_add' := fun X Y => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by
          rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        simp only [RingHom.id_apply]
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [Matrix.mul_smul, Matrix.smul_mul] }

@[simp]
theorem krausL_apply {m : Type*} [Fintype m] (A : m → 𝕄) (X : 𝕄) :
    krausL A X = ∑ j, A j * X * A j := rfl

/-- **`dissipator_split`**: the symmetric dissipator splits into the
Kraus part and a two-sided multiplication part,
`ℒ = Φ + (L_G + R_G)` with `G = −½ Σ_j A_j²`. -/
theorem dissipatorL_split {m : Type*} [Fintype m] (A : m → 𝕄) :
    clm (dissipatorL A)
      = krausL A
        + (leftMulL ((-(1 / 2) : ℂ) • ∑ j, A j * A j)
           + rightMulL ((-(1 / 2) : ℂ) • ∑ j, A j * A j)) := by
  refine ContinuousLinearMap.ext fun X => ?_
  have hL : dissipator A X
      = ∑ j, ((-(1 / 2) : ℂ) • (A j * (A j * X)) + A j * (X * A j)
          + (-(1 / 2) : ℂ) • (X * (A j * A j))) := by
    unfold dissipator comm
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    module
  have hR : krausL A X
      + (leftMulL ((-(1 / 2) : ℂ) • ∑ j, A j * A j)
         + rightMulL ((-(1 / 2) : ℂ) • ∑ j, A j * A j)) X
      = ∑ j, ((-(1 / 2) : ℂ) • (A j * (A j * X)) + A j * (X * A j)
          + (-(1 / 2) : ℂ) • (X * (A j * A j))) := by
    rw [ContinuousLinearMap.add_apply, krausL_apply, leftMulL_apply,
      rightMulL_apply]
    rw [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul,
      Finset.mul_sum, Finset.smul_sum, Finset.smul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_assoc]
    module
  show dissipator A X = _
  rw [hL, ← hR]
  rfl

/-! ### Ampliation by a finite ancilla -/

/-- General-index ampliation by a `k`-level ancilla (for `E = Fin n`
this is definitionally `NCG.Upstream.ampliate`). -/
noncomputable def ampliateE (k : ℕ) (Φ : 𝕄 →ₗ[ℂ] 𝕄) :
    Matrix (Fin k × E) (Fin k × E) ℂ →ₗ[ℂ]
      Matrix (Fin k × E) (Fin k × E) ℂ where
  toFun X := Matrix.of fun p q =>
    Φ (Matrix.of fun i j => X (p.1, i) (q.1, j)) p.2 q.2
  map_add' X Y := by
    ext p q
    show Φ (Matrix.of fun i j => (X + Y) (p.1, i) (q.1, j)) p.2 q.2
      = _
    rw [show (Matrix.of fun i j => (X + Y) (p.1, i) (q.1, j))
        = (Matrix.of fun i j => X (p.1, i) (q.1, j))
          + Matrix.of fun i j => Y (p.1, i) (q.1, j) from rfl,
      map_add]
    rfl
  map_smul' c X := by
    ext p q
    show Φ (Matrix.of fun i j => (c • X) (p.1, i) (q.1, j)) p.2 q.2
      = _
    rw [show (Matrix.of fun i j => (c • X) (p.1, i) (q.1, j))
        = c • Matrix.of fun i j => X (p.1, i) (q.1, j) from rfl,
      map_smul]
    rfl

@[simp]
theorem ampliateE_apply (k : ℕ) (Φ : 𝕄 →ₗ[ℂ] 𝕄)
    (X : Matrix (Fin k × E) (Fin k × E) ℂ) (p q : Fin k × E) :
    ampliateE k Φ X p q
      = Φ (Matrix.of fun i j => X (p.1, i) (q.1, j)) p.2 q.2 := rfl

/-- Ampliation is multiplicative in the transformation. -/
theorem ampliateE_comp (k : ℕ) (Φ Ψ : 𝕄 →ₗ[ℂ] 𝕄) :
    ampliateE k (Φ ∘ₗ Ψ) = ampliateE k Φ ∘ₗ ampliateE k Ψ := by
  refine LinearMap.ext fun X => ?_
  ext p q
  rfl

theorem ampliateE_id (k : ℕ) :
    ampliateE (E := E) k LinearMap.id = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  ext p q
  rfl

theorem ampliateE_add (k : ℕ) (Φ Ψ : 𝕄 →ₗ[ℂ] 𝕄) :
    ampliateE k (Φ + Ψ) = ampliateE k Φ + ampliateE k Ψ := by
  refine LinearMap.ext fun X => ?_
  ext p q
  show (Φ + Ψ) _ p.2 q.2 = _
  rw [LinearMap.add_apply]
  rfl

theorem ampliateE_smul (k : ℕ) (c : ℂ) (Φ : 𝕄 →ₗ[ℂ] 𝕄) :
    ampliateE k (c • Φ) = c • ampliateE k Φ := by
  refine LinearMap.ext fun X => ?_
  ext p q
  show (c • Φ) _ p.2 q.2 = _
  rw [LinearMap.smul_apply]
  rfl

/-- The ancilla extension `I_k ⊗ B` of a matrix. -/
def kronId (k : ℕ) (B : 𝕄) : Matrix (Fin k × E) (Fin k × E) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then B p.2 q.2 else 0

theorem kronId_conjTranspose (k : ℕ) {B : 𝕄} (hB : Bᴴ = B) :
    (kronId k B)ᴴ = kronId k B := by
  ext p q
  show star (kronId k B q p) = kronId k B p q
  simp only [kronId, Matrix.of_apply]
  by_cases h : q.1 = p.1
  · rw [if_pos h, if_pos h.symm]
    have hb := congrFun (congrFun hB p.2) q.2
    exact hb ▸ rfl
  · rw [if_neg h, if_neg (fun hh => h hh.symm), star_zero]

theorem kronId_mul_apply (k : ℕ) (B : 𝕄)
    (X : Matrix (Fin k × E) (Fin k × E) ℂ) (p s : Fin k × E) :
    (kronId k B * X) p s = ∑ a, B p.2 a * X (p.1, a) s := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  have hcollapse : ∀ r1 : Fin k,
      (∑ ra, kronId k B p (r1, ra) * X (r1, ra) s)
        = if p.1 = r1 then ∑ ra, B p.2 ra * X (r1, ra) s else 0 := by
    intro r1
    by_cases h : p.1 = r1
    · rw [if_pos h]
      exact Finset.sum_congr rfl fun ra _ => by
        show (if p.1 = r1 then B p.2 ra else 0) * _ = _
        rw [if_pos h]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun ra _ => ?_
      show (if p.1 = r1 then B p.2 ra else 0) * _ = 0
      rw [if_neg h, zero_mul]
  rw [Finset.sum_congr rfl (fun r1 _ => hcollapse r1)]
  rw [Finset.sum_ite_eq (Finset.univ) p.1
    (fun r1 => ∑ ra, B p.2 ra * X (r1, ra) s),
    if_pos (Finset.mem_univ _)]

theorem mul_kronId_apply (k : ℕ) (C : 𝕄)
    (X : Matrix (Fin k × E) (Fin k × E) ℂ) (p q : Fin k × E) :
    (X * kronId k C) p q = ∑ b, X p (q.1, b) * C b q.2 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  have hcollapse : ∀ s1 : Fin k,
      (∑ sb, X p (s1, sb) * kronId k C (s1, sb) q)
        = if s1 = q.1 then ∑ sb, X p (s1, sb) * C sb q.2 else 0 := by
    intro s1
    by_cases h : s1 = q.1
    · rw [if_pos h]
      exact Finset.sum_congr rfl fun sb _ => by
        show _ * (if s1 = q.1 then C sb q.2 else 0) = _
        rw [if_pos h]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun sb _ => ?_
      show _ * (if s1 = q.1 then C sb q.2 else 0) = 0
      rw [if_neg h, mul_zero]
  rw [Finset.sum_congr rfl (fun s1 _ => hcollapse s1)]
  rw [Finset.sum_ite_eq' (Finset.univ) q.1
    (fun s1 => ∑ sb, X p (s1, sb) * C sb q.2),
    if_pos (Finset.mem_univ _)]

/-- The ampliation of a two-sided multiplication is the two-sided
multiplication by the ancilla extensions. -/
theorem kronId_conj_entry (k : ℕ) (B C : 𝕄)
    (X : Matrix (Fin k × E) (Fin k × E) ℂ) (p q : Fin k × E) :
    (kronId k B * X * kronId k C) p q
      = (B * (Matrix.of fun i j => X (p.1, i) (q.1, j)) * C) p.2 q.2
    := by
  rw [mul_kronId_apply]
  rw [show (B * (Matrix.of fun i j => X (p.1, i) (q.1, j)) * C) p.2 q.2
      = ∑ b, (∑ a, B p.2 a * X (p.1, a) (q.1, b)) * C b q.2 from by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Matrix.mul_apply]
      simp only [Matrix.of_apply]]
  exact Finset.sum_congr rfl fun b _ => by rw [kronId_mul_apply]

/-! ### Ampliation stability of the building blocks -/

theorem posSemidef_sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin k × E) (Fin k × E) ℂ)
    (h : ∀ i ∈ s, (f i).PosSemidef) :
    (∑ i ∈ s, f i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable {k : ℕ}

/-- The ampliation of a Kraus map is the Kraus map of the ancilla
extensions. -/
theorem ampliateE_kraus {m : Type*} [Fintype m] (A : m → 𝕄)
    (X : Matrix (Fin k × E) (Fin k × E) ℂ) :
    ampliateE k (krausL A).toLinearMap X
      = ∑ j, kronId k (A j) * X * kronId k (A j) := by
  ext p q
  rw [ampliateE_apply]
  show krausL A _ p.2 q.2 = _
  rw [krausL_apply]
  rw [Matrix.sum_apply, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun j _ =>
    (kronId_conj_entry k (A j) (A j) X p q).symm

/-- **Ampliation stability of the Kraus part**: with hermitian
jumps, every ampliation of `X ↦ Σ_j A_j X A_j` preserves positive
semidefiniteness. -/
theorem ampliateE_kraus_posSemidef {m : Type*} [Fintype m]
    (A : m → 𝕄) (hA : ∀ j, (A j)ᴴ = A j)
    {X : Matrix (Fin k × E) (Fin k × E) ℂ} (hX : X.PosSemidef) :
    (ampliateE k (krausL A).toLinearMap X).PosSemidef := by
  rw [ampliateE_kraus]
  refine posSemidef_sum _ _ fun j _ => ?_
  have h := hX.mul_mul_conjTranspose_same (kronId k (A j))
  rwa [kronId_conjTranspose k (hA j)] at h

/-- The conjugation `X ↦ K X K` as the composite of the two
multiplications. -/
noncomputable def conjL (K : 𝕄) : 𝕄 →L[ℂ] 𝕄 :=
  (leftMulL K).comp (rightMulL K)

@[simp]
theorem conjL_apply (K X : 𝕄) : conjL K X = K * X * K := by
  show leftMulL K (rightMulL K X) = K * X * K
  rw [rightMulL_apply, leftMulL_apply, Matrix.mul_assoc]

/-- The ampliation of a conjugation is the conjugation by the
ancilla extension. -/
theorem ampliateE_conj (K : 𝕄)
    (X : Matrix (Fin k × E) (Fin k × E) ℂ) :
    ampliateE k (conjL K).toLinearMap X
      = kronId k K * X * kronId k K := by
  ext p q
  rw [ampliateE_apply]
  show conjL K _ p.2 q.2 = _
  rw [conjL_apply]
  exact (kronId_conj_entry k K K X p q).symm

/-- **Ampliation stability of hermitian conjugations**. -/
theorem ampliateE_conj_posSemidef {K : 𝕄} (hK : Kᴴ = K)
    {X : Matrix (Fin k × E) (Fin k × E) ℂ} (hX : X.PosSemidef) :
    (ampliateE k (conjL K).toLinearMap X).PosSemidef := by
  rw [ampliateE_conj]
  have h := hX.mul_mul_conjTranspose_same (kronId k K)
  rwa [kronId_conjTranspose k hK] at h

/-- **Ampliation stability of the Euler factor** `1 + s·Φ` for
`s ≥ 0` and a hermitian Kraus part. -/
theorem ampliateE_euler_posSemidef {m : Type*} [Fintype m]
    (A : m → 𝕄) (hA : ∀ j, (A j)ᴴ = A j) {s : ℝ} (hs : 0 ≤ s)
    {X : Matrix (Fin k × E) (Fin k × E) ℂ} (hX : X.PosSemidef) :
    (ampliateE k (LinearMap.id + (s : ℂ) • (krausL A).toLinearMap) X
      ).PosSemidef := by
  rw [ampliateE_add, ampliateE_smul, ampliateE_id]
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  refine hX.add ?_
  have h1 := ampliateE_kraus_posSemidef A hA hX (k := k)
  have hcoe : ((s : ℂ) • ampliateE k (krausL A).toLinearMap X)
      = s • ampliateE k (krausL A).toLinearMap X := by
    rw [Complex.coe_smul]
  rw [hcoe]
  exact h1.smul hs

/-! ### Hermiticity of the matrix exponential -/

theorem leftMulL_smul (c : ℂ) (B : 𝕄) :
    leftMulL (c • B) = c • leftMulL B := by
  refine ContinuousLinearMap.ext fun X => ?_
  rw [leftMulL_apply, ContinuousLinearMap.smul_apply, leftMulL_apply,
    Matrix.smul_mul]

theorem rightMulL_smul (c : ℂ) (B : 𝕄) :
    rightMulL (c • B) = c • rightMulL B := by
  refine ContinuousLinearMap.ext fun X => ?_
  rw [rightMulL_apply, ContinuousLinearMap.smul_apply, rightMulL_apply,
    Matrix.mul_smul]

/-- Conjugate transpose as a continuous `ℝ`-linear map on the
Frobenius space. -/
noncomputable def ctR : 𝕄 →L[ℝ] 𝕄 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Xᴴ
      map_add' := fun X Y => Matrix.conjTranspose_add X Y
      map_smul' := fun c X => by
        simp only [RingHom.id_apply]
        rw [Matrix.conjTranspose_smul, star_trivial] }

@[simp]
theorem ctR_apply (X : 𝕄) : ctR X = Xᴴ := rfl

/-- The exponential of a hermitian matrix is hermitian. -/
theorem matExp_conjTranspose {B : 𝕄} (hB : Bᴴ = B) :
    (matExp B)ᴴ = matExp B := by
  rw [matExp_eq_tsum]
  rw [show (∑' n : ℕ, (n !⁻¹ : ℂ) • B ^ n)ᴴ
      = ctR (∑' n : ℕ, (n !⁻¹ : ℂ) • B ^ n) from rfl]
  rw [ctR.map_tsum (matExp_summable B)]
  refine tsum_congr fun n => ?_
  rw [ctR_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_pow,
    hB]
  congr 1
  rw [star_inv₀, star_natCast]

/-- Hermiticity of the two-sided generator matrix `G = −½ Σ A_j²`. -/
theorem sumSq_conjTranspose {m : Type*} [Fintype m] (A : m → 𝕄)
    (hA : ∀ j, (A j)ᴴ = A j) :
    ((-(1 / 2) : ℂ) • ∑ j, A j * A j)ᴴ
      = (-(1 / 2) : ℂ) • ∑ j, A j * A j := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  rw [show star (-(1 / 2) : ℂ) = (-(1 / 2) : ℂ) from by
    rw [star_neg, star_div₀, star_one, star_ofNat]]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by
    rw [Matrix.conjTranspose_mul, hA j]

/-! ### Positivity is closed under limits -/

theorem isClosed_nonneg_complex : IsClosed {z : ℂ | 0 ≤ z} := by
  have hset : {z : ℂ | 0 ≤ z}
      = Complex.re ⁻¹' Set.Ici 0 ∩ Complex.im ⁻¹' {0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Ici, Set.mem_singleton_iff]
    rw [Complex.le_def]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa using h1, by simpa using h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa using h1, by simp [h2]⟩
  rw [hset]
  exact (isClosed_Ici.preimage Complex.continuous_re).inter
    (isClosed_singleton.preimage Complex.continuous_im)

/-- **Positive semidefiniteness is closed under limits** in the
Frobenius topology. -/
theorem posSemidef_of_tendsto {Y : ℕ → 𝕄} {L : 𝕄}
    (hY : ∀ n, (Y n).PosSemidef)
    (hlim : Filter.Tendsto Y Filter.atTop (nhds L)) :
    L.PosSemidef := by
  constructor
  · have hct : Filter.Tendsto (fun n => ctR (Y n)) Filter.atTop
        (nhds (ctR L)) := (ctR.continuous.tendsto L).comp hlim
    have heq : (fun n => ctR (Y n)) = Y := by
      funext n
      rw [ctR_apply]
      exact (hY n).1
    rw [heq] at hct
    exact tendsto_nhds_unique hct hlim
  · intro x
    set qf : 𝕄 →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
      { toFun := fun M => x.sum fun i xi => x.sum fun j xj =>
          star xi * M i j * xj
        map_add' := fun M N => by
          simp only [Finsupp.sum, Matrix.add_apply]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        map_smul' := fun c M => by
          simp only [RingHom.id_apply, Finsupp.sum, Matrix.smul_apply,
            smul_eq_mul]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring } with hqf
    have hq : Filter.Tendsto (fun n => qf (Y n)) Filter.atTop
        (nhds (qf L)) := (qf.continuous.tendsto L).comp hlim
    have hmem : ∀ n, qf (Y n) ∈ {z : ℂ | 0 ≤ z} := fun n => by
      show (0 : ℂ) ≤ qf (Y n)
      exact (hY n).2 x
    have hLmem := isClosed_nonneg_complex.mem_of_tendsto hq
      (Filter.Eventually.of_forall hmem)
    exact hLmem

/-! ### The second-order remainder bound for the exponential -/

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem norm_exp_sub_one_sub_le (z : 𝕄 →L[ℂ] 𝕄) :
    ‖NormedSpace.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  have hf : NormedSpace.exp z = ∑' n : ℕ, (n !⁻¹ : ℂ) • z ^ n :=
    congrFun (NormedSpace.exp_eq_tsum ℂ) z
  have hs : Summable fun n : ℕ => (n !⁻¹ : ℂ) • z ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) z
  have hs1 : Summable fun n : ℕ => (((n + 1) : ℕ) !⁻¹ : ℂ) • z ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hs
  have hsplit : NormedSpace.exp z - 1 - z
      = ∑' n : ℕ, ((((n + 2) : ℕ) !⁻¹ : ℂ)) • z ^ (n + 2) := by
    rw [hf, hs.tsum_eq_zero_add]
    rw [hs1.tsum_eq_zero_add]
    have h0 : ((0 : ℕ) !⁻¹ : ℂ) • z ^ 0 = 1 := by simp
    have h1 : (((0 + 1 : ℕ)) !⁻¹ : ℂ) • z ^ (0 + 1) = z := by simp
    rw [h0, h1]
    have h2 : (fun n : ℕ => (((n + 1 + 1 : ℕ)) !⁻¹ : ℂ) • z ^ (n + 1 + 1))
        = fun n : ℕ => ((((n + 2) : ℕ) !⁻¹ : ℂ)) • z ^ (n + 2) := rfl
    rw [h2]
    abel
  rw [hsplit]
  have hsum_norms : Summable fun n : ℕ =>
      ‖((((n + 2) : ℕ) !⁻¹ : ℂ)) • z ^ (n + 2)‖ :=
    (summable_nat_add_iff 2).mpr
      (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) z)
  have hdom : Summable fun n : ℕ =>
      ‖z‖ ^ 2 * (((n ! : ℝ))⁻¹ * ‖z‖ ^ n) := by
    refine Summable.mul_left _ ?_
    refine (Real.summable_pow_div_factorial ‖z‖).congr fun n => ?_
    rw [div_eq_mul_inv, mul_comm]
  have hnorm : ∀ n : ℕ, ‖((((n + 2) : ℕ) !⁻¹ : ℂ)) • z ^ (n + 2)‖
      ≤ ‖z‖ ^ 2 * (((n ! : ℝ))⁻¹ * ‖z‖ ^ n) := by
    intro n
    rw [norm_smul]
    have hfact : ‖((((n + 2) : ℕ) !⁻¹ : ℂ))‖ = ((((n + 2) : ℕ) ! : ℝ))⁻¹ := by
      rw [norm_inv, Complex.norm_natCast]
    rw [hfact]
    have hzpow : ‖z ^ (n + 2)‖ ≤ ‖z‖ ^ (n + 2) :=
      norm_pow_le' z (by omega)
    have hle : ((((n + 2) : ℕ) ! : ℝ))⁻¹ ≤ ((n ! : ℝ))⁻¹ := by
      rw [← one_div, ← one_div]
      refine one_div_le_one_div_of_le ?_ ?_
      · exact_mod_cast Nat.factorial_pos n
      · exact_mod_cast Nat.factorial_le (by omega)
    calc ((((n + 2) : ℕ) ! : ℝ))⁻¹ * ‖z ^ (n + 2)‖
        ≤ ((n ! : ℝ))⁻¹ * ‖z‖ ^ (n + 2) := by
          refine mul_le_mul hle hzpow (norm_nonneg _) ?_
          positivity
      _ = ‖z‖ ^ 2 * (((n ! : ℝ))⁻¹ * ‖z‖ ^ n) := by
          rw [pow_add]
          ring
  have hexp_real : (∑' n : ℕ, ((n ! : ℝ))⁻¹ * ‖z‖ ^ n)
      = Real.exp ‖z‖ := by
    rw [Real.exp_eq_exp_ℝ]
    rw [congrFun (NormedSpace.exp_eq_tsum ℝ) ‖z‖]
    exact tsum_congr fun n => by rw [smul_eq_mul]
  calc ‖∑' n : ℕ, ((((n + 2) : ℕ) !⁻¹ : ℂ)) • z ^ (n + 2)‖
      ≤ ∑' n : ℕ, ‖((((n + 2) : ℕ) !⁻¹ : ℂ)) • z ^ (n + 2)‖ :=
        norm_tsum_le_tsum_norm hsum_norms
    _ ≤ ∑' n : ℕ, ‖z‖ ^ 2 * (((n ! : ℝ))⁻¹ * ‖z‖ ^ n) :=
        hsum_norms.tsum_le_tsum hnorm hdom
    _ = ‖z‖ ^ 2 * ∑' n : ℕ, ((n ! : ℝ))⁻¹ * ‖z‖ ^ n :=
        tsum_mul_left
    _ = ‖z‖ ^ 2 * Real.exp ‖z‖ := by rw [hexp_real]

/-! ### Telescoping power estimate and the exponential norm bound -/

theorem norm_pow_le_of_le {y : 𝕄 →L[ℂ] 𝕄} {K : ℝ} (hy : ‖y‖ ≤ K)
    (n : ℕ) : ‖y ^ n‖ ≤ K ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
      rw [_root_.pow_succ, _root_.pow_succ]
      calc ‖y ^ n * y‖ ≤ ‖y ^ n‖ * ‖y‖ := norm_mul_le _ _
        _ ≤ K ^ n * K :=
            mul_le_mul ih hy (norm_nonneg _)
              (pow_nonneg (le_trans (norm_nonneg _) hy) n)

/-- Telescoping estimate for powers. -/
theorem norm_pow_sub_pow_le (x y : 𝕄 →L[ℂ] 𝕄) (K : ℝ)
    (hx : ‖x‖ ≤ K) (hy : ‖y‖ ≤ K) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ n * K ^ (n - 1) * ‖x - y‖ := by
  have hK : 0 ≤ K := le_trans (norm_nonneg _) hx
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit : x ^ (n + 1) - y ^ (n + 1)
          = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by
        rw [_root_.pow_succ', _root_.pow_succ', mul_sub, sub_mul]
        abel
      rw [hsplit]
      calc ‖x * (x ^ n - y ^ n) + (x - y) * y ^ n‖
          ≤ ‖x * (x ^ n - y ^ n)‖ + ‖(x - y) * y ^ n‖ :=
            norm_add_le _ _
        _ ≤ ‖x‖ * ‖x ^ n - y ^ n‖ + ‖x - y‖ * ‖y ^ n‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ K * (n * K ^ (n - 1) * ‖x - y‖) + ‖x - y‖ * K ^ n := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul hx ih (norm_nonneg _) hK
            · exact mul_le_mul_of_nonneg_left
                (norm_pow_le_of_le hy n) (norm_nonneg _)
        _ ≤ ((n + 1 : ℕ) : ℝ) * K ^ ((n + 1) - 1) * ‖x - y‖ := by
            rcases Nat.eq_zero_or_pos n with rfl | hn
            · simp
            · have hK1 : K * K ^ (n - 1) = K ^ n := by
                rw [← _root_.pow_succ']
                congr 1
                omega
              have e1 : K * (n * K ^ (n - 1) * ‖x - y‖)
                  = n * (K * K ^ (n - 1)) * ‖x - y‖ := by ring
              rw [e1, hK1]
              rw [show ((n + 1 : ℕ)) - 1 = n from by omega]
              refine le_of_eq ?_
              push_cast
              ring

/-- `‖e^z‖ ≤ e^{‖z‖}`. -/
theorem norm_exp_le_exp_norm (z : 𝕄 →L[ℂ] 𝕄) :
    ‖NormedSpace.exp z‖ ≤ Real.exp ‖z‖ := by
  rw [congrFun (NormedSpace.exp_eq_tsum ℂ) z]
  have hexp : Real.exp ‖z‖ = ∑' n : ℕ, ((n ! : ℝ))⁻¹ * ‖z‖ ^ n := by
    rw [Real.exp_eq_exp_ℝ, congrFun (NormedSpace.exp_eq_tsum ℝ) ‖z‖]
    exact tsum_congr fun n => by rw [smul_eq_mul]
  rw [hexp]
  refine le_trans (norm_tsum_le_tsum_norm
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) z)) ?_
  refine (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) z
    ).tsum_le_tsum (fun n => ?_) ?_
  · rw [norm_smul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_pow_le_of_le le_rfl n)
      (by positivity)
  · refine (Real.summable_pow_div_factorial ‖z‖).congr fun n => ?_
    rw [div_eq_mul_inv, mul_comm]

/-! ### Positivity preservation under every ampliation -/

/-- A transformation preserves positivity **in every ancillary
context** — the repo's operational reading of complete
positivity (`def:ancillary-stability`). -/
def PreservesPos (f : 𝕄 →ₗ[ℂ] 𝕄) : Prop :=
  ∀ (k : ℕ) (X : Matrix (Fin k × E) (Fin k × E) ℂ),
    X.PosSemidef → (ampliateE k f X).PosSemidef

theorem PreservesPos.comp {f g : 𝕄 →ₗ[ℂ] 𝕄}
    (hf : PreservesPos f) (hg : PreservesPos g) :
    PreservesPos (f ∘ₗ g) := by
  intro k X hX
  rw [ampliateE_comp]
  exact hf k _ (hg k X hX)

theorem PreservesPos.id : PreservesPos (LinearMap.id : 𝕄 →ₗ[ℂ] 𝕄) := by
  intro k X hX
  rw [ampliateE_id]
  exact hX

theorem PreservesPos.pow {f : 𝕄 →L[ℂ] 𝕄} (hf : PreservesPos f.toLinearMap)
    (p : ℕ) : PreservesPos (f ^ p).toLinearMap := by
  induction p with
  | zero =>
      have h : ((f ^ 0 : 𝕄 →L[ℂ] 𝕄)).toLinearMap = LinearMap.id := rfl
      rw [h]
      exact PreservesPos.id
  | succ p ih =>
      have h : ((f ^ (p + 1) : 𝕄 →L[ℂ] 𝕄)).toLinearMap
          = f.toLinearMap ∘ₗ (f ^ p).toLinearMap := by
        rw [_root_.pow_succ']
        rfl
      rw [h]
      exact hf.comp ih

theorem preservesPos_conjL {K : 𝕄} (hK : Kᴴ = K) :
    PreservesPos (conjL K).toLinearMap := fun k X hX =>
  ampliateE_conj_posSemidef hK hX

theorem preservesPos_euler {m : Type*} [Fintype m] (A : m → 𝕄)
    (hA : ∀ j, (A j)ᴴ = A j) {s : ℝ} (hs : 0 ≤ s) :
    PreservesPos (LinearMap.id + (s : ℂ) • (krausL A).toLinearMap) :=
  fun k X hX => ampliateE_euler_posSemidef A hA hs hX

/-- The real-scalar Euler factor as a continuous map, with its
underlying linear map in the stable form. -/
theorem eulerCLM_toLinearMap {m : Type*} [Fintype m] (A : m → 𝕄)
    (s : ℝ) :
    ((1 : 𝕄 →L[ℂ] 𝕄) + s • krausL A).toLinearMap
      = LinearMap.id + (s : ℂ) • (krausL A).toLinearMap := by
  refine LinearMap.ext fun X => ?_
  show (1 : 𝕄 →L[ℂ] 𝕄) X + (s • krausL A) X = X + (s : ℂ) • krausL A X
  rw [ContinuousLinearMap.smul_apply, Complex.coe_smul]
  rfl

theorem leftMulL_real_smul (r : ℝ) (B : 𝕄) :
    r • leftMulL B = leftMulL (r • B) := by
  refine ContinuousLinearMap.ext fun X => ?_
  rw [ContinuousLinearMap.smul_apply, leftMulL_apply, leftMulL_apply,
    smul_mul_assoc]

theorem rightMulL_real_smul (r : ℝ) (B : 𝕄) :
    r • rightMulL B = rightMulL (r • B) := by
  refine ContinuousLinearMap.ext fun X => ?_
  rw [ContinuousLinearMap.smul_apply, rightMulL_apply, rightMulL_apply]
  rw [show X * (r • B) = r • (X * B) from by
    rw [mul_smul_comm]]

set_option synthInstance.maxHeartbeats 400000 in
/-- The exponential of the real-scaled two-sided generator is the
hermitian conjugation. -/
theorem exp_smul_mulPair_eq_conjL (r : ℝ) (G : 𝕄) :
    NormedSpace.exp (r • (leftMulL G + rightMulL G))
      = conjL (matExp (r • G)) := by
  have harg : r • (leftMulL G + rightMulL G)
      = leftMulL (r • G) + rightMulL (r • G) := by
    refine ContinuousLinearMap.ext fun Y => ?_
    show r • ((leftMulL G + rightMulL G) Y)
      = leftMulL (r • G) Y + rightMulL (r • G) Y
    rw [ContinuousLinearMap.add_apply, leftMulL_apply,
      rightMulL_apply, leftMulL_apply, rightMulL_apply, smul_add,
      smul_mul_assoc, mul_smul_comm]
  rw [harg]
  refine ContinuousLinearMap.ext fun X => ?_
  rw [exp_mulPair, conjL_apply]

theorem matExp_real_smul_conjTranspose {G : 𝕄} (hG : Gᴴ = G)
    (r : ℝ) : (matExp (r • G))ᴴ = matExp (r • G) := by
  refine matExp_conjTranspose ?_
  rw [Matrix.conjTranspose_smul, star_trivial, hG]

/-! ### The Euler product converges to the semigroup -/

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **Euler–Trotter convergence**: the split Euler products converge
in operator norm to the full semigroup. -/
theorem euler_product_tendsto (P Q : 𝕄 →L[ℂ] 𝕄) (t : ℝ) :
    Filter.Tendsto (fun n : ℕ =>
      (NormedSpace.exp ((t / ((n : ℝ) + 1)) • P)
        * (1 + (t / ((n : ℝ) + 1)) • Q)) ^ (n + 1))
      Filter.atTop (nhds (NormedSpace.exp (t • (P + Q)))) := by
  letI : NormedAlgebra ℚ (𝕄 →L[ℂ] 𝕄) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  set c : ℝ := |t| * (‖P‖ + ‖Q‖) + 1 with hc
  have hc1 : 1 ≤ c := by
    rw [hc]
    have : 0 ≤ |t| * (‖P‖ + ‖Q‖) :=
      mul_nonneg (abs_nonneg t)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    linarith
  have hc0 : 0 ≤ c := by linarith
  set C : ℝ := c ^ 2 * Real.exp c * (1 + c) + c ^ 2
      + (2 * c) ^ 2 * Real.exp (2 * c) with hC
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _)
    (g := fun n : ℕ => C * Real.exp (2 * c) / ((n : ℝ) + 1)) ?_ ?_
  · intro n
    set N : ℝ := (n : ℝ) + 1 with hN
    have hN1 : (1 : ℝ) ≤ N := by
      rw [hN]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
    set a : 𝕄 →L[ℂ] 𝕄 := (t / N) • P with ha
    set b : 𝕄 →L[ℂ] 𝕄 := (t / N) • Q with hb
    have hna : ‖a‖ ≤ c / N := by
      rw [ha, norm_smul, Real.norm_eq_abs, abs_div,
        abs_of_pos hN0, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ hN0.le
      rw [hc]
      nlinarith [norm_nonneg P, norm_nonneg Q, abs_nonneg t]
    have hnb : ‖b‖ ≤ c / N := by
      rw [hb, norm_smul, Real.norm_eq_abs, abs_div,
        abs_of_pos hN0, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ hN0.le
      rw [hc]
      nlinarith [norm_nonneg P, norm_nonneg Q, abs_nonneg t]
    have hcN0 : 0 ≤ c / N := div_nonneg hc0 hN0.le
    have hcN : c / N ≤ c := by
      rw [div_le_iff₀ hN0]
      nlinarith
    have hna2 : ‖a‖ ≤ c := le_trans hna hcN
    have hnb2 : ‖b‖ ≤ c := le_trans hnb hcN
    have hsum : a + b = (t / N) • (P + Q) := by
      refine ContinuousLinearMap.ext fun Y => ?_
      show a Y + b Y = (t / N) • ((P + Q) Y)
      rw [ha, hb]
      show (t / N) • P Y + (t / N) • Q Y = _
      rw [ContinuousLinearMap.add_apply, smul_add]
    have hexp_pow : NormedSpace.exp (a + b) ^ (n + 1)
        = NormedSpace.exp (t • (P + Q)) := by
      rw [hsum, ← NormedSpace.exp_nsmul]
      congr 1
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      rw [show ((n + 1 : ℕ) : ℝ) = N from by rw [hN]; push_cast; ring]
      exact mul_div_cancel₀ t hN0.ne'
    set x : 𝕄 →L[ℂ] 𝕄 := NormedSpace.exp a * (1 + b) with hx
    set y : 𝕄 →L[ℂ] 𝕄 := NormedSpace.exp (a + b) with hy
    have hiden : x - y
        = (NormedSpace.exp a - 1 - a) * (1 + b) + a * b
          - (NormedSpace.exp (a + b) - 1 - (a + b)) := by
      rw [hx, hy]
      noncomm_ring
      try simp only [smul_mul_assoc, one_mul]
      try abel
    have hone_b : ‖(1 : 𝕄 →L[ℂ] 𝕄) + b‖ ≤ 1 + c := by
      refine le_trans (norm_add_le _ _) ?_
      exact add_le_add ContinuousLinearMap.norm_id_le hnb2
    have hRa : ‖NormedSpace.exp a - 1 - a‖
        ≤ (c / N) ^ 2 * Real.exp c := by
      refine le_trans (norm_exp_sub_one_sub_le a) ?_
      refine mul_le_mul ?_ ?_ (Real.exp_nonneg _) (by positivity)
      · exact pow_le_pow_left₀ (norm_nonneg _) hna 2
      · exact Real.exp_le_exp.mpr hna2
    have hab2 : ‖a + b‖ ≤ 2 * c / N := by
      refine le_trans (norm_add_le _ _) ?_
      calc ‖a‖ + ‖b‖ ≤ c / N + c / N := add_le_add hna hnb
        _ = 2 * c / N := by ring
    have hab3 : ‖a + b‖ ≤ 2 * c := by
      refine le_trans hab2 ?_
      rw [div_le_iff₀ hN0]
      nlinarith
    have hRab : ‖NormedSpace.exp (a + b) - 1 - (a + b)‖
        ≤ (2 * c / N) ^ 2 * Real.exp (2 * c) := by
      refine le_trans (norm_exp_sub_one_sub_le (a + b)) ?_
      refine mul_le_mul ?_ ?_ (Real.exp_nonneg _) (by positivity)
      · exact pow_le_pow_left₀ (norm_nonneg _) hab2 2
      · exact Real.exp_le_exp.mpr hab3
    have hxy : ‖x - y‖ ≤ C / N ^ 2 := by
      rw [hiden]
      have h1 : ‖(NormedSpace.exp a - 1 - a) * (1 + b) + a * b
          - (NormedSpace.exp (a + b) - 1 - (a + b))‖
          ≤ ‖(NormedSpace.exp a - 1 - a) * (1 + b)‖ + ‖a * b‖
            + ‖NormedSpace.exp (a + b) - 1 - (a + b)‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        exact add_le_add (norm_add_le _ _) le_rfl
      refine le_trans h1 ?_
      have h2 : ‖(NormedSpace.exp a - 1 - a) * (1 + b)‖
          ≤ (c / N) ^ 2 * Real.exp c * (1 + c) := by
        refine le_trans (norm_mul_le _ _) ?_
        refine mul_le_mul hRa hone_b (norm_nonneg _) (by positivity)
      have h3 : ‖a * b‖ ≤ (c / N) * (c / N) := by
        refine le_trans (norm_mul_le _ _) ?_
        exact mul_le_mul hna hnb (norm_nonneg _) hcN0
      rw [hC]
      rw [show (c ^ 2 * Real.exp c * (1 + c) + c ^ 2
          + (2 * c) ^ 2 * Real.exp (2 * c)) / N ^ 2
        = (c / N) ^ 2 * Real.exp c * (1 + c) + (c / N) * (c / N)
          + (2 * c / N) ^ 2 * Real.exp (2 * c) from by
        field_simp]
      exact add_le_add (add_le_add h2 h3) hRab
    have hxn : ‖x‖ ≤ Real.exp (2 * c / N) := by
      rw [hx]
      refine le_trans (norm_mul_le _ _) ?_
      have h4 : ‖NormedSpace.exp a‖ ≤ Real.exp (c / N) :=
        le_trans (norm_exp_le_exp_norm a) (Real.exp_le_exp.mpr hna)
      have h5 : ‖(1 : 𝕄 →L[ℂ] 𝕄) + b‖ ≤ Real.exp (c / N) := by
        refine le_trans (norm_add_le _ _) ?_
        refine le_trans (add_le_add ContinuousLinearMap.norm_id_le
          hnb) ?_
        rw [add_comm]
        exact Real.add_one_le_exp (c / N)
      calc ‖NormedSpace.exp a‖ * ‖(1 : 𝕄 →L[ℂ] 𝕄) + b‖
          ≤ Real.exp (c / N) * Real.exp (c / N) :=
            mul_le_mul h4 h5 (norm_nonneg _) (Real.exp_nonneg _)
        _ = Real.exp (2 * c / N) := by
            rw [← Real.exp_add]
            congr 1
            ring
    have hyn : ‖y‖ ≤ Real.exp (2 * c / N) := by
      rw [hy]
      refine le_trans (norm_exp_le_exp_norm _) ?_
      exact Real.exp_le_exp.mpr hab2
    have htel := norm_pow_sub_pow_le x y (Real.exp (2 * c / N))
      hxn hyn (n + 1)
    have hbase : (Real.exp (2 * c / N)) ^ ((n + 1) - 1)
        ≤ Real.exp (2 * c) := by
      have h6 : (Real.exp (2 * c / N)) ^ ((n + 1) - 1)
          ≤ (Real.exp (2 * c / N)) ^ (n + 1) := by
        refine pow_le_pow_right₀ ?_ (by omega)
        rw [Real.one_le_exp_iff]
        positivity
      refine le_trans h6 ?_
      rw [← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      rw [show ((n + 1 : ℕ) : ℝ) * (2 * c / N)
          = 2 * c * (((n + 1 : ℕ) : ℝ) / N) from by ring]
      rw [show ((n + 1 : ℕ) : ℝ) = N from by rw [hN]; push_cast; ring]
      rw [div_self hN0.ne', mul_one]
    have hfinal : ‖x ^ (n + 1) - y ^ (n + 1)‖
        ≤ C * Real.exp (2 * c) / N := by
      refine le_trans htel ?_
      calc ((n + 1 : ℕ) : ℝ)
            * (Real.exp (2 * c / N)) ^ ((n + 1) - 1) * ‖x - y‖
          ≤ N * Real.exp (2 * c) * (C / N ^ 2) := by
            rw [show ((n + 1 : ℕ) : ℝ) = N from by
              rw [hN]; push_cast; ring]
            refine mul_le_mul ?_ hxy (norm_nonneg _) ?_
            · exact mul_le_mul_of_nonneg_left hbase hN0.le
            · positivity
        _ = C * Real.exp (2 * c) / N := by
            field_simp
    rw [← hexp_pow]
    exact hfinal
  · have h7 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h8 := h7.const_mul (C * Real.exp (2 * c))
    rw [mul_zero] at h8
    refine h8.congr fun n => ?_
    rw [mul_one_div]

/-! ### Complete positivity of the Lindblad semigroup -/

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **`thm:stable-pointer-selection` clause (ii)**: the Lindblad
semigroup `e^{tℒ}` of the symmetric dissipator with hermitian jumps
is **completely positive** — every matrix ampliation preserves
positive semidefiniteness, for every `t ≥ 0`.  Proof: each Euler
factor `e^{tM/n}(1 + (t/n)Φ)` is a hermitian conjugation composed
with a positive-multiple-of-Kraus perturbation, hence ampliation
stable; the Euler products converge in operator norm to the
semigroup; and positivity is closed under limits. -/
theorem exp_dissipator_preservesPos {m : Type*} [Fintype m]
    (A : m → 𝕄) (hA : ∀ j, (A j)ᴴ = A j) {t : ℝ} (ht : 0 ≤ t) :
    PreservesPos
      (NormedSpace.exp (t • clm (dissipatorL A))).toLinearMap := by
  intro k X hX
  set G : 𝕄 := (-(1 / 2) : ℂ) • ∑ j, A j * A j with hG
  have hGh : Gᴴ = G := sumSq_conjTranspose A hA
  set Mg : 𝕄 →L[ℂ] 𝕄 := leftMulL G + rightMulL G with hMg
  have hD : clm (dissipatorL A) = krausL A + Mg := dissipatorL_split A
  -- the Euler iterates and their stability
  set T : ℕ → 𝕄 →L[ℂ] 𝕄 := fun n =>
    (NormedSpace.exp ((t / ((n : ℝ) + 1)) • Mg)
      * (1 + (t / ((n : ℝ) + 1)) • krausL A)) ^ (n + 1) with hT
  have hstab : ∀ n : ℕ, PreservesPos (T n).toLinearMap := by
    intro n
    rw [hT]
    refine PreservesPos.pow ?_ (n + 1)
    have hfac :
        (NormedSpace.exp ((t / ((n : ℝ) + 1)) • Mg)
          * (1 + (t / ((n : ℝ) + 1)) • krausL A)).toLinearMap
        = (conjL (matExp ((t / ((n : ℝ) + 1)) • G))).toLinearMap
          ∘ₗ (LinearMap.id
            + ((t / ((n : ℝ) + 1) : ℝ) : ℂ) • (krausL A).toLinearMap)
        := by
      rw [hMg, exp_smul_mulPair_eq_conjL,
        ← eulerCLM_toLinearMap A (t / ((n : ℝ) + 1))]
      rfl
    rw [hfac]
    refine PreservesPos.comp ?_ ?_
    · exact preservesPos_conjL
        (matExp_real_smul_conjTranspose hGh (t / ((n : ℝ) + 1)))
    · refine preservesPos_euler A hA ?_
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_nonneg ht this.le
  -- convergence of the iterates to the semigroup
  have hconv : Filter.Tendsto T Filter.atTop
      (nhds (NormedSpace.exp (t • clm (dissipatorL A)))) := by
    rw [hD]
    have h := euler_product_tendsto Mg (krausL A) t
    rw [show Mg + krausL A = krausL A + Mg from add_comm _ _] at h
    exact h
  -- the pointwise ampliated evaluation is continuous linear
  set F : (𝕄 →L[ℂ] 𝕄) →ₗ[ℂ]
      Matrix (Fin k × E) (Fin k × E) ℂ :=
    { toFun := fun Ψ => ampliateE k Ψ.toLinearMap X
      map_add' := fun Ψ₁ Ψ₂ => by
        rw [show (Ψ₁ + Ψ₂).toLinearMap
            = Ψ₁.toLinearMap + Ψ₂.toLinearMap from rfl, ampliateE_add]
        rfl
      map_smul' := fun cc Ψ => by
        simp only [RingHom.id_apply]
        rw [show (cc • Ψ).toLinearMap = cc • Ψ.toLinearMap from rfl,
          ampliateE_smul]
        rfl } with hF
  have hFcont : Continuous F := LinearMap.continuous_of_finiteDimensional F
  have hFlim : Filter.Tendsto (fun n => F (T n)) Filter.atTop
      (nhds (F (NormedSpace.exp (t • clm (dissipatorL A))))) :=
    (hFcont.tendsto _).comp hconv
  refine posSemidef_of_tendsto (Y := fun n => F (T n)) ?_ hFlim
  intro n
  exact hstab n k X hX

end NCG.Upstream
