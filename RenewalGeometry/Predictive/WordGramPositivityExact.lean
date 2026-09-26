/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.FlatWordReconstructionExact
import RenewalGeometry.Krein.PositiveKreinDistinct

/-!
# Positivity and faithfulness of the regular trace; the word-Gram panels
  (`thm:supp-word-flatness`, `eq:supp-regular-trace`, `eq:supp-word-gram`,
  `eq:supp-flat-stop`; emergent-spacetime manuscript)

## The regular trace on a matrix star-subalgebra

For a star-subalgebra `S` of `Matrix M M ℂ` (the represented history algebra
`A^hist`), the normalized regular trace `τ̂_reg(a) = Tr_ℂ(L_a)/dim S`
(`eq:supp-regular-trace`, `RenewalGeometry.normalizedRegularTrace`) is
computed through the Hilbert–Schmidt space: `matrixToHS` identifies matrices
with `EuclideanSpace ℂ (M × M)`, `hsImage S` is the image of `S` and
`hsEquiv S : S ≃ₗ hsImage S`; conjugating `L_z` to `hsImage S` and expanding
the trace in an orthonormal basis `(e_i)` of `hsImage S`
(`LinearMap.trace_eq_sum_inner`) gives `Tr(L_z) = ∑_i ⟪e_i, z e_i⟫_HS`
(`trace_lmul_eq_sum_inner`).  The Hilbert–Schmidt adjoint identity
`⟪X, a^* Y⟫ = ⟪a X, Y⟫` (`inner_matrixToHS_star_mul`) then yields

* `trace_lmul_star_mul_self`: `Tr(L_{a^* a}) = ∑_i ‖a e_i‖²`;
* `normalizedRegularTrace_star_mul_self_nonneg` / `_im`: `τ̂_reg(a^* a) ≥ 0`
  is real;
* `normalizedRegularTrace_star_mul_self_eq_zero_iff`: faithfulness
  `τ̂_reg(a^* a) = 0 ↔ a = 0`;
* `normalizedRegularTrace_star`: `τ̂_reg(a^*) = conj τ̂_reg(a)`.

## The word-Gram panels

`𝕂_{X,r}(v, w) = τ̂_reg([v]^* [w])` (`wordGramLevel`, `eq:supp-word-gram`) is
the Gram kernel of the word family for the positive faithful functional
`τ̂_reg` on `A^hist = historyAlgebra gen`:

* `wordGramLevel_positive`, `wordGramLevel_positive'`: every `𝕂_{X,r}` is
  positive semidefinite (first clause of `thm:supp-word-flatness`), and
  Hermitian (`wordGramLevel_conj`);
* `regularForm`: the faithful positive form `τ̂_reg(x^* y)` is the pull-back
  of the Euclidean inner product by the injective map
  `Φ x = (dim S)^{-1/2} (x e_i)_i` (`regularEmbedding`);
* `wordGramLevel_rank`: `rank 𝕂_{X,r} = dim 𝒲_{X,≤r}` (the Gram kernel is
  exactly the represented word-relation space), so `eq:supp-flat-stop`
  `rank 𝕂_{X,r_X} = rank 𝕂_{X,r_X+1}` is the dimension condition of
  `FlatWordReconstructionExact.lean`;
* `flat_word_reconstruction_rank`: `thm:supp-word-flatness` with the
  literal rank condition `eq:supp-flat-stop`: positivity of every panel,
  the least depth `r_X` with `rank 𝕂_{X,r_X} = rank 𝕂_{X,r_X+1}`, and the
  exhaustion `𝒲_{X,≤r_X} = A^hist` with constancy from `r_X` on.

Scoped hypotheses: the carrier `M` is nonempty (so `dim A^hist ≥ 1`) and the
word index types `Words Γ r` carry `Fintype`/`DecidableEq` instances (finite
alphabet).  Not covered: the reconstruction of units, multiplication,
involution, predictive core algebras and mixed histories from the panel
through depth `r_X + 1` (last clause of the theorem).
-/

open Matrix Module ComplexConjugate
open scoped ComplexOrder

namespace RenewalGeometry

/-- The inner product of an inner product space over `ℂ` (forcing the
`InnerProductSpace` instance path). -/
local notation "⟪" x ", " y "⟫" => @inner ℂ _ InnerProductSpace.toInner x y

noncomputable section

/-! ### The Hilbert–Schmidt space of matrices -/

section HS

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- Matrices as the Euclidean (Hilbert–Schmidt) space on `M × M`. -/
def matrixToHS : Matrix M M ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (M × M) where
  toFun X := WithLp.toLp 2 fun p => X p.1 p.2
  invFun x := Matrix.of fun i j => WithLp.ofLp x (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := by ext i j; rfl
  right_inv x := rfl

theorem inner_matrixToHS (X Y : Matrix M M ℂ) :
    ⟪matrixToHS X, matrixToHS Y⟫ = ∑ i, ∑ j, conj (X i j) * Y i j := by
  change ⟪WithLp.toLp 2 (fun p : M × M => X p.1 p.2),
    WithLp.toLp 2 (fun p : M × M => Y p.1 p.2)⟫ = _
  rw [EuclideanSpace.inner_toLp_toLp]
  unfold dotProduct
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def]
  ring

/-- The Hilbert–Schmidt adjoint identity `⟪X, a^* Y⟫ = ⟪a X, Y⟫`. -/
theorem inner_matrixToHS_star_mul (a X Y : Matrix M M ℂ) :
    ⟪matrixToHS X, matrixToHS (star a * Y)⟫ = ⟪matrixToHS (a * X), matrixToHS Y⟫ := by
  rw [inner_matrixToHS, inner_matrixToHS]
  simp only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def, Finset.mul_sum, map_sum,
    map_mul, Finset.sum_mul]
  calc ∑ i, ∑ j, ∑ k, conj (X i j) * (conj (a k i) * Y k j)
      = ∑ i, ∑ k, ∑ j, conj (X i j) * (conj (a k i) * Y k j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, conj (X i j) * (conj (a k i) * Y k j) := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, conj (a k i) * conj (X i j) * Y k j := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

end HS

/-! ### The regular trace on a matrix star-subalgebra -/

section StarSubalgebra

variable {M : Type*} [Fintype M] [DecidableEq M] (S : StarSubalgebra ℂ (Matrix M M ℂ))

/-- The image of `S` in the Hilbert–Schmidt space. -/
def hsImage : Submodule ℂ (EuclideanSpace ℂ (M × M)) :=
  (Subalgebra.toSubmodule S.toSubalgebra).map (matrixToHS.toLinearMap)

/-- `S ≃ₗ hsImage S`. -/
def hsEquiv : S ≃ₗ[ℂ] hsImage S :=
  matrixToHS.submoduleMap (Subalgebra.toSubmodule S.toSubalgebra)

theorem hsEquiv_apply (x : S) :
    (hsEquiv S x : EuclideanSpace ℂ (M × M)) = matrixToHS (x : Matrix M M ℂ) :=
  LinearEquiv.submoduleMap_apply _ _ _

/-- The orthonormal basis of the Hilbert–Schmidt image pulled back to `S`. -/
def hsBasisVec (i : Fin (finrank ℂ (hsImage S))) : S :=
  (hsEquiv S).symm (stdOrthonormalBasis ℂ (hsImage S) i)

theorem hsEquiv_hsBasisVec (i : Fin (finrank ℂ (hsImage S))) :
    hsEquiv S (hsBasisVec S i) = stdOrthonormalBasis ℂ (hsImage S) i :=
  LinearEquiv.apply_symm_apply _ _

/-- `Tr_S(L_z) = ∑_i ⟪e_i, z e_i⟫` over the pulled-back orthonormal basis. -/
theorem trace_lmul_eq_sum_inner (z : S) :
    LinearMap.trace ℂ S (Algebra.lmul ℂ S z)
      = ∑ i, ⟪hsEquiv S (hsBasisVec S i), hsEquiv S (z * hsBasisVec S i)⟫ := by
  rw [← LinearMap.trace_conj' _ (hsEquiv S),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ (hsImage S))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsEquiv_hsBasisVec]
  rfl

/-- `⟪e x, e (a^* y)⟫ = ⟪e (a x), e (a y)⟫` in `S`. -/
theorem inner_hsEquiv_star_mul (a x y : S) :
    ⟪hsEquiv S x, hsEquiv S (star a * y)⟫ = ⟪hsEquiv S (a * x), hsEquiv S y⟫ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, hsEquiv_apply, hsEquiv_apply, hsEquiv_apply,
    hsEquiv_apply]
  push_cast
  exact inner_matrixToHS_star_mul _ _ _

/-- `Tr_S(L_{x^* y}) = ∑_i ⟪x e_i, y e_i⟫`. -/
theorem trace_lmul_star_mul (x y : S) :
    LinearMap.trace ℂ S (Algebra.lmul ℂ S (star x * y))
      = ∑ i, ⟪hsEquiv S (x * hsBasisVec S i), hsEquiv S (y * hsBasisVec S i)⟫ := by
  rw [trace_lmul_eq_sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, inner_hsEquiv_star_mul]

/-- `Tr_S(L_{a^* a}) = ∑_i ‖a e_i‖²`. -/
theorem trace_lmul_star_mul_self (a : S) :
    LinearMap.trace ℂ S (Algebra.lmul ℂ S (star a * a))
      = ((∑ i, ‖hsEquiv S (a * hsBasisVec S i)‖ ^ 2 : ℝ) : ℂ) := by
  rw [trace_lmul_star_mul]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  rfl

theorem normalizedRegularTrace_apply' (z : S) :
    normalizedRegularTrace S z
      = (finrank ℂ S : ℂ)⁻¹ * LinearMap.trace ℂ S (Algebra.lmul ℂ S z) := rfl

/-- `τ̂_reg(a^* a)` as a real nonnegative number. -/
theorem normalizedRegularTrace_star_mul_self (a : S) :
    normalizedRegularTrace S (star a * a)
      = (((finrank ℂ S : ℝ)⁻¹ * ∑ i, ‖hsEquiv S (a * hsBasisVec S i)‖ ^ 2 : ℝ) : ℂ) := by
  rw [normalizedRegularTrace_apply', trace_lmul_star_mul_self]
  push_cast
  rfl

/-- Positivity of the regular trace: `τ̂_reg(a^* a) ≥ 0`. -/
theorem normalizedRegularTrace_star_mul_self_nonneg (a : S) :
    0 ≤ (normalizedRegularTrace S (star a * a)).re := by
  rw [normalizedRegularTrace_star_mul_self, Complex.ofReal_re]
  positivity

/-- `τ̂_reg(a^* a)` is real. -/
theorem normalizedRegularTrace_star_mul_self_im (a : S) :
    (normalizedRegularTrace S (star a * a)).im = 0 := by
  rw [normalizedRegularTrace_star_mul_self, Complex.ofReal_im]

/-- `τ̂_reg(a^*) = conj τ̂_reg(a)`. -/
theorem normalizedRegularTrace_star (a : S) :
    normalizedRegularTrace S (star a) = conj (normalizedRegularTrace S a) := by
  rw [normalizedRegularTrace_apply', normalizedRegularTrace_apply', map_mul, map_inv₀,
    Complex.conj_natCast]
  congr 1
  have h1 := trace_lmul_star_mul S a 1
  have h2 := trace_lmul_star_mul S 1 a
  rw [mul_one] at h1
  rw [star_one, one_mul] at h2
  rw [h1, h2, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [one_mul, ← inner_conj_symm]

instance instFiniteDimensionalStarSubalgebra : FiniteDimensional ℂ S :=
  inferInstanceAs (FiniteDimensional ℂ (Subalgebra.toSubmodule S.toSubalgebra))

theorem finrank_pos_of_nonempty [Nonempty M] : 0 < finrank ℂ S := by
  have : Nontrivial S := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg (fun x : S => (x : Matrix M M ℂ)) h
    simp only [ZeroMemClass.coe_zero, OneMemClass.coe_one] at h'
    exact zero_ne_one h'
  exact Module.finrank_pos

/-- Faithfulness of the regular trace: `τ̂_reg(a^* a) = 0 ↔ a = 0`. -/
theorem normalizedRegularTrace_star_mul_self_eq_zero_iff [Nonempty M] (a : S) :
    normalizedRegularTrace S (star a * a) = 0 ↔ a = 0 := by
  constructor
  · intro h
    rw [normalizedRegularTrace_star_mul_self, Complex.ofReal_eq_zero] at h
    have hD : ((finrank ℂ S : ℝ)⁻¹) ≠ 0 := by
      have := finrank_pos_of_nonempty S
      positivity
    have hsum : ∑ i, ‖hsEquiv S (a * hsBasisVec S i)‖ ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left hD
    have hzero : ∀ i, a * hsBasisVec S i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg
        ‖hsEquiv S (a * hsBasisVec S j)‖).mp hsum i (Finset.mem_univ i)
      have h0 : hsEquiv S (a * hsBasisVec S i) = 0 := by
        rw [sq_eq_zero_iff, norm_eq_zero] at this
        exact this
      exact (hsEquiv S).map_eq_zero_iff.mp h0
    -- `L_a` vanishes on a basis of `S`, hence `a = a * 1 = 0`
    have hbasis : (Algebra.lmul ℂ S a : S →ₗ[ℂ] S) = 0 := by
      apply ((stdOrthonormalBasis ℂ (hsImage S)).toBasis.map (hsEquiv S).symm).ext
      intro i
      rw [Basis.map_apply, OrthonormalBasis.coe_toBasis, LinearMap.zero_apply]
      exact hzero i
    have := congrArg (fun f : S →ₗ[ℂ] S => f 1) hbasis
    simpa using this
  · rintro rfl
    simp

/-! ### The regular embedding `Φ x = (dim S)^{-1/2} (x e_i)_i` -/

/-- The normalization `(dim S)^{-1/2}`. -/
def regNorm : ℝ := (Real.sqrt (finrank ℂ S))⁻¹

/-- The regular embedding `Φ x = (dim S)^{-1/2} (x e_i)_i` of `S` into a Euclidean space,
whose inner product is the regular form `τ̂_reg(x^* y)`. -/
def regularEmbedding :
    S →ₗ[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ (hsImage S)) × (M × M)) where
  toFun x := WithLp.toLp 2 fun q =>
    (regNorm S : ℂ) * WithLp.ofLp (hsEquiv S (x * hsBasisVec S q.1) : EuclideanSpace ℂ (M × M)) q.2
  map_add' x y := by
    ext q
    simp only [add_mul, map_add, Submodule.coe_add, WithLp.ofLp_add, Pi.add_apply, mul_add]
  map_smul' c x := by
    ext q
    simp only [smul_mul_assoc, map_smul, Submodule.coe_smul, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

theorem regularEmbedding_apply (x : S) (q : Fin (finrank ℂ (hsImage S)) × (M × M)) :
    WithLp.ofLp (regularEmbedding S x) q
      = (regNorm S : ℂ)
        * WithLp.ofLp (hsEquiv S (x * hsBasisVec S q.1) : EuclideanSpace ℂ (M × M)) q.2 := rfl

theorem inner_regularEmbedding (x y : S) :
    ⟪regularEmbedding S x, regularEmbedding S y⟫
      = ((regNorm S ^ 2 : ℝ) : ℂ)
        * ∑ i, ⟪hsEquiv S (x * hsBasisVec S i), hsEquiv S (y * hsBasisVec S i)⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [regularEmbedding_apply, Pi.star_apply, Complex.star_def, map_mul,
    Complex.conj_ofReal]
  push_cast
  ring

theorem regNorm_sq [Nonempty M] : regNorm S ^ 2 = (finrank ℂ S : ℝ)⁻¹ := by
  unfold regNorm
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The regular form is the pull-back of the Euclidean inner product:
`τ̂_reg(x^* y) = ⟪Φ x, Φ y⟫`. -/
theorem normalizedRegularTrace_star_mul_eq_inner [Nonempty M] (x y : S) :
    normalizedRegularTrace S (star x * y) = ⟪regularEmbedding S x, regularEmbedding S y⟫ := by
  rw [inner_regularEmbedding, regNorm_sq, normalizedRegularTrace_apply', trace_lmul_star_mul]
  push_cast
  rfl

theorem regularEmbedding_injective [Nonempty M] : Function.Injective (regularEmbedding S) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h := normalizedRegularTrace_star_mul_eq_inner S x x
  rw [hx, inner_zero_left] at h
  exact (normalizedRegularTrace_star_mul_self_eq_zero_iff S x).mp h

end StarSubalgebra

/-! ### The word-Gram panels of the history algebra -/

section WordGram

open FiniteGrandTensor (historyAlgebra wordOp wordOp_mem Words wordGramLevel wordPair
  historyWordSpan genLetter wordOp_mem_historyWordSpan exists_least_flat_depth
  flat_word_reconstruction_partial)

variable {M : Type*} [Fintype M] [DecidableEq M] {Γ : Type*}

/-- The represented word `[w]` as an element of `A^hist`. -/
def wordElt (gen : Γ → Matrix M M ℂ) (w : List Γ) : historyAlgebra gen :=
  ⟨wordOp gen w, wordOp_mem gen w⟩

theorem wordPair_eq (gen : Γ → Matrix M M ℂ) (v w : List Γ) :
    wordPair gen v w = star (wordElt gen v) * wordElt gen w := rfl

/-- `𝕂_{X,r}` is the word Gram of the family `[w]` for the regular trace. -/
theorem wordGramLevel_eq_wordGram (gen : Γ → Matrix M M ℂ) (r : ℕ) (v w : Words Γ r) :
    wordGramLevel gen r v w
      = RenewalGeometry.wordGram (normalizedRegularTrace (historyAlgebra gen))
          (fun u : Words Γ r => wordElt gen u.1) v w := rfl

/-- **First clause of `thm:supp-word-flatness`**: every panel `𝕂_{X,r}` is positive
semidefinite: `∑_{v,w} conj(c_v) c_w 𝕂_{X,r}(v, w) ≥ 0` for every finite family of words of
length `≤ r`. -/
theorem wordGramLevel_positive (gen : Γ → Matrix M M ℂ) (r : ℕ) {ι : Type*} [Fintype ι]
    (w : ι → Words Γ r) (c : ι → ℂ) :
    0 ≤ (∑ i, ∑ j, star (c i) * c j * wordGramLevel gen r (w i) (w j)).re :=
  RenewalGeometry.wordGram_positive (normalizedRegularTrace (historyAlgebra gen))
    (fun a => normalizedRegularTrace_star_mul_self_nonneg _ a) (fun i => wordElt gen (w i).1) c

/-- Positivity of `𝕂_{X,r}` as a matrix indexed by all words of length `≤ r`. -/
theorem wordGramLevel_positive' (gen : Γ → Matrix M M ℂ) (r : ℕ) [Fintype (Words Γ r)]
    (c : Words Γ r → ℂ) :
    0 ≤ (∑ v, ∑ w, star (c v) * c w * wordGramLevel gen r v w).re :=
  wordGramLevel_positive gen r id c

/-- `𝕂_{X,r}` is Hermitian. -/
theorem wordGramLevel_conj (gen : Γ → Matrix M M ℂ) (r : ℕ) (v w : Words Γ r) :
    conj (wordGramLevel gen r v w) = wordGramLevel gen r w v := by
  rw [wordGramLevel_eq_wordGram, wordGramLevel_eq_wordGram]
  unfold RenewalGeometry.wordGram
  rw [← normalizedRegularTrace_star, star_mul, star_star]

/-- The word span `𝒲_{X,≤r}` is the span of the represented words of length `≤ r`. -/
theorem historyWordSpan_eq_span (gen : Γ → Matrix M M ℂ) (r : ℕ) :
    historyWordSpan gen r
      = Submodule.span ℂ (Set.range fun v : Words Γ r => wordOp gen v.1) := by
  apply le_antisymm
  · induction r with
    | zero =>
      unfold historyWordSpan
      rw [wordSpan_zero, Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Submodule.subset_span ⟨⟨[], Nat.le_refl 0⟩, rfl⟩
    | succ r ih =>
      unfold historyWordSpan at ih ⊢
      rw [wordSpan_succ]
      refine sup_le (ih.trans (Submodule.span_mono ?_)) (iSup_le fun γ => ?_)
      · rintro _ ⟨v, rfl⟩
        exact ⟨⟨v.1, v.2.trans (Nat.le_succ r)⟩, rfl⟩
      · refine (Submodule.map_mono ih).trans ?_
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
        refine Submodule.subset_span ⟨⟨γ :: v.1, ?_⟩, rfl⟩
        simp only [List.length_cons]
        exact Nat.succ_le_succ v.2
  · rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact wordOp_mem_historyWordSpan gen v.1 r v.2

/-- The panel `𝕂_{X,r}` as a matrix indexed by the words of length `≤ r`. -/
def gramPanel (gen : Γ → Matrix M M ℂ) (r : ℕ) : Matrix (Words Γ r) (Words Γ r) ℂ :=
  Matrix.of fun v w => wordGramLevel gen r v w

/-- The coordinates of the words in the regular embedding: `C_{q v} = (Φ [v])_q`. -/
def wordCoordinates (gen : Γ → Matrix M M ℂ) (r : ℕ) :
    Matrix (Fin (finrank ℂ (hsImage (historyAlgebra gen))) × (M × M)) (Words Γ r) ℂ :=
  Matrix.of fun q v => WithLp.ofLp (regularEmbedding (historyAlgebra gen) (wordElt gen v.1)) q

/-- `𝕂_{X,r} = C^* C`. -/
theorem conjTranspose_mul_wordCoordinates [Nonempty M] (gen : Γ → Matrix M M ℂ) (r : ℕ)
    [Fintype (Words Γ r)] :
    (wordCoordinates gen r)ᴴ * wordCoordinates gen r = gramPanel gen r := by
  ext v w
  rw [Matrix.mul_apply, gramPanel, Matrix.of_apply, wordGramLevel_eq_wordGram,
    RenewalGeometry.wordGram, normalizedRegularTrace_star_mul_eq_inner,
    EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Matrix.conjTranspose_apply, wordCoordinates, Matrix.of_apply, Pi.star_apply,
    Complex.star_def]
  ring

/-- Finite rank is preserved by injective linear maps. -/
theorem finrank_map_of_injective {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (p : Submodule ℂ V) :
    finrank ℂ (p.map f) = finrank ℂ p := by
  have h : p.map f = LinearMap.range (f ∘ₗ p.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hinj : Function.Injective (f ∘ₗ p.subtype) := by
    rw [LinearMap.coe_comp]
    exact hf.comp (Submodule.injective_subtype p)
  rw [h, LinearMap.finrank_range_of_inj hinj]

/-- **`rank 𝕂_{X,r} = dim 𝒲_{X,≤r}`**: the Gram kernel is exactly the represented
word-relation space (faithfulness of the regular trace). -/
theorem rank_gramPanel [Nonempty M] (gen : Γ → Matrix M M ℂ) (r : ℕ) [Fintype (Words Γ r)] :
    (gramPanel gen r).rank = finrank ℂ (historyWordSpan gen r) := by
  rw [← conjTranspose_mul_wordCoordinates, Matrix.rank_conjTranspose_mul_self,
    Matrix.rank_eq_finrank_span_cols, historyWordSpan_eq_span]
  set S := historyAlgebra gen
  set f : S →ₗ[ℂ] (Fin (finrank ℂ (hsImage S)) × (M × M) → ℂ) :=
    (WithLp.linearEquiv 2 ℂ _).toLinearMap ∘ₗ regularEmbedding S with hf
  have hfinj : Function.Injective f := by
    rw [hf, LinearMap.coe_comp, LinearEquiv.coe_coe]
    exact (WithLp.linearEquiv 2 ℂ _).injective.comp (regularEmbedding_injective S)
  set u : Words Γ r → S := fun v => wordElt gen v.1 with hu
  have hcol : Set.range (wordCoordinates gen r).col = f '' Set.range u := by
    ext x
    simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
    rfl
  set ι : S →ₗ[ℂ] Matrix M M ℂ := (Subalgebra.val S.toSubalgebra).toLinearMap with hι
  have hιinj : Function.Injective ι := Subtype.val_injective
  have hrange : Set.range (fun v : Words Γ r => wordOp gen v.1) = ι '' Set.range u := by
    ext x
    simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
    rfl
  rw [hcol, hrange, ← Submodule.map_span, ← Submodule.map_span, finrank_map_of_injective f hfinj,
    finrank_map_of_injective ι hιinj]

/-- **`thm:supp-word-flatness`, positivity / flat-stop / exhaustion clauses** with the
literal rank condition `eq:supp-flat-stop`.  For a star-closed represented generator
family on a nonempty finite carrier: every panel `𝕂_{X,r}` is positive; there is a least
depth `r_X` with `rank 𝕂_{X,r_X} = rank 𝕂_{X,r_X+1}` (and strict growth below); at that
depth the represented word span is the whole history algebra `A^hist`, and the word spans
are constant from `r_X` on. -/
theorem flat_word_reconstruction_rank [Nonempty M] (gen : Γ → Matrix M M ℂ)
    [∀ r, Fintype (Words Γ r)] (hstar : ∀ γ, ∃ γ', star (gen γ) = gen γ') :
    (∀ (r : ℕ) (c : Words Γ r → ℂ),
        0 ≤ (∑ v, ∑ w, star (c v) * c w * wordGramLevel gen r v w).re) ∧
    ∃ r : ℕ,
      ((gramPanel gen r).rank = (gramPanel gen (r + 1)).rank ∧
        ∀ r' < r, (gramPanel gen r').rank ≠ (gramPanel gen (r' + 1)).rank) ∧
      historyWordSpan gen r = Subalgebra.toSubmodule (historyAlgebra gen).toSubalgebra ∧
      ∀ s, r ≤ s → historyWordSpan gen s = historyWordSpan gen r := by
  refine ⟨fun r c => wordGramLevel_positive' gen r c, ?_⟩
  obtain ⟨r, ⟨hr, hmin⟩, hex, hconst⟩ := flat_word_reconstruction_partial gen hstar
  refine ⟨r, ⟨?_, fun r' hr' => ?_⟩, hex, hconst⟩
  · rw [rank_gramPanel, rank_gramPanel]; exact hr
  · rw [rank_gramPanel, rank_gramPanel]; exact hmin r' hr'

end WordGram

end

end RenewalGeometry
