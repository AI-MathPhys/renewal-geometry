/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.IntrinsicRegularTrace
import RenewalGeometry.Predictive.ExactSourceSchurResidual

/-!
# Word-module recognition, word-native shadows and inserted word moments

Covers `thm:word-module-recognition`, `def:word-native-shadow`,
`thm:inserted-word-moments` and `cor:table-native-ancestry` of the
spacetime–gauge duality paper.

* On the regular word carrier `𝒲 = A` of a finite-dimensional unital algebra `A`
  (the underlying vector space of `L²(A, τ_reg)`), with `L_a = mulLeft a`,
  `R_b = mulRight b` and `U_g = α_g` for a family of algebra automorphisms,
  `word_module_recognition` proves `R(A)' ∩ U(G)' = L(A^G)` inside `End(𝒲)`,
  and `word_module_recognition_iff` the "if and only if / unique coefficient `T 1`" form.
* `WordNativeShadow` / `IsWordNative`: the maps `X ↦ ∑_α c_α A_α X B_α`
  (`def:word-native-shadow`), with the compression, conjugation, sum, scalar and
  finite-average closure clauses.
* `inserted_one_moment`, `inserted_two_moments`: the inserted word-moment compiler
  (`thm:inserted-word-moments`) for the `τ_reg`-inner product `⟨y, x⟩ = τ_reg(y^* x)`.
* `table_native_GCH`, `table_native_ancestry_short`,
  `table_native_ancestry_short_determined_by_panels`: the table-native Gram blocks
  `G, C, H` and the ancestry short `R_{T|S} = H − C^* G^† C` (`cor:table-native-ancestry`).
-/

open Matrix

namespace RenewalGeometry

/-! ### `thm:word-module-recognition` -/

section WordModule

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Right multiplications `R_b` on the regular word carrier. -/
def rightMultiplications (A : Type*) [Ring A] [Algebra ℂ A] : Set (Module.End ℂ A) :=
  Set.range (LinearMap.mulRight ℂ : A → Module.End ℂ A)

/-- The symmetry operators `U_g x = α_g(x)` on the regular word carrier. -/
def symmetryOperators {G : Type*} (α : G → (A ≃ₐ[ℂ] A)) : Set (Module.End ℂ A) :=
  Set.range fun g => ((α g).toLinearMap : Module.End ℂ A)

/-- The invariant historical elements `A^G = {a ∈ A : α_g(a) = a for all g}`. -/
def invariantElements {G : Type*} (α : G → (A ≃ₐ[ℂ] A)) : Set A :=
  {a | ∀ g, α g a = a}

theorem mulLeft_mem_centralizer_rightMultiplications (a : A) :
    (LinearMap.mulLeft ℂ a : Module.End ℂ A) ∈ Set.centralizer (rightMultiplications A) := by
  rintro _ ⟨b, rfl⟩
  ext x
  simp [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc]

/-- `U_g L_a U_g⁻¹ = L_{α_g(a)}`: conjugating a left multiplication by a symmetry. -/
theorem symmetry_mul_mulLeft {G : Type*} (α : G → (A ≃ₐ[ℂ] A)) (g : G) (a : A) :
    ((α g).toLinearMap : Module.End ℂ A) * LinearMap.mulLeft ℂ a =
      LinearMap.mulLeft ℂ (α g a) * (α g).toLinearMap := by
  ext x
  simp [Module.End.mul_apply, LinearMap.mulLeft_apply]

/-- A commutant element of all right multiplications is the left multiplication by `T 1`. -/
theorem eq_mulLeft_of_mem_centralizer_rightMultiplications (T : Module.End ℂ A)
    (hT : T ∈ Set.centralizer (rightMultiplications A)) :
    T = LinearMap.mulLeft ℂ (T 1) := by
  ext b
  have h := hT (LinearMap.mulRight ℂ b) ⟨b, rfl⟩
  have h1 := congrArg (fun S : Module.End ℂ A => S 1) h
  simp only [Module.End.mul_apply, LinearMap.mulRight_apply, one_mul] at h1
  rw [LinearMap.mulLeft_apply, ← h1]

/-- Left multiplication by `a` commutes with every `U_g` iff `a` is invariant. -/
theorem mulLeft_mem_centralizer_symmetry_iff {G : Type*} (α : G → (A ≃ₐ[ℂ] A)) (a : A) :
    (LinearMap.mulLeft ℂ a : Module.End ℂ A) ∈ Set.centralizer (symmetryOperators α) ↔
      a ∈ invariantElements α := by
  constructor
  · intro h g
    have hg := h ((α g).toLinearMap) ⟨g, rfl⟩
    have h1 := congrArg (fun S : Module.End ℂ A => S 1) hg
    simpa [Module.End.mul_apply, LinearMap.mulLeft_apply] using h1
  · rintro ha _ ⟨g, rfl⟩
    rw [symmetry_mul_mulLeft, ha g]

/-- **Word-module recognition of historical internal actions
(`thm:word-module-recognition`).**  On the regular word carrier,
`R(A)' ∩ U(G)' = L(A^G)`: the endomorphisms commuting with every right multiplication and
every symmetry `U_g` are exactly the left multiplications by invariant elements. -/
theorem word_module_recognition {G : Type*} (α : G → (A ≃ₐ[ℂ] A)) :
    Set.centralizer (rightMultiplications A) ∩ Set.centralizer (symmetryOperators α) =
      (LinearMap.mulLeft ℂ : A → Module.End ℂ A) '' invariantElements α := by
  ext T
  constructor
  · rintro ⟨hR, hU⟩
    have hT := eq_mulLeft_of_mem_centralizer_rightMultiplications T hR
    refine ⟨T 1, ?_, hT.symm⟩
    rw [← mulLeft_mem_centralizer_symmetry_iff α, ← hT]
    exact hU
  · rintro ⟨a, ha, rfl⟩
    exact ⟨mulLeft_mem_centralizer_rightMultiplications a,
      (mulLeft_mem_centralizer_symmetry_iff α a).mpr ha⟩

/-- The "equivalently" clause of `thm:word-module-recognition`: `T ∈ End(𝒲)` is left
multiplication by a unique invariant historical element iff it commutes with every right
multiplication and every `U_g`; the coefficient is `T 1`. -/
theorem word_module_recognition_iff {G : Type*} (α : G → (A ≃ₐ[ℂ] A)) (T : Module.End ℂ A) :
    ((∀ b : A, T * LinearMap.mulRight ℂ b = LinearMap.mulRight ℂ b * T) ∧
        ∀ g, T * (α g).toLinearMap = (α g).toLinearMap * T) ↔
      ∃! a : A, a ∈ invariantElements α ∧ T = LinearMap.mulLeft ℂ a := by
  have hmem : T ∈ Set.centralizer (rightMultiplications A) ∩
      Set.centralizer (symmetryOperators α) ↔
      ((∀ b : A, T * LinearMap.mulRight ℂ b = LinearMap.mulRight ℂ b * T) ∧
        ∀ g, T * (α g).toLinearMap = (α g).toLinearMap * T) := by
    constructor
    · rintro ⟨hR, hU⟩
      exact ⟨fun b => (hR _ ⟨b, rfl⟩).symm, fun g => (hU _ ⟨g, rfl⟩).symm⟩
    · rintro ⟨hR, hU⟩
      exact ⟨by rintro _ ⟨b, rfl⟩; exact (hR b).symm,
        by rintro _ ⟨g, rfl⟩; exact (hU g).symm⟩
  rw [← hmem, word_module_recognition α]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ⟨ha, rfl⟩, ?_⟩
    rintro a' ⟨_, ha'⟩
    have := congrArg (fun S : Module.End ℂ A => S 1) ha'
    simpa [LinearMap.mulLeft_apply] using this.symm
  · rintro ⟨a, ⟨ha, rfl⟩, _⟩
    exact ⟨a, ha, rfl⟩

/-- The coefficient in `thm:word-module-recognition` is `T 1`. -/
theorem word_module_recognition_coefficient (T : Module.End ℂ A)
    (hR : ∀ b : A, T * LinearMap.mulRight ℂ b = LinearMap.mulRight ℂ b * T) :
    T = LinearMap.mulLeft ℂ (T 1) :=
  eq_mulLeft_of_mem_centralizer_rightMultiplications T
    (by rintro _ ⟨b, rfl⟩; exact (hR b).symm)

end WordModule

/-! ### `def:word-native-shadow` -/

section WordNative

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **Word-native linear shadow (`def:word-native-shadow`)**: the declared data
`(c_α, A_α, B_α)_{α < m}` of a map `X ↦ ∑_α c_α A_α X B_α` with `A_α, B_α` historical-algebra
elements and coefficients `c_α` fixed in advance. -/
structure WordNativeShadow (A : Type*) [Ring A] [Algebra ℂ A] where
  /-- number of terms -/
  m : ℕ
  /-- the fixed coefficients `c_α` -/
  coeff : Fin m → ℂ
  /-- the left insertions `A_α` -/
  left : Fin m → A
  /-- the right insertions `B_α` -/
  right : Fin m → A

namespace WordNativeShadow

/-- The linear map `X ↦ ∑_α c_α A_α X B_α` of a word-native shadow. -/
def toLinearMap (L : WordNativeShadow A) : Module.End ℂ A :=
  ∑ i, L.coeff i • (LinearMap.mulLeft ℂ (L.left i) * LinearMap.mulRight ℂ (L.right i))

theorem toLinearMap_apply (L : WordNativeShadow A) (X : A) :
    L.toLinearMap X = ∑ i, L.coeff i • (L.left i * X * L.right i) := by
  simp [toLinearMap, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, mul_assoc]

end WordNativeShadow

/-- A linear map `A → A` is word native iff it is `X ↦ ∑_α c_α A_α X B_α` for some
word-native shadow data (`eq:word-native-shadow`). -/
def IsWordNative (T : Module.End ℂ A) : Prop :=
  ∃ L : WordNativeShadow A, T = L.toLinearMap

theorem isWordNative_iff (T : Module.End ℂ A) :
    IsWordNative T ↔ ∃ (m : ℕ) (c : Fin m → ℂ) (P Q : Fin m → A),
      ∀ X, T X = ∑ i, c i • (P i * X * Q i) := by
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨L.m, L.coeff, L.left, L.right, L.toLinearMap_apply⟩
  · rintro ⟨m, c, P, Q, h⟩
    refine ⟨⟨m, c, P, Q⟩, ?_⟩
    ext X
    rw [h X, WordNativeShadow.toLinearMap_apply]

/-- A single insertion `X ↦ P X Q` is word native. -/
theorem isWordNative_mulLeft_mul_mulRight (P Q : A) :
    IsWordNative (LinearMap.mulLeft ℂ P * LinearMap.mulRight ℂ Q : Module.End ℂ A) := by
  refine ⟨⟨1, fun _ => 1, fun _ => P, fun _ => Q⟩, ?_⟩
  ext X
  simp [WordNativeShadow.toLinearMap_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, mul_assoc]

/-- Finite compressions `X ↦ p X p` by elements of `A` are word native. -/
theorem isWordNative_compression (p : A) :
    IsWordNative (LinearMap.mulLeft ℂ p * LinearMap.mulRight ℂ p : Module.End ℂ A) :=
  isWordNative_mulLeft_mul_mulRight p p

/-- Conjugations `X ↦ u X u⁻¹` by units of `A` are word native. -/
theorem isWordNative_conjugation (u : Aˣ) :
    IsWordNative (LinearMap.mulLeft ℂ (u : A) * LinearMap.mulRight ℂ ((u⁻¹ : Aˣ) : A) :
      Module.End ℂ A) :=
  isWordNative_mulLeft_mul_mulRight _ _

/-- The identity is word native. -/
theorem isWordNative_one : IsWordNative (1 : Module.End ℂ A) := by
  refine ⟨⟨1, fun _ => 1, fun _ => 1, fun _ => 1⟩, ?_⟩
  ext X
  simp [WordNativeShadow.toLinearMap_apply]

theorem isWordNative_zero : IsWordNative (0 : Module.End ℂ A) := by
  refine ⟨⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, ?_⟩
  ext X
  simp [WordNativeShadow.toLinearMap_apply]

/-- Scalar multiples of word-native maps are word native. -/
theorem IsWordNative.smul {T : Module.End ℂ A} (h : IsWordNative T) (c : ℂ) :
    IsWordNative (c • T) := by
  obtain ⟨L, rfl⟩ := h
  refine ⟨⟨L.m, fun i => c * L.coeff i, L.left, L.right⟩, ?_⟩
  ext X
  simp [WordNativeShadow.toLinearMap_apply, Finset.smul_sum, smul_smul]

/-- Sums of word-native maps are word native. -/
theorem IsWordNative.add {T T' : Module.End ℂ A} (h : IsWordNative T) (h' : IsWordNative T') :
    IsWordNative (T + T') := by
  obtain ⟨L, rfl⟩ := h
  obtain ⟨L', rfl⟩ := h'
  refine ⟨⟨L.m + L'.m, Fin.append L.coeff L'.coeff, Fin.append L.left L'.left,
    Fin.append L.right L'.right⟩, ?_⟩
  ext X
  simp only [LinearMap.add_apply, WordNativeShadow.toLinearMap_apply, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right]

/-- Finite sums of word-native maps are word native. -/
theorem isWordNative_sum {ι : Type*} (s : Finset ι) (T : ι → Module.End ℂ A)
    (h : ∀ i ∈ s, IsWordNative (T i)) : IsWordNative (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isWordNative_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Finite group averages `X ↦ |G|⁻¹ ∑_g u_g X u_g⁻¹` of conjugations by units are word
native. -/
theorem isWordNative_groupAverage {G : Type*} [Fintype G] (u : G → Aˣ) :
    IsWordNative ((Fintype.card G : ℂ)⁻¹ •
      ∑ g, (LinearMap.mulLeft ℂ (u g : A) * LinearMap.mulRight ℂ (((u g)⁻¹ : Aˣ) : A) :
        Module.End ℂ A)) :=
  (isWordNative_sum Finset.univ _ fun g _ => isWordNative_conjugation (u g)).smul _

end WordNative

/-! ### `thm:inserted-word-moments` -/

section InsertedMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]

/-- The `τ`-inner product `⟨y, x⟩ = τ(y^* x)` on the word carrier for a linear functional
`τ`; with `τ = τ_reg` this is the Hilbert–Schmidt inner product of `L²(A, τ_reg)`. -/
def wordInner (τ : A →ₗ[ℂ] ℂ) (y x : A) : ℂ :=
  τ (star y * x)

/-- The regular-trace (Hilbert–Schmidt) inner product `⟨y, x⟩_HS = τ_reg(y^* x)`. -/
noncomputable def regularWordInner (y x : A) : ℂ :=
  wordInner (normalizedRegularTrace A) y x

/-- One inserted moment (`eq:inserted-one-moment`) for an arbitrary linear functional. -/
theorem wordInner_shadow (τ : A →ₗ[ℂ] ℂ) (L : WordNativeShadow A) (y x : A) :
    wordInner τ y (L.toLinearMap x) =
      ∑ i, L.coeff i • τ (star y * L.left i * x * L.right i) := by
  simp only [wordInner, WordNativeShadow.toLinearMap_apply, Finset.mul_sum, map_sum,
    mul_smul_comm, map_smul, mul_assoc]

/-- Two inserted moments (`eq:inserted-two-moments`) for an arbitrary linear functional. -/
theorem wordInner_shadow_shadow [StarModule ℂ A] (τ : A →ₗ[ℂ] ℂ) (L M : WordNativeShadow A)
    (x z : A) :
    wordInner τ (L.toLinearMap x) (M.toLinearMap z) =
      ∑ i, ∑ j, (star (L.coeff i) * M.coeff j) •
        τ (star (L.right i) * star x * star (L.left i) * M.left j * z * M.right j) := by
  simp only [wordInner, WordNativeShadow.toLinearMap_apply, star_sum, star_smul, star_mul,
    Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_smul_comm, map_smul, mul_assoc]
  rw [Finset.sum_comm]

/-- **Inserted word-moment compiler, one insertion (`eq:inserted-one-moment`).**
`⟨y, 𝓛(x)⟩_HS = ∑_α c_α τ_reg(y^* A_α x B_α)`. -/
theorem inserted_one_moment (L : WordNativeShadow A) (y x : A) :
    regularWordInner y (L.toLinearMap x) =
      ∑ i, L.coeff i • normalizedRegularTrace A (star y * L.left i * x * L.right i) :=
  wordInner_shadow _ L y x

/-- **Inserted word-moment compiler, two insertions (`eq:inserted-two-moments`).**
`⟨𝓛(x), 𝓜(z)⟩_HS = ∑_{α,β} conj(c_α) d_β τ_reg(B_α^* x^* A_α^* C_β z D_β)`. -/
theorem inserted_two_moments [StarModule ℂ A] (L M : WordNativeShadow A) (x z : A) :
    regularWordInner (L.toLinearMap x) (M.toLinearMap z) =
      ∑ i, ∑ j, (star (L.coeff i) * M.coeff j) •
        normalizedRegularTrace A
          (star (L.right i) * star x * star (L.left i) * M.left j * z * M.right j) :=
  wordInner_shadow_shadow _ L M x z

/-- The ordinary–shadow Gram block is a finite linear combination of ordinary word
moments `τ_reg(w)` of represented words `w = y^* A_α x B_α`: the paper's "hence" clause. -/
theorem inserted_one_moment_mem_span (L : WordNativeShadow A) (y x : A) :
    regularWordInner y (L.toLinearMap x) ∈
      Submodule.span ℂ (Set.range fun w : A => normalizedRegularTrace A w) := by
  rw [inserted_one_moment]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The shadow–shadow Gram block is a finite linear combination of ordinary word moments. -/
theorem inserted_two_moments_mem_span [StarModule ℂ A] (L M : WordNativeShadow A) (x z : A) :
    regularWordInner (L.toLinearMap x) (M.toLinearMap z) ∈
      Submodule.span ℂ (Set.range fun w : A => normalizedRegularTrace A w) := by
  rw [inserted_two_moments]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end InsertedMoments

/-! ### `cor:table-native-ancestry` -/

section TableNative

/-- The historical word Gram panel `K^{00} = W_r^* W_r`. -/
def panelK00 {h r : ℕ} (Wr : Matrix (Fin h) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Wrᴴ * Wr

/-- The ordinary–shadow panel `K^{0L} = W_r^* 𝓛 W_r`. -/
def panelK0L {h r : ℕ} (L : Matrix (Fin h) (Fin h) ℂ) (Wr : Matrix (Fin h) (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Wrᴴ * L * Wr

/-- The shadow–shadow panel `K^{LL} = W_r^* 𝓛^* 𝓛 W_r`. -/
def panelKLL {h r : ℕ} (L : Matrix (Fin h) (Fin h) ℂ) (Wr : Matrix (Fin h) (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Wrᴴ * Lᴴ * L * Wr

/-- The table-native ancestry short `R_{T|S} = H − C^* G^† C` built from the panels:
`G = B_S^* K^{00} B_S`, `C = B_S^* K^{0L} B_T`, `H = B_T^* K^{LL} B_T`, with the Moore–Penrose
inverse of `G = S^* S` (`sourceGramPseudoinverse`). -/
noncomputable def tableNativeShort {h r e₁ e₂ : ℕ} (L : Matrix (Fin h) (Fin h) ℂ)
    (Wr : Matrix (Fin h) (Fin r) ℂ) (BS : Matrix (Fin r) (Fin e₁) ℂ)
    (BT : Matrix (Fin r) (Fin e₂) ℂ) : Matrix (Fin e₂) (Fin e₂) ℂ :=
  BTᴴ * panelKLL L Wr * BT -
    (BSᴴ * panelK0L L Wr * BT)ᴴ * sourceGramPseudoinverse (Wr * BS) *
      (BSᴴ * panelK0L L Wr * BT)

/-- **Table-native Gram blocks (`eq:table-native-GCH`).**  With `S = W_r B_S` and
`T = 𝓛 W_r B_T`: `G = S^* S = B_S^* K^{00} B_S`, `C = S^* T = B_S^* K^{0L} B_T`,
`H = T^* T = B_T^* K^{LL} B_T`. -/
theorem table_native_GCH {h r e₁ e₂ : ℕ} (L : Matrix (Fin h) (Fin h) ℂ)
    (Wr : Matrix (Fin h) (Fin r) ℂ) (BS : Matrix (Fin r) (Fin e₁) ℂ)
    (BT : Matrix (Fin r) (Fin e₂) ℂ) :
    (Wr * BS)ᴴ * (Wr * BS) = BSᴴ * panelK00 Wr * BS ∧
    (Wr * BS)ᴴ * (L * Wr * BT) = BSᴴ * panelK0L L Wr * BT ∧
    (L * Wr * BT)ᴴ * (L * Wr * BT) = BTᴴ * panelKLL L Wr * BT := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [panelK00, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · simp only [panelK0L, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · simp only [panelKLL, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Table-native ancestry short (`eq:table-native-short`).**  The exact source Schur
residual `R_{T|S} = T^*T − (S^*T)^* (S^*S)^† (S^*T)` of `S = W_r B_S`, `T = 𝓛 W_r B_T`
equals `H − C^* G^† C` computed from the panels `K^{00}, K^{0L}, K^{LL}`. -/
theorem table_native_ancestry_short {h r e₁ e₂ : ℕ} (L : Matrix (Fin h) (Fin h) ℂ)
    (Wr : Matrix (Fin h) (Fin r) ℂ) (BS : Matrix (Fin r) (Fin e₁) ℂ)
    (BT : Matrix (Fin r) (Fin e₂) ℂ) :
    sourceSchurResidual (Wr * BS) (L * Wr * BT) = tableNativeShort L Wr BS BT := by
  obtain ⟨_, hC, hH⟩ := table_native_GCH L Wr BS BT
  rw [sourceSchurResidual, tableNativeShort, hC, hH]

/-- The source Gram pseudo-inverse depends on the source only through its Gram matrix. -/
theorem sourceGramPseudoinverse_congr {h h' e : ℕ} (S : Matrix (Fin h) (Fin e) ℂ)
    (S' : Matrix (Fin h') (Fin e) ℂ) (hG : Sᴴ * S = S'ᴴ * S') :
    sourceGramPseudoinverse S = sourceGramPseudoinverse S' := by
  unfold sourceGramPseudoinverse
  generalize_proofs h1 h2
  revert h1 h2
  rw [hG]
  intro h1 h2
  rfl

/-- **Determinacy clause of `cor:table-native-ancestry`.**  Two synthesized word banks
with the same panels `K^{00}, K^{0L}, K^{LL}` (possibly on carriers of different size) and the
same coefficient matrices `B_S, B_T` give the same ancestry short: `R_{T|S}` is a
deterministic function of the panels and the coefficients. -/
theorem table_native_ancestry_short_determined_by_panels {h h' r e₁ e₂ : ℕ}
    (L : Matrix (Fin h) (Fin h) ℂ) (Wr : Matrix (Fin h) (Fin r) ℂ)
    (L' : Matrix (Fin h') (Fin h') ℂ) (Wr' : Matrix (Fin h') (Fin r) ℂ)
    (BS : Matrix (Fin r) (Fin e₁) ℂ) (BT : Matrix (Fin r) (Fin e₂) ℂ)
    (h00 : panelK00 Wr = panelK00 Wr') (h0L : panelK0L L Wr = panelK0L L' Wr')
    (hLL : panelKLL L Wr = panelKLL L' Wr') :
    sourceSchurResidual (Wr * BS) (L * Wr * BT) =
      sourceSchurResidual (Wr' * BS) (L' * Wr' * BT) := by
  rw [table_native_ancestry_short, table_native_ancestry_short]
  have hpinv : sourceGramPseudoinverse (Wr * BS) = sourceGramPseudoinverse (Wr' * BS) := by
    apply sourceGramPseudoinverse_congr
    rw [(table_native_GCH L Wr BS BT).1, (table_native_GCH L' Wr' BS BT).1, h00]
  simp only [tableNativeShort, h0L, hLL, hpinv]

end TableNative

end RenewalGeometry
