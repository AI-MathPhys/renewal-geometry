/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.WordModuleRecognition
import RenewalGeometry.Predictive.ExternalShadowNoGo
import RenewalGeometry.StandardModel.DeterminantIncidenceExact
/-!
# Historical typed-compilation criterion (`cor:historical-typed-compilation`)

`cor:historical-typed-compilation` of the spacetime–gauge duality manuscript.

## The objects

* `FlatWordTable A`: a *flat historical word hierarchy*: a finite word bank `w_1, …, w_r` of
  the historical `*`-algebra `A` together with its **multiplication table**
  `w_i w_j = ∑_k t_{ijk} w_k`, and flatness (the bank spans `A`, so every represented element
  and every finite functional-calculus element `p(a)`, `a ∈ A`, is a bank combination).
* `FlatWordTable.gram τ`: the **word Gram** `G_{ij} = τ(w_i^* w_j)` for the inner product
  `⟨y, x⟩ = τ(y^* x)` (`wordInner`; `τ = τ_reg` gives the Grand-Tensor word Gram).
* `TableNativeShadow T`: a word-native shadow (`def:word-native-shadow`)
  `X ↦ ∑_α c_α A_α X B_α` whose insertions `A_α, B_α` are *declared in the table* as bank
  coefficient vectors; compressions by typing projectors, conjugations by routers, finite
  symmetry averages and compositions of such are table-native (`compression`,
  `groupAverage`, `comp`).
* `TableNativeShadow.compile`: the **compiler**: the bank coefficient vector of `𝓛(x)` for a
  bank combination `x`, obtained by reducing every inserted product in the multiplication
  table (`eval_compile`).
* `gramForm G a b = ∑_{ij} conj(a_i) b_j G_{ij}`: the Gram of two bank combinations from the
  word Gram alone (`wordInner_eval`).
* `ancestryShort G C H = H − C^* G^† C`: the Schur ancestry residual at the Gram level
  (`eq:table-native-short`), with the Moore–Penrose inverse of the Hermitian Gram by spectral
  functional calculus.

## The criterion

`historical_typed_compilation`: on a flat hierarchy, for table-native typed shadows,
1. every ordinary–shadow and shadow–shadow block of the complete mixed ancestry Gram equals
   the explicit expression `gramForm` of the compiled coefficient vectors, i.e. a deterministic
   function of the word Gram, the multiplication table and the declared shadow data;
2. the Schur ancestry residual of the typed shadows relative to the ordinary sources equals
   `ancestryShort` of the compiled panels;
3. the alternating determinant shadow (`DetIncidence.alt`, fixed linear postprocessing) of an
   incidence tensor compiled from typed Gram blocks equals its value on the compiled entries;
4. (determinacy) two flat hierarchies, on possibly different historical algebras, with the
   same multiplication table, the same word Gram and the same declared shadow data have the
   same mixed ancestry Gram, the same ancestry residual and the same alternating determinant
   shadow — no independent mixed cross-Hankel source row is required;
5. (converse) for a typing shadow external to the historical algebra, no function of the
   word-Gram hierarchy returns the cross block (`thm:external-shadow-no-go`,
   `external_shadow_no_go`).

Disclosed renderings: "represented elements or finite functional-calculus elements of the
historical algebra" is rendered as "bank combinations" (all elements of `A`, by flatness);
"the Store–Clifford and matter-incidence shadows" are rendered as arbitrary table-native
shadows and their compositions; the Gram-level residual `ancestryShort` is the manuscript's
display `H − C^* G^† C` (`eq:table-native-short`) with `G^†` the spectral Moore–Penrose
inverse; the incidence tensor entering the alternating determinant shadow is taken to be
compiled entrywise from typed Gram blocks.
-/

open Matrix

namespace RenewalGeometry
namespace HistoricalTypedCompilation

/-! ### Flat word banks with multiplication table -/

/-- A **flat historical word hierarchy**: a finite word bank `w_1, …, w_r` of the historical
algebra `A`, its multiplication table `w_i w_j = ∑_k t_{ijk} w_k`, and flatness (the bank spans
`A`). -/
structure FlatWordTable (A : Type*) [Ring A] [Algebra ℂ A] where
  /-- the bank size -/
  r : ℕ
  /-- the bank words -/
  bank : Fin r → A
  /-- the multiplication table `t_{ijk}` -/
  mulTable : Fin r → Fin r → Fin r → ℂ
  /-- the table reduces every product of bank words -/
  mul_eq : ∀ i j, bank i * bank j = ∑ k, mulTable i j k • bank k
  /-- flatness: the bank spans the historical algebra -/
  flat : Submodule.span ℂ (Set.range bank) = ⊤

namespace FlatWordTable

variable {A : Type*} [Ring A] [Algebra ℂ A] (T : FlatWordTable A)

/-- The bank combination with coefficient vector `a`. -/
def eval (a : Fin T.r → ℂ) : A := ∑ i, a i • T.bank i

/-- Coefficient vector of the product of two bank combinations, reduced in the table. -/
def tableMul (a b : Fin T.r → ℂ) : Fin T.r → ℂ :=
  fun k => ∑ i, ∑ j, a i * b j * T.mulTable i j k

theorem eval_add (a b : Fin T.r → ℂ) : T.eval (a + b) = T.eval a + T.eval b := by
  simp [eval, add_smul, Finset.sum_add_distrib]

theorem eval_smul (c : ℂ) (a : Fin T.r → ℂ) : T.eval (c • a) = c • T.eval a := by
  simp [eval, smul_smul, Finset.smul_sum]

theorem eval_sum {ι : Type*} (s : Finset ι) (a : ι → Fin T.r → ℂ) :
    T.eval (∑ i ∈ s, a i) = ∑ i ∈ s, T.eval (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eval]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, eval_add, ih]

/-- The table reduces products of bank combinations. -/
theorem eval_tableMul (a b : Fin T.r → ℂ) : T.eval (T.tableMul a b) = T.eval a * T.eval b := by
  have h1 : T.eval (T.tableMul a b)
      = ∑ k, ∑ i, ∑ j, (a i * b j * T.mulTable i j k) • T.bank k := by
    simp only [eval, tableMul, Finset.sum_smul]
  have h2 : T.eval a * T.eval b
      = ∑ i, ∑ j, ∑ k, (a i * b j * T.mulTable i j k) • T.bank k := by
    simp only [eval, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, T.mul_eq,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  rw [h1, h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- Flatness: every element of the historical algebra is a bank combination. -/
theorem exists_eval_eq (x : A) : ∃ a : Fin T.r → ℂ, T.eval a = x := by
  have hx : x ∈ Submodule.span ℂ (Set.range T.bank) := by rw [T.flat]; exact Submodule.mem_top
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx

/-! ### The word Gram -/

section Gram

variable [StarRing A]

/-- The word Gram `G_{ij} = τ(w_i^* w_j)` of the bank for the inner product `⟨y, x⟩ = τ(y^* x)`. -/
def gram (τ : A →ₗ[ℂ] ℂ) : Matrix (Fin T.r) (Fin T.r) ℂ :=
  fun i j => τ (star (T.bank i) * T.bank j)

/-- The Gram of two bank combinations computed from a word Gram matrix alone:
`∑_{ij} conj(a_i) b_j G_{ij}`. -/
def gramForm (G : Matrix (Fin T.r) (Fin T.r) ℂ) (a b : Fin T.r → ℂ) : ℂ :=
  ∑ i, ∑ j, star (a i) * b j * G i j

/-- The inner product of two bank combinations is the `gramForm` of the word Gram. -/
theorem wordInner_eval [StarModule ℂ A] (τ : A →ₗ[ℂ] ℂ) (a b : Fin T.r → ℂ) :
    wordInner τ (T.eval a) (T.eval b) = T.gramForm (T.gram τ) a b := by
  simp only [wordInner, eval, gram, gramForm, star_sum, star_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, smul_eq_mul, mul_assoc]
  rw [Finset.sum_comm]

end Gram

end FlatWordTable

/-! ### Table-native typed shadows and the compiler -/

/-- A **table-native shadow**: a word-native shadow `X ↦ ∑_α c_α A_α X B_α`
(`def:word-native-shadow`) whose insertions are declared as bank coefficient vectors. -/
structure TableNativeShadow {A : Type*} [Ring A] [Algebra ℂ A] (T : FlatWordTable A) where
  /-- number of terms -/
  m : ℕ
  /-- the fixed coefficients `c_α` -/
  coeff : Fin m → ℂ
  /-- the left insertions `A_α`, as bank coefficient vectors -/
  left : Fin m → Fin T.r → ℂ
  /-- the right insertions `B_α`, as bank coefficient vectors -/
  right : Fin m → Fin T.r → ℂ

namespace TableNativeShadow

variable {A : Type*} [Ring A] [Algebra ℂ A] {T : FlatWordTable A}

/-- The word-native shadow realized in the historical algebra. -/
def toShadow (L : TableNativeShadow T) : WordNativeShadow A :=
  ⟨L.m, L.coeff, fun α => T.eval (L.left α), fun α => T.eval (L.right α)⟩

/-- The realized linear map `X ↦ ∑_α c_α A_α X B_α`. -/
def toLinearMap (L : TableNativeShadow T) : Module.End ℂ A := L.toShadow.toLinearMap

theorem toLinearMap_apply (L : TableNativeShadow T) (X : A) :
    L.toLinearMap X = ∑ α, L.coeff α • (T.eval (L.left α) * X * T.eval (L.right α)) := by
  simp [toLinearMap, toShadow, WordNativeShadow.toLinearMap_apply]

/-- Table-native shadows are word native. -/
theorem isWordNative (L : TableNativeShadow T) : IsWordNative L.toLinearMap :=
  ⟨L.toShadow, rfl⟩

/-- **The compiler**: the bank coefficient vector of `𝓛(x)` for the bank combination
`x = eval a`, obtained by reducing every inserted product in the multiplication table. -/
def compile (L : TableNativeShadow T) (a : Fin T.r → ℂ) : Fin T.r → ℂ :=
  ∑ α, L.coeff α • T.tableMul (T.tableMul (L.left α) a) (L.right α)

/-- The compiled vector realizes the shadow: `eval (compile 𝓛 a) = 𝓛(eval a)`. -/
theorem eval_compile (L : TableNativeShadow T) (a : Fin T.r → ℂ) :
    T.eval (L.compile a) = L.toLinearMap (T.eval a) := by
  rw [compile, FlatWordTable.eval_sum, toLinearMap_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [FlatWordTable.eval_smul, FlatWordTable.eval_tableMul, FlatWordTable.eval_tableMul]

/-- A compression `X ↦ p X p` by a bank combination (a typing projector represented in the
historical algebra) is table native. -/
def compression (p : Fin T.r → ℂ) : TableNativeShadow T :=
  ⟨1, fun _ => 1, fun _ => p, fun _ => p⟩

theorem compression_apply (p : Fin T.r → ℂ) (X : A) :
    (compression (T := T) p).toLinearMap X = T.eval p * X * T.eval p := by
  simp [toLinearMap_apply, compression]

/-- A finite symmetry average `X ↦ |G|⁻¹ ∑_g u_g X v_g` with represented `u_g, v_g`
(a router average, `v_g = u_g⁻¹`) is table native. -/
noncomputable def groupAverage {G : Type*} [Fintype G] (e : G ≃ Fin (Fintype.card G))
    (u v : G → Fin T.r → ℂ) : TableNativeShadow T :=
  ⟨Fintype.card G, fun _ => (Fintype.card G : ℂ)⁻¹, fun k => u (e.symm k), fun k => v (e.symm k)⟩

theorem groupAverage_apply {G : Type*} [Fintype G] (e : G ≃ Fin (Fintype.card G))
    (u v : G → Fin T.r → ℂ) (X : A) :
    (groupAverage (T := T) e u v).toLinearMap X =
      (Fintype.card G : ℂ)⁻¹ • ∑ g, T.eval (u g) * X * T.eval (v g) := by
  simp only [toLinearMap_apply, groupAverage, Finset.smul_sum]
  exact (Fintype.sum_equiv e.symm _ _ fun _ => rfl)

/-- Composition of table-native shadows (a compression after a router average, etc.) is table
native. -/
def comp (L M : TableNativeShadow T) : TableNativeShadow T :=
  ⟨L.m * M.m, fun k => L.coeff (finProdFinEquiv.symm k).1 * M.coeff (finProdFinEquiv.symm k).2,
    fun k => T.tableMul (L.left (finProdFinEquiv.symm k).1) (M.left (finProdFinEquiv.symm k).2),
    fun k => T.tableMul (M.right (finProdFinEquiv.symm k).2) (L.right (finProdFinEquiv.symm k).1)⟩

theorem comp_apply (L M : TableNativeShadow T) (X : A) :
    (L.comp M).toLinearMap X = L.toLinearMap (M.toLinearMap X) := by
  have hR : L.toLinearMap (M.toLinearMap X) = ∑ p : Fin L.m × Fin M.m,
      (L.coeff p.1 * M.coeff p.2) • (T.eval (L.left p.1) * T.eval (M.left p.2) * X
        * (T.eval (M.right p.2) * T.eval (L.right p.1))) := by
    simp only [toLinearMap_apply, Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    congr 1
    simp only [mul_assoc]
  rw [hR, toLinearMap_apply]
  simp only [comp, FlatWordTable.eval_tableMul]
  exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun k => rfl)

end TableNativeShadow

/-! ### Gram-level Schur ancestry residual -/

/-- The spectral Moore–Penrose inverse `x ↦ x⁻¹` on the nonzero spectrum. -/
noncomputable def spectralPseudoinverse (x : ℝ) : ℝ := if x = 0 then 0 else x⁻¹

/-- The Moore–Penrose inverse `G^†` of a Hermitian Gram matrix by spectral functional calculus
(`0` if `G` is not Hermitian). -/
noncomputable def gramPseudoinverse {e : ℕ} (G : Matrix (Fin e) (Fin e) ℂ) :
    Matrix (Fin e) (Fin e) ℂ :=
  if h : G.IsHermitian then h.cfc spectralPseudoinverse else 0

/-- The Schur ancestry residual at the Gram level, `R_{T|S} = H − C^* G^† C`
(`eq:table-native-short`). -/
noncomputable def ancestryShort {e₁ e₂ : ℕ} (G : Matrix (Fin e₁) (Fin e₁) ℂ)
    (C : Matrix (Fin e₁) (Fin e₂) ℂ) (H : Matrix (Fin e₂) (Fin e₂) ℂ) :
    Matrix (Fin e₂) (Fin e₂) ℂ :=
  H - Cᴴ * gramPseudoinverse G * C

/-! ### The mixed ancestry Gram of typed shadows -/

section Ancestry

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  (T : FlatWordTable A) (τ : A →ₗ[ℂ] ℂ)

/-- The ordinary source family `S_i = eval (s i)`. -/
def ordinarySource {e₁ : ℕ} (s : Fin e₁ → Fin T.r → ℂ) (i : Fin e₁) : A := T.eval (s i)

/-- The typed shadow family `T_j = 𝓛_j(eval (x j))`. -/
def typedShadow {e₂ : ℕ} (L : Fin e₂ → TableNativeShadow T) (x : Fin e₂ → Fin T.r → ℂ)
    (j : Fin e₂) : A := (L j).toLinearMap (T.eval (x j))

/-- The ordinary Gram block `G_{ij} = ⟨S_i, S_j⟩`. -/
def ordinaryGram {e₁ : ℕ} (s : Fin e₁ → Fin T.r → ℂ) : Matrix (Fin e₁) (Fin e₁) ℂ :=
  fun i j => wordInner τ (ordinarySource T s i) (ordinarySource T s j)

/-- The ordinary–shadow block `C_{ij} = ⟨S_i, T_j⟩`. -/
def mixedGram {e₁ e₂ : ℕ} (s : Fin e₁ → Fin T.r → ℂ) (L : Fin e₂ → TableNativeShadow T)
    (x : Fin e₂ → Fin T.r → ℂ) : Matrix (Fin e₁) (Fin e₂) ℂ :=
  fun i j => wordInner τ (ordinarySource T s i) (typedShadow T L x j)

/-- The shadow–shadow block `H_{ij} = ⟨T_i, T_j⟩`. -/
def shadowGram {e₂ : ℕ} (L : Fin e₂ → TableNativeShadow T) (x : Fin e₂ → Fin T.r → ℂ) :
    Matrix (Fin e₂) (Fin e₂) ℂ :=
  fun i j => wordInner τ (typedShadow T L x i) (typedShadow T L x j)

/-- The compiled ordinary block, from the word Gram and the declared sources. -/
def compiledOrdinaryGram {e₁ : ℕ} (G : Matrix (Fin T.r) (Fin T.r) ℂ) (s : Fin e₁ → Fin T.r → ℂ) :
    Matrix (Fin e₁) (Fin e₁) ℂ :=
  fun i j => T.gramForm G (s i) (s j)

/-- The compiled ordinary–shadow block, from the word Gram, the multiplication table and the
declared shadow data. -/
def compiledMixedGram {e₁ e₂ : ℕ} (G : Matrix (Fin T.r) (Fin T.r) ℂ) (s : Fin e₁ → Fin T.r → ℂ)
    (L : Fin e₂ → TableNativeShadow T) (x : Fin e₂ → Fin T.r → ℂ) :
    Matrix (Fin e₁) (Fin e₂) ℂ :=
  fun i j => T.gramForm G (s i) ((L j).compile (x j))

/-- The compiled shadow–shadow block. -/
def compiledShadowGram {e₂ : ℕ} (G : Matrix (Fin T.r) (Fin T.r) ℂ)
    (L : Fin e₂ → TableNativeShadow T) (x : Fin e₂ → Fin T.r → ℂ) :
    Matrix (Fin e₂) (Fin e₂) ℂ :=
  fun i j => T.gramForm G ((L i).compile (x i)) ((L j).compile (x j))

/-- Ordinary–shadow blocks are compiled from the word Gram and the table
(`eq:inserted-one-moment` reduced in the table). -/
theorem mixedGram_eq_compiled {e₁ e₂ : ℕ} (s : Fin e₁ → Fin T.r → ℂ)
    (L : Fin e₂ → TableNativeShadow T) (x : Fin e₂ → Fin T.r → ℂ) :
    mixedGram T τ s L x = compiledMixedGram T (T.gram τ) s L x := by
  ext i j
  simp only [mixedGram, compiledMixedGram, ordinarySource, typedShadow]
  rw [← TableNativeShadow.eval_compile, FlatWordTable.wordInner_eval]

/-- Shadow–shadow blocks are compiled from the word Gram and the table
(`eq:inserted-two-moments` reduced in the table). -/
theorem shadowGram_eq_compiled {e₂ : ℕ} (L : Fin e₂ → TableNativeShadow T)
    (x : Fin e₂ → Fin T.r → ℂ) :
    shadowGram T τ L x = compiledShadowGram T (T.gram τ) L x := by
  ext i j
  simp only [shadowGram, compiledShadowGram, typedShadow]
  rw [← TableNativeShadow.eval_compile, ← TableNativeShadow.eval_compile,
    FlatWordTable.wordInner_eval]

theorem ordinaryGram_eq_compiled {e₁ : ℕ} (s : Fin e₁ → Fin T.r → ℂ) :
    ordinaryGram T τ s = compiledOrdinaryGram T (T.gram τ) s := by
  ext i j
  simp only [ordinaryGram, compiledOrdinaryGram, ordinarySource]
  rw [FlatWordTable.wordInner_eval]

/-- **`cor:historical-typed-compilation` (Historical typed-compilation criterion).**
Let the historical word hierarchy be flat (`T : FlatWordTable A`), and let the typing
projections, routers and finite symmetry averages forming the typed shadows be table native
(`L j : TableNativeShadow T`).  Then, for the inner product `⟨y, x⟩ = τ(y^* x)`:

1. the complete mixed ancestry Gram — the ordinary block `G`, the ordinary–shadow block `C`
   and the shadow–shadow block `H` — equals its compiled form, an explicit function of the
   word Gram `T.gram τ`, the multiplication table (through `compile`) and the declared data;
2. the Schur ancestry residual `H − C^* G^† C` equals `ancestryShort` of the compiled panels;
3. the alternating determinant shadow of an incidence tensor compiled entrywise from typed
   Gram blocks equals its value on the compiled entries (fixed linear postprocessing).

No independent mixed cross-Hankel source row enters: every quantity is computed from
`T.gram τ`, `T.mulTable` and the declared shadow data. -/
theorem historical_typed_compilation {e₁ e₂ : ℕ} (s : Fin e₁ → Fin T.r → ℂ)
    (L : Fin e₂ → TableNativeShadow T) (x : Fin e₂ → Fin T.r → ℂ)
    (sI : Fin 3 → Fin 2 → Fin 2 → Fin 3 → Fin T.r → ℂ)
    (LI : Fin 3 → Fin 2 → Fin 2 → Fin 3 → TableNativeShadow T)
    (xI : Fin 3 → Fin 2 → Fin 2 → Fin 3 → Fin T.r → ℂ) :
    (ordinaryGram T τ s = compiledOrdinaryGram T (T.gram τ) s
      ∧ mixedGram T τ s L x = compiledMixedGram T (T.gram τ) s L x
      ∧ shadowGram T τ L x = compiledShadowGram T (T.gram τ) L x)
    ∧ ancestryShort (ordinaryGram T τ s) (mixedGram T τ s L x) (shadowGram T τ L x)
        = ancestryShort (compiledOrdinaryGram T (T.gram τ) s)
            (compiledMixedGram T (T.gram τ) s L x) (compiledShadowGram T (T.gram τ) L x)
    ∧ DetIncidence.alt (fun a b c d =>
          wordInner τ (T.eval (sI a b c d)) ((LI a b c d).toLinearMap (T.eval (xI a b c d))))
        = DetIncidence.alt (fun a b c d =>
          T.gramForm (T.gram τ) (sI a b c d) ((LI a b c d).compile (xI a b c d))) := by
  refine ⟨⟨ordinaryGram_eq_compiled T τ s, mixedGram_eq_compiled T τ s L x,
    shadowGram_eq_compiled T τ L x⟩, ?_, ?_⟩
  · rw [ordinaryGram_eq_compiled, mixedGram_eq_compiled, shadowGram_eq_compiled]
  · congr 1
    funext a b c d
    rw [← TableNativeShadow.eval_compile, FlatWordTable.wordInner_eval]

end Ancestry

/-! ### Determinacy across realizations and the converse -/

/-- Transport of declared shadow data between two hierarchies with the same bank size. -/
def TableNativeShadow.transport {A A' : Type*} [Ring A] [Algebra ℂ A] [Ring A'] [Algebra ℂ A']
    {T : FlatWordTable A} {T' : FlatWordTable A'} (hr : T.r = T'.r)
    (L : TableNativeShadow T) : TableNativeShadow T' :=
  ⟨L.m, L.coeff, fun α => L.left α ∘ (finCongr hr).symm, fun α => L.right α ∘ (finCongr hr).symm⟩

/-- **Determinacy clause of `cor:historical-typed-compilation`.**  Two flat historical
hierarchies `T`, `T'` on possibly different historical algebras with the same bank size, the
same multiplication table and the same word Gram, together with the same declared sources and
typed shadows, have the same complete mixed ancestry Gram, the same Schur ancestry residual and
the same alternating determinant shadow: these are deterministic functions of the word Gram,
the multiplication table and the declared shadow data alone. -/
theorem historical_typed_compilation_determined {A A' : Type*}
    [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Ring A'] [Algebra ℂ A'] [StarRing A'] [StarModule ℂ A']
    (T : FlatWordTable A) (T' : FlatWordTable A') (τ : A →ₗ[ℂ] ℂ) (τ' : A' →ₗ[ℂ] ℂ)
    (hr : T.r = T'.r)
    (htable : ∀ i j k, T.mulTable i j k = T'.mulTable (finCongr hr i) (finCongr hr j) (finCongr hr k))
    (hgram : ∀ i j, T.gram τ i j = T'.gram τ' (finCongr hr i) (finCongr hr j))
    {e₁ e₂ : ℕ} (s : Fin e₁ → Fin T.r → ℂ)
    (L : Fin e₂ → TableNativeShadow T) (x : Fin e₂ → Fin T.r → ℂ)
    (sI : Fin 3 → Fin 2 → Fin 2 → Fin 3 → Fin T.r → ℂ)
    (LI : Fin 3 → Fin 2 → Fin 2 → Fin 3 → TableNativeShadow T)
    (xI : Fin 3 → Fin 2 → Fin 2 → Fin 3 → Fin T.r → ℂ) :
    (ordinaryGram T τ s = ordinaryGram T' τ' (fun i => s i ∘ (finCongr hr).symm)
      ∧ mixedGram T τ s L x = mixedGram T' τ' (fun i => s i ∘ (finCongr hr).symm)
          (fun j => (L j).transport hr) (fun j => x j ∘ (finCongr hr).symm)
      ∧ shadowGram T τ L x = shadowGram T' τ' (fun j => (L j).transport hr)
          (fun j => x j ∘ (finCongr hr).symm))
    ∧ ancestryShort (ordinaryGram T τ s) (mixedGram T τ s L x) (shadowGram T τ L x)
        = ancestryShort (ordinaryGram T' τ' (fun i => s i ∘ (finCongr hr).symm))
            (mixedGram T' τ' (fun i => s i ∘ (finCongr hr).symm)
              (fun j => (L j).transport hr) (fun j => x j ∘ (finCongr hr).symm))
            (shadowGram T' τ' (fun j => (L j).transport hr) (fun j => x j ∘ (finCongr hr).symm))
    ∧ DetIncidence.alt (fun a b c d =>
          wordInner τ (T.eval (sI a b c d)) ((LI a b c d).toLinearMap (T.eval (xI a b c d))))
        = DetIncidence.alt (fun a b c d =>
          wordInner τ' (T'.eval (sI a b c d ∘ (finCongr hr).symm))
            (((LI a b c d).transport hr).toLinearMap
              (T'.eval (xI a b c d ∘ (finCongr hr).symm)))) := by
  -- the compiled quantities agree termwise
  have htm : ∀ a b : Fin T.r → ℂ,
      T.tableMul a b ∘ (finCongr hr).symm =
        T'.tableMul (a ∘ (finCongr hr).symm) (b ∘ (finCongr hr).symm) := by
    intro a b
    funext k
    simp only [Function.comp, FlatWordTable.tableMul]
    rw [← (finCongr hr).sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (finCongr hr).sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Equiv.symm_apply_apply, htable, Equiv.apply_symm_apply]
  have hgf : ∀ a b : Fin T.r → ℂ,
      T.gramForm (T.gram τ) a b =
        T'.gramForm (T'.gram τ') (a ∘ (finCongr hr).symm) (b ∘ (finCongr hr).symm) := by
    intro a b
    simp only [FlatWordTable.gramForm]
    rw [← (finCongr hr).sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (finCongr hr).sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp, Equiv.symm_apply_apply, hgram]
  have hcomp : ∀ (M : TableNativeShadow T) (a : Fin T.r → ℂ),
      M.compile a ∘ (finCongr hr).symm = (M.transport hr).compile (a ∘ (finCongr hr).symm) := by
    intro M a
    funext k
    simp only [Function.comp, TableNativeShadow.compile, TableNativeShadow.transport,
      Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h1 := congrFun (htm (T.tableMul (M.left α) a) (M.right α)) k
    have h2 := htm (M.left α) a
    simp only [Function.comp] at h1 h2
    rw [h1, h2]
  have hO : ordinaryGram T τ s = ordinaryGram T' τ' (fun i => s i ∘ (finCongr hr).symm) := by
    rw [ordinaryGram_eq_compiled, ordinaryGram_eq_compiled]
    ext i j
    simp only [compiledOrdinaryGram, hgf]
  have hC : mixedGram T τ s L x = mixedGram T' τ' (fun i => s i ∘ (finCongr hr).symm)
      (fun j => (L j).transport hr) (fun j => x j ∘ (finCongr hr).symm) := by
    rw [mixedGram_eq_compiled, mixedGram_eq_compiled]
    ext i j
    simp only [compiledMixedGram, hgf, hcomp]
  have hH : shadowGram T τ L x = shadowGram T' τ' (fun j => (L j).transport hr)
      (fun j => x j ∘ (finCongr hr).symm) := by
    rw [shadowGram_eq_compiled, shadowGram_eq_compiled]
    ext i j
    simp only [compiledShadowGram, hgf, hcomp]
  refine ⟨⟨hO, hC, hH⟩, by rw [hO, hC, hH], ?_⟩
  congr 1
  funext a b c d
  rw [← TableNativeShadow.eval_compile, FlatWordTable.wordInner_eval,
    ← TableNativeShadow.eval_compile, FlatWordTable.wordInner_eval, hgf, hcomp]

/-- **Converse clause of `cor:historical-typed-compilation`** (`thm:external-shadow-no-go`):
for a required typing shadow external to the historical algebra — the grading-changing cross
block of a conservative extension — no function of the word-Gram hierarchy returns the cross
block of both the even and the odd extension, so its historical occurrence cannot be inferred
from the old word moments alone. -/
theorem external_shadow_not_compilable {h ι : Type*} [Fintype h] [DecidableEq h] [Nonempty h]
    (K : ι → Matrix h h ℂ) :
    (∀ w₁ w₂ : List ι,
      extensionWordGram (gradingEvenProcessExtension K) w₁ w₂ =
        extensionWordGram (gradingOddProcessExtension K) w₁ w₂) ∧
    ¬ ∃ Φ : (List ι → List ι → ℂ) → Matrix (h × Fin 2) (h × Fin 2) ℂ,
      Φ (extensionWordGram (gradingEvenProcessExtension K)) =
          gradingCrossBlock (gradingEvenProcessExtension K) ∧
      Φ (extensionWordGram (gradingOddProcessExtension K)) =
          gradingCrossBlock (gradingOddProcessExtension K) := by
  obtain ⟨-, -, hgram, -, -, -, -, hno⟩ := external_shadow_no_go K
  exact ⟨fun w₁ w₂ => (hgram w₁ w₂).1, hno⟩

end HistoricalTypedCompilation
end RenewalGeometry
