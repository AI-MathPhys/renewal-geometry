/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.FlatWordSpan
import RenewalGeometry.Commutant.MatrixFactorNormalForm

/-!
# Terminating multiplicity obstruction (`cor:flat-multiplicity-obstruction`)

`cor:flat-multiplicity-obstruction` of the spacetime–gauge duality manuscript, generalizing
`Predictive/FlatDepthColourObstruction.lean` from the trivial external type and `n = 3` to an
arbitrary external type `λ` and an arbitrary internal factor size `n`.

Setting.  A finite-dimensional carrier `E`, represented source letters `L ℓ`, seed space `V0`,
the depth-`s` word carrier `𝒱_s = wordSpan L V0 s`, an external symmetry family
`ρ : G → E →ₗ[ℂ] E` and an external type `λ` given as a family `σ : G → W →ₗ[ℂ] W` on a
finite-dimensional space `W`.  The `λ`-multiplicity space of a carrier `V` is the intertwiner
space `M_λ(V) = Hom_G(W, V) = {f : W → E | range f ⊆ V, f ∘ σ g = ρ g ∘ f}` (`multSpace`), and
`m_{λ}(V) = dim M_λ(V)` (`multiplicity`); by `thm:active-isotypic` the `λ`-block of the relative
commutant of the external action on `V` is `End_ℂ(M_λ(V)) ≅ M_{m_λ}(ℂ)`.  An internal `M_n(ℂ)`
factor carried by the `λ`-multiplicity space is a unital algebra homomorphism
`M_n(ℂ) →ₐ[ℂ] End_ℂ(M_λ(V))` (automatically injective for `n ≥ 1` and `M_λ(V) ≠ 0`, since
`M_n(ℂ)` is simple); the obstruction is proved even for injective *linear* maps.

* `no_Mn_of_multiplicity_lt`: with `m_λ(V) < n` no injective linear map
  `M_n(ℂ) → End_ℂ(M_λ(V))` exists (`n² ≤ m²` forces `n ≤ m`);
* `no_unital_Mn_of_multiplicity_lt`: the unital-algebra-hom form;
* `flat_multiplicity_obstruction`: **`cor:flat-multiplicity-obstruction`** — at a flat word
  depth `r` (dimension form `dim 𝒱_{r+1} ≤ dim 𝒱_r` of `rank K_r = rank K_{r+1}`), failure of
  `m_{λ,r} ≥ n` gives `𝒱_s = 𝒱_r` for all `s ≥ r`, `m_{λ,s} < n` at **every** depth `s`, and no
  internal `M_n(ℂ)` factor on the `λ`-multiplicity space at any depth;
* `flat_multiplicity_obstruction_of_gram_rank`: the same with the literal Gram-rank hypothesis.
-/

open Matrix Module

namespace RenewalGeometry
namespace FlatMultiplicity

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι G : Type*}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-! ### The `λ`-multiplicity space -/

/-- The `λ`-multiplicity space `M_λ(V) = Hom_G(W, V)`: intertwiners from the external type
`σ` on `W` into the external action `ρ` on `E` landing in `V`. -/
def multSpace (ρ : G → E →ₗ[ℂ] E) (σ : G → W →ₗ[ℂ] W) (V : Submodule ℂ E) :
    Submodule ℂ (W →ₗ[ℂ] E) where
  carrier := {f | (∀ w, f w ∈ V) ∧ ∀ g w, f (σ g w) = ρ g (f w)}
  add_mem' := by
    rintro f₁ f₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    refine ⟨fun w => V.add_mem (h₁ w) (h₂ w), fun g w => ?_⟩
    simp [h₁' g w, h₂' g w]
  zero_mem' := ⟨fun _ => V.zero_mem, fun _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h, h'⟩
    refine ⟨fun w => V.smul_mem c (h w), fun g w => ?_⟩
    simp [h' g w]

theorem mem_multSpace {ρ : G → E →ₗ[ℂ] E} {σ : G → W →ₗ[ℂ] W} {V : Submodule ℂ E}
    {f : W →ₗ[ℂ] E} :
    f ∈ multSpace ρ σ V ↔ (∀ w, f w ∈ V) ∧ ∀ g w, f (σ g w) = ρ g (f w) :=
  Iff.rfl

/-- The multiplicity space is monotone in the carrier. -/
theorem multSpace_mono (ρ : G → E →ₗ[ℂ] E) (σ : G → W →ₗ[ℂ] W)
    {V V' : Submodule ℂ E} (h : V ≤ V') : multSpace ρ σ V ≤ multSpace ρ σ V' :=
  fun _ hf => ⟨fun w => h (hf.1 w), hf.2⟩

/-- The external multiplicity `m_λ(V) = dim Hom_G(W, V)`. -/
noncomputable def multiplicity (ρ : G → E →ₗ[ℂ] E) (σ : G → W →ₗ[ℂ] W)
    (V : Submodule ℂ E) : ℕ :=
  finrank ℂ (multSpace ρ σ V)

theorem multiplicity_mono [FiniteDimensional ℂ E] [FiniteDimensional ℂ W]
    (ρ : G → E →ₗ[ℂ] E) (σ : G → W →ₗ[ℂ] W)
    {V V' : Submodule ℂ E} (h : V ≤ V') :
    multiplicity ρ σ V ≤ multiplicity ρ σ V' :=
  Submodule.finrank_mono (multSpace_mono ρ σ h)

/-- The depth-`s` external multiplicity `m_{λ,s} = m_λ(𝒱_s)`. -/
noncomputable def mult (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (ρ : G → E →ₗ[ℂ] E)
    (σ : G → W →ₗ[ℂ] W) (s : ℕ) : ℕ :=
  multiplicity ρ σ (wordSpan L V0 s)

/-- The `λ`-block `End_ℂ(M_λ(𝒱_s)) ≅ M_{m_{λ,s}}(ℂ)` of the depth-`s` relative commutant
(`eq:external-isotypic-commutant`). -/
abbrev lambdaBlock (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (ρ : G → E →ₗ[ℂ] E)
    (σ : G → W →ₗ[ℂ] W) (s : ℕ) :=
  Module.End ℂ ↥(multSpace ρ σ (wordSpan L V0 s))

/-! ### The dimension-count obstruction -/

theorem finrank_matrix_fin (n : ℕ) : finrank ℂ (Matrix (Fin n) (Fin n) ℂ) = n * n := by
  rw [Module.finrank_matrix, Module.finrank_self]
  simp

/-- **`thm:active-isotypic`, multiplicity clause**: if `m_λ(V) < n`, `M_n(ℂ)` admits no
injective linear map into `End_ℂ(M_λ(V))` (dimension `m_λ² < n²`). -/
theorem no_Mn_of_multiplicity_lt [FiniteDimensional ℂ E] [FiniteDimensional ℂ W]
    (ρ : G → E →ₗ[ℂ] E) (σ : G → W →ₗ[ℂ] W) (V : Submodule ℂ E) {n : ℕ}
    (h : multiplicity ρ σ V < n)
    (f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ ↥(multSpace ρ σ V)) :
    ¬Function.Injective f := by
  intro hinj
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_linearMap, finrank_matrix_fin] at hle
  unfold multiplicity at h
  nlinarith

/-- The unital-algebra-hom form: for `n ≥ 1` and a nonzero multiplicity space, an internal
`M_n(ℂ)` factor on `M_λ(V)` is impossible when `m_λ(V) < n`. -/
theorem no_unital_Mn_of_multiplicity_lt [FiniteDimensional ℂ E] [FiniteDimensional ℂ W]
    (ρ : G → E →ₗ[ℂ] E) (σ : G → W →ₗ[ℂ] W) (V : Submodule ℂ E) {n : ℕ} [NeZero n]
    (hpos : 0 < multiplicity ρ σ V) (h : multiplicity ρ σ V < n)
    (φ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] Module.End ℂ ↥(multSpace ρ σ V)) : False := by
  have : Nontrivial ↥(multSpace ρ σ V) := Module.nontrivial_of_finrank_pos hpos
  have hinj : Function.Injective φ := RingHom.injective φ.toRingHom
  exact no_Mn_of_multiplicity_lt ρ σ V h φ.toLinearMap hinj

/-! ### The terminating obstruction -/

/-- **`cor:flat-multiplicity-obstruction`** (dimension form of the flatness hypothesis).
At a flat word depth `r` (`dim 𝒱_{r+1} ≤ dim 𝒱_r`), failure of `m_{λ,r} ≥ n` is permanent:
`𝒱_s = 𝒱_r` for all `s ≥ r`, `m_{λ,s} < n` at every depth `s`, and no depth carries an
internal `M_n(ℂ)` factor on the `λ`-multiplicity space (no injective linear map, a fortiori no
unital algebra homomorphism, `M_n(ℂ) → End_ℂ(M_λ(𝒱_s))`). -/
theorem flat_multiplicity_obstruction [FiniteDimensional ℂ E] [FiniteDimensional ℂ W]
    (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (ρ : G → E →ₗ[ℂ] E) (σ : G → W →ₗ[ℂ] W)
    (r n : ℕ)
    (hflat : finrank ℂ (wordSpan L V0 (r + 1)) ≤ finrank ℂ (wordSpan L V0 r))
    (hm : mult L V0 ρ σ r < n) :
    (∀ s, r ≤ s → wordSpan L V0 s = wordSpan L V0 r)
    ∧ (∀ s, mult L V0 ρ σ s < n)
    ∧ (∀ s, ∀ f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] lambdaBlock L V0 ρ σ s,
        ¬Function.Injective f)
    ∧ (∀ s, [NeZero n] → 0 < mult L V0 ρ σ s →
        ∀ _φ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] lambdaBlock L V0 ρ σ s, False) := by
  have hfreeze := (flat_word_span L V0 r hflat).2.2
  have hm' : ∀ s, mult L V0 ρ σ s < n := by
    intro s
    rcases le_or_gt r s with hrs | hsr
    · unfold mult
      rw [hfreeze s hrs]
      exact hm
    · exact lt_of_le_of_lt (multiplicity_mono ρ σ (wordSpan_mono L V0 hsr.le)) hm
  refine ⟨hfreeze, hm', fun s f => no_Mn_of_multiplicity_lt ρ σ _ (hm' s) f,
    fun s _ hpos φ => no_unital_Mn_of_multiplicity_lt ρ σ _ hpos (hm' s) φ⟩

/-- **`cor:flat-multiplicity-obstruction`** in the literal Gram-rank form: `C_r`, `C_{r+1}` are
labelled spanning families (columns) of `𝒱_r`, `𝒱_{r+1}` and `rank K_r = rank K_{r+1}` for the
Grams `K = Cᴴ C`. -/
theorem flat_multiplicity_obstruction_of_gram_rank {N : Type*} [Fintype N]
    [FiniteDimensional ℂ W]
    (L : ι → (N → ℂ) →ₗ[ℂ] (N → ℂ)) (V0 : Submodule ℂ (N → ℂ))
    (ρ : G → (N → ℂ) →ₗ[ℂ] (N → ℂ)) (σ : G → W →ₗ[ℂ] W) (r n : ℕ)
    {q q' : Type*} [Fintype q] [Fintype q']
    (Cr : Matrix N q ℂ) (Cr' : Matrix N q' ℂ)
    (hCr : Submodule.span ℂ (Set.range Cr.col) = wordSpan L V0 r)
    (hCr' : Submodule.span ℂ (Set.range Cr'.col) = wordSpan L V0 (r + 1))
    (hrank : (Crᴴ * Cr).rank = (Cr'ᴴ * Cr').rank)
    (hm : mult L V0 ρ σ r < n) :
    (∀ s, r ≤ s → wordSpan L V0 s = wordSpan L V0 r)
    ∧ (∀ s, mult L V0 ρ σ s < n)
    ∧ (∀ s, ∀ f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] lambdaBlock L V0 ρ σ s,
        ¬Function.Injective f)
    ∧ (∀ s, [NeZero n] → 0 < mult L V0 ρ σ s →
        ∀ _φ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] lambdaBlock L V0 ρ σ s, False) := by
  apply flat_multiplicity_obstruction L V0 ρ σ r n _ hm
  rw [gram_rank_eq_finrank_span_cols, gram_rank_eq_finrank_span_cols, hCr, hCr'] at hrank
  exact hrank.symm.le

end FlatMultiplicity
end RenewalGeometry
