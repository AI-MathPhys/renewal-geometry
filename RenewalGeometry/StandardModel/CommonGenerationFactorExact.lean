/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.SqrtPolar

/-!
# Abstract replication and source-determined generation frames
  (`thm:common-generation-factor`)

`thm:common-generation-factor` of the spacetime–gauge duality manuscript.  The matter carrier
`⊕_f V_f ⊗ N_f` is `Σ f, V_f × N_f` (the spinor factor may be absorbed in `V_f`).

* `blockUnitary W = ⊕_f I_{V_f} ⊗ W_f^*` for any family of unitaries `W_f : G_f → N_f`;
  `generation_transport`: it is unitary from `⊕_f V_f ⊗ N_f` onto `⊕_f V_f ⊗ G_f`, the
  gauge/typing operators `⊕_f a_f ⊗ I_{N_f}` become `⊕_f a_f ⊗ I_{G_f}` (trivial action on the
  generation factor), and the `(h, f)` block of every operator transforms as
  `(I ⊗ W_h^*) X_{hf} (I ⊗ W_f)`; an arrow block `A ⊗ B` becomes `A ⊗ W_h^* B W_f`;
* `abstract_generation_factor` (`eq:abstract-global-generation-factor`): with all `N_f` of the
  same dimension `g = dim G`, unitaries exist (`exists_unitary_of_card_eq`) and any choice gives
  `⊕_f V_f ⊗ N_f ≅ (⊕_f V_f) ⊗ G`;
* `polar_unitary`: for a source `S_f : G_C → N_f` with `S_f^*S_f ≻ 0` and `Ran S_f = N_f`, the
  polar map `U_f = S_f (S_f^*S_f)^{-1/2}` is unitary (and `dim N_f = dim G_C`);
* `componentwise_generation_factor` (`eq:componentwise-generation-factorization`) and
  `common_generation_factor` (`eq:common-generation-factorization`);
* `generation_neutral_iff` (`eq:generation-neutral-incidence`,
  `eq:generation-compatibility-defect`): an arrow preserves the full common generation algebra
  iff `U_h^* B U_f ∈ ℂ I` iff `∑_{ij} ‖B U_f E_ij U_f^* − U_h E_ij U_h^* B‖²_HS = 0`;
* `relative_frame_change` (`eq:relative-generation-coordinate-change`): replacing the component
  frames by `J_C U_C` conjugates the represented tuple by the unitary
  `𝒰_U = ⊕_C I ⊗ U_C^*`; words transform covariantly, block-diagonal operators stay block
  diagonal, and traces of all words (hence trace polynomials and spectra) are unchanged, so no
  such invariant selects a point of `U(g)^{pi0}/U(g)_diag`.

Renderings disclosed: Hilbert spaces are coordinate spaces; "unitary `W : G → N`" is a
rectangular matrix with `W^*W = I`, `WW^* = I`; the regrouping
`Σ f, V_f × G ≅ (Σ f, V_f) × G` (and by components) is the canonical reindexing and is not
spelled out; the quotient description of the relative frames is rendered by the invariance
statement `relative_frame_change`.
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder

namespace RenewalGeometry
namespace CommonGenerationFactor

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {𝓕 : Type*} [Fintype 𝓕] [DecidableEq 𝓕]
variable {V N Gf : 𝓕 → Type*} [∀ f, Fintype (V f)] [∀ f, DecidableEq (V f)]
  [∀ f, Fintype (N f)] [∀ f, DecidableEq (N f)] [∀ f, Fintype (Gf f)] [∀ f, DecidableEq (Gf f)]

/-- The `(h, f)` block of an operator on a sigma carrier. -/
def blk {A B : 𝓕 → Type*} (X : Matrix (Σ f, A f) (Σ f, B f) ℂ) (h f : 𝓕) :
    Matrix (A h) (B f) ℂ :=
  Matrix.of fun i j => X ⟨h, i⟩ ⟨f, j⟩

theorem blk_blockDiagonal'_mul {A B C : 𝓕 → Type*} [∀ f, Fintype (B f)]
    (L : ∀ f, Matrix (A f) (B f) ℂ) (Y : Matrix (Σ f, B f) (Σ f, C f) ℂ) (h f : 𝓕) :
    blk (blockDiagonal' L * Y) h f = L h * blk Y h f := by
  ext i j
  simp only [blk, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single h]
  · simp only [blockDiagonal'_apply_eq]
  · intro k _ hk
    exact Finset.sum_eq_zero fun y _ => by rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hk), zero_mul]
  · simp

theorem blk_mul_blockDiagonal' {A B C : 𝓕 → Type*} [∀ f, Fintype (B f)]
    (Y : Matrix (Σ f, A f) (Σ f, B f) ℂ) (R : ∀ f, Matrix (B f) (C f) ℂ) (h f : 𝓕) :
    blk (Y * blockDiagonal' R) h f = blk Y h f * R f := by
  ext i j
  simp only [blk, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single f]
  · simp only [blockDiagonal'_apply_eq]
  · intro k _ hk
    exact Finset.sum_eq_zero fun y _ => by rw [blockDiagonal'_apply_ne _ _ _ hk, mul_zero]
  · simp

theorem blk_blockDiagonal'_mul_mul {A B C D : 𝓕 → Type*} [∀ f, Fintype (B f)]
    [∀ f, Fintype (C f)] (L : ∀ f, Matrix (A f) (B f) ℂ) (X : Matrix (Σ f, B f) (Σ f, C f) ℂ)
    (R : ∀ f, Matrix (C f) (D f) ℂ) (h f : 𝓕) :
    blk (blockDiagonal' L * X * blockDiagonal' R) h f = L h * blk X h f * R f := by
  rw [blk_mul_blockDiagonal', blk_blockDiagonal'_mul]

variable (V) in
/-- `𝒲 = ⊕_f I_{V_f} ⊗ W_f^*`, from `⊕_f V_f ⊗ N_f` to `⊕_f V_f ⊗ G_f`. -/
def blockUnitary (W : ∀ f, Matrix (N f) (Gf f) ℂ) :
    Matrix (Σ f, V f × Gf f) (Σ f, V f × N f) ℂ :=
  blockDiagonal' fun f => (1 : Matrix (V f) (V f) ℂ) ⊗ₖ (W f)ᴴ

/-- The gauge/typing operators `⊕_f a_f ⊗ I_{K_f}` on a factorized carrier. -/
def gaugeOn (K : 𝓕 → Type*) [∀ f, Fintype (K f)] [∀ f, DecidableEq (K f)]
    (a : ∀ f, Matrix (V f) (V f) ℂ) : Matrix (Σ f, V f × K f) (Σ f, V f × K f) ℂ :=
  blockDiagonal' fun f => a f ⊗ₖ (1 : Matrix (K f) (K f) ℂ)

/-- **Transport by a family of unitaries.**  `𝒲 = ⊕_f I ⊗ W_f^*` is unitary; the gauge and typing
operators act trivially on the new factor; each `(h, f)` block transforms by
`(I ⊗ W_h^*) X_{hf} (I ⊗ W_f)`, so an arrow `A ⊗ B` becomes `A ⊗ W_h^* B W_f`. -/
theorem generation_transport (W : ∀ f, Matrix (N f) (Gf f) ℂ)
    (hW1 : ∀ f, (W f)ᴴ * W f = 1) (hW2 : ∀ f, W f * (W f)ᴴ = 1) :
    blockUnitary V W * (blockUnitary V W)ᴴ = 1 ∧
    (blockUnitary V W)ᴴ * blockUnitary V W = 1 ∧
    (∀ a : ∀ f, Matrix (V f) (V f) ℂ,
      blockUnitary V W * gaugeOn N a * (blockUnitary V W)ᴴ = gaugeOn Gf a) ∧
    (∀ (X : Matrix (Σ f, V f × N f) (Σ f, V f × N f) ℂ) (h f : 𝓕),
      blk (blockUnitary V W * X * (blockUnitary V W)ᴴ) h f =
        ((1 : Matrix (V h) (V h) ℂ) ⊗ₖ (W h)ᴴ) * blk X h f * ((1 : Matrix (V f) (V f) ℂ) ⊗ₖ W f)) ∧
    (∀ (X : Matrix (Σ f, V f × N f) (Σ f, V f × N f) ℂ) (h f : 𝓕)
      (A : Matrix (V h) (V f) ℂ) (B : Matrix (N h) (N f) ℂ), blk X h f = A ⊗ₖ B →
      blk (blockUnitary V W * X * (blockUnitary V W)ᴴ) h f = A ⊗ₖ ((W h)ᴴ * B * W f)) := by
  have hH : (blockUnitary V W)ᴴ = blockDiagonal' fun f => (1 : Matrix (V f) (V f) ℂ) ⊗ₖ W f := by
    rw [blockUnitary, blockDiagonal'_conjTranspose]
    congr 1
    funext f
    rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_conjTranspose]
  have hblk : ∀ (X : Matrix (Σ f, V f × N f) (Σ f, V f × N f) ℂ) (h f : 𝓕),
      blk (blockUnitary V W * X * (blockUnitary V W)ᴴ) h f =
        ((1 : Matrix (V h) (V h) ℂ) ⊗ₖ (W h)ᴴ) * blk X h f *
          ((1 : Matrix (V f) (V f) ℂ) ⊗ₖ W f) := by
    intro X h f
    rw [hH, blockUnitary, blk_blockDiagonal'_mul_mul]
  refine ⟨?_, ?_, ?_, hblk, ?_⟩
  · rw [hH, blockUnitary, ← blockDiagonal'_mul, ← blockDiagonal'_one]
    congr 1
    funext f
    rw [← mul_kronecker_mul, Matrix.one_mul, hW1, one_kronecker_one]
    rfl
  · rw [hH, blockUnitary, ← blockDiagonal'_mul, ← blockDiagonal'_one]
    congr 1
    funext f
    rw [← mul_kronecker_mul, Matrix.one_mul, hW2, one_kronecker_one]
    rfl
  · intro a
    rw [hH, blockUnitary, gaugeOn, gaugeOn, ← blockDiagonal'_mul, ← blockDiagonal'_mul]
    congr 1
    funext f
    rw [← mul_kronecker_mul, ← mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, hW1]
  · intro X h f A B hX
    rw [hblk, hX, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- A unitary `G → N` exists when `dim N = dim G`. -/
theorem exists_unitary_of_card_eq {Nn G : Type*} [Fintype Nn] [DecidableEq Nn] [Fintype G]
    [DecidableEq G] (h : Fintype.card Nn = Fintype.card G) :
    ∃ W : Matrix Nn G ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = 1 := by
  let e : Nn ≃ G := Fintype.equivOfCardEq h
  refine ⟨(1 : Matrix G G ℂ).submatrix e id, ?_, ?_⟩
  · rw [conjTranspose_submatrix, conjTranspose_one,
      show ((1 : Matrix G G ℂ).submatrix id e) = (1 : Matrix G G ℂ).submatrix id e from rfl,
      submatrix_mul_equiv (1 : Matrix G G ℂ) (1 : Matrix G G ℂ) id e id, Matrix.mul_one]
    exact submatrix_id_id _
  · rw [conjTranspose_submatrix, conjTranspose_one]
    change (1 : Matrix G G ℂ).submatrix e (Equiv.refl G) *
      (1 : Matrix G G ℂ).submatrix (Equiv.refl G) e = 1
    rw [submatrix_mul_equiv (1 : Matrix G G ℂ) (1 : Matrix G G ℂ) e (Equiv.refl G) e,
      Matrix.mul_one]
    exact submatrix_one_equiv e

/-- **`eq:abstract-global-generation-factor`.**  If every populated `N_f` has dimension
`g = dim G`, unitaries `W_f : G → N_f` exist, and for any such choice
`⊕_f I ⊗ W_f^*` identifies `⊕_f V_f ⊗ N_f` with `⊕_f V_f ⊗ G = (⊕_f V_f) ⊗ G`, with arrows
`B : N_f → N_h` becoming `W_h^* B W_f ∈ M_g(ℂ)`. -/
theorem abstract_generation_factor {G : Type*} [Fintype G] [DecidableEq G]
    (hdim : ∀ f, Fintype.card (N f) = Fintype.card G) :
    (∃ W : ∀ f, Matrix (N f) G ℂ, ∀ f, (W f)ᴴ * W f = 1 ∧ W f * (W f)ᴴ = 1) ∧
    ∀ W : ∀ f, Matrix (N f) G ℂ, (∀ f, (W f)ᴴ * W f = 1) → (∀ f, W f * (W f)ᴴ = 1) →
      blockUnitary V (Gf := fun _ => G) W * (blockUnitary V (Gf := fun _ => G) W)ᴴ = 1 ∧
      (blockUnitary V (Gf := fun _ => G) W)ᴴ * blockUnitary V (Gf := fun _ => G) W = 1 ∧
      ∀ (X : Matrix (Σ f, V f × N f) (Σ f, V f × N f) ℂ) (h f : 𝓕)
        (A : Matrix (V h) (V f) ℂ) (B : Matrix (N h) (N f) ℂ), blk X h f = A ⊗ₖ B →
        blk (blockUnitary V (Gf := fun _ => G) W * X *
          (blockUnitary V (Gf := fun _ => G) W)ᴴ) h f = A ⊗ₖ ((W h)ᴴ * B * W f) := by
  refine ⟨⟨fun f => (exists_unitary_of_card_eq (hdim f)).choose,
    fun f => (exists_unitary_of_card_eq (hdim f)).choose_spec⟩, fun W hW1 hW2 => ?_⟩
  obtain ⟨t1, t2, -, -, t5⟩ := generation_transport (V := V) (Gf := fun _ => G) W hW1 hW2
  exact ⟨t1, t2, t5⟩

/-! ### Source-determined polar frames -/

/-- **Polar maps of faithful complete sources are unitary**: for `S : G_C → N_f` with
`S^*S ≻ 0` and `Ran S = N_f`, `dim N_f = dim G_C` and `U = S (S^*S)^{-1/2}` satisfies
`U^*U = I`, `UU^* = I`. -/
theorem polar_unitary {Nn G : Type*} [Fintype Nn] [DecidableEq Nn] [Fintype G] [DecidableEq G]
    (S : Matrix Nn G ℂ) (hpd : (Sᴴ * S).PosDef) (hran : LinearMap.range S.mulVecLin = ⊤) :
    Fintype.card Nn = Fintype.card G ∧
    (S * (CFC.sqrt (Sᴴ * S))⁻¹)ᴴ * (S * (CFC.sqrt (Sᴴ * S))⁻¹) = 1 ∧
    (S * (CFC.sqrt (Sᴴ * S))⁻¹) * (S * (CFC.sqrt (Sᴴ * S))⁻¹)ᴴ = 1 := by
  set P := CFC.sqrt (Sᴴ * S) with hPdef
  have hPu : IsUnit P := sqrt_isUnit hpd
  haveI := hPu.invertible
  have hP2 : P * P = Sᴴ * S := sqrt_mul_self_eq _ hpd.posSemidef
  have hPinvH : P⁻¹ᴴ = P⁻¹ := sqrt_inv_isHermitian _
  have hUU : (S * P⁻¹)ᴴ * (S * P⁻¹) = 1 := by
    rw [conjTranspose_mul, hPinvH]
    calc P⁻¹ * Sᴴ * (S * P⁻¹) = P⁻¹ * ((Sᴴ * S) * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (P * (P * P⁻¹)) := by rw [← hP2]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.mul_inv_of_invertible, Matrix.mul_one, Matrix.inv_mul_of_invertible]
  have hcard : Fintype.card Nn = Fintype.card G := by
    have h1 : S.rank = Fintype.card Nn := by
      rw [Matrix.rank, hran, finrank_top, Module.finrank_fintype_fun_eq_card]
    have h2 : S.rank = Fintype.card G := by
      rw [← Matrix.rank_conjTranspose_mul_self, Matrix.rank_of_isUnit _ hpd.isUnit]
    omega
  exact ⟨hcard, hUU,
    (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard.symm)).1 hUU⟩

/-- **`eq:componentwise-generation-factorization`.**  For incidence components `C` with
specified rank-three endpoint sources `G_C` and faithful complete maps `S_f : G_C → N_f`
(`f ∈ C`), the polar maps `U_f = S_f (S_f^*S_f)^{-1/2}` are unitary, `dim N_f = 3`, and
`⊕_f I ⊗ U_f^*` identifies `ℋ_mat` with `⊕_C (⊕_{f ∈ C} V_f) ⊗ G_C`; the gauge and typing
algebras act trivially on `G_C`, and every arrow `A ⊗ B` becomes `A ⊗ U_h^* B U_f`. -/
theorem componentwise_generation_factor {Cpt : Type*} (comp : 𝓕 → Cpt) (Gc : Cpt → Type*)
    [∀ C, Fintype (Gc C)] [∀ C, DecidableEq (Gc C)] (hrank : ∀ C, Fintype.card (Gc C) = 3)
    (S : ∀ f, Matrix (N f) (Gc (comp f)) ℂ) (hpd : ∀ f, ((S f)ᴴ * S f).PosDef)
    (hran : ∀ f, LinearMap.range (S f).mulVecLin = ⊤) :
    let U : ∀ f, Matrix (N f) (Gc (comp f)) ℂ := fun f => S f * (CFC.sqrt ((S f)ᴴ * S f))⁻¹
    (∀ f, Fintype.card (N f) = 3) ∧ (∀ f, (U f)ᴴ * U f = 1 ∧ U f * (U f)ᴴ = 1) ∧
    blockUnitary V (Gf := fun f => Gc (comp f)) U *
      (blockUnitary V (Gf := fun f => Gc (comp f)) U)ᴴ = 1 ∧
    (blockUnitary V (Gf := fun f => Gc (comp f)) U)ᴴ *
      blockUnitary V (Gf := fun f => Gc (comp f)) U = 1 ∧
    (∀ a : ∀ f, Matrix (V f) (V f) ℂ,
      blockUnitary V (Gf := fun f => Gc (comp f)) U * gaugeOn N a *
        (blockUnitary V (Gf := fun f => Gc (comp f)) U)ᴴ = gaugeOn (fun f => Gc (comp f)) a) ∧
    (∀ (X : Matrix (Σ f, V f × N f) (Σ f, V f × N f) ℂ) (h f : 𝓕)
      (A : Matrix (V h) (V f) ℂ) (B : Matrix (N h) (N f) ℂ), blk X h f = A ⊗ₖ B →
      blk (blockUnitary V (Gf := fun f => Gc (comp f)) U * X *
        (blockUnitary V (Gf := fun f => Gc (comp f)) U)ᴴ) h f = A ⊗ₖ ((U h)ᴴ * B * U f)) := by
  intro U
  have hU : ∀ f, Fintype.card (N f) = Fintype.card (Gc (comp f)) ∧
      (U f)ᴴ * U f = 1 ∧ U f * (U f)ᴴ = 1 := fun f => polar_unitary (S f) (hpd f) (hran f)
  obtain ⟨t1, t2, t3, -, t5⟩ := generation_transport (V := V) (Gf := fun f => Gc (comp f)) U
    (fun f => (hU f).2.1) (fun f => (hU f).2.2)
  exact ⟨fun f => (hU f).1.trans (hrank _), fun f => (hU f).2, t1, t2, t3, t5⟩

/-- **`eq:common-generation-factorization`.**  If a single represented endpoint source
`G_gen` (`dim G_gen = 3`) supplies all types, the polar maps identify
`ℋ_mat ≅ (⊕_f V_f) ⊗ G_gen`, with gauge/typing acting trivially on `G_gen` and arrows
`B ↦ U_h^* B U_f`. -/
theorem common_generation_factor {Ggen : Type*} [Fintype Ggen] [DecidableEq Ggen]
    (hrank : Fintype.card Ggen = 3) (S : ∀ f, Matrix (N f) Ggen ℂ)
    (hpd : ∀ f, ((S f)ᴴ * S f).PosDef) (hran : ∀ f, LinearMap.range (S f).mulVecLin = ⊤) :
    let U : ∀ f, Matrix (N f) Ggen ℂ := fun f => S f * (CFC.sqrt ((S f)ᴴ * S f))⁻¹
    (∀ f, Fintype.card (N f) = 3) ∧ (∀ f, (U f)ᴴ * U f = 1 ∧ U f * (U f)ᴴ = 1) ∧
    blockUnitary V (Gf := fun _ => Ggen) U * (blockUnitary V (Gf := fun _ => Ggen) U)ᴴ = 1 ∧
    (blockUnitary V (Gf := fun _ => Ggen) U)ᴴ * blockUnitary V (Gf := fun _ => Ggen) U = 1 ∧
    (∀ a : ∀ f, Matrix (V f) (V f) ℂ,
      blockUnitary V (Gf := fun _ => Ggen) U * gaugeOn N a *
        (blockUnitary V (Gf := fun _ => Ggen) U)ᴴ = gaugeOn (fun _ => Ggen) a) ∧
    (∀ (X : Matrix (Σ f, V f × N f) (Σ f, V f × N f) ℂ) (h f : 𝓕)
      (A : Matrix (V h) (V f) ℂ) (B : Matrix (N h) (N f) ℂ), blk X h f = A ⊗ₖ B →
      blk (blockUnitary V (Gf := fun _ => Ggen) U * X *
        (blockUnitary V (Gf := fun _ => Ggen) U)ᴴ) h f = A ⊗ₖ ((U h)ᴴ * B * U f)) :=
  componentwise_generation_factor (V := V) (fun _ => ()) (fun _ => Ggen) (fun _ => hrank) S hpd
    hran

/-! ### Generation-neutral incidences -/

/-- The squared Hilbert–Schmidt norm. -/
noncomputable def hsSq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

theorem hsSq_nonneg {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : 0 ≤ hsSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem hsSq_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    hsSq A = 0 ↔ A = 0 := by
  rw [hsSq, Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (A i j)]
  constructor
  · intro h
    ext i j
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1
      (h i (Finset.mem_univ i)) j (Finset.mem_univ j)
    simpa using this
  · rintro rfl i _
    simp

/-- **`eq:generation-neutral-incidence`, `eq:generation-compatibility-defect`.**  With unitary
polar frames `U_f, U_h`, an arrow `B : N_f → N_h` intertwines the full common generation
algebra (`B U_f M U_f^* = U_h M U_h^* B` for all `M ∈ M_g`) iff `U_h^* B U_f ∈ ℂ I`, iff
`∑_{ij} ‖B U_f E_ij U_f^* − U_h E_ij U_h^* B‖²_HS = 0`. -/
theorem generation_neutral_iff {Nf Nh G : Type*} [Fintype Nf] [Fintype Nh] [Fintype G]
    [DecidableEq Nf] [DecidableEq Nh] [DecidableEq G] (Uf : Matrix Nf G ℂ) (Uh : Matrix Nh G ℂ) (hf1 : Ufᴴ * Uf = 1)
    (hf2 : Uf * Ufᴴ = 1) (hh1 : Uhᴴ * Uh = 1) (hh2 : Uh * Uhᴴ = 1) (B : Matrix Nh Nf ℂ) :
    ((∀ M : Matrix G G ℂ, B * (Uf * M * Ufᴴ) = (Uh * M * Uhᴴ) * B) ↔
        Uhᴴ * B * Uf ∈ Set.range (Matrix.scalar G)) ∧
    ((∑ i : G, ∑ j : G, hsSq (B * (Uf * Matrix.single i j (1 : ℂ) * Ufᴴ) -
        (Uh * Matrix.single i j (1 : ℂ) * Uhᴴ) * B)) = 0 ↔
      Uhᴴ * B * Uf ∈ Set.range (Matrix.scalar G)) := by
  set C := Uhᴴ * B * Uf
  have hB : B = Uh * C * Ufᴴ := by
    calc B = (Uh * Uhᴴ) * B * (Uf * Ufᴴ) := by rw [hh2, hf2, Matrix.one_mul, Matrix.mul_one]
      _ = Uh * C * Ufᴴ := by simp only [C, Matrix.mul_assoc]
  have key : ∀ M : Matrix G G ℂ,
      B * (Uf * M * Ufᴴ) = (Uh * M * Uhᴴ) * B ↔ C * M = M * C := by
    intro M
    constructor
    · intro h
      have := congrArg (fun Z => Uhᴴ * Z * Uf) h
      simp only [Matrix.mul_assoc] at this
      simp only [C, Matrix.mul_assoc]
      calc Uhᴴ * (B * (Uf * M)) = Uhᴴ * (B * (Uf * (M * (Ufᴴ * Uf)))) := by
            rw [hf1, Matrix.mul_one]
        _ = (Uhᴴ * Uh) * (M * (Uhᴴ * (B * Uf))) := by
            simp only [Matrix.mul_assoc]; exact this
        _ = M * (Uhᴴ * (B * Uf)) := by rw [hh1, Matrix.one_mul]
    · intro h
      rw [hB]
      calc Uh * C * Ufᴴ * (Uf * M * Ufᴴ) = Uh * (C * M) * Ufᴴ := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Ufᴴ Uf, hf1, Matrix.one_mul]
        _ = Uh * (M * C) * Ufᴴ := by rw [h]
        _ = Uh * M * Uhᴴ * (Uh * C * Ufᴴ) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Uhᴴ Uh, hh1, Matrix.one_mul]
  have hscalar : C ∈ Set.range (Matrix.scalar G) ↔ ∀ i j, C * Matrix.single i j (1 : ℂ) =
      Matrix.single i j (1 : ℂ) * C := by
    rw [Matrix.mem_range_scalar_iff_commute_single']
    exact forall₂_congr fun i j => ⟨fun h => h.eq.symm, fun h => h.symm⟩
  constructor
  · constructor
    · intro h
      exact hscalar.2 fun i j => (key _).1 (h _)
    · rintro ⟨c, hc⟩ M
      rw [key, ← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · rw [hscalar]
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hsSq_nonneg _]
    constructor
    · intro h i j
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hsSq_nonneg _).1
        (h i (Finset.mem_univ i)) j (Finset.mem_univ j)
      rw [hsSq_eq_zero_iff, sub_eq_zero] at this
      exact (key _).1 this
    · intro h i _
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hsSq_eq_zero_iff, sub_eq_zero]
      exact (key _).2 (h i j)

/-! ### Relative generation frames -/

/-- **Relative frame change (`eq:relative-generation-coordinate-change`).**  For components
`C` with fibres `𝒱_C ⊗ G` and any family of unitaries `U_C ∈ U(g)`, the frame change
`J_C ↦ J_C U_C` conjugates the represented tuple by the unitary `𝒰_U = ⊕_C I ⊗ U_C^*`.  This
conjugation is unital, multiplicative and `*`-preserving (words, Grams and commutants transform
covariantly), maps component-block-diagonal operators to component-block-diagonal operators,
and preserves the trace of every word (hence trace polynomials and spectra): no such datum
distinguishes the frames, which therefore form the homogeneous space
`U(g)^{pi0}/U(g)_diag` (a common `U_C = U` only changes the basis of the reference space). -/
theorem relative_frame_change {Cpt : Type*} [Fintype Cpt] [DecidableEq Cpt] {𝒱 : Cpt → Type*}
    [∀ C, Fintype (𝒱 C)] [∀ C, DecidableEq (𝒱 C)] {G : Type*} [Fintype G] [DecidableEq G]
    (U : Cpt → Matrix G G ℂ) (hU1 : ∀ C, (U C)ᴴ * U C = 1) (hU2 : ∀ C, U C * (U C)ᴴ = 1) :
    let 𝒰 := blockUnitary 𝒱 (N := fun _ => G) (Gf := fun _ => G) U
    let conj : Matrix (Σ C, 𝒱 C × G) (Σ C, 𝒱 C × G) ℂ → Matrix (Σ C, 𝒱 C × G)
        (Σ C, 𝒱 C × G) ℂ := fun X => 𝒰 * X * 𝒰ᴴ
    𝒰 * 𝒰ᴴ = 1 ∧ 𝒰ᴴ * 𝒰 = 1 ∧ conj 1 = 1 ∧
    (∀ X Y, conj (X * Y) = conj X * conj Y) ∧ (∀ X, conj Xᴴ = (conj X)ᴴ) ∧
    (∀ w : List (Matrix (Σ C, 𝒱 C × G) (Σ C, 𝒱 C × G) ℂ),
      conj w.prod = (w.map conj).prod ∧ (conj w.prod).trace = w.prod.trace) ∧
    (∀ Xc : ∀ C, Matrix (𝒱 C × G) (𝒱 C × G) ℂ,
      conj (blockDiagonal' Xc) = blockDiagonal' fun C =>
        ((1 : Matrix (𝒱 C) (𝒱 C) ℂ) ⊗ₖ (U C)ᴴ) * Xc C * ((1 : Matrix (𝒱 C) (𝒱 C) ℂ) ⊗ₖ U C)) := by
  intro 𝒰 conj
  obtain ⟨t1, t2, -, -, -⟩ := generation_transport (V := 𝒱) (N := fun _ => G)
    (Gf := fun _ => G) U hU1 hU2
  have hmul : ∀ X Y, conj (X * Y) = conj X * conj Y := by
    intro X Y
    simp only [conj, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc 𝒰ᴴ 𝒰, t2, Matrix.one_mul]
  have hone : conj 1 = 1 := by
    show 𝒰 * 1 * 𝒰ᴴ = 1
    rw [Matrix.mul_one]
    exact t1
  refine ⟨t1, t2, hone, hmul, ?_, ?_, ?_⟩
  · intro X
    simp only [conj, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  · intro w
    constructor
    · induction w with
      | nil => simpa using hone
      | cons X w ih => rw [List.prod_cons, hmul, ih, List.map_cons, List.prod_cons]
    · simp only [conj]
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, t2, Matrix.one_mul]
  · intro Xc
    have hH : 𝒰ᴴ = blockDiagonal' fun C => (1 : Matrix (𝒱 C) (𝒱 C) ℂ) ⊗ₖ U C := by
      simp only [𝒰, blockUnitary, blockDiagonal'_conjTranspose, conjTranspose_kronecker,
        conjTranspose_one, conjTranspose_conjTranspose]
    show 𝒰 * blockDiagonal' Xc * 𝒰ᴴ = _
    rw [hH]
    simp only [𝒰, blockUnitary]
    rw [← blockDiagonal'_mul, ← blockDiagonal'_mul]

end CommonGenerationFactor
end RenewalGeometry
