/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The five-channel matter geometry
  (`prop:five-channel-decomp`, SM_emergence)

On `H_F = F_L ⊕ F_R ⊕ S_L ⊕ S_{R0} ⊕ S_{R1}` with the weak ⊗ colour
factorization `F_L = w × c`, `F_R = w' × c`, the one-way scalar
tangent supported on the four oriented edges decomposes as
`X₅ = (2,2,1) ⊕ (2,2,15) ⊕ (1,2,4) ⊕ 2·(2,1,4)`:

* `edge_orthogonal` — matter modules supported on distinct oriented
  edges are Hilbert–Schmidt orthogonal (distinct central supports);
* `colourSinglet` / `colourTraceless` — the `F_R → F_L` edge block
  splits along `End(ℂ⁴) ≅ 𝟏 ⊕ 𝟏𝟓`: the colour-singlet part is the
  range of `W ↦ W ⊗ 1` and the adjoint part is the kernel of the
  partial colour trace `ptr`, which is its Hilbert–Schmidt adjoint
  (`kronOne_ptr_adjoint`);
* `colour_compl` / `colour_orthogonal` — the splitting is an exact
  orthogonal direct sum;
* `finrank_colourSinglet` / `finrank_colourTraceless` — dimensions
  `|w||w'|` and `|w||w'|(|c|² − 1)`; for `w = w' = ℂ²`, `c = ℂ⁴`
  this is `(2,2,1) ⊕ (2,2,15)` with dims `4 ⊕ 60`
  (`five_channel_colour_count`);
* `five_modules_orthogonal` — the four embedded edge modules of the
  selected support tree are pairwise HS-orthogonal, and the same-edge
  pair `(Φ, Ω)` is orthogonal by the colour splitting
  (`embFF_colour_orthogonal`).

The `SU(2)×SU(2)×SU(4)` equivariance labels on the summands are the
disclosed representation-theory layer.
-/

namespace NCG.FiveChannel

open Matrix

open scoped Kronecker

noncomputable section

variable {w w' c sL sR0 sR1 : Type*}
  [Fintype w] [Fintype w'] [Fintype c] [Fintype sL] [Fintype sR0]
  [Fintype sR1] [DecidableEq c]

/-- The five-sector space `F_L ⊕ F_R ⊕ S_L ⊕ S_{R0} ⊕ S_{R1}` with
weak ⊗ colour structure on the flavoured sectors. -/
abbrev HF (w w' c sL sR0 sR1 : Type*) :=
  (w × c) ⊕ ((w' × c) ⊕ (sL ⊕ (sR0 ⊕ sR1)))

/-- Sector label of an index. -/
def sec : HF w w' c sL sR0 sR1 → Fin 5
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr (.inl _))) => 3
  | .inr (.inr (.inr (.inr _))) => 4

/-- A matter module supported on the oriented edge `s → t` (rows in
sector `t`, columns in sector `s`). -/
def EdgeSupported (t s : Fin 5)
    (M : Matrix (HF w w' c sL sR0 sR1) (HF w w' c sL sR0 sR1) ℂ) :
    Prop :=
  ∀ i j, M i j ≠ 0 → sec i = t ∧ sec j = s

omit [DecidableEq c] in
/-- `prop:five-channel-decomp` (distinct central supports): modules
supported on distinct oriented edges are Hilbert–Schmidt orthogonal. -/
theorem edge_orthogonal {t s t' s' : Fin 5} (h : (t, s) ≠ (t', s'))
    {M N : Matrix (HF w w' c sL sR0 sR1) (HF w w' c sL sR0 sR1) ℂ}
    (hM : EdgeSupported t s M) (hN : EdgeSupported t' s' N) :
    trace (Mᴴ * N) = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.conjTranspose_apply]
  by_cases hMji : M j i = 0
  · rw [hMji, star_zero, zero_mul]
  · by_cases hNji : N j i = 0
    · rw [hNji, mul_zero]
    · obtain ⟨h1, h2⟩ := hM j i hMji
      obtain ⟨h3, h4⟩ := hN j i hNji
      exact absurd (by rw [← h1, ← h2, h3, h4]) h

/-! ## The colour splitting of the `F_R → F_L` edge block -/

/-- The colour-singlet embedding `W ↦ W ⊗ 1`. -/
def kronOne : Matrix w w' ℂ →ₗ[ℂ] Matrix (w × c) (w' × c) ℂ where
  toFun W := W ⊗ₖ (1 : Matrix c c ℂ)
  map_add' A B := Matrix.add_kronecker A B 1
  map_smul' r A := Matrix.smul_kronecker r A 1

/-- The partial colour trace, the Hilbert–Schmidt adjoint of
`kronOne`. -/
def ptr : Matrix (w × c) (w' × c) ℂ →ₗ[ℂ] Matrix w w' ℂ where
  toFun M := Matrix.of fun p q => ∑ k : c, M (p, k) (q, k)
  map_add' A B := by
    ext p q
    simp [Finset.sum_add_distrib]
  map_smul' r A := by
    ext p q
    simp [Finset.mul_sum]

/-- The colour-singlet (`(2,2,1)`-type) summand of the edge block. -/
def colourSinglet : Submodule ℂ (Matrix (w × c) (w' × c) ℂ) :=
  LinearMap.range (kronOne (w := w) (w' := w') (c := c))

/-- The colour-adjoint (`(2,2,15)`-type) summand of the edge block. -/
def colourTraceless : Submodule ℂ (Matrix (w × c) (w' × c) ℂ) :=
  LinearMap.ker (ptr (w := w) (w' := w') (c := c))

omit [Fintype w] [Fintype w'] [Fintype c] in
private lemma kronOne_apply (W : Matrix w w' ℂ) (p : w) (k : c) (q : w')
    (l : c) :
    kronOne W (p, k) (q, l) = if k = l then W p q else 0 := by
  simp [kronOne, Matrix.one_apply, mul_ite, mul_one, mul_zero]

omit [Fintype w] [Fintype w'] in
private lemma ptr_kronOne (W : Matrix w w' ℂ) :
    ptr (kronOne (c := c) W) = (Fintype.card c : ℂ) • W := by
  ext p q
  simp [ptr, kronOne_apply, mul_comm]

variable [Nonempty c]

omit [DecidableEq c] in
private lemma card_c_ne : (Fintype.card c : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

omit [Fintype w] [Fintype w'] in
/-- `prop:five-channel-decomp` (edge splitting): the `F_R → F_L` edge
block is the exact direct sum of its colour-singlet and
colour-adjoint parts, `(2,2,1) ⊕ (2,2,15)`. -/
theorem colour_compl :
    IsCompl (colourSinglet (w := w) (w' := w') (c := c))
      (colourTraceless (w := w) (w' := w') (c := c)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro M hM1 hM2
    obtain ⟨W, rfl⟩ := hM1
    have h0 : ptr (kronOne (c := c) W) = 0 := hM2
    rw [ptr_kronOne] at h0
    have hW : W = 0 := by
      have hs := congrArg (fun X => (Fintype.card c : ℂ)⁻¹ • X) h0
      simpa [smul_smul, inv_mul_cancel₀ card_c_ne] using hs
    rw [hW, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro M _
    have hsplit : M
        = kronOne ((Fintype.card c : ℂ)⁻¹ • ptr M)
          + (M - kronOne ((Fintype.card c : ℂ)⁻¹ • ptr M)) := by
      abel
    rw [hsplit]
    apply Submodule.add_mem_sup
    · exact ⟨_, rfl⟩
    · refine LinearMap.mem_ker.mpr ?_
      rw [map_sub, ptr_kronOne, smul_smul, mul_inv_cancel₀ card_c_ne,
        one_smul, sub_self]

omit [Nonempty c] in
/-- The Hilbert–Schmidt adjunction `⟨W ⊗ 1, N⟩ = ⟨W, ptr N⟩`. -/
theorem kronOne_ptr_adjoint (W : Matrix w w' ℂ)
    (N : Matrix (w × c) (w' × c) ℂ) :
    trace ((kronOne (c := c) W)ᴴ * N) = trace (Wᴴ * ptr N) := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, kronOne_apply,
    apply_ite (star : ℂ → ℂ), star_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, ptr,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact Finset.sum_comm

omit [Nonempty c] in
/-- `prop:five-channel-decomp` (same-edge orthogonality): the
colour-singlet and colour-adjoint summands are Hilbert–Schmidt
orthogonal. -/
theorem colour_orthogonal {M N : Matrix (w × c) (w' × c) ℂ}
    (hM : M ∈ colourSinglet (w := w) (w' := w') (c := c))
    (hN : N ∈ colourTraceless (w := w) (w' := w') (c := c)) :
    trace (Mᴴ * N) = 0 := by
  obtain ⟨W, rfl⟩ := hM
  have hptr : ptr N = 0 := hN
  rw [kronOne_ptr_adjoint, hptr, Matrix.mul_zero, Matrix.trace_zero]

omit [Fintype c] in
/-- Dimension of the colour-singlet summand: `|w|·|w'|` (the
`(2,2,1)` count). -/
theorem finrank_colourSinglet [Finite c] :
    Module.finrank ℂ (colourSinglet (w := w) (w' := w') (c := c))
      = Fintype.card w * Fintype.card w' := by
  haveI := Fintype.ofFinite c
  have hinj : Function.Injective (kronOne (w := w) (w' := w') (c := c)) := by
    intro A B hAB
    have h := congrArg (ptr (w := w) (w' := w') (c := c)) hAB
    rw [ptr_kronOne, ptr_kronOne] at h
    exact smul_right_injective _ card_c_ne h
  rw [colourSinglet, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_matrix]
  simp

omit [DecidableEq c] in
/-- Dimension of the colour-adjoint summand:
`|w|·|w'|·(|c|² − 1)` (the `(2,2,15)` count). -/
theorem finrank_colourTraceless :
    Module.finrank ℂ (colourTraceless (w := w) (w' := w') (c := c))
      = Fintype.card w * Fintype.card w'
        * (Fintype.card c ^ 2 - 1) := by
  classical
  have hsurj : Function.Surjective (ptr (w := w) (w' := w') (c := c)) := by
    intro W
    refine ⟨kronOne ((Fintype.card c : ℂ)⁻¹ • W), ?_⟩
    rw [ptr_kronOne, smul_smul, mul_inv_cancel₀ card_c_ne, one_smul]
  have hrk := LinearMap.finrank_range_add_finrank_ker
    (ptr (w := w) (w' := w') (c := c))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_matrix, Module.finrank_matrix, Module.finrank_self,
    mul_one, Fintype.card_prod, Fintype.card_prod] at hrk
  have hcpos : 1 ≤ Fintype.card c := Fintype.card_pos
  have harith : Fintype.card w * Fintype.card c
      * (Fintype.card w' * Fintype.card c)
      = Fintype.card w * Fintype.card w' * Fintype.card c ^ 2 := by
    ring
  rw [harith] at hrk
  have hexp : Fintype.card w * Fintype.card w'
      * (Fintype.card c ^ 2 - 1)
      = Fintype.card w * Fintype.card w' * Fintype.card c ^ 2
        - Fintype.card w * Fintype.card w' := by
    rw [Nat.mul_sub, mul_one]
  rw [colourTraceless, hexp]
  omega

/-- The `(2,2,1) ⊕ (2,2,15)` instantiation: for weak doublets and
`SU(4)` colour the two summands have dimensions `4` and `60 = 4·15`. -/
theorem five_channel_colour_count :
    Module.finrank ℂ
        (colourSinglet (w := Fin 2) (w' := Fin 2) (c := Fin 4)) = 4
      ∧ Module.finrank ℂ
        (colourTraceless (w := Fin 2) (w' := Fin 2) (c := Fin 4))
          = 60 := by
  constructor
  · rw [finrank_colourSinglet]
    simp
  · rw [finrank_colourTraceless]
    simp

/-! ## The embedded support tree -/

/-- Embed the `F_R → F_L` edge block. -/
def embFF (M : Matrix (w × c) (w' × c) ℂ) :
    Matrix (HF w w' c sL sR0 sR1) (HF w w' c sL sR0 sR1) ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | .inl p, .inr (.inl q) => M p q
    | _, _ => 0

/-- Embed the `S_L → F_L` edge block. -/
def embLS (M : Matrix (w × c) sL ℂ) :
    Matrix (HF w w' c sL sR0 sR1) (HF w w' c sL sR0 sR1) ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | .inl p, .inr (.inr (.inl q)) => M p q
    | _, _ => 0

/-- Embed the `S_{R0} → F_R` edge block. -/
def embR0 (M : Matrix (w' × c) sR0 ℂ) :
    Matrix (HF w w' c sL sR0 sR1) (HF w w' c sL sR0 sR1) ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | .inr (.inl p), .inr (.inr (.inr (.inl q))) => M p q
    | _, _ => 0

/-- Embed the `S_{R1} → F_R` edge block. -/
def embR1 (M : Matrix (w' × c) sR1 ℂ) :
    Matrix (HF w w' c sL sR0 sR1) (HF w w' c sL sR0 sR1) ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | .inr (.inl p), .inr (.inr (.inr (.inr q))) => M p q
    | _, _ => 0

omit [Fintype w] [Fintype w'] [Fintype c] [Fintype sL] [Fintype sR0]
  [Fintype sR1] [DecidableEq c] [Nonempty c] in
private lemma embFF_supported (M : Matrix (w × c) (w' × c) ℂ) :
    EdgeSupported (sL := sL) (sR0 := sR0) (sR1 := sR1) 0 1 (embFF M) := by
  rintro (i | i | i | i | i) (j | j | j | j | j) h <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd rfl h

omit [Fintype w] [Fintype w'] [Fintype c] [Fintype sL] [Fintype sR0]
  [Fintype sR1] [DecidableEq c] [Nonempty c] in
private lemma embLS_supported (M : Matrix (w × c) sL ℂ) :
    EdgeSupported (w' := w') (sR0 := sR0) (sR1 := sR1) 0 2 (embLS M) := by
  rintro (i | i | i | i | i) (j | j | j | j | j) h <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd rfl h

omit [Fintype w] [Fintype w'] [Fintype c] [Fintype sL] [Fintype sR0]
  [Fintype sR1] [DecidableEq c] [Nonempty c] in
private lemma embR0_supported (M : Matrix (w' × c) sR0 ℂ) :
    EdgeSupported (w := w) (sL := sL) (sR1 := sR1) 1 3 (embR0 M) := by
  rintro (i | i | i | i | i) (j | j | j | j | j) h <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd rfl h

omit [Fintype w] [Fintype w'] [Fintype c] [Fintype sL] [Fintype sR0]
  [Fintype sR1] [DecidableEq c] [Nonempty c] in
private lemma embR1_supported (M : Matrix (w' × c) sR1 ℂ) :
    EdgeSupported (w := w) (sL := sL) (sR0 := sR0) 1 4 (embR1 M) := by
  rintro (i | i | i | i | i) (j | j | j | j | j) h <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd rfl h

omit [DecidableEq c] [Nonempty c] in
/-- `prop:five-channel-decomp` (pairwise orthogonality of the support
tree): the four embedded edge modules `Φ⊕Ω`, `χ_L`, `χ_{R0}`,
`χ_{R1}` are pairwise Hilbert–Schmidt orthogonal. -/
theorem five_modules_orthogonal (M : Matrix (w × c) (w' × c) ℂ)
    (NL : Matrix (w × c) sL ℂ) (N0 : Matrix (w' × c) sR0 ℂ)
    (N1 : Matrix (w' × c) sR1 ℂ) :
    trace ((embFF (sL := sL) (sR0 := sR0) (sR1 := sR1) M)ᴴ
        * embLS NL) = 0
      ∧ trace ((embFF (sL := sL) (sR0 := sR0) (sR1 := sR1) M)ᴴ
        * embR0 N0) = 0
      ∧ trace ((embFF (sL := sL) (sR0 := sR0) (sR1 := sR1) M)ᴴ
        * embR1 N1) = 0
      ∧ trace ((embLS (w' := w') (sR0 := sR0) (sR1 := sR1) NL)ᴴ
        * embR0 N0) = 0
      ∧ trace ((embLS (w' := w') (sR0 := sR0) (sR1 := sR1) NL)ᴴ
        * embR1 N1) = 0
      ∧ trace ((embR0 (w := w) (sL := sL) (sR1 := sR1) N0)ᴴ
        * embR1 N1) = 0 :=
  ⟨edge_orthogonal (by decide) (embFF_supported M) (embLS_supported NL),
    edge_orthogonal (by decide) (embFF_supported M) (embR0_supported N0),
    edge_orthogonal (by decide) (embFF_supported M) (embR1_supported N1),
    edge_orthogonal (by decide) (embLS_supported NL) (embR0_supported N0),
    edge_orthogonal (by decide) (embLS_supported NL) (embR1_supported N1),
    edge_orthogonal (by decide) (embR0_supported N0) (embR1_supported N1)⟩

omit [Nonempty c] in
/-- The embedded trace pairing on the `F_R → F_L` edge reduces to the
block pairing, so `Φ ⊥ Ω` holds inside the full five-sector space. -/
theorem embFF_colour_orthogonal {M N : Matrix (w × c) (w' × c) ℂ}
    (hM : M ∈ colourSinglet (w := w) (w' := w') (c := c))
    (hN : N ∈ colourTraceless (w := w) (w' := w') (c := c)) :
    trace ((embFF (sL := sL) (sR0 := sR0) (sR1 := sR1) M)ᴴ
      * embFF N) = 0 := by
  have hred : trace ((embFF (sL := sL) (sR0 := sR0) (sR1 := sR1) M)ᴴ
      * embFF N) = trace (Mᴴ * N) := by
    rw [Matrix.trace, Matrix.trace]
    rw [Fintype.sum_sum_type]
    simp only [Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_sum_type, embFF,
      Matrix.of_apply, star_zero, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add]
  rw [hred]
  exact colour_orthogonal hM hN

end

end NCG.FiveChannel

