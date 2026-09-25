/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.InternalAssemblyExact
import RenewalGeometry.Commutant.FiniteComplexStarSubalgebraSemisimplicity

/-!
# Central separation of the landed internal blocks

`thm:central-separation` of the spacetime–gauge duality paper, on the concrete
census carrier `ℂ³ ⊕ ℂ² ⊕ ℂ ⊕ ℂ = ℂ⁷` of `InternalAssemblyExact`, where
`M₃(ℂ) ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ` is the block algebra `blockAlgebra` (blocks
`{0,1,2}`, `{3,4}`, `{5}`, `{6}`).

Let `B` be a unital `*`-subalgebra of `M₇(ℂ)` contained in the block algebra whose
projection onto the `M₃` factor and onto the `M₂` factor are surjective
(the projections onto the two scalar factors are automatically surjective since
`B` is unital).  Then exactly one of

* `B = M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` (`blockAlgebra`, dimension `15`), or
* `B = {(A, B, z, z)}` (`lockedAlgebra`, dimension `14`)

occurs (`central_separation_dichotomy`, `finrank_blockAlgebra`,
`finrank_lockedAlgebra`), and for a generating bank `b : ι → M₇(ℂ)` the full
product occurs iff the scalar characters `χ₁ = (·) 5 5`, `χ₂ = (·) 6 6` are
separated, `η_cen = ∑ |χ₁(b_j) - χ₂(b_j)|² > 0` (`central_separation_criterion`);
a represented scalar central projector discharges the condition
(`eta_pos_of_central_projector`).

## Proof architecture

The nontrivial step is that a unital subdirect product of matrix algebras can only
correlate isomorphic factors.  Here it is proved directly: for the source block
`s` (colour or weak) the kernel `K = {b ∈ B | P_s b = 0}` is a left ideal of `B`,
and its trace-orthogonal complement `J` inside `B`
(`FiniteComplexStarSubalgebraSemisimplicity.leftIdealOrthogonalComplement`) is a
two-sided ideal with `J ∩ K = 0` and `J + K = B`, so the block restriction
`j ↦ j.submatrix ι_s ι_s` is a bijection `J ≃ M_{d_s}(ℂ)` (`exists_sourceIdeal`).
Transporting along it, each other block projection becomes a non-unital ring
homomorphism `ψ_t : M_{d_s}(ℂ) → M₇(ℂ)`; its kernel is a two-sided ideal of the
simple ring `M_{d_s}(ℂ)`, so `ψ_t` is injective or zero, and injectivity is
excluded by dimension when the target block is smaller (`sourceIdeal_kills_small`).
For the weak source and the colour target (`4 < 9`) the dimension count is
replaced by the ideal property once `M₃ ⊕ 0 ⊆ B` is known
(`sourceIdeal_kills_of_unit_mem`).  Hence `M₃ ⊕ 0 ⊆ B` and `0 ⊕ M₂ ⊆ B`
(`block_le_of_kills`), and the remaining scalar part is a unital subalgebra of
`ℂ ⊕ ℂ`: the diagonal or everything.
-/

open Finset Matrix
open RenewalGeometry.InternalAssembly (blockOf blockAlgebra)

namespace RenewalGeometry
namespace CentralSeparation

/-! ### Matrices supported on a finite set of index pairs -/

section Supported

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Matrices supported on the finite set `P` of index pairs. -/
def supportedOn (P : Finset (m × n)) : Submodule ℂ (Matrix m n ℂ) where
  carrier := {X | ∀ i j, (i, j) ∉ P → X i j = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun {X Y} hX hY i j h => by simp [hX i j h, hY i j h]
  smul_mem' := fun c {X} hX i j h => by simp [hX i j h]

theorem mem_supportedOn {P : Finset (m × n)} {X : Matrix m n ℂ} :
    X ∈ supportedOn P ↔ ∀ i j, (i, j) ∉ P → X i j = 0 := Iff.rfl

/-- Coordinates on `P` identify `supportedOn P` with `P → ℂ`. -/
def supportedOnEquiv (P : Finset (m × n)) : supportedOn P ≃ₗ[ℂ] (P → ℂ) where
  toFun X := fun p => X.1 p.1.1 p.1.2
  map_add' X Y := by ext p; simp
  map_smul' c X := by ext p; simp
  invFun f := ⟨Matrix.of fun i j => if h : (i, j) ∈ P then f ⟨(i, j), h⟩ else 0,
    fun i j h => by simp [h]⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    by_cases h : (i, j) ∈ P
    · simp [h]
    · simp [h, X.2 i j h]
  right_inv f := by
    ext ⟨⟨i, j⟩, h⟩
    simp [h]

theorem finrank_supportedOn (P : Finset (m × n)) :
    Module.finrank ℂ (supportedOn P) = P.card := by
  rw [(supportedOnEquiv P).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

end Supported

/-! ### Central projectors of the census carrier -/

/-- The central projector `P_k` onto block `k`. -/
def centralProj (k : Fin 4) : Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.diagonal fun i => if blockOf i = k then 1 else 0

theorem centralProj_mul_apply (k : Fin 4) (X : Matrix (Fin 7) (Fin 7) ℂ) (i j : Fin 7) :
    (centralProj k * X) i j = if blockOf i = k then X i j else 0 := by
  rw [centralProj, Matrix.diagonal_mul]
  split_ifs <;> simp

theorem mul_centralProj_apply (k : Fin 4) (X : Matrix (Fin 7) (Fin 7) ℂ) (i j : Fin 7) :
    (X * centralProj k) i j = if blockOf j = k then X i j else 0 := by
  rw [centralProj, Matrix.mul_diagonal]
  split_ifs <;> simp

theorem centralProj_mul_self (k : Fin 4) : centralProj k * centralProj k = centralProj k := by
  ext i j
  rw [centralProj_mul_apply]
  split_ifs with h
  · rfl
  · rw [centralProj, Matrix.diagonal_apply]
    split_ifs with hij
    · simp [hij, h]
    · rfl

theorem centralProj_mul_centralProj_of_ne {k l : Fin 4} (h : k ≠ l) :
    centralProj k * centralProj l = 0 := by
  ext i j
  rw [centralProj_mul_apply, Matrix.zero_apply]
  split_ifs with hi
  · rw [centralProj, Matrix.diagonal_apply]
    split_ifs with hij hl
    · exact absurd (hi.symm.trans hl) h
    · rfl
    · rfl
  · rfl

theorem sum_centralProj : ∑ k : Fin 4, centralProj k = 1 := by
  ext i j
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [centralProj, Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    simp
  · simp [hij]

theorem centralProj_mem_blockAlgebra (k : Fin 4) : centralProj k ∈ blockAlgebra := by
  intro i j hij
  rw [centralProj, Matrix.diagonal_apply]
  split_ifs with h
  · exact absurd (by rw [h]) hij
  · rfl
  · rfl

/-- Central projectors commute with the block algebra. -/
theorem centralProj_comm {X : Matrix (Fin 7) (Fin 7) ℂ} (hX : X ∈ blockAlgebra) (k : Fin 4) :
    centralProj k * X = X * centralProj k := by
  ext i j
  rw [centralProj_mul_apply, mul_centralProj_apply]
  by_cases hb : blockOf i = blockOf j
  · rw [hb]
  · rw [hX i j hb]; simp

/-- Block-supported matrices `P_t X` of a block-diagonal `X` are supported on the
pairs of block `t`. -/
theorem centralProj_mul_mem_supportedOn {X : Matrix (Fin 7) (Fin 7) ℂ} (hX : X ∈ blockAlgebra)
    (t : Fin 4) :
    centralProj t * X ∈ supportedOn (Finset.univ.filter
      fun p : Fin 7 × Fin 7 => blockOf p.1 = t ∧ blockOf p.2 = t) := by
  intro i j hij
  rw [centralProj_mul_apply]
  split_ifs with hi
  · by_cases hj : blockOf j = t
    · exact absurd (by simp [hi, hj]) hij
    · exact hX i j (fun hc => hj (hc.symm.trans hi))
  · rfl

/-! ### Block restriction along an enumeration of a block -/

section Restriction

variable {d : ℕ} {s : Fin 4} (ι : Fin d → Fin 7)

/-- Multiplicativity of block restriction on block-diagonal matrices. -/
theorem submatrix_mul_of_mem_blockAlgebra (hinj : Function.Injective ι)
    (hι : ∀ i, blockOf i = s ↔ ∃ a, ι a = i)
    {X Y : Matrix (Fin 7) (Fin 7) ℂ} (hX : X ∈ blockAlgebra) :
    (X * Y).submatrix ι ι = X.submatrix ι ι * Y.submatrix ι ι := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_image (f := fun m => X (ι a) m * Y m (ι b)) (s := Finset.univ)
    (fun x _ y _ hxy => hinj hxy)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro m _ hm
  have hblock : blockOf m ≠ s := by
    intro hc
    obtain ⟨c, hc⟩ := (hι m).mp hc
    exact hm (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩)
  have hιa : blockOf (ι a) = s := (hι (ι a)).mpr ⟨a, rfl⟩
  rw [hX (ι a) m (fun hc => hblock (hc.symm.trans hιa)), zero_mul]

/-- On block-diagonal matrices, vanishing of the `s`-corner is vanishing of the
restriction. -/
theorem centralProj_mul_eq_zero_iff (hι : ∀ i, blockOf i = s ↔ ∃ a, ι a = i)
    {Z : Matrix (Fin 7) (Fin 7) ℂ} (hZ : Z ∈ blockAlgebra) :
    centralProj s * Z = 0 ↔ Z.submatrix ι ι = 0 := by
  constructor
  · intro h
    ext a b
    have := congrFun (congrFun h (ι a)) (ι b)
    rw [centralProj_mul_apply, if_pos ((hι (ι a)).mpr ⟨a, rfl⟩)] at this
    simpa using this
  · intro h
    ext i j
    rw [centralProj_mul_apply, Matrix.zero_apply]
    split_ifs with hi
    · by_cases hj : blockOf j = s
      · obtain ⟨a, rfl⟩ := (hι i).mp hi
        obtain ⟨b, rfl⟩ := (hι j).mp hj
        have := congrFun (congrFun h a) b
        simpa using this
      · exact hZ i j (fun hc => hj (hc.symm.trans hi))
    · rfl

end Restriction

/-! ### The source ideal of a surjective block -/

section SourceIdeal

open FiniteComplexStarSubalgebraSemisimplicity

/-- Entrywise forms of the linearity of block restriction. -/
theorem submatrix_add' {d : ℕ} (ι : Fin d → Fin 7) (A C : Matrix (Fin 7) (Fin 7) ℂ) :
    (A + C).submatrix ι ι = A.submatrix ι ι + C.submatrix ι ι := by ext; simp

theorem submatrix_sub' {d : ℕ} (ι : Fin d → Fin 7) (A C : Matrix (Fin 7) (Fin 7) ℂ) :
    (A - C).submatrix ι ι = A.submatrix ι ι - C.submatrix ι ι := by ext; simp

theorem submatrix_smul' {d : ℕ} (ι : Fin d → Fin 7) (c : ℂ) (A : Matrix (Fin 7) (Fin 7) ℂ) :
    (c • A).submatrix ι ι = c • A.submatrix ι ι := by ext; simp

theorem submatrix_zero' {d : ℕ} (ι : Fin d → Fin 7) :
    (0 : Matrix (Fin 7) (Fin 7) ℂ).submatrix ι ι = 0 := by ext; simp

variable (B : StarSubalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ)) (hB : ∀ b ∈ B, b ∈ blockAlgebra)

include hB

/-- The kernel `K = {b ∈ B | P_s b = 0}` of the `s`-corner, a left ideal of `B`. -/
def kerIdeal (s : Fin 4) : Submodule B B where
  carrier := {x | centralProj s * (x : Matrix (Fin 7) (Fin 7) ℂ) = 0}
  zero_mem' := by
    change centralProj s * ((0 : B) : Matrix (Fin 7) (Fin 7) ℂ) = 0
    simp
  add_mem' := fun {x y} hx hy => by
    have hx' : centralProj s * (x : Matrix (Fin 7) (Fin 7) ℂ) = 0 := hx
    have hy' : centralProj s * (y : Matrix (Fin 7) (Fin 7) ℂ) = 0 := hy
    change centralProj s * ((x : Matrix (Fin 7) (Fin 7) ℂ) + y) = 0
    rw [Matrix.mul_add, hx', hy', add_zero]
  smul_mem' := fun a {x} hx => by
    have hx' : centralProj s * (x : Matrix (Fin 7) (Fin 7) ℂ) = 0 := hx
    change centralProj s * ((a : Matrix (Fin 7) (Fin 7) ℂ) * x) = 0
    rw [← Matrix.mul_assoc, centralProj_comm (hB a a.2), Matrix.mul_assoc, hx', Matrix.mul_zero]

theorem mem_kerIdeal {s : Fin 4} {x : B} :
    x ∈ kerIdeal B hB s ↔ centralProj s * (x : Matrix (Fin 7) (Fin 7) ℂ) = 0 := Iff.rfl

/-- Membership in the trace-orthogonal complement of the kernel ideal. -/
theorem mem_orth_iff {s : Fin 4} {x : B} :
    x ∈ leftIdealOrthogonalComplement B (kerIdeal B hB s) ↔
      ∀ y ∈ kerIdeal B hB s,
        Matrix.trace ((y : Matrix (Fin 7) (Fin 7) ℂ)ᴴ * (x : Matrix (Fin 7) (Fin 7) ℂ)) = 0 := by
  constructor
  · intro h y hy
    exact h (star y) (star_mem_adjointSubspace B _ hy)
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact h y hy

/-- The orthogonal complement is also a right ideal. -/
theorem orth_mul_mem {s : Fin 4} {x : B}
    (hx : x ∈ leftIdealOrthogonalComplement B (kerIdeal B hB s)) (a : B) :
    x * a ∈ leftIdealOrthogonalComplement B (kerIdeal B hB s) := by
  rw [mem_orth_iff] at hx ⊢
  intro y hy
  have hmem : y * star a ∈ kerIdeal B hB s := by
    rw [mem_kerIdeal] at hy ⊢
    change centralProj s * ((y : Matrix (Fin 7) (Fin 7) ℂ) * (a : Matrix (Fin 7) (Fin 7) ℂ)ᴴ) = 0
    rw [← Matrix.mul_assoc, hy, Matrix.zero_mul]
  have := hx (y * star a) hmem
  change Matrix.trace (((y : Matrix (Fin 7) (Fin 7) ℂ) * (a : Matrix (Fin 7) (Fin 7) ℂ)ᴴ)ᴴ *
    (x : Matrix (Fin 7) (Fin 7) ℂ)) = 0 at this
  change Matrix.trace ((y : Matrix (Fin 7) (Fin 7) ℂ)ᴴ *
    ((x : Matrix (Fin 7) (Fin 7) ℂ) * (a : Matrix (Fin 7) (Fin 7) ℂ))) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] at this
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_assoc]
  exact this

/-- **The source ideal.**  If the `s`-corner of `B` is onto `M_d(ℂ)` (along the
enumeration `ι` of block `s`), there is a two-sided ideal `J ⊆ B` on which the
`s`-corner is injective and whose block restriction is onto `M_d(ℂ)`. -/
theorem exists_sourceIdeal {s : Fin 4} {d : ℕ} (ι : Fin d → Fin 7)
    (hι : ∀ i, blockOf i = s ↔ ∃ a, ι a = i)
    (hsurj : ∀ X : Matrix (Fin d) (Fin d) ℂ, ∃ b ∈ B, b.submatrix ι ι = X) :
    ∃ J : Submodule ℂ (Matrix (Fin 7) (Fin 7) ℂ),
      (∀ j ∈ J, j ∈ B) ∧
      (∀ j ∈ J, ∀ a ∈ B, a * j ∈ J ∧ j * a ∈ J) ∧
      (∀ j ∈ J, centralProj s * j = 0 → j = 0) ∧
      (∀ X : Matrix (Fin d) (Fin d) ℂ, ∃ j ∈ J, j.submatrix ι ι = X) := by
  set K := kerIdeal B hB s with hK
  set Jo := leftIdealOrthogonalComplement B K with hJo
  have hcompl := leftIdealOrthogonalComplement_isCompl B K
  refine ⟨{ carrier := {x | ∃ y : B, y ∈ Jo ∧ (y : Matrix (Fin 7) (Fin 7) ℂ) = x}
            zero_mem' := ⟨0, Jo.zero_mem, rfl⟩
            add_mem' := fun {x x'} hx hx' => by
              obtain ⟨y, hy, rfl⟩ := hx
              obtain ⟨y', hy', rfl⟩ := hx'
              exact ⟨y + y', Jo.add_mem hy hy', rfl⟩
            smul_mem' := fun c {x} hx => by
              obtain ⟨y, hy, rfl⟩ := hx
              exact ⟨c • y, (Jo.restrictScalars ℂ).smul_mem c hy, rfl⟩ }, ?_, ?_, ?_, ?_⟩
  · rintro j ⟨y, -, rfl⟩
    exact y.2
  · rintro j ⟨y, hy, rfl⟩ a ha
    exact ⟨⟨⟨a, ha⟩ • y, Jo.smul_mem _ hy, rfl⟩, ⟨y * ⟨a, ha⟩, orth_mul_mem B hB hy _, rfl⟩⟩
  · rintro j ⟨y, hy, rfl⟩ hj
    have hyK : y ∈ K := hj
    have := Submodule.disjoint_def.mp hcompl.disjoint y hyK hy
    rw [this]; rfl
  · intro X
    obtain ⟨b, hb, hbX⟩ := hsurj X
    have hsup : (⟨b, hb⟩ : B) ∈ K ⊔ Jo := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨k, hk, y, hy, hky⟩ := Submodule.mem_sup.mp hsup
    refine ⟨y, ⟨y, hy, rfl⟩, ?_⟩
    have hb' : (b : Matrix (Fin 7) (Fin 7) ℂ) = k + y := by
      have := congrArg (fun z : B => (z : Matrix (Fin 7) (Fin 7) ℂ)) hky
      simpa using this.symm
    have hk0 : (k : Matrix (Fin 7) (Fin 7) ℂ).submatrix ι ι = 0 :=
      (centralProj_mul_eq_zero_iff ι hι (hB k k.2)).mp hk
    rw [hb', submatrix_add', hk0, zero_add] at hbX
    exact hbX

/-- A block `s` is contained in `B` once its source ideal is killed by all other
central projectors. -/
theorem block_le_of_kills {s : Fin 4} {d : ℕ} (ι : Fin d → Fin 7)
    (hι : ∀ i, blockOf i = s ↔ ∃ a, ι a = i)
    (J : Submodule ℂ (Matrix (Fin 7) (Fin 7) ℂ)) (hJB : ∀ j ∈ J, j ∈ B)
    (hJinj : ∀ j ∈ J, centralProj s * j = 0 → j = 0)
    (hJsurj : ∀ X : Matrix (Fin d) (Fin d) ℂ, ∃ j ∈ J, j.submatrix ι ι = X)
    (hkill : ∀ j ∈ J, ∀ t, t ≠ s → centralProj t * j = 0) :
    ∀ Y ∈ blockAlgebra, centralProj s * Y = Y → Y ∈ B := by
  intro Y hY hYs
  obtain ⟨j, hj, hjY⟩ := hJsurj (Y.submatrix ι ι)
  have hjs : centralProj s * j = j := by
    calc centralProj s * j = ∑ t : Fin 4, centralProj t * j := by
          rw [Finset.sum_eq_single s]
          · intro t _ hts; exact hkill j hj t hts
          · intro h; exact absurd (Finset.mem_univ s) h
      _ = j := by rw [← Finset.sum_mul, sum_centralProj, Matrix.one_mul]
  have hdiff : centralProj s * (j - Y) = 0 := by
    rw [centralProj_mul_eq_zero_iff ι hι (blockAlgebra.sub_mem (hB j (hJB j hj)) hY),
      submatrix_sub', hjY, sub_self]
  rw [Matrix.mul_sub, hjs, hYs, sub_eq_zero] at hdiff
  rw [← hdiff]
  exact hJB j hj

/-- **Small targets are killed.**  If the target block `t ≠ s` has fewer than
`d²` matrix entries, the `t`-corner vanishes on the source ideal of an
`M_d(ℂ)`-block: the transported corner is a non-unital ring homomorphism out of
the simple ring `M_d(ℂ)`, hence injective or zero, and injectivity is excluded by
dimension. -/
theorem sourceIdeal_kills_small {s : Fin 4} {d : ℕ} [NeZero d] (ι : Fin d → Fin 7)
    (hinj : Function.Injective ι) (hι : ∀ i, blockOf i = s ↔ ∃ a, ι a = i)
    (J : Submodule ℂ (Matrix (Fin 7) (Fin 7) ℂ)) (hJB : ∀ j ∈ J, j ∈ B)
    (hJideal : ∀ j ∈ J, ∀ a ∈ B, a * j ∈ J ∧ j * a ∈ J)
    (hJinj : ∀ j ∈ J, centralProj s * j = 0 → j = 0)
    (hJsurj : ∀ X : Matrix (Fin d) (Fin d) ℂ, ∃ j ∈ J, j.submatrix ι ι = X)
    (t : Fin 4)
    (hdim : (Finset.univ.filter fun p : Fin 7 × Fin 7 =>
      blockOf p.1 = t ∧ blockOf p.2 = t).card < d * d) :
    ∀ j ∈ J, centralProj t * j = 0 := by
  have huniq : ∀ j ∈ J, ∀ j' ∈ J, j.submatrix ι ι = j'.submatrix ι ι → j = j' := by
    intro j hj j' hj' h
    have hsub : j - j' ∈ J := J.sub_mem hj hj'
    have := hJinj (j - j') hsub ((centralProj_mul_eq_zero_iff ι hι
      (hB _ (hJB _ hsub))).mpr (by rw [submatrix_sub', h, sub_self]))
    exact sub_eq_zero.mp this
  choose jOf hjOf using hJsurj
  have hjOf_add : ∀ X Y, jOf (X + Y) = jOf X + jOf Y := fun X Y =>
    huniq _ (hjOf _).1 _ (J.add_mem (hjOf X).1 (hjOf Y).1)
      (by rw [(hjOf _).2, submatrix_add', (hjOf X).2, (hjOf Y).2])
  have hjOf_zero : jOf 0 = 0 :=
    huniq _ (hjOf _).1 _ J.zero_mem (by rw [(hjOf _).2, submatrix_zero'])
  have hjOf_smul : ∀ (c : ℂ) X, jOf (c • X) = c • jOf X := fun c X =>
    huniq _ (hjOf _).1 _ (J.smul_mem c (hjOf X).1)
      (by rw [(hjOf _).2, submatrix_smul', (hjOf X).2])
  have hjOf_mul : ∀ X Y, jOf (X * Y) = jOf X * jOf Y := fun X Y =>
    huniq _ (hjOf _).1 _ (hJideal _ (hjOf Y).1 _ (hJB _ (hjOf X).1)).1
      (by rw [(hjOf _).2, submatrix_mul_of_mem_blockAlgebra ι hinj hι (hB _ (hJB _ (hjOf X).1)),
        (hjOf X).2, (hjOf Y).2])
  have hcomm : ∀ X, centralProj t * jOf X = jOf X * centralProj t :=
    fun X => centralProj_comm (hB _ (hJB _ (hjOf X).1)) t
  -- the transported corner as a non-unital ring homomorphism
  let ψ : Matrix (Fin d) (Fin d) ℂ →ₙ+* Matrix (Fin 7) (Fin 7) ℂ :=
    { toFun := fun X => centralProj t * jOf X
      map_mul' := fun X Y => by
        show centralProj t * jOf (X * Y) = centralProj t * jOf X * (centralProj t * jOf Y)
        rw [hjOf_mul]
        calc centralProj t * (jOf X * jOf Y)
            = centralProj t * (centralProj t * jOf X) * jOf Y := by
              rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, centralProj_mul_self]
          _ = centralProj t * (jOf X * centralProj t) * jOf Y := by rw [hcomm X]
          _ = centralProj t * jOf X * (centralProj t * jOf Y) := by
              simp only [Matrix.mul_assoc]
      map_zero' := by
        show centralProj t * jOf 0 = 0
        rw [hjOf_zero, Matrix.mul_zero]
      map_add' := fun X Y => by
        show centralProj t * jOf (X + Y) = centralProj t * jOf X + centralProj t * jOf Y
        rw [hjOf_add, Matrix.mul_add] }
  have hψ : ∀ X, ψ X = centralProj t * jOf X := fun X => rfl
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top (TwoSidedIdeal.ker ψ) with hk | hk
  · -- injective: excluded by dimension
    exfalso
    have hinjψ : Function.Injective ψ := (TwoSidedIdeal.ker_eq_bot ψ).mp hk
    let P : Finset (Fin 7 × Fin 7) :=
      Finset.univ.filter fun p : Fin 7 × Fin 7 => blockOf p.1 = t ∧ blockOf p.2 = t
    let ψL : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] supportedOn P :=
      { toFun := fun X => ⟨ψ X, centralProj_mul_mem_supportedOn (hB _ (hJB _ (hjOf X).1)) t⟩
        map_add' := fun X Y => by apply Subtype.ext; simp [hψ, hjOf_add, Matrix.mul_add]
        map_smul' := fun c X => by apply Subtype.ext; simp [hψ, hjOf_smul, Matrix.mul_smul] }
    have hinjL : Function.Injective ψL := by
      intro X Y hXY
      apply hinjψ
      have := congrArg (fun z : supportedOn P => (z : Matrix (Fin 7) (Fin 7) ℂ)) hXY
      simpa [ψL] using this
    have := LinearMap.finrank_le_finrank_of_injective hinjL
    rw [Module.finrank_matrix, Fintype.card_fin, finrank_supportedOn, Module.finrank_self,
      mul_one] at this
    exact absurd this (not_le.mpr hdim)
  · intro j hj
    have hjeq : j = jOf (j.submatrix ι ι) := huniq _ hj _ (hjOf _).1 (hjOf _).2.symm
    have hmem : j.submatrix ι ι ∈ TwoSidedIdeal.ker ψ := by rw [hk]; exact TwoSidedIdeal.mem_top _
    rw [TwoSidedIdeal.mem_ker, hψ] at hmem
    rw [hjeq]
    exact hmem

omit hB in
/-- **Targets whose unit lies in `B` are killed.**  If the central projector `P_t`
(`t ≠ s`) already belongs to `B`, the `t`-corner vanishes on the source ideal of
block `s` (ideal property plus injectivity of the `s`-corner). -/
theorem sourceIdeal_kills_of_unit_mem {s : Fin 4}
    (J : Submodule ℂ (Matrix (Fin 7) (Fin 7) ℂ))
    (hJideal : ∀ j ∈ J, ∀ a ∈ B, a * j ∈ J ∧ j * a ∈ J)
    (hJinj : ∀ j ∈ J, centralProj s * j = 0 → j = 0)
    {t : Fin 4} (hts : t ≠ s) (hPt : centralProj t ∈ B) :
    ∀ j ∈ J, centralProj t * j = 0 := by
  intro j hj
  apply hJinj _ (hJideal j hj _ hPt).1
  rw [← Matrix.mul_assoc, centralProj_mul_centralProj_of_ne (Ne.symm hts), Matrix.zero_mul]

end SourceIdeal

/-! ### The colour and weak blocks land in `B` -/

/-- Enumeration of the colour block `{0,1,2}`. -/
def ι0 : Fin 3 → Fin 7 := ![0, 1, 2]

/-- Enumeration of the weak block `{3,4}`. -/
def ι1 : Fin 2 → Fin 7 := ![3, 4]

theorem ι0_spec : ∀ i, blockOf i = 0 ↔ ∃ a, ι0 a = i := by decide

theorem ι1_spec : ∀ i, blockOf i = 1 ↔ ∃ a, ι1 a = i := by decide

theorem ι0_injective : Function.Injective ι0 := by decide

theorem ι1_injective : Function.Injective ι1 := by decide

/-- Number of matrix entries of each block: `9, 4, 1, 1`. -/
theorem card_blockPairs :
    ∀ t : Fin 4, (Finset.univ.filter fun p : Fin 7 × Fin 7 =>
      blockOf p.1 = t ∧ blockOf p.2 = t).card = ![9, 4, 1, 1] t := by
  decide

section Blocks

variable (B : StarSubalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ)) (hB : ∀ b ∈ B, b ∈ blockAlgebra)

include hB

/-- **`M₃ ⊕ 0 ⊆ B`**: every block-diagonal matrix supported on the colour block
belongs to `B` once the colour corner of `B` is onto `M₃(ℂ)`. -/
theorem colour_block_mem
    (hsurj0 : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, ∃ b ∈ B, b.submatrix ι0 ι0 = X) :
    ∀ Y ∈ blockAlgebra, centralProj 0 * Y = Y → Y ∈ B := by
  obtain ⟨J, hJB, hJideal, hJinj, hJsurj⟩ := exists_sourceIdeal B hB ι0 ι0_spec hsurj0
  refine block_le_of_kills B hB ι0 ι0_spec J hJB hJinj hJsurj ?_
  intro j hj t ht
  refine sourceIdeal_kills_small B hB ι0 ι0_injective ι0_spec J hJB hJideal hJinj hJsurj t ?_ j hj
  rw [card_blockPairs]
  fin_cases t
  · exact absurd rfl ht
  · decide
  · decide
  · decide

/-- **`0 ⊕ M₂ ⊕ 0 ⊆ B`**: every block-diagonal matrix supported on the weak block
belongs to `B` once both nonabelian corners of `B` are onto. -/
theorem weak_block_mem
    (hsurj0 : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, ∃ b ∈ B, b.submatrix ι0 ι0 = X)
    (hsurj1 : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, ∃ b ∈ B, b.submatrix ι1 ι1 = X) :
    ∀ Y ∈ blockAlgebra, centralProj 1 * Y = Y → Y ∈ B := by
  have hP0 : centralProj 0 ∈ B :=
    colour_block_mem B hB hsurj0 _ (centralProj_mem_blockAlgebra 0) (centralProj_mul_self 0)
  obtain ⟨J, hJB, hJideal, hJinj, hJsurj⟩ := exists_sourceIdeal B hB ι1 ι1_spec hsurj1
  refine block_le_of_kills B hB ι1 ι1_spec J hJB hJinj hJsurj ?_
  intro j hj t ht
  fin_cases t
  · exact sourceIdeal_kills_of_unit_mem B J hJideal hJinj ht hP0 j hj
  · exact absurd rfl ht
  · exact sourceIdeal_kills_small B hB ι1 ι1_injective ι1_spec J hJB hJideal hJinj hJsurj 2
      (by rw [card_blockPairs]; decide) j hj
  · exact sourceIdeal_kills_small B hB ι1 ι1_injective ι1_spec J hJB hJideal hJinj hJsurj 3
      (by rw [card_blockPairs]; decide) j hj

end Blocks

/-! ### The scalar-locked algebra and the dichotomy -/

/-- The scalar decomposition `X = P₀X + P₁X + X₅₅E₅₅ + X₆₆E₆₆` of a block-diagonal
matrix. -/
theorem scalar_decomp {X : Matrix (Fin 7) (Fin 7) ℂ} (hX : X ∈ blockAlgebra) :
    X = centralProj 0 * X + centralProj 1 * X + X 5 5 • Matrix.single 5 5 1 +
      X 6 6 • Matrix.single 6 6 1 := by
  have hX' : ∀ i j, blockOf i ≠ blockOf j → X i j = 0 := hX
  ext i j
  simp only [Matrix.add_apply, centralProj_mul_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  fin_cases i <;> fin_cases j <;> simp +decide (disch := decide) [hX']

/-- `E₅₅ + E₆₆ = 1 - P₀ - P₁`. -/
theorem single_add_single_eq :
    Matrix.single (5 : Fin 7) 5 (1 : ℂ) + Matrix.single 6 6 1 = 1 - centralProj 0 - centralProj 1 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply, centralProj,
    Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp +decide

theorem blockOf_ne_of_ne_five : ∀ m : Fin 7, m ≠ 5 → blockOf m ≠ blockOf 5 := by decide

theorem blockOf_ne_of_ne_six : ∀ m : Fin 7, m ≠ 6 → blockOf m ≠ blockOf 6 := by decide

/-- The scalar-locked algebra `{(A, B, z, z)} ⊆ M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ`
(`eq:central-locked-14`). -/
def lockedAlgebra : Subalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ) where
  carrier := {X | X ∈ blockAlgebra ∧ X 5 5 = X 6 6}
  zero_mem' := ⟨blockAlgebra.zero_mem, rfl⟩
  one_mem' := ⟨blockAlgebra.one_mem, by simp⟩
  add_mem' := fun {X Y} hX hY =>
    ⟨blockAlgebra.add_mem hX.1 hY.1, by simp [Matrix.add_apply, hX.2, hY.2]⟩
  mul_mem' := fun {X Y} hX hY => by
    refine ⟨blockAlgebra.mul_mem hX.1 hY.1, ?_⟩
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single 5, Finset.sum_eq_single 6,
      hX.2, hY.2]
    · intro m _ hm; rw [hX.1 6 m (Ne.symm (blockOf_ne_of_ne_six m hm)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro m _ hm; rw [hX.1 5 m (Ne.symm (blockOf_ne_of_ne_five m hm)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  algebraMap_mem' := fun c =>
    ⟨blockAlgebra.algebraMap_mem c, by simp [Matrix.algebraMap_matrix_apply]⟩

theorem mem_lockedAlgebra {X : Matrix (Fin 7) (Fin 7) ℂ} :
    X ∈ lockedAlgebra ↔ X ∈ blockAlgebra ∧ X 5 5 = X 6 6 := Iff.rfl

theorem lockedAlgebra_le : lockedAlgebra ≤ blockAlgebra := fun _ hX => hX.1

theorem single_five_mem_blockAlgebra : Matrix.single (5 : Fin 7) 5 (1 : ℂ) ∈ blockAlgebra :=
  InternalAssembly.single_mem_blockAlgebra rfl 1

theorem single_five_not_mem_lockedAlgebra : Matrix.single (5 : Fin 7) 5 (1 : ℂ) ∉ lockedAlgebra := by
  intro h
  have := h.2
  simp at this

theorem blockAlgebra_ne_lockedAlgebra : blockAlgebra ≠ lockedAlgebra := fun h =>
  single_five_not_mem_lockedAlgebra (h ▸ single_five_mem_blockAlgebra)

section Dichotomy

variable (B : StarSubalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ)) (hB : ∀ b ∈ B, b ∈ blockAlgebra)

include hB

/-- **`thm:central-separation`, dichotomy.**  A unital `*`-subalgebra of
`M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` whose colour and weak corners are onto is either the full
block algebra or the scalar-locked algebra, and not both. -/
theorem central_separation_dichotomy
    (hsurj0 : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, ∃ b ∈ B, b.submatrix ι0 ι0 = X)
    (hsurj1 : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, ∃ b ∈ B, b.submatrix ι1 ι1 = X) :
    Xor (B.toSubalgebra = blockAlgebra) (B.toSubalgebra = lockedAlgebra) := by
  have hP0X : ∀ X ∈ blockAlgebra, centralProj 0 * X ∈ B := fun X hX =>
    colour_block_mem B hB hsurj0 _ (blockAlgebra.mul_mem (centralProj_mem_blockAlgebra 0) hX)
      (by rw [← Matrix.mul_assoc, centralProj_mul_self])
  have hP1X : ∀ X ∈ blockAlgebra, centralProj 1 * X ∈ B := fun X hX =>
    weak_block_mem B hB hsurj0 hsurj1 _
      (blockAlgebra.mul_mem (centralProj_mem_blockAlgebra 1) hX)
      (by rw [← Matrix.mul_assoc, centralProj_mul_self])
  have hP0 : centralProj 0 ∈ B := by simpa using hP0X 1 blockAlgebra.one_mem
  have hP1 : centralProj 1 ∈ B := by simpa using hP1X 1 blockAlgebra.one_mem
  have hE : Matrix.single (5 : Fin 7) 5 (1 : ℂ) + Matrix.single 6 6 1 ∈ B := by
    rw [single_add_single_eq]
    exact B.sub_mem (B.sub_mem B.one_mem hP0) hP1
  by_cases hlock : ∀ b ∈ B, b 5 5 = b 6 6
  · right
    refine ⟨?_, ?_⟩
    · ext X
      rw [StarSubalgebra.mem_toSubalgebra, mem_lockedAlgebra]
      constructor
      · intro hX; exact ⟨hB X hX, hlock X hX⟩
      · rintro ⟨hXb, hX56⟩
        have hdec := scalar_decomp hXb
        rw [hX56, add_assoc, ← smul_add] at hdec
        rw [hdec]
        exact B.add_mem (B.add_mem (hP0X X hXb) (hP1X X hXb)) (B.smul_mem hE _)
    · intro h
      have hmem : Matrix.single (5 : Fin 7) 5 (1 : ℂ) ∈ B := by
        rw [← StarSubalgebra.mem_toSubalgebra, h]; exact single_five_mem_blockAlgebra
      have := hlock _ hmem
      simp at this
  · left
    push_neg at hlock
    obtain ⟨b, hb, hb56⟩ := hlock
    have hE55 : Matrix.single (5 : Fin 7) 5 (1 : ℂ) ∈ B := by
      have h1 : b - centralProj 0 * b - centralProj 1 * b -
          b 6 6 • (Matrix.single 5 5 1 + Matrix.single 6 6 1) ∈ B :=
        B.sub_mem (B.sub_mem (B.sub_mem hb (hP0X b (hB b hb))) (hP1X b (hB b hb))) (B.smul_mem hE _)
      have h2 : b - centralProj 0 * b - centralProj 1 * b -
          b 6 6 • (Matrix.single 5 5 1 + Matrix.single 6 6 1) =
          (b 5 5 - b 6 6) • Matrix.single 5 5 1 := by
        have hdec := scalar_decomp (hB b hb)
        nth_rewrite 1 [hdec]
        simp only [smul_add, sub_smul]
        abel
      rw [h2] at h1
      have := B.smul_mem h1 (b 5 5 - b 6 6)⁻¹
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hb56), one_smul] at this
    have hE66 : Matrix.single (6 : Fin 7) 6 (1 : ℂ) ∈ B := by
      have := B.sub_mem hE hE55
      rwa [add_sub_cancel_left] at this
    refine ⟨?_, ?_⟩
    · apply le_antisymm
      · intro X hX; exact hB X hX
      · intro X hX
        rw [StarSubalgebra.mem_toSubalgebra]
        rw [scalar_decomp hX]
        exact B.add_mem (B.add_mem (B.add_mem (hP0X X hX) (hP1X X hX)) (B.smul_mem hE55 _))
          (B.smul_mem hE66 _)
    · intro h
      have hmem : Matrix.single (5 : Fin 7) 5 (1 : ℂ) ∈ lockedAlgebra := by
        rw [← h, StarSubalgebra.mem_toSubalgebra]; exact hE55
      exact single_five_not_mem_lockedAlgebra hmem

end Dichotomy

/-! ### Dimensions `15` and `14` -/

/-- The same-block index pairs (15 of them). -/
def blockPairs : Finset (Fin 7 × Fin 7) :=
  Finset.univ.filter fun p => blockOf p.1 = blockOf p.2

theorem blockPairs_card : blockPairs.card = 15 := by decide

theorem toSubmodule_blockAlgebra : Subalgebra.toSubmodule blockAlgebra = supportedOn blockPairs := by
  ext X
  rw [Subalgebra.mem_toSubmodule, mem_supportedOn]
  change (∀ i j, blockOf i ≠ blockOf j → X i j = 0) ↔ _
  simp [blockPairs, Finset.mem_filter]

/-- `dim_ℂ (M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ) = 15` (`eq:central-separated-15`). -/
theorem finrank_blockAlgebra : Module.finrank ℂ blockAlgebra = 15 := by
  rw [← Subalgebra.finrank_toSubmodule, toSubmodule_blockAlgebra, finrank_supportedOn,
    blockPairs_card]

/-- The same-block pairs without `(6,6)` (14 of them). -/
def lockedPairs : Finset (Fin 7 × Fin 7) := blockPairs.erase (6, 6)

theorem lockedPairs_card : lockedPairs.card = 14 := by decide

theorem mem_lockedPairs {p : Fin 7 × Fin 7} :
    p ∈ lockedPairs ↔ p ≠ (6, 6) ∧ blockOf p.1 = blockOf p.2 := by
  simp [lockedPairs, blockPairs, Finset.mem_erase, Finset.mem_filter]

theorem single_six_apply_of_ne {i j : Fin 7} (h : blockOf i ≠ blockOf j) :
    Matrix.single (6 : Fin 7) 6 (1 : ℂ) i j = 0 := by
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h rfl

/-- The scalar-locked algebra is linearly `supportedOn lockedPairs`
(drop the redundant `(6,6)` coordinate). -/
def lockedEquiv : lockedAlgebra ≃ₗ[ℂ] supportedOn lockedPairs where
  toFun X := ⟨X.1 - X.1 6 6 • Matrix.single 6 6 1, by
    intro i j hij
    rw [mem_lockedPairs, not_and_or, not_not] at hij
    rcases hij with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
      simp
    · rw [Matrix.sub_apply, X.2.1 i j h, Matrix.smul_apply, single_six_apply_of_ne h, smul_zero,
        sub_zero]⟩
  map_add' X Y := by
    apply Subtype.ext; ext i j; simp [Matrix.single_apply]; split_ifs <;> ring
  map_smul' c X := by
    apply Subtype.ext; ext i j; simp [Matrix.single_apply]; split_ifs <;> ring
  invFun Y := ⟨Y.1 + Y.1 5 5 • Matrix.single 6 6 1, by
    refine ⟨?_, ?_⟩
    · intro i j hij
      rw [Matrix.add_apply, Y.2 i j (fun hm => (mem_lockedPairs.mp hm).2 |> hij),
        Matrix.smul_apply, single_six_apply_of_ne hij, smul_zero, add_zero]
    · have h66 : Y.1 6 6 = 0 := Y.2 6 6 (fun hm => (mem_lockedPairs.mp hm).1 rfl)
      simp [h66]⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    have h56 := X.2.2
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply,
      smul_eq_mul]
    by_cases hi : i = 6 <;> by_cases hj : j = 6 <;> simp [hi, hj, h56]
  right_inv Y := by
    apply Subtype.ext
    ext i j
    have h66 : Y.1 6 6 = 0 := Y.2 6 6 (fun hm => (mem_lockedPairs.mp hm).1 rfl)
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply,
      smul_eq_mul]
    by_cases hi : i = 6 <;> by_cases hj : j = 6 <;> simp [hi, hj, h66]

/-- `dim_ℂ {(A, B, z, z)} = 14` (`eq:central-locked-14`). -/
theorem finrank_lockedAlgebra : Module.finrank ℂ lockedAlgebra = 14 := by
  rw [lockedEquiv.finrank_eq, finrank_supportedOn, lockedPairs_card]

/-! ### The separation margin `η_cen` -/

/-- The block algebra as a `*`-subalgebra. -/
def blockStarAlgebra : StarSubalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ) :=
  { blockAlgebra with
    star_mem' := fun {X} hX i j hij => by
      rw [Matrix.star_apply, hX j i (Ne.symm hij), star_zero] }

theorem mem_blockStarAlgebra {X : Matrix (Fin 7) (Fin 7) ℂ} :
    X ∈ blockStarAlgebra ↔ X ∈ blockAlgebra := Iff.rfl

/-- The scalar-locked algebra as a `*`-subalgebra. -/
def lockedStarAlgebra : StarSubalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ) :=
  { lockedAlgebra with
    star_mem' := fun {X} hX =>
      ⟨blockStarAlgebra.star_mem' hX.1, by simp [Matrix.star_apply, hX.2]⟩ }

theorem mem_lockedStarAlgebra {X : Matrix (Fin 7) (Fin 7) ℂ} :
    X ∈ lockedStarAlgebra ↔ X ∈ lockedAlgebra := Iff.rfl

/-- The central separation margin `η_cen = ∑_j |χ₁(b_j) - χ₂(b_j)|²` of a bank,
with the scalar characters `χ₁ = (·) 5 5`, `χ₂ = (·) 6 6`. -/
noncomputable def etaCen {ι : Type*} [Fintype ι] (b : ι → Matrix (Fin 7) (Fin 7) ℂ) : ℝ :=
  ∑ j, Complex.normSq (b j 5 5 - b j 6 6)

theorem etaCen_nonneg {ι : Type*} [Fintype ι] (b : ι → Matrix (Fin 7) (Fin 7) ℂ) :
    0 ≤ etaCen b :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem etaCen_pos_iff {ι : Type*} [Fintype ι] (b : ι → Matrix (Fin 7) (Fin 7) ℂ) :
    0 < etaCen b ↔ ∃ j, b j 5 5 ≠ b j 6 6 := by
  constructor
  · intro h
    by_contra hall
    push_neg at hall
    have : etaCen b = 0 := Finset.sum_eq_zero fun j _ => by simp [hall j]
    rw [this] at h
    exact lt_irrefl _ h
  · rintro ⟨j, hj⟩
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg _)
      (Finset.mem_univ j))
    exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hj)

/-- **`thm:central-separation`, margin form** (`eq:central-separation-margin`).
For a bank `b` of block-diagonal generators whose generated `*`-algebra has onto
colour and weak corners, the generated algebra is the full product
`M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` iff `η_cen > 0`. -/
theorem central_separation_criterion {ι : Type*} [Fintype ι]
    (b : ι → Matrix (Fin 7) (Fin 7) ℂ) (hb : ∀ j, b j ∈ blockAlgebra)
    (hsurj0 : ∀ X : Matrix (Fin 3) (Fin 3) ℂ,
      ∃ y ∈ StarAlgebra.adjoin ℂ (Set.range b), y.submatrix ι0 ι0 = X)
    (hsurj1 : ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
      ∃ y ∈ StarAlgebra.adjoin ℂ (Set.range b), y.submatrix ι1 ι1 = X) :
    (StarAlgebra.adjoin ℂ (Set.range b)).toSubalgebra = blockAlgebra ↔ 0 < etaCen b := by
  set B := StarAlgebra.adjoin ℂ (Set.range b) with hBdef
  have hB : ∀ x ∈ B, x ∈ blockAlgebra := fun x hx =>
    StarAlgebra.adjoin_le (S := blockStarAlgebra)
      (by rintro _ ⟨j, rfl⟩; exact hb j) hx
  have hdich := central_separation_dichotomy B hB hsurj0 hsurj1
  rw [etaCen_pos_iff]
  constructor
  · intro hfull
    by_contra hall
    push_neg at hall
    have hle : B ≤ lockedStarAlgebra :=
      StarAlgebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact ⟨hb j, hall j⟩)
    have hmem : Matrix.single (5 : Fin 7) 5 (1 : ℂ) ∈ B := by
      rw [← StarSubalgebra.mem_toSubalgebra, hfull]; exact single_five_mem_blockAlgebra
    exact single_five_not_mem_lockedAlgebra (hle hmem)
  · rintro ⟨j, hj⟩
    rcases hdich with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exfalso
      have hmem : b j ∈ lockedAlgebra := by
        rw [← h, StarSubalgebra.mem_toSubalgebra]
        exact StarAlgebra.subset_adjoin ℂ _ ⟨j, rfl⟩
      exact hj hmem.2

/-- A represented scalar central projector `E₅₅` (or `E₆₆`) in the bank discharges
`η_cen > 0` automatically. -/
theorem etaCen_pos_of_central_projector {ι : Type*} [Fintype ι]
    (b : ι → Matrix (Fin 7) (Fin 7) ℂ) (j : ι)
    (hj : b j = Matrix.single 5 5 1 ∨ b j = Matrix.single 6 6 1) :
    0 < etaCen b := by
  rw [etaCen_pos_iff]
  refine ⟨j, ?_⟩
  rcases hj with h | h <;> rw [h] <;> simp

/-- **`thm:central-separation`, assembled.**  Exactly one of the two alternatives
occurs, with the stated dimensions `15` and `14`. -/
theorem central_separation (B : StarSubalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ))
    (hB : ∀ b ∈ B, b ∈ blockAlgebra)
    (hsurj0 : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, ∃ b ∈ B, b.submatrix ι0 ι0 = X)
    (hsurj1 : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, ∃ b ∈ B, b.submatrix ι1 ι1 = X) :
    Xor (B.toSubalgebra = blockAlgebra ∧ Module.finrank ℂ B = 15)
      (B.toSubalgebra = lockedAlgebra ∧ Module.finrank ℂ B = 14) := by
  have hfin : ∀ S : Subalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ), B.toSubalgebra = S →
      Module.finrank ℂ B = Module.finrank ℂ S := by
    intro S hS
    subst hS
    rfl
  rcases central_separation_dichotomy B hB hsurj0 hsurj1 with ⟨h, hn⟩ | ⟨h, hn⟩
  · exact Or.inl ⟨⟨h, (hfin _ h).trans finrank_blockAlgebra⟩, fun hc => hn hc.1⟩
  · exact Or.inr ⟨⟨h, (hfin _ h).trans finrank_lockedAlgebra⟩, fun hc => hn hc.1⟩

end CentralSeparation
end RenewalGeometry
