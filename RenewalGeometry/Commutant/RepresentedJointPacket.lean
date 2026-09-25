/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.SupportPolarActionAlgebra
import RenewalGeometry.Commutant.JointTypedActionAlgebra

/-!
# Finite source-complete joint packets, represented

Covers `def:joint-packet` of the spacetime–gauge duality paper.

A `RepresentedJointPacket` is the represented data (J1)–(J5) of a finite source-complete
spacetime–gauge packet, written in the coordinates of its central type decomposition:

* the type index `Λ`, the internal type carriers `V_λ` and the multiplicity carriers `M_λ`,
  so that the common finite Hilbert carrier is `ℋ = ⊕_λ ℂ⁴ ⊗ V_λ ⊗ M_λ`
  (`Carrier`, the sigma type `Σ λ, (Fin 4 × V λ) × M λ`);
* (J1) the reconstructed external Clifford factor `𝒜_ext ≅ M_4(ℂ)` acting as
  `⊕_λ a ⊗ I ⊗ I` (`extAction`; faithful by `extAction_injective`, a `*`-representation by
  `extAction_mul`, `extAction_one`, `extAction_conjTranspose`);
* (J2)/(J3) the commuting typed internal algebra
  `𝒜_int = ⊕_λ I_4 ⊗ B(V_λ) ⊗ I_{M_λ}` (`intAction`, `intAlgebra`;
  `extAction_commute_intAction`);
* (J4) a finite directed incidence graph `Γ = (Λ, E)` with source and target maps and
  represented incidence histories `Y_e : ℂ⁴ ⊗ V_{s(e)} ⊗ M_{s(e)} → ℂ⁴ ⊗ V_{t(e)} ⊗ M_{t(e)}`
  (`src`, `tgt`, `Y`), placed on the common carrier by `incidenceOp`;
* (J5) the mixed history words: the products and adjoints of all of the above on the one
  common carrier, i.e. the joint typed action algebra
  `𝒜_act = C^*(𝒜_ext, 𝒜_int, Y_e, Y_e^*)` (`actionAlgebra`, via `jointActionAlgebra` of
  `def:action-algebra`).

No inverse incidence map is part of the data.  The paper's carrier is only required to be
unitarily equivalent to the displayed sum; the structure fixes those coordinates.
-/

open Matrix
open scoped Kronecker

namespace RenewalGeometry

set_option linter.unusedSectionVars false

/-- **Finite source-complete joint packet (`def:joint-packet`)**: the represented data
(J1)–(J5) in the coordinates of the central type decomposition
`ℋ = ⊕_{λ ∈ Λ} ℂ⁴ ⊗ V_λ ⊗ M_λ`.  The fields are the directed incidence graph `(Λ, E, src, tgt)`
and the represented incidence histories `Y_e`; the external and internal algebras are
determined by the decomposition (`extAction`, `intAction`). -/
structure RepresentedJointPacket (Λ : Type*) [Fintype Λ] [DecidableEq Λ]
    (V M : Λ → Type*) [∀ l, Fintype (V l)] [∀ l, DecidableEq (V l)]
    [∀ l, Fintype (M l)] [∀ l, DecidableEq (M l)] (E : Type*) [Fintype E] where
  /-- source vertex `s(e)` of an incidence edge -/
  src : E → Λ
  /-- target vertex `t(e)` of an incidence edge -/
  tgt : E → Λ
  /-- the represented incidence history
  `Y_e : ℂ⁴ ⊗ V_{s(e)} ⊗ M_{s(e)} → ℂ⁴ ⊗ V_{t(e)} ⊗ M_{t(e)}` -/
  Y : ∀ e, Matrix ((Fin 4 × V (tgt e)) × M (tgt e)) ((Fin 4 × V (src e)) × M (src e)) ℂ

namespace RepresentedJointPacket

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {V M : Λ → Type*} [∀ l, Fintype (V l)] [∀ l, DecidableEq (V l)]
  [∀ l, Fintype (M l)] [∀ l, DecidableEq (M l)] {E : Type*} [Fintype E]

/-- The sector carrier `ℂ⁴ ⊗ V_λ ⊗ M_λ`. -/
abbrev SectorCarrier (V M : Λ → Type*) (l : Λ) : Type _ := (Fin 4 × V l) × M l

/-- The common finite Hilbert carrier `ℋ = ⊕_λ ℂ⁴ ⊗ V_λ ⊗ M_λ`. -/
abbrev Carrier (V M : Λ → Type*) : Type _ := Σ l : Λ, SectorCarrier V M l

variable (V M) in
/-- (J1) The external Clifford factor `a ∈ M_4(ℂ)` acting as `⊕_λ a ⊗ I_{V_λ} ⊗ I_{M_λ}`. -/
def extAction (a : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Carrier V M) (Carrier V M) ℂ :=
  blockDiagonal' fun l => (a ⊗ₖ (1 : Matrix (V l) (V l) ℂ)) ⊗ₖ (1 : Matrix (M l) (M l) ℂ)

variable (V M) in
/-- (J2)/(J3) The internal element `(b_λ)_λ` acting as `⊕_λ I_4 ⊗ b_λ ⊗ I_{M_λ}`. -/
def intAction (b : ∀ l, Matrix (V l) (V l) ℂ) : Matrix (Carrier V M) (Carrier V M) ℂ :=
  blockDiagonal' fun l => ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ b l) ⊗ₖ (1 : Matrix (M l) (M l) ℂ)

variable (V M) in
/-- The represented external Clifford algebra `𝒜_ext = {⊕_λ a ⊗ I ⊗ I : a ∈ M_4(ℂ)}`. -/
def extAlgebra : Set (Matrix (Carrier V M) (Carrier V M) ℂ) :=
  Set.range (extAction V M)

variable (V M) in
/-- (J3) The typed internal algebra `𝒜_int = ⊕_λ I_4 ⊗ B(V_λ) ⊗ I_{M_λ}`. -/
def intAlgebra : Set (Matrix (Carrier V M) (Carrier V M) ℂ) :=
  Set.range (intAction V M)

theorem mem_intAlgebra_iff (X : Matrix (Carrier V M) (Carrier V M) ℂ) :
    X ∈ intAlgebra V M ↔ ∃ b : ∀ l, Matrix (V l) (V l) ℂ,
      X = blockDiagonal' fun l =>
        ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ b l) ⊗ₖ (1 : Matrix (M l) (M l) ℂ) :=
  ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

/-- `extAction` is multiplicative. -/
theorem extAction_mul (a a' : Matrix (Fin 4) (Fin 4) ℂ) :
    extAction V M (a * a') = extAction V M a * extAction V M a' := by
  unfold extAction
  rw [← blockDiagonal'_mul]
  congr 1
  funext l
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]

/-- `extAction` is unital. -/
theorem extAction_one : extAction V M 1 = 1 := by
  unfold extAction
  rw [← blockDiagonal'_one]
  congr 1
  funext l
  rw [Matrix.one_kronecker_one, Matrix.one_kronecker_one]
  rfl

/-- `extAction` is star-preserving. -/
theorem extAction_conjTranspose (a : Matrix (Fin 4) (Fin 4) ℂ) :
    (extAction V M a)ᴴ = extAction V M aᴴ := by
  unfold extAction
  rw [blockDiagonal'_conjTranspose]
  congr 1
  funext l
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.conjTranspose_one]

/-- `intAction` is multiplicative. -/
theorem intAction_mul (b b' : ∀ l, Matrix (V l) (V l) ℂ) :
    intAction V M (b * b') = intAction V M b * intAction V M b' := by
  unfold intAction
  rw [← blockDiagonal'_mul]
  congr 1
  funext l
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  rfl

/-- `intAction` is unital. -/
theorem intAction_one : intAction V M 1 = 1 := by
  unfold intAction
  rw [← blockDiagonal'_one]
  congr 1
  funext l
  rw [Pi.one_apply, Matrix.one_kronecker_one, Matrix.one_kronecker_one]
  rfl

/-- `intAction` is star-preserving. -/
theorem intAction_conjTranspose (b : ∀ l, Matrix (V l) (V l) ℂ) :
    (intAction V M b)ᴴ = intAction V M (star b) := by
  unfold intAction
  rw [blockDiagonal'_conjTranspose]
  congr 1
  funext l
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.conjTranspose_one]
  rfl

/-- (J1) Faithfulness: the external factor acts faithfully as soon as some sector is
nonempty. -/
theorem extAction_injective (h : ∃ l, Nonempty (V l) ∧ Nonempty (M l)) :
    Function.Injective (extAction V M) := by
  obtain ⟨l, ⟨v⟩, ⟨m⟩⟩ := h
  intro a a' haa'
  ext i j
  have := congrFun (congrFun haa' ⟨l, ((i, v), m)⟩) ⟨l, ((j, v), m)⟩
  simp only [extAction, blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
    mul_one] at this
  exact this

/-- (J2) The external and internal actions commute. -/
theorem extAction_commute_intAction (a : Matrix (Fin 4) (Fin 4) ℂ)
    (b : ∀ l, Matrix (V l) (V l) ℂ) :
    extAction V M a * intAction V M b = intAction V M b * extAction V M a := by
  unfold extAction intAction
  rw [← blockDiagonal'_mul, ← blockDiagonal'_mul]
  congr 1
  funext l
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]

/-- The external and internal algebras commute elementwise. -/
theorem extAlgebra_commute_intAlgebra :
    ∀ x ∈ extAlgebra V M, ∀ y ∈ intAlgebra V M, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact extAction_commute_intAction a b

variable (P : RepresentedJointPacket Λ V M E)

/-- (J4) The incidence history `Y_e` placed on the `(t(e), s(e))` corner of the common
carrier (extended by zero). -/
def incidenceOp (e : E) : Matrix (Carrier V M) (Carrier V M) ℂ :=
  GraphLoadedEdgeCommutant.blockEmbed (SectorCarrier V M) (P.Y e)

/-- (J5) The mixed history words: the joint typed action algebra
`𝒜_act = C^*(𝒜_ext, 𝒜_int, Y_e, Y_e^* : e ∈ E)` on the common carrier
(`def:action-algebra`). -/
def actionAlgebra : Subalgebra ℂ (Matrix (Carrier V M) (Carrier V M) ℂ) :=
  jointActionAlgebra (extAlgebra V M) (intAlgebra V M) P.incidenceOp

theorem extAlgebra_subset_actionAlgebra : extAlgebra V M ⊆ P.actionAlgebra :=
  ext_subset_jointActionAlgebra _ _ _

theorem intAlgebra_subset_actionAlgebra : intAlgebra V M ⊆ P.actionAlgebra :=
  int_subset_jointActionAlgebra _ _ _

theorem incidenceOp_mem_actionAlgebra (e : E) : P.incidenceOp e ∈ P.actionAlgebra :=
  incidence_mem_jointActionAlgebra _ _ _ e

theorem incidenceOp_conjTranspose_mem_actionAlgebra (e : E) :
    (P.incidenceOp e)ᴴ ∈ P.actionAlgebra :=
  incidence_conjTranspose_mem_jointActionAlgebra _ _ _ e

theorem actionAlgebra_starClosed : ∀ a ∈ P.actionAlgebra, aᴴ ∈ P.actionAlgebra :=
  jointActionAlgebra_starClosed _ _ _

/-- The residual multiplicity algebra `𝓜_type = 𝒜_act'` of the packet. -/
def multiplicityAlgebra : Set (Matrix (Carrier V M) (Carrier V M) ℂ) :=
  matCommutant (P.actionAlgebra : Set (Matrix (Carrier V M) (Carrier V M) ℂ))

end RepresentedJointPacket

end RenewalGeometry
