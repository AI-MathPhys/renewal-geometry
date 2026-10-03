/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.FiniteEinsteinStandardModelInterface
import RenewalGeometry.StandardModel.SMDescentYukawaBlocksExact

/-!
# The finite Einstein–Standard-Model interface with the tabulated fermion packet
  (`def:finite-interface`, item (I2), `tab:SM-representations`;
  Einstein–Standard-Model action-closure manuscript)

`RenewalGeometry.StandardModel.FiniteEinsteinStandardModelInterface` encodes (I1)–(I5) with an
*arbitrary* one-generation fermion representation and chirality involution.  Item (I2) of
`def:finite-interface` requires "the chiral fermion representations of
`tab:SM-representations`".  This file ties the fermion carrier to the table rows defined in
`RenewalGeometry.StandardModel.SMDescentYukawaBlocksExact`:

| row | rep | chirality |
|---|---|---|
| `Q_L` | `repQL` = `U₃ ⊗ U₂` | left (`+1`) |
| `L_L` | `repLL` = `(det U₂)⁻¹ U₂` | left (`+1`) |
| `u_R` | `repUR` = `det U₂ · U₃` | right (`-1`) |
| `d_R` | `repDR` = `U₃` | right (`-1`) |
| `e_R` | `repER` = `(det U₂)⁻¹` | right (`-1`) |
| `ν_R` (declared neutrino branch only) | `repNR` = `1` | right (`-1`) |

* `NeutrinoBranch` — the declared branch (`minimal` or `neutrino`, the optional `ν_R` row).
* `TableRow b = (Q_L ⊕ L_L) ⊕ RightRow b` — the one-generation row index of the table, with
  `RightRow minimal = (u_R ⊕ d_R) ⊕ e_R` and `RightRow neutrino = ((u_R ⊕ d_R) ⊕ e_R) ⊕ ν_R`.
* `tableRep b` — the block-diagonal sum of the table rows (`blockSumHom`), a monoid hom
  `G_SM →* M_{15}(ℂ)` (resp. `M_{16}(ℂ)`); `tableChirality b = diag(+1_left, -1_right)` read off
  the chirality column.
* `TabulatedFiniteInterface h` — a `FiniteInterface h` together with the declared branch, a
  linear equivalence `OneGeneration ≃ₗ[ℂ] (TableRow b → ℂ)` **intertwining** `fermionRep` with
  `tableRep b` and `chirality` with `tableChirality b`, and an identification of the declared
  neutral blocks with the neutral rows of the branch.
* Derived consequences: the fermion representation and chirality are *determined* by the
  table (`fermionRep_eq_table`, `chirality_eq_table`); `finrank OneGeneration = 15` on the
  minimal and `16` on the neutrino branch (`finrank_oneGeneration_minimal`,
  `finrank_oneGeneration_neutrino`); a fermion is left-handed (`chirality v = v`) iff its
  `u_R, d_R, e_R[, ν_R]` components vanish (`chirality_eq_self_iff`).
* `TabulatedFiniteInterface.ofTable` — constructor from the remaining (I1), (I3)–(I5) data, with
  the fermion carrier, representation, chirality and the involution/equivariance fields *derived*
  from the table (`tableChirality_mul_self`, `tableChirality_commute`); a concrete non-vacuity
  instance with nontrivial `G_SM` action is `trivialGeometryInterface`.

Rendering still disclosed (unchanged from the parent file): relabeling covariance and the smooth
comparison cylinder/reconstruction map are not encoded; the realified Majorana doubling of the
`ν_R` block concerns the bilinear, not the representation rows, and is not part of this record.
-/

open Matrix

namespace RenewalGeometry

namespace FiniteInterfaceTable

open SMDescentYukawa

/-! ### Block sums of matrix representations -/

/-- The block-diagonal sum `y ↦ diag(ρ₁ y, ρ₂ y)` of two matrix representations of `G_SM`. -/
noncomputable def blockSumHom {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ρ₁ : SMGaugeGroup →* Matrix m m ℂ) (ρ₂ : SMGaugeGroup →* Matrix n n ℂ) :
    SMGaugeGroup →* Matrix (m ⊕ n) (m ⊕ n) ℂ where
  toFun y := fromBlocks (ρ₁ y) 0 0 (ρ₂ y)
  map_one' := by simp [fromBlocks_one]
  map_mul' x y := by simp [fromBlocks_multiply]

@[simp] theorem blockSumHom_apply {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (ρ₁ : SMGaugeGroup →* Matrix m m ℂ) (ρ₂ : SMGaugeGroup →* Matrix n n ℂ)
    (y : SMGaugeGroup) : blockSumHom ρ₁ ρ₂ y = fromBlocks (ρ₁ y) 0 0 (ρ₂ y) := rfl

/-! ### The rows of `tab:SM-representations` -/

/-- The declared branch: the minimal packet, or the declared neutrino extension with `ν_R`. -/
inductive NeutrinoBranch
  | minimal
  | neutrino
  deriving DecidableEq

/-- Left-handed rows of one generation: `Q_L ⊕ L_L` (dimension `6 + 2`). -/
abbrev LeftRow : Type := (Fin 3 × Fin 2) ⊕ Fin 2

/-- Right-handed rows of the minimal packet: `(u_R ⊕ d_R) ⊕ e_R` (dimension `3 + 3 + 1`). -/
abbrev RightRowMin : Type := (Fin 3 ⊕ Fin 3) ⊕ Unit

/-- Right-handed rows on the neutrino branch: `((u_R ⊕ d_R) ⊕ e_R) ⊕ ν_R`. -/
abbrev RightRowExt : Type := RightRowMin ⊕ Unit

/-- Right-handed rows of the declared branch. -/
def RightRow : NeutrinoBranch → Type
  | .minimal => RightRowMin
  | .neutrino => RightRowExt

instance RightRow.instFintype : (b : NeutrinoBranch) → Fintype (RightRow b)
  | .minimal => inferInstanceAs (Fintype RightRowMin)
  | .neutrino => inferInstanceAs (Fintype RightRowExt)

instance RightRow.instDecidableEq : (b : NeutrinoBranch) → DecidableEq (RightRow b)
  | .minimal => inferInstanceAs (DecidableEq RightRowMin)
  | .neutrino => inferInstanceAs (DecidableEq RightRowExt)

/-- The one-generation row index of `tab:SM-representations` on the declared branch. -/
abbrev TableRow (b : NeutrinoBranch) : Type := LeftRow ⊕ RightRow b

/-- The neutral rows declared on the branch (`ν_R` on the neutrino branch, none otherwise). -/
def neutralRows : NeutrinoBranch → Type
  | .minimal => Empty
  | .neutrino => Unit

instance neutralRows.instFintype : (b : NeutrinoBranch) → Fintype (neutralRows b)
  | .minimal => inferInstanceAs (Fintype Empty)
  | .neutrino => inferInstanceAs (Fintype Unit)

/-- `G_SM` on the left-handed rows: `repQL ⊕ repLL`. -/
noncomputable def repLeft : SMGaugeGroup →* Matrix LeftRow LeftRow ℂ := blockSumHom repQL repLL

/-- `G_SM` on the minimal right-handed rows: `(repUR ⊕ repDR) ⊕ repER`. -/
noncomputable def repRightMin : SMGaugeGroup →* Matrix RightRowMin RightRowMin ℂ :=
  blockSumHom (blockSumHom repUR repDR) repER

/-- `G_SM` on the right-handed rows of the branch (`repNR` added on the neutrino branch). -/
noncomputable def repRight : (b : NeutrinoBranch) → SMGaugeGroup →* Matrix (RightRow b) (RightRow b) ℂ
  | .minimal => repRightMin
  | .neutrino => blockSumHom repRightMin repNR

/-- **The table representation** of one generation on the declared branch. -/
noncomputable def tableRep (b : NeutrinoBranch) : SMGaugeGroup →* Matrix (TableRow b) (TableRow b) ℂ :=
  blockSumHom repLeft (repRight b)

/-- **The table chirality**: `+1` on the left-handed rows `Q_L, L_L`, `-1` on the right-handed
rows `u_R, d_R, e_R` (and `ν_R`), as in the chirality column of `tab:SM-representations`. -/
def tableChirality (b : NeutrinoBranch) : Matrix (TableRow b) (TableRow b) ℂ :=
  fromBlocks 1 0 0 (-1)

/-- The table representation as a linear representation on `ℂ^{TableRow b}`. -/
noncomputable def tableRepresentation (b : NeutrinoBranch) :
    Representation ℂ SMGaugeGroup (TableRow b → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (TableRow b) (TableRow b) ℂ ≃ₐ[ℂ] _).toAlgHom.toMonoidHom.comp
    (tableRep b)

theorem tableRepresentation_apply (b : NeutrinoBranch) (g : SMGaugeGroup) (w : TableRow b → ℂ) :
    tableRepresentation b g w = tableRep b g *ᵥ w := rfl

/-- The table chirality is an involution. -/
theorem tableChirality_mul_self (b : NeutrinoBranch) :
    tableChirality b * tableChirality b = 1 := by
  unfold tableChirality
  rw [fromBlocks_multiply]
  simp [fromBlocks_one]

/-- The table chirality commutes with the table representation (each row is homogeneous in
chirality). -/
theorem tableChirality_commute (b : NeutrinoBranch) (g : SMGaugeGroup) :
    tableChirality b * tableRep b g = tableRep b g * tableChirality b := by
  unfold tableChirality tableRep
  rw [blockSumHom_apply, fromBlocks_multiply, fromBlocks_multiply]
  simp

/-- `tableChirality *ᵥ w` keeps the left rows and negates the right rows. -/
theorem tableChirality_mulVec (b : NeutrinoBranch) (w : TableRow b → ℂ) :
    tableChirality b *ᵥ w = Sum.elim (fun i => w (Sum.inl i)) (fun r => -w (Sum.inr r)) := by
  have hw : w = Sum.elim (fun i => w (Sum.inl i)) (fun r => w (Sum.inr r)) := by
    funext x; cases x <;> rfl
  unfold tableChirality
  rw [hw, fromBlocks_mulVec]
  funext x
  cases x <;> simp [Matrix.neg_mulVec]

theorem card_tableRow_minimal : Fintype.card (TableRow .minimal) = 15 := rfl

theorem card_tableRow_neutrino : Fintype.card (TableRow .neutrino) = 16 := rfl

end FiniteInterfaceTable

open FiniteInterfaceTable

/-! ### The interface with the tabulated fermion packet -/

/-- **`def:finite-interface` with (I2) tied to `tab:SM-representations`.**  A finite
Einstein–Standard-Model interface whose one-generation fermion representation is the table
packet of the declared branch: a linear equivalence of the carrier with `ℂ^{TableRow b}`
intertwines `fermionRep` with the table rows `repQL, repLL, repUR, repDR, repER (, repNR)` and
`chirality` with the table chirality column, and the declared neutral blocks are the neutral
rows of the branch. -/
structure TabulatedFiniteInterface (h : ℝ) extends FiniteInterface h where
  /-- (I2) the declared branch (minimal packet or neutrino extension) -/
  branch : NeutrinoBranch
  /-- (I2) identification of one generation with the table rows -/
  tableEquiv : OneGeneration ≃ₗ[ℂ] (TableRow branch → ℂ)
  /-- (I2) the fermion representation is the table representation -/
  tableEquiv_fermionRep : ∀ g v, tableEquiv (fermionRep g v) = tableRep branch g *ᵥ tableEquiv v
  /-- (I2) the chirality is the table chirality -/
  tableEquiv_chirality : ∀ v, tableEquiv (chirality v) = tableChirality branch *ᵥ tableEquiv v
  /-- (I2) the declared neutral blocks are the neutral rows of the branch -/
  neutralEquiv : NeutralBlock ≃ neutralRows branch

namespace TabulatedFiniteInterface

variable {h : ℝ} (I : TabulatedFiniteInterface h)

/-- The fermion representation is determined by the table:
`fermionRep g = Φ⁻¹ ∘ tableRep g ∘ Φ`. -/
theorem fermionRep_eq_table (g : SMGaugeGroup) :
    I.fermionRep g = I.tableEquiv.symm.toLinearMap ∘ₗ Matrix.toLin' (tableRep I.branch g) ∘ₗ
      I.tableEquiv.toLinearMap := by
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply]
  rw [← I.tableEquiv_fermionRep, LinearEquiv.symm_apply_apply]

/-- The chirality is determined by the table: `chirality = Φ⁻¹ ∘ tableChirality ∘ Φ`. -/
theorem chirality_eq_table :
    I.chirality = I.tableEquiv.symm.toLinearMap ∘ₗ Matrix.toLin' (tableChirality I.branch) ∘ₗ
      I.tableEquiv.toLinearMap := by
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply]
  rw [← I.tableEquiv_chirality, LinearEquiv.symm_apply_apply]

/-- A fermion of one generation is left-handed (`chirality v = v`) iff its components on the
right-handed rows `u_R, d_R, e_R` (and `ν_R`) vanish. -/
theorem chirality_eq_self_iff (v : I.OneGeneration) :
    I.chirality v = v ↔ ∀ r : RightRow I.branch, I.tableEquiv v (Sum.inr r) = 0 := by
  constructor
  · intro hv r
    have h1 := I.tableEquiv_chirality v
    rw [hv, tableChirality_mulVec] at h1
    have := congrFun h1 (Sum.inr r)
    simp only [Sum.elim_inr] at this
    have h2 : (2 : ℂ) * I.tableEquiv v (Sum.inr r) = 0 := by linear_combination this
    simpa using h2
  · intro hr
    apply I.tableEquiv.injective
    rw [I.tableEquiv_chirality, tableChirality_mulVec]
    funext x
    cases x with
    | inl i => rfl
    | inr r => simp [hr r]

/-- On the minimal branch one generation has complex dimension `15`. -/
theorem finrank_oneGeneration_minimal (hb : I.branch = .minimal) :
    Module.finrank ℂ I.OneGeneration = 15 := by
  rw [I.tableEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, hb, card_tableRow_minimal]

/-- On the neutrino branch one generation has complex dimension `16`. -/
theorem finrank_oneGeneration_neutrino (hb : I.branch = .neutrino) :
    Module.finrank ℂ I.OneGeneration = 16 := by
  rw [I.tableEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, hb, card_tableRow_neutrino]

/-- **Constructor from the paper's input data.**  Given the declared branch and the (I1), (I3),
(I4), (I5) data on the table carrier `ℂ^{TableRow b}` (with covariance against the table
representation), the fermion representation, the chirality, the neutral blocks and the
involution/equivariance fields of (I2) are produced from `tab:SM-representations`. -/
noncomputable def ofTable (h : ℝ) (b : NeutrinoBranch)
    (Site : Type) [Fintype Site]
    (Config : Type) [NormedAddCommGroup Config] [InnerProductSpace ℝ Config]
    [FiniteDimensional ℝ Config]
    (coframe : Config → Site → Matrix (Fin 4) (Fin 4) ℝ)
    (coframe_oriented : ∀ q x, 0 < (coframe q x).det)
    (coframe_timeOriented : ∀ q x, 0 < coframe q x 0 0)
    (higgs : Config → Site → (Fin 2 → ℂ))
    (YukawaSector : Type) [Fintype YukawaSector]
    (coefficients : CoefficientBank YukawaSector)
    (dirac : Config → ((Site → Fin 3 → TableRow b → ℂ) →ₗ[ℂ] (Site → Fin 3 → TableRow b → ℂ)))
    (gaugeAct : (Site → SMGaugeGroup) → Config → Config)
    (higgs_covariant : ∀ γ q x, higgs (gaugeAct γ q) x = higgsRep (γ x) (higgs q x))
    (dirac_covariant : ∀ γ q (ψ : Site → Fin 3 → TableRow b → ℂ) x n,
      dirac (gaugeAct γ q) (fun y m => tableRep b (γ y) *ᵥ ψ y m) x n
        = tableRep b (γ x) *ᵥ dirac q ψ x n)
    (gravityAction matterAction : Config → ℝ) (ν : ℝ) (hν : 0 < ν)
    (action_differentiable : Differentiable ℝ (fun q => gravityAction q + ν * matterAction q))
    (action_gauge_invariant : ∀ γ q,
      gravityAction (gaugeAct γ q) + ν * matterAction (gaugeAct γ q)
        = gravityAction q + ν * matterAction q)
    (retained : Submodule ℝ Config) (gram : Config →ₗ[ℝ] Config)
    (gram_symmetric : ∀ u v, inner ℝ (gram u) v = inner ℝ u (gram v))
    (gram_nonneg : ∀ v, 0 ≤ inner ℝ v (gram v))
    (gram_pos_retained : ∀ v ∈ retained, v ≠ 0 → 0 < inner ℝ v (gram v)) :
    TabulatedFiniteInterface h where
  Site := Site
  Config := Config
  coframe := coframe
  coframe_oriented := coframe_oriented
  coframe_timeOriented := coframe_timeOriented
  OneGeneration := TableRow b → ℂ
  fermionRep := tableRepresentation b
  chirality := Matrix.toLin' (tableChirality b)
  chirality_involutive := by
    rw [← Matrix.toLin'_mul, tableChirality_mul_self, Matrix.toLin'_one]
  chirality_equivariant g := by
    show Matrix.toLin' (tableChirality b) ∘ₗ Matrix.toLin' (tableRep b g)
      = Matrix.toLin' (tableRep b g) ∘ₗ Matrix.toLin' (tableChirality b)
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, tableChirality_commute]
  NeutralBlock := neutralRows b
  higgs := higgs
  YukawaSector := YukawaSector
  coefficients := coefficients
  dirac := dirac
  gaugeAct := gaugeAct
  higgs_covariant := higgs_covariant
  dirac_covariant := dirac_covariant
  gravityAction := gravityAction
  matterAction := matterAction
  relativeNormalization := ν
  relativeNormalization_pos := hν
  action_differentiable := action_differentiable
  action_gauge_invariant := action_gauge_invariant
  retained := retained
  gram := gram
  gram_symmetric := gram_symmetric
  gram_nonneg := gram_nonneg
  gram_pos_retained := gram_pos_retained
  branch := b
  tableEquiv := LinearEquiv.refl ℂ _
  tableEquiv_fermionRep _ _ := rfl
  tableEquiv_chirality _ := rfl
  neutralEquiv := Equiv.refl _

/-- **Non-vacuity**: a concrete tabulated interface on one site with the flat coframe, trivial
Dirac operator and Gram `= id` on `𝒬_h = ℝ`; its fermion carrier is the full table packet of the
declared branch with the nontrivial `G_SM` action of `tab:SM-representations`. -/
noncomputable def trivialGeometryInterface (h : ℝ) (b : NeutrinoBranch) :
    TabulatedFiniteInterface h :=
  ofTable h b Unit ℝ (fun _ _ => 1) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ => 0) Unit
    ⟨0, 0, 0, 0, 0, 0, 0, fun _ => 0⟩
    (fun _ => 0) (fun _ q => q)
    (fun _ _ _ => by simp)
    (fun _ _ _ _ _ => by simp)
    (fun _ => 0) (fun _ => 0) 1 one_pos
    (by simpa using (differentiable_const (0 : ℝ)))
    (fun _ _ => rfl)
    ⊤ LinearMap.id
    (fun _ _ => rfl)
    (fun v => by rw [LinearMap.id_apply]; exact real_inner_self_nonneg)
    (fun v _ hv => by
      rw [LinearMap.id_apply, real_inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.mpr hv) 2)

example : Module.finrank ℂ (trivialGeometryInterface 1 .neutrino).OneGeneration = 16 :=
  (trivialGeometryInterface 1 .neutrino).finrank_oneGeneration_neutrino rfl

/-- The `G_SM` action on the tabulated carrier is nontrivial: the image of the cover element
`(1, 1, e^{iπ/6})` acts on the `e_R` row by `(det U₂)⁻¹ = -1`. -/
example : ∃ g : SMGaugeGroup, tableRep .minimal g ≠ 1 := by
  set z : Circle := Circle.exp (Real.pi / 6) with hzdef
  have hz : (z : ℂ) ^ 6 = -1 := by
    rw [hzdef, Circle.coe_exp, ← Complex.exp_nat_mul,
      show ((6 : ℕ) : ℂ) * (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I by
        push_cast; ring]
    exact Complex.exp_pi_mul_I
  refine ⟨smGaugeHom ((1, 1), z), fun hg => ?_⟩
  have hchi := SMDescentYukawa.smChi_smGaugeHom ((1, 1), z)
  have h2 : (tableRep .minimal (smGaugeHom ((1, 1), z))) (Sum.inr (Sum.inr ()))
      (Sum.inr (Sum.inr ())) = SMDescentYukawa.smChi (smGaugeHom ((1, 1), z)) ^ (-1 : ℤ) * 1 := rfl
  rw [hg, hchi, hz] at h2
  norm_num at h2

end TabulatedFiniteInterface

end RenewalGeometry
