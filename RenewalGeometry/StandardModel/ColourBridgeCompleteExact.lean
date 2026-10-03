/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.BridgeRouterResidualsExact
import RenewalGeometry.StandardModel.CentralSeparationExact
import RenewalGeometry.Commutant.JointTypedActionAlgebra
import RenewalGeometry.StandardModel.InternalSeedSaturationWords

/-!
# Colour bridge, weak router, and central separation: the complete statement
  (`thm:colour-bridge`)

* **Colour** (`eq:colour-M3` and zero bridge), on `T ⊕ H_priv = ℂ ⊕ ℂ²`:
  `colour_bridge_M3_iff` (`C^*(ℂp_T ⊕ M₂(H_priv), u) = M₃ ⟺ ω_col(u) > 0`) and
  `colour_bridge_zero` (at `ω_col(u) = 0` the algebra is **exactly** `ℂ ⊕ M₂`, the block
  algebra `InternalSeed.blockDiag`, of dimension `5`, `finrank_blockDiag`).
* **Weak router** (`eq:weak-M2`), for unit vectors `t, h` of the multiplicity plane `ℂ²`:
  `weak_M2_iff` : `0 < |⟨t,h⟩| < 1 ⟺ C^*(p_t, p_h) = M₂(ℂ)`; the reverse direction uses
  that orthogonal or equal projections commute (`proj_mul_proj_comm_of_overlap_zero`,
  `adjoin_ne_top_of_commute`).
* **Single projection**: `single_projection` — a rank-one projection `p` of `ℂ²`
  generates `span{1, p}`, isomorphic as a unital algebra to `ℂ × ℂ` via
  `x ↦ (tr(xp), tr(x(1−p)))`, of dimension `2`, and not `M₂(ℂ)`.
* **Central separation** (`eq:central-locked-14`): `subdirect_dichotomy` — a unital
  subalgebra (no `*`-closedness assumed) of `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` surjecting onto the colour and
  weak factors (scalar surjectivity is automatic) is the full `15`-dimensional product or the
  `14`-dimensional scalar-locked algebra, and not both.  Proof: if no nonzero colour-only
  element existed, `ker(1 − P₀) ≤ ker P₀` on `B` would force `9 ≤ 6` by rank–nullity
  (`colour_block_mem_of_surj`); a nonzero colour-only element and surjectivity generate all
  colour matrix units (`block_mem_of_supported`); likewise for the weak block with `4 ≤ 2`
  (`weak_block_mem_of_surj`).  The margin criterion `eq:central-separation-margin`
  (`η_cen > 0` iff full product, for a generating bank) is
  `CentralSeparation.central_separation_criterion`; independent scalar central supports
  suffice (`CentralSeparation.etaCen_pos_of_central_projector`).

`colour_bridge` assembles the proposition.
-/

open Matrix Module

namespace RenewalGeometry
namespace ColourBridgeComplete

open BridgeRouter

/-! ### Colour: `M₃` iff `ω_col > 0`, exactly `ℂ ⊕ M₂` at zero bridge -/

/-- The reducing block algebra `ℂ ⊕ M₂` on `T ⊕ H_priv` has dimension `5`. -/
theorem finrank_blockDiag : finrank ℂ InternalSeed.blockDiag = 5 := by
  have h : Subalgebra.toSubmodule InternalSeed.blockDiag =
      CentralSeparation.supportedOn (Finset.univ.filter fun p : Fin 3 × Fin 3 =>
        (p.1 = 0 ↔ p.2 = 0)) := by
    ext X
    rw [Subalgebra.mem_toSubmodule, CentralSeparation.mem_supportedOn]
    constructor
    · rintro ⟨h01, h02, h10, h20⟩ i j hij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro h
      refine ⟨h 0 1 (by simp), h 0 2 (by simp), h 1 0 (by simp), h 2 0 (by simp)⟩
  rw [← Subalgebra.finrank_toSubmodule, h, CentralSeparation.finrank_supportedOn]
  decide

/-- **`eq:colour-M3`.** -/
theorem colour_bridge_M3_iff (u : Matrix (Fin 3) (Fin 3) ℂ) :
    Algebra.adjoin ℂ (InternalSeed.gens u) = ⊤ ↔ 0 < colourResidual u :=
  adjoin_eq_top_iff_colourResidual_pos u

/-- **Zero bridge**: at `ω_col(u) = 0` the generated algebra is exactly `ℂ ⊕ M₂`. -/
theorem colour_bridge_zero (u : Matrix (Fin 3) (Fin 3) ℂ) (h : colourResidual u = 0) :
    Algebra.adjoin ℂ (InternalSeed.gens u) = InternalSeed.blockDiag ∧
      finrank ℂ (Algebra.adjoin ℂ (InternalSeed.gens u)) = 5 := by
  have he := (adjoin_eq_blockDiag_iff_colourResidual_zero u).mpr h
  refine ⟨he, ?_⟩
  rw [he, finrank_blockDiag]

/-! ### Weak router: `0 < |⟨t,h⟩| < 1` iff `C^*(p_t, p_h) = M₂` -/

theorem proj_conjTranspose (v : Fin 2 → ℂ) : (proj v)ᴴ = proj v := by
  rw [proj, conjTranspose_vecMulVec, star_star]

/-- Two self-adjoint generators: `C^*(p, q) = alg(p, q)`. -/
theorem starAdjoin_proj_pair (t h : Fin 2 → ℂ) :
    starAdjoin ({proj t, proj h} : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
      Algebra.adjoin ℂ {proj t, proj h} := by
  rw [starAdjoin_eq_adjoin]
  congr 1
  apply Set.union_eq_left.mpr
  intro x hx
  rw [Set.mem_star] at hx
  rcases hx with hx | hx
  · rw [← star_star x, hx, star_eq_conjTranspose, proj_conjTranspose]; exact Or.inl rfl
  · rw [Set.mem_singleton_iff] at hx
    rw [← star_star x, hx, star_eq_conjTranspose, proj_conjTranspose]; exact Or.inr rfl

/-- A commuting pair generates a commutative algebra, which is not `M₂`. -/
theorem adjoin_ne_top_of_commute {p q : Matrix (Fin 2) (Fin 2) ℂ} (hpq : p * q = q * p) :
    Algebra.adjoin ℂ {p, q} ≠ ⊤ := by
  intro htop
  have hgen : ∀ a ∈ ({p, q} : Set (Matrix (Fin 2) (Fin 2) ℂ)),
      ∀ b ∈ ({p, q} : Set (Matrix (Fin 2) (Fin 2) ℂ)), Commute a b := by
    rintro a (rfl | rfl) b (rfl | rfl)
    · exact Commute.refl _
    · exact hpq
    · exact hpq.symm
    · exact Commute.refl _
  have hcomm : ∀ x ∈ Algebra.adjoin ℂ {p, q}, ∀ y ∈ Algebra.adjoin ℂ {p, q}, x * y = y * x := by
    intro x hx y hy
    have hgy : ∀ g ∈ ({p, q} : Set (Matrix (Fin 2) (Fin 2) ℂ)), Commute g y := fun g hg =>
      Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy (hgen g hg)
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun g hg => (hgy g hg).symm).symm
  have h := hcomm (Matrix.single 0 1 1) (htop ▸ Algebra.mem_top) (Matrix.single 1 0 1)
    (htop ▸ Algebra.mem_top)
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two] at h00

/-- Orthogonal carriers multiply to zero in both orders. -/
theorem proj_mul_proj_comm_of_overlap_zero (t h : Fin 2 → ℂ) (h0 : overlap t h = 0) :
    proj t * proj h = proj h * proj t := by
  have h0' : (∑ m, star (h m) * t m) = 0 := by
    have : (∑ m, star (h m) * t m) = star (overlap t h) := by
      rw [overlap, star_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [star_mul, star_star]
    rw [this, h0, star_zero]
  rw [proj, proj, WeakReset.vecMulVec_mul, WeakReset.vecMulVec_mul]
  rw [show (∑ m, star (t m) * h m) = overlap t h from rfl, h0, h0', zero_smul, zero_smul]

/-- **`eq:weak-M2`**: for unit vectors `t, h` of the standard multiplicity plane,
`0 < |⟨t,h⟩| < 1` iff the two rank-one projections generate `M₂(ℂ)` as a `C^*`-algebra. -/
theorem weak_M2_iff (t h : Fin 2 → ℂ) (ht : normSqVec t = 1) (hh : normSqVec h = 1) :
    (0 < ‖overlap t h‖ ∧ ‖overlap t h‖ < 1) ↔
      starAdjoin ({proj t, proj h} : Set (Matrix (Fin 2) (Fin 2) ℂ)) = ⊤ := by
  rw [starAdjoin_proj_pair]
  constructor
  · rintro ⟨hpos, hlt⟩
    have hov : overlap t h ≠ 0 := norm_pos_iff.mp hpos
    have hns : Complex.normSq (overlap t h) < 1 := by
      rw [Complex.normSq_eq_norm_sq]
      have := norm_nonneg (overlap t h)
      nlinarith
    have hd : t 0 * h 1 - t 1 * h 0 ≠ 0 := by
      intro hd
      have := lagrange_identity t h
      rw [hd, ht, hh, Complex.normSq_zero, zero_add, mul_one] at this
      linarith
    exact WeakReset.two_lines_generate t h hd hov
  · intro htop
    refine ⟨?_, ?_⟩
    · rw [norm_pos_iff]
      intro h0
      exact adjoin_ne_top_of_commute (proj_mul_proj_comm_of_overlap_zero t h h0) htop
    · by_contra hge
      push_neg at hge
      have hle : Complex.normSq (overlap t h) ≤ 1 := normSq_overlap_le_one t h ht hh
      have h1 : Complex.normSq (overlap t h) = 1 := by
        rw [Complex.normSq_eq_norm_sq] at hle ⊢
        nlinarith [norm_nonneg (overlap t h)]
      have heq := (proj_eq_iff t h ht hh).mpr h1
      apply adjoin_ne_top_of_commute (p := proj t) (q := proj h) (by rw [heq]) htop

/-! ### A single rank-one projection generates `ℂ²` -/

section Single

variable {t : Fin 2 → ℂ} (ht : normSqVec t = 1)
include ht

theorem proj_mul_self : proj t * proj t = proj t := by
  rw [proj, WeakReset.vecMulVec_mul]
  have h1 := sum_mul_star_eq_one ht
  have h2 : (∑ m, star (t m) * t m) = 1 := by
    rw [← h1]; exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  rw [h2, one_smul]

theorem trace_proj : (proj t).trace = 1 := by
  rw [proj, trace_vecMulVec]
  exact sum_mul_star_eq_one ht

theorem pair_mul (a b c d : ℂ) :
    (a • 1 + b • proj t) * (c • 1 + d • proj t) = (a * c) • 1 + (a * d + b * c + b * d) • proj t := by
  have hp := proj_mul_self ht
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hp, smul_smul, smul_smul,
    smul_smul, smul_smul, add_smul, add_smul]
  rw [mul_comm b c]
  abel

theorem pair_mul_proj (a b : ℂ) : (a • 1 + b • proj t) * proj t = (a + b) • proj t := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, proj_mul_self ht,
    add_smul]

theorem pair_mul_compl (a b : ℂ) : (a • 1 + b • proj t) * (1 - proj t) = a • (1 - proj t) := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.mul_one, proj_mul_self ht, sub_self, smul_zero, add_zero]

theorem trace_compl : (1 - proj t).trace = 1 := by
  rw [trace_sub, trace_one, trace_proj ht, Fintype.card_fin]; norm_num

/-- The two characters `x ↦ (tr(xp), tr(x(1 − p)))`. -/
noncomputable def chi (x : Matrix (Fin 2) (Fin 2) ℂ) : ℂ × ℂ :=
  ((x * proj t).trace, (x * (1 - proj t)).trace)

theorem chi_pair (a b : ℂ) : chi (t := t) (a • 1 + b • proj t) = (a + b, a) := by
  rw [chi, pair_mul_proj ht, pair_mul_compl ht, trace_smul, trace_smul, trace_proj ht,
    trace_compl ht, smul_eq_mul, smul_eq_mul, mul_one, mul_one]

/-- The algebra `{a + b p}` spanned by `1` and the idempotent `p`. -/
def pairAlg : Subalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {x | ∃ a b : ℂ, a • 1 + b • proj t = x}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by rw [add_smul, add_smul]; abel⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨_, _, (pair_mul ht a b c d).symm⟩
  algebraMap_mem' c := ⟨c, 0, by rw [zero_smul, add_zero, Algebra.algebraMap_eq_smul_one]⟩

omit ht in
theorem pairAlg_eq_adjoin (ht : normSqVec t = 1) :
    pairAlg ht = Algebra.adjoin ℂ {proj t} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, rfl⟩ := hx
    exact add_mem (Subalgebra.smul_mem (Algebra.adjoin ℂ {proj t})
      (Subalgebra.one_mem (Algebra.adjoin ℂ {proj t})) a)
      (Subalgebra.smul_mem (Algebra.adjoin ℂ {proj t})
        (Algebra.subset_adjoin (Set.mem_singleton (proj t))) b)
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨0, 1, by simp⟩

/-- The two characters on the generated algebra, as a unital algebra map to `ℂ × ℂ`. -/
noncomputable def pairChar : pairAlg ht →ₐ[ℂ] ℂ × ℂ where
  toFun x := chi (t := t) x.1
  map_one' := by
    have h := chi_pair ht 1 0
    rw [zero_smul, add_zero, one_smul, add_zero] at h
    exact h
  map_mul' := by
    rintro ⟨_, a, b, rfl⟩ ⟨_, c, d, rfl⟩
    show chi ((a • 1 + b • proj t) * (c • 1 + d • proj t)) =
      chi (a • 1 + b • proj t) * chi (c • 1 + d • proj t)
    rw [pair_mul ht, chi_pair ht, chi_pair ht, chi_pair ht, Prod.mk_mul_mk]
    congr 1; ring
  map_zero' := by
    show chi 0 = 0
    simp [chi]
  map_add' := by
    rintro x y
    show chi (x.1 + y.1) = chi x.1 + chi y.1
    simp [chi, Matrix.add_mul, trace_add]
  commutes' c := by
    show chi (algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) c) = algebraMap ℂ (ℂ × ℂ) c
    have h := chi_pair ht c 0
    rw [zero_smul, add_zero, add_zero] at h
    rw [Algebra.algebraMap_eq_smul_one, h]
    ext <;> simp

/-- **A single rank-one projection generates only `ℂ²`**: the algebra generated by `p_t`
is `span{1, p_t}`, isomorphic as a unital algebra to `ℂ × ℂ` via the two characters
`x ↦ (tr(x p_t), tr(x(1 − p_t)))`, of dimension `2`, and it is not `M₂(ℂ)`. -/
theorem single_projection :
    Nonempty (Algebra.adjoin ℂ {proj t} ≃ₐ[ℂ] ℂ × ℂ) ∧
      finrank ℂ (Algebra.adjoin ℂ {proj t}) = 2 ∧ Algebra.adjoin ℂ {proj t} ≠ ⊤ := by
  have hinj : Function.Injective (pairChar ht) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨_, a, b, rfl⟩ hx
    have hx' : chi (t := t) (a • 1 + b • proj t) = 0 := hx
    rw [chi_pair ht, Prod.mk_eq_zero] at hx'
    obtain ⟨h1, h2⟩ := hx'
    subst h2
    rw [zero_add] at h1
    subst h1
    apply Subtype.ext
    simp
  have hsurj : Function.Surjective (pairChar ht) := by
    rintro ⟨α, β⟩
    refine ⟨⟨β • 1 + (α - β) • proj t, β, α - β, rfl⟩, ?_⟩
    show chi (β • 1 + (α - β) • proj t) = (α, β)
    rw [chi_pair ht]
    congr 1; ring
  let φ : pairAlg ht ≃ₐ[ℂ] ℂ × ℂ := AlgEquiv.ofBijective (pairChar ht) ⟨hinj, hsurj⟩
  let ψ : Algebra.adjoin ℂ {proj t} ≃ₐ[ℂ] ℂ × ℂ :=
    (Subalgebra.equivOfEq _ _ (pairAlg_eq_adjoin ht).symm).trans φ
  have hfin : finrank ℂ (Algebra.adjoin ℂ {proj t}) = 2 := by
    rw [ψ.toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_self]
  refine ⟨⟨ψ⟩, hfin, fun htop => ?_⟩
  rw [htop, Subalgebra.topEquiv.toLinearEquiv.finrank_eq, Module.finrank_matrix] at hfin
  simp at hfin

end Single

/-! ### Assembly -/

/-- **`thm:colour-bridge`** (spacetime–gauge duality paper). -/
theorem colour_bridge :
    -- `eq:colour-M3`
    (∀ u : Matrix (Fin 3) (Fin 3) ℂ,
      Algebra.adjoin ℂ (InternalSeed.gens u) = ⊤ ↔ 0 < colourResidual u) ∧
    -- zero bridge: exactly `ℂ ⊕ M₂`
    (∀ u : Matrix (Fin 3) (Fin 3) ℂ, colourResidual u = 0 →
      Algebra.adjoin ℂ (InternalSeed.gens u) = InternalSeed.blockDiag ∧
        finrank ℂ (Algebra.adjoin ℂ (InternalSeed.gens u)) = 5) ∧
    -- `eq:weak-M2`
    (∀ t h : Fin 2 → ℂ, normSqVec t = 1 → normSqVec h = 1 →
      ((0 < ‖overlap t h‖ ∧ ‖overlap t h‖ < 1) ↔
        starAdjoin ({proj t, proj h} : Set (Matrix (Fin 2) (Fin 2) ℂ)) = ⊤)) ∧
    -- a single rank-one projection generates only `ℂ²`
    (∀ t : Fin 2 → ℂ, normSqVec t = 1 →
      Nonempty (Algebra.adjoin ℂ {proj t} ≃ₐ[ℂ] ℂ × ℂ) ∧
        finrank ℂ (Algebra.adjoin ℂ {proj t}) = 2) ∧
    -- central separation: the `15 / 14` dichotomy
    (∀ B : StarSubalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ),
      (∀ b ∈ B, b ∈ InternalAssembly.blockAlgebra) →
      (∀ X : Matrix (Fin 3) (Fin 3) ℂ, ∃ b ∈ B, b.submatrix CentralSeparation.ι0
        CentralSeparation.ι0 = X) →
      (∀ X : Matrix (Fin 2) (Fin 2) ℂ, ∃ b ∈ B, b.submatrix CentralSeparation.ι1
        CentralSeparation.ι1 = X) →
      Xor (B.toSubalgebra = InternalAssembly.blockAlgebra ∧ finrank ℂ B = 15)
        (B.toSubalgebra = CentralSeparation.lockedAlgebra ∧ finrank ℂ B = 14)) ∧
    -- `eq:central-separation-margin`
    (∀ {ι : Type} [Fintype ι] (b : ι → Matrix (Fin 7) (Fin 7) ℂ),
      (∀ j, b j ∈ InternalAssembly.blockAlgebra) →
      (∀ X : Matrix (Fin 3) (Fin 3) ℂ,
        ∃ y ∈ StarAlgebra.adjoin ℂ (Set.range b), y.submatrix CentralSeparation.ι0
          CentralSeparation.ι0 = X) →
      (∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        ∃ y ∈ StarAlgebra.adjoin ℂ (Set.range b), y.submatrix CentralSeparation.ι1
          CentralSeparation.ι1 = X) →
      ((StarAlgebra.adjoin ℂ (Set.range b)).toSubalgebra = InternalAssembly.blockAlgebra ↔
        0 < CentralSeparation.etaCen b)) ∧
    -- independent represented scalar central supports suffice
    (∀ {ι : Type} [Fintype ι] (b : ι → Matrix (Fin 7) (Fin 7) ℂ) (j : ι),
      (b j = Matrix.single 5 5 1 ∨ b j = Matrix.single 6 6 1) →
      0 < CentralSeparation.etaCen b) :=
  ⟨colour_bridge_M3_iff, colour_bridge_zero, weak_M2_iff,
    fun t ht => ⟨(single_projection ht).1, (single_projection ht).2.1⟩,
    CentralSeparation.central_separation,
    fun b hb h0 h1 => CentralSeparation.central_separation_criterion b hb h0 h1,
    fun b j hj => CentralSeparation.etaCen_pos_of_central_projector b j hj⟩

/-! ### Subdirect dichotomy for unital (not necessarily `*`-closed) subalgebras -/

section Subdirect

open InternalAssembly (blockOf blockAlgebra)
open CentralSeparation (centralProj centralProj_mul_apply mul_centralProj_apply
  centralProj_mul_self centralProj_comm supportedOn mem_supportedOn finrank_supportedOn)

/-- Rank–nullity comparison: `ker g ≤ ker f` forces `rank f ≤ rank g`. -/
theorem finrank_range_le_of_ker_le {V W W' : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (f : V →ₗ[ℂ] W) (g : V →ₗ[ℂ] W') (h : LinearMap.ker g ≤ LinearMap.ker f) :
    finrank ℂ (LinearMap.range f) ≤ finrank ℂ (LinearMap.range g) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  have h3 := Submodule.finrank_mono h
  omega

variable {B : Subalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ)}

/-- Left multiplication by `P`, restricted to `B`. -/
def leftMul (B : Subalgebra ℂ (Matrix (Fin 7) (Fin 7) ℂ)) (P : Matrix (Fin 7) (Fin 7) ℂ) :
    B →ₗ[ℂ] Matrix (Fin 7) (Fin 7) ℂ :=
  (LinearMap.mulLeft ℂ P).comp (Subalgebra.val B).toLinearMap

theorem leftMul_apply (P : Matrix (Fin 7) (Fin 7) ℂ) (b : B) : leftMul B P b = P * b.1 := rfl

theorem sandwich_apply (k : Fin 4) (Z : Matrix (Fin 7) (Fin 7) ℂ) (i j : Fin 7) :
    (centralProj k * Z * centralProj k) i j =
      if blockOf i = k ∧ blockOf j = k then Z i j else 0 := by
  rw [mul_centralProj_apply, centralProj_mul_apply]
  by_cases hi : blockOf i = k <;> by_cases hj : blockOf j = k <;> simp [hi, hj]

/-- A subalgebra containing the matrix units of block `k` contains every `P_k Z P_k`. -/
theorem sandwich_mem_of_units (k : Fin 4)
    (hunits : ∀ i j, blockOf i = k → blockOf j = k → Matrix.single i j (1 : ℂ) ∈ B)
    (Z : Matrix (Fin 7) (Fin 7) ℂ) : centralProj k * Z * centralProj k ∈ B := by
  rw [Matrix.matrix_eq_sum_single (centralProj k * Z * centralProj k)]
  refine B.sum_mem fun i _ => B.sum_mem fun j _ => ?_
  rw [sandwich_apply]
  split_ifs with h
  · rw [show Matrix.single i j (Z i j) = Z i j • Matrix.single i j 1 from by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]]
    exact B.smul_mem (hunits i j h.1 h.2) _
  · rw [Matrix.single_zero]; exact B.zero_mem

theorem sandwich_single {k : Fin 4} {i j : Fin 7} (hi : blockOf i = k) (hj : blockOf j = k) :
    centralProj k * Matrix.single i j (1 : ℂ) * centralProj k = Matrix.single i j 1 := by
  ext a c
  rw [sandwich_apply, Matrix.single_apply]
  split_ifs with h1 h2 h2 <;> try rfl
  · exact absurd ⟨h2.1 ▸ hi, h2.2 ▸ hj⟩ h1

theorem mul_centralProj_eq_sandwich {X : Matrix (Fin 7) (Fin 7) ℂ} (hX : X ∈ blockAlgebra)
    (k : Fin 4) : X * centralProj k = centralProj k * X * centralProj k := by
  rw [centralProj_comm hX, Matrix.mul_assoc, centralProj_mul_self]

theorem centralProj_mul_eq_sandwich {X : Matrix (Fin 7) (Fin 7) ℂ} (hX : X ∈ blockAlgebra)
    (k : Fin 4) : centralProj k * X = centralProj k * X * centralProj k := by
  rw [Matrix.mul_assoc, ← centralProj_comm hX, ← Matrix.mul_assoc, centralProj_mul_self]

/-- **Units from one block-supported element.**  If `B ≤ M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` surjects onto
block `k` and contains a nonzero element supported on block `k`, then `B` contains the whole
block `k`. -/
theorem block_mem_of_supported (hBle : B ≤ blockAlgebra) (k : Fin 4)
    (hsurj : ∀ Z, ∃ b ∈ B, centralProj k * b * centralProj k = centralProj k * Z * centralProj k)
    {b : Matrix (Fin 7) (Fin 7) ℂ} (hbB : b ∈ B) (hb0 : b ≠ 0) (hbk : centralProj k * b = b) :
    ∀ Z, centralProj k * Z * centralProj k ∈ B := by
  have hbb := hBle hbB
  obtain ⟨i, j, hij⟩ : ∃ i j, b i j ≠ 0 := by
    by_contra hall; push_neg at hall; exact hb0 (Matrix.ext hall)
  have hi : blockOf i = k := by
    by_contra hik
    apply hij
    rw [← hbk, centralProj_mul_apply, if_neg hik]
  have hj : blockOf j = k := by
    by_contra hjk
    exact hij (hbb i j (fun h => hjk (h ▸ hi)))
  apply sandwich_mem_of_units k
  intro a c ha hc
  obtain ⟨c1, hc1B, hc1⟩ := hsurj (Matrix.single a i 1)
  obtain ⟨c2, hc2B, hc2⟩ := hsurj (Matrix.single j c 1)
  rw [sandwich_single ha hi] at hc1
  rw [sandwich_single hj hc] at hc2
  have hprod : c1 * b * c2 = b i j • Matrix.single a c 1 := by
    have e1 : c1 * b = Matrix.single a i 1 * b := by
      rw [← hbk, ← Matrix.mul_assoc, mul_centralProj_eq_sandwich (hBle hc1B), hc1, hbk]
    have e2 : b * c2 = b * Matrix.single j c 1 := by
      have hbk' : b * centralProj k = b := by
        rw [mul_centralProj_eq_sandwich hbb, ← centralProj_mul_eq_sandwich hbb, hbk]
      calc b * c2 = b * centralProj k * c2 := by rw [hbk']
        _ = b * (centralProj k * c2 * centralProj k) := by
          rw [Matrix.mul_assoc]; congr 1; exact centralProj_mul_eq_sandwich (hBle hc2B) k
        _ = b * Matrix.single j c 1 := by rw [hc2]
    rw [e1, Matrix.mul_assoc, e2, ← Matrix.mul_assoc, Matrix.single_mul_mul_single, one_mul,
      mul_one, Matrix.smul_single, smul_eq_mul, mul_one]
  have h := B.smul_mem (mul_mem (mul_mem hc1B hbB) hc2B) (b i j)⁻¹
  rwa [hprod, smul_smul, inv_mul_cancel₀ hij, one_smul] at h

/-- The block-`k` matrices as a submodule. -/
def blockSub (k : Fin 4) : Submodule ℂ (Matrix (Fin 7) (Fin 7) ℂ) :=
  supportedOn (Finset.univ.filter fun p : Fin 7 × Fin 7 => blockOf p.1 = k ∧ blockOf p.2 = k)

theorem card_blockSub0 :
    (Finset.univ.filter fun p : Fin 7 × Fin 7 => blockOf p.1 = 0 ∧ blockOf p.2 = 0).card = 9 := by
  decide

theorem card_blockSub1 :
    (Finset.univ.filter fun p : Fin 7 × Fin 7 => blockOf p.1 = 1 ∧ blockOf p.2 = 1).card = 4 := by
  decide

theorem blockSub_le_range (hBle : B ≤ blockAlgebra) (k : Fin 4)
    (hsurj : ∀ Z, ∃ b ∈ B, centralProj k * b * centralProj k = centralProj k * Z * centralProj k) :
    blockSub k ≤ LinearMap.range (leftMul B (centralProj k)) := by
  intro X hX
  have hXs : centralProj k * X * centralProj k = X := by
    ext i j
    rw [sandwich_apply]
    split_ifs with h
    · rfl
    · symm
      apply (mem_supportedOn.mp hX) i j
      simpa using h
  obtain ⟨b, hbB, hb⟩ := hsurj X
  refine ⟨⟨b, hbB⟩, ?_⟩
  rw [leftMul_apply, centralProj_mul_eq_sandwich (hBle hbB), hb, hXs]

/-- **Colour block.**  A unital subalgebra of `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` surjecting onto the colour
factor contains the whole colour block (the rest of the algebra has dimension `6 < 9`). -/
theorem colour_block_mem_of_surj (hBle : B ≤ blockAlgebra)
    (hsurj : ∀ Z, ∃ b ∈ B, centralProj 0 * b * centralProj 0 = centralProj 0 * Z * centralProj 0) :
    ∀ Z, centralProj 0 * Z * centralProj 0 ∈ B := by
  by_cases hex : ∃ b ∈ B, b ≠ 0 ∧ centralProj 0 * b = b
  · obtain ⟨b, hbB, hb0, hbk⟩ := hex
    exact block_mem_of_supported hBle 0 hsurj hbB hb0 hbk
  · exfalso
    push_neg at hex
    -- `ker (1 - P₀) ≤ ker P₀` on `B`
    have hker : LinearMap.ker (leftMul B (1 - centralProj 0)) ≤
        LinearMap.ker (leftMul B (centralProj 0)) := by
      intro b hb
      rw [LinearMap.mem_ker, leftMul_apply] at hb ⊢
      have hb' : centralProj 0 * b.1 = b.1 := by
        rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hb; exact hb.symm
      by_contra hne
      exact hex b.1 b.2 (fun h0 => hne (by rw [h0, Matrix.mul_zero])) hb'
    have hle := finrank_range_le_of_ker_le _ _ hker
    have h9 : 9 ≤ finrank ℂ (LinearMap.range (leftMul B (centralProj 0))) := by
      have := Submodule.finrank_mono (blockSub_le_range hBle 0 hsurj)
      rwa [blockSub, finrank_supportedOn, card_blockSub0] at this
    have hrest : LinearMap.range (leftMul B (1 - centralProj 0)) ≤
        supportedOn (Finset.univ.filter fun p : Fin 7 × Fin 7 =>
          blockOf p.1 ≠ 0 ∧ blockOf p.1 = blockOf p.2) := by
      rintro _ ⟨b, rfl⟩
      rw [mem_supportedOn]
      intro i j hij
      rw [leftMul_apply, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, centralProj_mul_apply]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at hij
      rcases hij with h | h
      · rw [if_pos h, sub_self]
      · rw [hBle b.2 i j h, zero_sub, neg_eq_zero]; split_ifs <;> rfl
    have h6 := Submodule.finrank_mono hrest
    rw [finrank_supportedOn] at h6
    have hc : (Finset.univ.filter fun p : Fin 7 × Fin 7 =>
        blockOf p.1 ≠ 0 ∧ blockOf p.1 = blockOf p.2).card = 6 := by decide
    rw [hc] at h6
    omega

/-- **Weak block.**  Once the colour block is in `B`, surjectivity onto the weak factor puts
the whole weak block in `B` (the scalar part has dimension `2 < 4`). -/
theorem weak_block_mem_of_surj (hBle : B ≤ blockAlgebra)
    (hcol : ∀ Z, centralProj 0 * Z * centralProj 0 ∈ B)
    (hsurj : ∀ Z, ∃ b ∈ B, centralProj 1 * b * centralProj 1 = centralProj 1 * Z * centralProj 1) :
    ∀ Z, centralProj 1 * Z * centralProj 1 ∈ B := by
  by_cases hex : ∃ b ∈ B, b ≠ 0 ∧ centralProj 1 * b = b
  · obtain ⟨b, hbB, hb0, hbk⟩ := hex
    exact block_mem_of_supported hBle 1 hsurj hbB hb0 hbk
  · exfalso
    push_neg at hex
    have hsplit : ∀ b : Matrix (Fin 7) (Fin 7) ℂ,
        b = centralProj 0 * b + centralProj 1 * b + (centralProj 2 + centralProj 3) * b := by
      intro b
      rw [← Matrix.add_mul, ← Matrix.add_mul, ← add_assoc]
      conv_lhs => rw [← Matrix.one_mul b, ← CentralSeparation.sum_centralProj]
      rw [Fin.sum_univ_four]
    have hker : LinearMap.ker (leftMul B (centralProj 2 + centralProj 3)) ≤
        LinearMap.ker (leftMul B (centralProj 1)) := by
      intro b hb
      rw [LinearMap.mem_ker, leftMul_apply] at hb ⊢
      have hbb := hBle b.2
      have hP0b : centralProj 0 * b.1 ∈ B := by
        rw [centralProj_mul_eq_sandwich hbb]; exact hcol _
      have hw : centralProj 1 * b.1 = b.1 - centralProj 0 * b.1 := by
        have h := hsplit b.1
        rw [hb, add_zero] at h
        exact eq_sub_of_add_eq' h.symm
      have hwB : centralProj 1 * b.1 ∈ B := by rw [hw]; exact B.sub_mem b.2 hP0b
      by_contra hne
      exact hex _ hwB hne (by rw [← Matrix.mul_assoc, centralProj_mul_self])
    have hle := finrank_range_le_of_ker_le _ _ hker
    have h4 : 4 ≤ finrank ℂ (LinearMap.range (leftMul B (centralProj 1))) := by
      have := Submodule.finrank_mono (blockSub_le_range hBle 1 hsurj)
      rwa [blockSub, finrank_supportedOn, card_blockSub1] at this
    have hrest : LinearMap.range (leftMul B (centralProj 2 + centralProj 3)) ≤
        supportedOn (Finset.univ.filter fun p : Fin 7 × Fin 7 =>
          (blockOf p.1 = 2 ∨ blockOf p.1 = 3) ∧ blockOf p.1 = blockOf p.2) := by
      rintro _ ⟨b, rfl⟩
      rw [mem_supportedOn]
      intro i j hij
      rw [leftMul_apply, Matrix.add_mul, Matrix.add_apply, centralProj_mul_apply,
        centralProj_mul_apply]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or] at hij
      rcases hij with h | h
      · push_neg at h
        rw [if_neg h.1, if_neg h.2, add_zero]
      · rw [hBle b.2 i j h]; simp
    have h2 := Submodule.finrank_mono hrest
    rw [finrank_supportedOn] at h2
    have hc : (Finset.univ.filter fun p : Fin 7 × Fin 7 =>
        (blockOf p.1 = 2 ∨ blockOf p.1 = 3) ∧ blockOf p.1 = blockOf p.2).card = 2 := by decide
    rw [hc] at h2
    omega

/-- **Subdirect dichotomy (`eq:central-locked-14`) for unital subalgebras.**  A unital
subalgebra of `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` surjecting onto the colour and weak factors (surjectivity
onto the two scalar factors is automatic for a unital subalgebra) is either the full
`15`-dimensional product or the `14`-dimensional scalar-locked algebra `{(A, B, z, z)}`, and
not both.  No `*`-closedness is assumed. -/
theorem subdirect_dichotomy (hBle : B ≤ blockAlgebra)
    (hsurj0 : ∀ Z, ∃ b ∈ B, centralProj 0 * b * centralProj 0 = centralProj 0 * Z * centralProj 0)
    (hsurj1 : ∀ Z, ∃ b ∈ B, centralProj 1 * b * centralProj 1 = centralProj 1 * Z * centralProj 1) :
    Xor (B = blockAlgebra ∧ finrank ℂ B = 15)
      (B = CentralSeparation.lockedAlgebra ∧ finrank ℂ B = 14) := by
  have hcol := colour_block_mem_of_surj hBle hsurj0
  have hweak := weak_block_mem_of_surj hBle hcol hsurj1
  have hP : ∀ k : Fin 4, (∀ Z, centralProj k * Z * centralProj k ∈ B) →
      ∀ X ∈ blockAlgebra, centralProj k * X ∈ B := by
    intro k hk X hX
    rw [centralProj_mul_eq_sandwich hX]; exact hk X
  have hP0 : centralProj 0 ∈ B := by
    have h := hP 0 hcol 1 blockAlgebra.one_mem; rwa [Matrix.mul_one] at h
  have hP1 : centralProj 1 ∈ B := by
    have h := hP 1 hweak 1 blockAlgebra.one_mem; rwa [Matrix.mul_one] at h
  have hE : Matrix.single (5 : Fin 7) 5 (1 : ℂ) + Matrix.single 6 6 1 ∈ B := by
    rw [CentralSeparation.single_add_single_eq]
    exact B.sub_mem (B.sub_mem B.one_mem hP0) hP1
  by_cases hlock : ∀ b ∈ B, b 5 5 = b 6 6
  · have heq : B = CentralSeparation.lockedAlgebra := by
      ext X
      rw [CentralSeparation.mem_lockedAlgebra]
      constructor
      · intro hX; exact ⟨hBle hX, hlock X hX⟩
      · rintro ⟨hXb, hX56⟩
        have hdec := CentralSeparation.scalar_decomp hXb
        rw [hX56, add_assoc, ← smul_add] at hdec
        rw [hdec]
        exact B.add_mem (B.add_mem (hP 0 hcol X hXb) (hP 1 hweak X hXb)) (B.smul_mem hE _)
    refine Or.inr ⟨⟨heq, by rw [heq, CentralSeparation.finrank_lockedAlgebra]⟩, ?_⟩
    rintro ⟨h, -⟩
    exact CentralSeparation.blockAlgebra_ne_lockedAlgebra (h.symm.trans heq)
  · push_neg at hlock
    have heq : B = blockAlgebra :=
      InternalSeedWords.eq_blockAlgebra_of_blocks hBle hcol hweak hlock
    refine Or.inl ⟨⟨heq, by rw [heq, CentralSeparation.finrank_blockAlgebra]⟩, ?_⟩
    rintro ⟨h, -⟩
    exact CentralSeparation.blockAlgebra_ne_lockedAlgebra (heq.symm.trans h)

end Subdirect

end ColourBridgeComplete
end RenewalGeometry
