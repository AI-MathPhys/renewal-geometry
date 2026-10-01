/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.EndpointAllocationCompilerExact
import RenewalGeometry.StandardModel.LinearAnomalyRigidityExact
import RenewalGeometry.Commutant.EquivariantMultiplicityFactorization

/-!
# Endpoint ancestry, endpoint allocation and the source-native three-count
  (`thm:endpoint-ancestry-compiler`, `thm:endpoint-allocation`,
  `cor:source-native-endpoint-allocation`, spacetime–gauge duality manuscript)

## Endpoint allocation (`thm:endpoint-allocation`)

`S : E_f → N_f` is a complete typed synthesis (`Function.Surjective S.mulVec`) and
`T : G_gen → N_f` an endpoint subsource with `A_f = T* T ≻ 0`.  No surjectivity of `T` and no
factorisation `T = S J` is assumed: completeness of `S` produces `J` with `T = S J`
(`endpointAlloc_exists_mul_eq_of_surjective`), and the matrix content proved in
`EndpointAllocationCompilerExact` applies.  `endpoint_allocation` gives
`𝔸_{f|G} = S*(I − P_fG)S ⪰ 0`, `a_{f|G} = ‖(I − P_fG)S‖²_HS`,
`n_f = dim(E_f/Ker G_f) = rank G_f = dim G_gen + rank 𝔸_{f|G}` and the four-way equivalence
`a = 0 ⟺ 𝔸 = 0 ⟺ Ran T_f = N_f ⟺ n_f = dim G_gen`;
`endpoint_allocation_quotient_unitary` is the descended unitary from
`(E_f/Ker G_f, ⟨·, G_f ·⟩)` onto `N_f`; `endpoint_allocation_anomaly_excess` is
`eq:allocation-anomaly-excess` (from `Δ_lin = 0` alone, via the rows of
`LinearAnomalyRigidity`).  `dim G_gen = 3` (`eq:three-generations`, proved in
`EndpointGenerationCarrierExact`) is the specialisation `Fintype.card G = 3`
(`endpoint_allocation_three`).

## Endpoint-ancestry compiler (`thm:endpoint-ancestry-compiler`)

Coordinates: `V = V_f` (irreducible gauge carrier, generators `ρ j = ρ_f(X_j)`), `N = N_f`,
`G = G_gen`, `K` indexes the type block `P_{f,ε_f} 𝒦_F^min`, on which the represented
generators `X j`, the central generator `Y` and the chirality `Γ_F` act; `ev : V ⊗ N → K` is the
unitary evaluation map of `prop:canonical-chiral-projectors`, intertwining `ρ_f(X_j) ⊗ I` with
`X_j`, and on the type block `Y = y_f`, `Γ_F = ε_f` (`Y ev = y_f ev`, `Γ_F ev = ε_f ev`).
Irreducibility of `V_f` is the hypothesis that the only `ρ`-invariant subspaces are `⊥, ⊤`;
Schur's lemma (`endpointAnc_schur_scalar`) is derived from it.

`endpoint_ancestry_compiler`: `Δ_f^anc(Ξ_f) = 0 ⟺ Ξ̂_f = I_{V_f} ⊗ T_f` for a unique `T_f`
(`eq:endpoint-ancestry-factorization`); on that branch `T_f = d_f⁻¹ Tr_{V_f} Ξ̂_f`
(`eq:endpoint-ancestry-partial-trace`), `Ξ_f* Ξ_f = I ⊗ T_f* T_f`,
`‖Ξ_f‖²_HS = d_f ‖T_f‖²_HS` (`eq:endpoint-ancestry-Gram`), and `T_f* T_f ≻ 0 ⟺ Ξ_f* Ξ_f ≻ 0`.
Because `Ξ_f` is typed into the block, the `Y` and `Γ_F` terms of the defect vanish
identically; they are kept for fidelity.

## Source-native allocation (`cor:source-native-endpoint-allocation`)

`source_native_endpoint_allocation`: on the zero-defect faithful branch, with the canonical
coefficient `T_f = endpointAncCoefficient ev Ξ_f`, `a_{f|G} = 0 ⟺ Ran Ξ_f = P_{f,ε}𝒦_F^min ⟺
Ran Ξ̂_f = V_f ⊗ N_f ⟺ n_f = dim G_gen` (`eq:source-native-three-count`).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace RenewalGeometry
namespace EndpointAncestryAllocation

open EndpointAllocationCompiler

/-! ## Generic finite-matrix facts -/

section Generic

/-- Completeness of a synthesis lets every map into its target factor through it. -/
theorem endpointAlloc_exists_mul_eq_of_surjective {N E G : Type*} [Fintype E]
    (S : Matrix N E ℂ) (hS : Function.Surjective S.mulVec) (T : Matrix N G ℂ) :
    ∃ J : Matrix E G ℂ, S * J = T := by
  choose f hf using fun g : G => hS (fun n => T n g)
  refine ⟨Matrix.of fun i g => f g i, ?_⟩
  ext n g
  have := congrFun (hf g) n
  rw [Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct] using this

/-- `Ran S = target` iff `rank S = dim target`. -/
theorem endpointAlloc_surjective_iff_rank {N E : Type*} [Fintype N] [Fintype E]
    (S : Matrix N E ℂ) : Function.Surjective S.mulVec ↔ S.rank = Fintype.card N := by
  constructor
  · intro h
    have hr : LinearMap.range S.mulVecLin = ⊤ := LinearMap.range_eq_top.mpr h
    rw [Matrix.rank, hr, finrank_top, Module.finrank_fintype_fun_eq_card]
  · intro h
    have hr : LinearMap.range S.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fintype_fun_eq_card]
      exact h
    exact LinearMap.range_eq_top.mp hr

theorem endpointAlloc_injective_iff {m n : Type*} [Fintype n] (M : Matrix m n ℂ) :
    Function.Injective M.mulVec ↔ ∀ x, M *ᵥ x = 0 → x = 0 :=
  ⟨fun h x hx => h (by rw [hx, Matrix.mulVec_zero]),
    fun h a b hab => sub_eq_zero.mp (h _ (by rw [Matrix.mulVec_sub, hab, sub_self]))⟩

/-- A Gram matrix is positive definite iff the map is injective. -/
theorem endpointAlloc_posDef_gram_iff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : (Mᴴ * M).PosDef ↔ Function.Injective M.mulVec := by
  constructor
  · intro h a b hab
    have hu : Function.Injective (Mᴴ * M).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr h.isUnit
    apply hu
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hab]
  · intro h
    exact Matrix.PosDef.conjTranspose_mul_self M h

theorem endpointAlloc_hsNormSq_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : 0 ≤ hsNormSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem endpointAlloc_hsNormSq_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : hsNormSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (A i j)).mp h
    ext i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg (A i j)).mp
      (h1 i (Finset.mem_univ _)) j (Finset.mem_univ _)
    simpa using h2
  · rintro rfl
    simp [hsNormSq]

/-- `‖A‖²_HS = Tr(A* A)`. -/
theorem endpointAlloc_hsNormSq_eq_trace {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : (hsNormSq A : ℂ) = (Aᴴ * A).trace := by
  have hentry : ∀ j, (Aᴴ * A) j j = ∑ i, ((Complex.normSq (A i j) : ℝ) : ℂ) := by
    intro j
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  simp only [Matrix.trace, Matrix.diag, hentry, hsNormSq]
  push_cast
  rw [Finset.sum_comm]

/-- Coordinates of `(I_V ⊗ T) x`. -/
theorem endpointAlloc_one_kronecker_mulVec {V N G : Type*} [Fintype V] [DecidableEq V]
    [Fintype G] (T : Matrix N G ℂ) (x : V × G → ℂ) (v : V) (n : N) :
    (((1 : Matrix V V ℂ) ⊗ₖ T) *ᵥ x) (v, n) = (T *ᵥ fun g => x (v, g)) n := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_eq_single v]
  · simp
  · intro w hw
    simp [Ne.symm hw]

theorem endpointAlloc_injective_one_kronecker_iff {V N G : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] [Fintype G] (T : Matrix N G ℂ) :
    Function.Injective ((1 : Matrix V V ℂ) ⊗ₖ T).mulVec ↔ Function.Injective T.mulVec := by
  rw [endpointAlloc_injective_iff, endpointAlloc_injective_iff]
  constructor
  · intro h y hy
    obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
    let x : V × G → ℂ := fun p => if p.1 = v₀ then y p.2 else 0
    have hx : ((1 : Matrix V V ℂ) ⊗ₖ T) *ᵥ x = 0 := by
      ext ⟨v, n⟩
      rw [endpointAlloc_one_kronecker_mulVec]
      by_cases hv : v = v₀
      · subst hv; simp [x, hy]
      · simp [x, hv, Matrix.mulVec, dotProduct]
    have h0 := h x hx
    ext g
    have := congrFun h0 (v₀, g)
    simpa [x] using this
  · intro h x hx
    have hv : ∀ v, (fun g => x (v, g)) = 0 := by
      intro v
      apply h
      ext n
      have := congrFun hx (v, n)
      rw [endpointAlloc_one_kronecker_mulVec] at this
      simpa using this
    ext ⟨v, g⟩
    exact congrFun (hv v) g

theorem endpointAlloc_surjective_one_kronecker_iff {V N G : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] [Fintype G] (T : Matrix N G ℂ) :
    Function.Surjective ((1 : Matrix V V ℂ) ⊗ₖ T).mulVec ↔ Function.Surjective T.mulVec := by
  constructor
  · intro h z
    obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
    obtain ⟨x, hx⟩ := h (fun p => z p.2)
    refine ⟨fun g => x (v₀, g), ?_⟩
    ext n
    have := congrFun hx (v₀, n)
    rw [endpointAlloc_one_kronecker_mulVec] at this
    exact this
  · intro h y
    choose f hf using fun v : V => h (fun n => y (v, n))
    refine ⟨fun p => f p.1 p.2, ?_⟩
    ext ⟨v, n⟩
    rw [endpointAlloc_one_kronecker_mulVec]
    exact congrFun (hf v) n

end Generic

/-! ## `thm:endpoint-allocation` -/

section Allocation

variable {N E G : Type*} [Fintype N] [Fintype E] [Fintype G] [DecidableEq N] [DecidableEq E]
  [DecidableEq G]

/-- **`thm:endpoint-allocation`** (`eq:endpoint-allocation-positive`,
`eq:endpoint-generation-excess`, `eq:endpoint-allocation-zero`).  For a complete typed
synthesis `S : E_f → N_f` (onto) and an endpoint subsource `T : G_gen → N_f` with
`A_f = T* T ≻ 0` (no surjectivity of `T` assumed):
`𝔸 = S*(I − P_fG)S ⪰ 0`, `a = Tr 𝔸 = ‖(I − P_fG)S‖²_HS`,
`dim(E_f/Ker G_f) = rank G_f = n_f = dim G_gen + rank 𝔸`, and
`a = 0 ⟺ 𝔸 = 0 ⟺ Ran T_f = N_f ⟺ n_f = dim G_gen`. -/
theorem endpoint_allocation (S : Matrix N E ℂ) (hS : Function.Surjective S.mulVec)
    (T : Matrix N G ℂ) (hA : (Tᴴ * T).PosDef) :
    allocationResidual S T = Sᴴ * (1 - subsourceProjector T) * S ∧
    (allocationResidual S T).PosSemidef ∧
    (allocationResidual S T).trace = (hsNormSq ((1 - subsourceProjector T) * S) : ℂ) ∧
    Module.finrank ℂ ((E → ℂ) ⧸ LinearMap.ker (Sᴴ * S).mulVecLin) = (Sᴴ * S).rank ∧
    (Sᴴ * S).rank = Fintype.card N ∧
    Fintype.card N = Fintype.card G + (allocationResidual S T).rank ∧
    ((allocationResidual S T).trace = 0 ↔ allocationResidual S T = 0) ∧
    (allocationResidual S T = 0 ↔ Function.Surjective T.mulVec) ∧
    (Function.Surjective T.mulVec ↔ Fintype.card N = Fintype.card G) := by
  have hTrank : T.rank = Fintype.card G := rank_eq_card_of_posDef hA
  obtain ⟨J, rfl⟩ := endpointAlloc_exists_mul_eq_of_surjective S hS T
  have hGrank : (Sᴴ * S).rank = Fintype.card N := by
    rw [Matrix.rank_conjTranspose_mul_self, ← endpointAlloc_surjective_iff_rank]
    exact hS
  have hexc := rank_eq_card_add_rank_allocationResidual S J hA
  have hzero := allocationResidual_zero_iff S J hA
  have hsurj : Function.Surjective (S * J).mulVec ↔ Fintype.card N = Fintype.card G := by
    rw [endpointAlloc_surjective_iff_rank, hTrank]
    exact eq_comm
  refine ⟨allocationResidual_eq_orthogonal S _, allocationResidual_posSemidef S hA,
    allocationResidual_trace_hs S hA, ?_, hGrank, by rw [← hGrank, hexc], hzero.1, ?_, hsurj⟩
  · exact (LinearMap.quotKerEquivRange _).finrank_eq
  · rw [hzero.2.2, hGrank, hsurj]

omit [DecidableEq N] [DecidableEq E] in
/-- **`thm:endpoint-allocation`, quotient clause.**  `Ker G_f = Ker S_f`, and `S_f` descends to
a linear isomorphism from `E_f / Ker G_f` onto `N_f` which is unitary for the inner product
induced by `G_f`: `⟨S e, S e'⟩ = ⟨e, G_f e'⟩`. -/
theorem endpoint_allocation_quotient_unitary (S : Matrix N E ℂ)
    (hS : Function.Surjective S.mulVec) :
    LinearMap.ker (Sᴴ * S).mulVecLin = LinearMap.ker S.mulVecLin ∧
    ∃ q : ((E → ℂ) ⧸ LinearMap.ker (Sᴴ * S).mulVecLin) ≃ₗ[ℂ] (N → ℂ),
      (∀ x, q (Submodule.Quotient.mk x) = S *ᵥ x) ∧
      ∀ x y, star (q (Submodule.Quotient.mk x)) ⬝ᵥ q (Submodule.Quotient.mk y)
        = star x ⬝ᵥ ((Sᴴ * S) *ᵥ y) := by
  have hker := Matrix.ker_mulVecLin_conjTranspose_mul_self S
  refine ⟨hker, (Submodule.quotEquivOfEq _ _ hker).trans
    (S.mulVecLin.quotKerEquivOfSurjective hS), fun x => rfl, fun x y => ?_⟩
  change star (S *ᵥ x) ⬝ᵥ (S *ᵥ y) = star x ⬝ᵥ ((Sᴴ * S) *ᵥ y)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

/-- **`eq:allocation-anomaly-excess`.**  If the linear anomaly residual vanishes and the
populated type `f` (species `s`) has multiplicity `n_f = dim N_f`, then every charged
multiplicity equals `dim G_gen + rank 𝔸_{f|G}`. -/
theorem endpoint_allocation_anomaly_excess (S : Matrix N E ℂ)
    (hS : Function.Surjective S.mulVec) (T : Matrix N G ℂ) (hA : (Tᴴ * T).PosDef)
    (n : LinearAnomalyRigidity.ChargedMultiplicities)
    (hlin : LinearAnomalyRigidity.deltaLin n = 0) (s : Fin 5)
    (hs : n.vec s = (Fintype.card N : ℤ)) :
    n = LinearAnomalyRigidity.common
      ((Fintype.card G + (allocationResidual S T).rank : ℕ) : ℤ) := by
  have hcount := (endpoint_allocation S hS T hA).2.2.2.2.2.1
  obtain ⟨h1, h2, h3, h4⟩ := (LinearAnomalyRigidity.deltaLin_eq_zero_iff_rows n).mp hlin
  simp only [LinearAnomalyRigidity.r3, LinearAnomalyRigidity.r3Y, LinearAnomalyRigidity.r2Y,
    LinearAnomalyRigidity.rgY] at h1 h2 h3 h4
  have hs' : n.vec s = ((Fintype.card G + (allocationResidual S T).rank : ℕ) : ℤ) := by
    rw [hs, hcount]
  fin_cases s <;>
    simp [LinearAnomalyRigidity.ChargedMultiplicities.vec] at hs' <;>
    ext <;> simp only [LinearAnomalyRigidity.common] <;> push_cast at hs' ⊢ <;> omega

/-- `thm:endpoint-allocation` with `dim G_gen = 3` (`eq:three-generations`):
`n_f = 3 + rank 𝔸` and `a_{f|G} = 0 ⟺ n_f = 3`. -/
theorem endpoint_allocation_three (S : Matrix N E ℂ) (hS : Function.Surjective S.mulVec)
    (T : Matrix N G ℂ) (hA : (Tᴴ * T).PosDef) (hG : Fintype.card G = 3) :
    Fintype.card N = 3 + (allocationResidual S T).rank ∧
    ((allocationResidual S T).trace = 0 ↔ Fintype.card N = 3) := by
  obtain ⟨-, -, -, -, -, hc, h1, h2, h3⟩ := endpoint_allocation S hS T hA
  rw [hG] at hc h3
  exact ⟨hc, h1.trans (h2.trans h3)⟩

end Allocation

/-! ## `thm:endpoint-ancestry-compiler` -/

section Ancestry

variable {ι V N G K : Type*} [Fintype ι] [Fintype V] [DecidableEq V] [Fintype N]
  [DecidableEq N] [Fintype G] [DecidableEq G] [Fintype K] [DecidableEq K]

/-- The positive covariance defect `Δ_f^anc(Ξ_f)` (`eq:endpoint-ancestry-defect`). -/
noncomputable def endpointAncDefect (ρ : ι → Matrix V V ℂ) (X : ι → Matrix K K ℂ)
    (Yc Γ : Matrix K K ℂ) (y ε : ℂ) (Ξ : Matrix K (V × G) ℂ) : ℝ :=
  ∑ j, hsNormSq (X j * Ξ - Ξ * (ρ j ⊗ₖ (1 : Matrix G G ℂ))) + hsNormSq (Yc * Ξ - y • Ξ)
    + hsNormSq (Γ * Ξ - ε • Ξ)

/-- The partial trace `Tr_{V}` contracting the input and output `V` legs. -/
def endpointAncPartialTrace (M : Matrix (V × N) (V × G) ℂ) : Matrix N G ℂ :=
  fun n g => ∑ v, M (v, n) (v, g)

/-- The canonical coefficient `T_f = d_f⁻¹ Tr_{V_f}(ev_f* Ξ_f)`
(`eq:endpoint-ancestry-partial-trace`). -/
noncomputable def endpointAncCoefficient (ev : Matrix K (V × N) ℂ) (Ξ : Matrix K (V × G) ℂ) :
    Matrix N G ℂ :=
  ((Fintype.card V : ℂ)⁻¹) • endpointAncPartialTrace (evᴴ * Ξ)

omit [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G] in
theorem endpointAncPartialTrace_one_kronecker (T : Matrix N G ℂ) :
    endpointAncPartialTrace ((1 : Matrix V V ℂ) ⊗ₖ T) = (Fintype.card V : ℂ) • T := by
  ext n g
  simp [endpointAncPartialTrace, Matrix.kroneckerMap_apply]

omit [Fintype ι] [DecidableEq V] [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]
  [DecidableEq K] in
/-- Schur's lemma from irreducibility: every operator commuting with an irreducible family on
`V ≠ 0` is a unique scalar. -/
theorem endpointAnc_schur_scalar [DecidableEq V] [Nonempty V] (ρ : ι → Matrix V V ℂ)
    (hirr : ∀ W : Submodule ℂ (V → ℂ), (∀ j, ∀ x ∈ W, ρ j *ᵥ x ∈ W) → W = ⊥ ∨ W = ⊤)
    (Z : Matrix V V ℂ) (hZ : ∀ j, ρ j * Z = Z * ρ j) : ∃! c : ℂ, Z = c • 1 := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' Z)
  have hmem : ∀ x, x ∈ Module.End.eigenspace (Matrix.toLin' Z) c ↔ Z *ᵥ x = c • x := by
    intro x
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hinv : ∀ j, ∀ x ∈ Module.End.eigenspace (Matrix.toLin' Z) c,
      ρ j *ᵥ x ∈ Module.End.eigenspace (Matrix.toLin' Z) c := by
    intro j x hx
    rw [hmem] at hx ⊢
    rw [Matrix.mulVec_mulVec, ← hZ j, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
  have htop : Module.End.eigenspace (Matrix.toLin' Z) c = ⊤ := by
    rcases hirr _ hinv with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.mp hc)
    · exact h
  have hZc : Z = c • 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    have hx : x ∈ Module.End.eigenspace (Matrix.toLin' Z) c := htop ▸ Submodule.mem_top
    rw [hmem] at hx
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hx, Matrix.smul_mulVec, Matrix.one_mulVec]
  refine ⟨c, hZc, fun c' hc' => ?_⟩
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  have := congrFun (congrFun (hc'.symm.trans hZc) v₀) v₀
  simpa using this

omit [Fintype ι] [DecidableEq V] in
/-- Transport of each gauge term of the defect by the unitary evaluation map. -/
theorem endpointAnc_gauge_term (ρ : ι → Matrix V V ℂ) (X : ι → Matrix K K ℂ)
    (ev : Matrix K (V × N) ℂ) (hev2 : ev * evᴴ = 1)
    (hX : ∀ j, X j * ev = ev * (ρ j ⊗ₖ (1 : Matrix N N ℂ))) (Ξ : Matrix K (V × G) ℂ) (j : ι) :
    X j * Ξ - Ξ * (ρ j ⊗ₖ (1 : Matrix G G ℂ))
      = ev * ((ρ j ⊗ₖ (1 : Matrix N N ℂ)) * (evᴴ * Ξ)
          - (evᴴ * Ξ) * (ρ j ⊗ₖ (1 : Matrix G G ℂ))) := by
  have hΞ : Ξ = ev * (evᴴ * Ξ) := by rw [← Matrix.mul_assoc, hev2, Matrix.one_mul]
  conv_lhs => rw [hΞ]
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, hX j, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc]

/-- `Δ_f^anc(Ξ_f) = 0` iff `Ξ̂_f = ev* Ξ_f` intertwines `ρ_f(X_j) ⊗ I`. -/
theorem endpointAnc_defect_eq_zero_iff (ρ : ι → Matrix V V ℂ) (X : ι → Matrix K K ℂ)
    (Yc Γ : Matrix K K ℂ) (y ε : ℂ) (ev : Matrix K (V × N) ℂ) (hev1 : evᴴ * ev = 1)
    (hev2 : ev * evᴴ = 1) (hX : ∀ j, X j * ev = ev * (ρ j ⊗ₖ (1 : Matrix N N ℂ)))
    (hY : Yc * ev = y • ev) (hΓ : Γ * ev = ε • ev) (Ξ : Matrix K (V × G) ℂ) :
    endpointAncDefect ρ X Yc Γ y ε Ξ = 0 ↔
      ∀ j, (ρ j ⊗ₖ (1 : Matrix N N ℂ)) * (evᴴ * Ξ)
        = (evᴴ * Ξ) * (ρ j ⊗ₖ (1 : Matrix G G ℂ)) := by
  have hΞ : Ξ = ev * (evᴴ * Ξ) := by rw [← Matrix.mul_assoc, hev2, Matrix.one_mul]
  have hYt : Yc * Ξ - y • Ξ = 0 := by
    rw [hΞ, ← Matrix.mul_assoc, hY, Matrix.smul_mul, sub_self]
  have hΓt : Γ * Ξ - ε • Ξ = 0 := by
    rw [hΞ, ← Matrix.mul_assoc, hΓ, Matrix.smul_mul, sub_self]
  unfold endpointAncDefect
  rw [hYt, hΓt]
  have h0 : hsNormSq (0 : Matrix K (V × G) ℂ) = 0 :=
    (endpointAlloc_hsNormSq_eq_zero_iff _).mpr rfl
  rw [h0, add_zero, add_zero, Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => endpointAlloc_hsNormSq_nonneg _)]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun j => ?_
  rw [endpointAlloc_hsNormSq_eq_zero_iff, endpointAnc_gauge_term ρ X ev hev2 hX Ξ j]
  constructor
  · intro h
    have key : ∀ M : Matrix (V × N) (V × G) ℂ, ev * M = 0 → M = 0 := fun M hM => by
      rw [← Matrix.one_mul M, ← hev1, Matrix.mul_assoc, hM, Matrix.mul_zero]
    exact sub_eq_zero.mp (key _ h)
  · intro h
    rw [h, sub_self, Matrix.mul_zero]

/-- **`thm:endpoint-ancestry-compiler`.**  Under the evaluation-map hypotheses and
irreducibility of `V_f`:
(1) `Δ_f^anc(Ξ_f) = 0 ⟺ Ξ̂_f = I_{V_f} ⊗ T_f` for a unique `T_f`
(`eq:endpoint-ancestry-factorization`);
(2) on that branch `T_f = d_f⁻¹ Tr_{V_f} Ξ̂_f` (`eq:endpoint-ancestry-partial-trace`),
`Ξ_f* Ξ_f = I ⊗ T_f* T_f` and `‖Ξ_f‖²_HS = d_f ‖T_f‖²_HS` (`eq:endpoint-ancestry-Gram`), and
endpoint faithfulness `T_f* T_f ≻ 0` is equivalent to `Ξ_f* Ξ_f ≻ 0`. -/
theorem endpoint_ancestry_compiler [Nonempty V] (ρ : ι → Matrix V V ℂ)
    (hirr : ∀ W : Submodule ℂ (V → ℂ), (∀ j, ∀ x ∈ W, ρ j *ᵥ x ∈ W) → W = ⊥ ∨ W = ⊤)
    (X : ι → Matrix K K ℂ) (Yc Γ : Matrix K K ℂ) (y ε : ℂ) (ev : Matrix K (V × N) ℂ)
    (hev1 : evᴴ * ev = 1) (hev2 : ev * evᴴ = 1)
    (hX : ∀ j, X j * ev = ev * (ρ j ⊗ₖ (1 : Matrix N N ℂ)))
    (hY : Yc * ev = y • ev) (hΓ : Γ * ev = ε • ev) (Ξ : Matrix K (V × G) ℂ) :
    (endpointAncDefect ρ X Yc Γ y ε Ξ = 0 ↔
      ∃! T : Matrix N G ℂ, evᴴ * Ξ = (1 : Matrix V V ℂ) ⊗ₖ T) ∧
    ∀ T : Matrix N G ℂ, evᴴ * Ξ = (1 : Matrix V V ℂ) ⊗ₖ T →
      T = endpointAncCoefficient ev Ξ ∧
      Ξᴴ * Ξ = (1 : Matrix V V ℂ) ⊗ₖ (Tᴴ * T) ∧
      hsNormSq Ξ = (Fintype.card V : ℝ) * hsNormSq T ∧
      ((Tᴴ * T).PosDef ↔ (Ξᴴ * Ξ).PosDef) := by
  have hΞ : Ξ = ev * (evᴴ * Ξ) := by rw [← Matrix.mul_assoc, hev2, Matrix.one_mul]
  have hcard : (Fintype.card V : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨?_, fun T hT => ?_⟩
  · rw [endpointAnc_defect_eq_zero_iff ρ X Yc Γ y ε ev hev1 hev2 hX hY hΓ Ξ]
    constructor
    · intro h
      exact equivariantOperator_unique_kroneckerFactorization ρ ρ (1 : Matrix V V ℂ)
        (endpointAnc_schur_scalar ρ hirr) (evᴴ * Ξ) h
    · rintro ⟨T, hT, -⟩ j
      rw [hT, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
        Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  · have hgram : Ξᴴ * Ξ = (1 : Matrix V V ℂ) ⊗ₖ (Tᴴ * T) := by
      have : Ξᴴ * Ξ = (evᴴ * Ξ)ᴴ * (evᴴ * Ξ) := by
        conv_lhs => rw [hΞ]
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc evᴴ ev, hev1,
          Matrix.one_mul]
      rw [this, hT, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    refine ⟨?_, hgram, ?_, ?_⟩
    · rw [endpointAncCoefficient, hT, endpointAncPartialTrace_one_kronecker, smul_smul,
        inv_mul_cancel₀ hcard, one_smul]
    · apply Complex.ofReal_injective
      rw [endpointAlloc_hsNormSq_eq_trace, hgram, Matrix.trace_kronecker, Matrix.trace_one,
        Complex.ofReal_mul, endpointAlloc_hsNormSq_eq_trace]
      push_cast
      rfl
    · have hgram' : Ξᴴ * Ξ = ((1 : Matrix V V ℂ) ⊗ₖ T)ᴴ * ((1 : Matrix V V ℂ) ⊗ₖ T) := by
        rw [hgram, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
          ← Matrix.mul_kronecker_mul, Matrix.one_mul]
      rw [hgram', endpointAlloc_posDef_gram_iff, endpointAlloc_posDef_gram_iff,
        endpointAlloc_injective_one_kronecker_iff]

end Ancestry

/-! ## `cor:source-native-endpoint-allocation` -/

section SourceNative

variable {ι V N G K E : Type*} [Fintype ι] [Fintype V] [DecidableEq V] [Fintype N]
  [DecidableEq N] [Fintype G] [DecidableEq G] [Fintype K] [DecidableEq K] [Fintype E]
  [DecidableEq E]

/-- **`cor:source-native-endpoint-allocation`** (`eq:source-native-three-count`).  On the
zero-defect branch `Δ_f^anc(Ξ_f) = 0` with faithful canonical coefficient
`T_f = d_f⁻¹ Tr_{V_f}(ev* Ξ_f)` (`T_f* T_f ≻ 0`) and a complete typed synthesis `S_f`
(onto `N_f`): `Ξ̂_f = I ⊗ T_f`, the allocation short is
`allocationResidual S_f T_f`, a function of `(S_f, Ξ_f)` only, and
`a_{f|G} = 0 ⟺ Ran Ξ_f = P_{f,ε}𝒦_F^min`, `Ran Ξ_f = P_{f,ε}𝒦_F^min ⟺ Ran Ξ̂_f = V_f ⊗ N_f`,
`Ran Ξ_f = P_{f,ε}𝒦_F^min ⟺ n_f = rank G_f = dim G_gen`. -/
theorem source_native_endpoint_allocation [Nonempty V] (ρ : ι → Matrix V V ℂ)
    (hirr : ∀ W : Submodule ℂ (V → ℂ), (∀ j, ∀ x ∈ W, ρ j *ᵥ x ∈ W) → W = ⊥ ∨ W = ⊤)
    (X : ι → Matrix K K ℂ) (Yc Γ : Matrix K K ℂ) (y ε : ℂ) (ev : Matrix K (V × N) ℂ)
    (hev1 : evᴴ * ev = 1) (hev2 : ev * evᴴ = 1)
    (hX : ∀ j, X j * ev = ev * (ρ j ⊗ₖ (1 : Matrix N N ℂ)))
    (hY : Yc * ev = y • ev) (hΓ : Γ * ev = ε • ev) (Ξ : Matrix K (V × G) ℂ)
    (hdef : endpointAncDefect ρ X Yc Γ y ε Ξ = 0)
    (hpos : ((endpointAncCoefficient ev Ξ)ᴴ * endpointAncCoefficient ev Ξ).PosDef)
    (S : Matrix N E ℂ) (hS : Function.Surjective S.mulVec) :
    evᴴ * Ξ = (1 : Matrix V V ℂ) ⊗ₖ endpointAncCoefficient ev Ξ ∧
    ((allocationResidual S (endpointAncCoefficient ev Ξ)).trace = 0 ↔
      Function.Surjective Ξ.mulVec) ∧
    (Function.Surjective Ξ.mulVec ↔ Function.Surjective (evᴴ * Ξ).mulVec) ∧
    (Function.Surjective Ξ.mulVec ↔ (Sᴴ * S).rank = Fintype.card G) := by
  have hcomp := endpoint_ancestry_compiler ρ hirr X Yc Γ y ε ev hev1 hev2 hX hY hΓ Ξ
  obtain ⟨T, hT, -⟩ := hcomp.1.mp hdef
  have hTc : T = endpointAncCoefficient ev Ξ := ((hcomp.2 T hT).1)
  rw [← hTc] at hpos ⊢
  obtain ⟨-, -, -, -, hGrank, -, h1, h2, h3⟩ := endpoint_allocation S hS T hpos
  have hΞ : Ξ = ev * (evᴴ * Ξ) := by rw [← Matrix.mul_assoc, hev2, Matrix.one_mul]
  have hsurjhat : Function.Surjective Ξ.mulVec ↔ Function.Surjective (evᴴ * Ξ).mulVec := by
    constructor
    · intro h z
      obtain ⟨x, hx⟩ := h (ev *ᵥ z)
      refine ⟨x, ?_⟩
      rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_mulVec, hev1, Matrix.one_mulVec]
    · intro h w
      obtain ⟨x, hx⟩ := h (evᴴ *ᵥ w)
      refine ⟨x, ?_⟩
      rw [hΞ, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_mulVec, hev2, Matrix.one_mulVec]
  have hsurjT : Function.Surjective Ξ.mulVec ↔ Function.Surjective T.mulVec := by
    rw [hsurjhat, hT, endpointAlloc_surjective_one_kronecker_iff]
  refine ⟨hT, ?_, hsurjhat, ?_⟩
  · rw [h1, h2, hsurjT]
  · rw [hsurjT, h3, hGrank]

/-- `cor:source-native-endpoint-allocation` with `dim G_gen = 3`:
`a_{f|G} = 0 ⟺ Ran Ξ_f = P_{f,ε}𝒦_F^min ⟺ n_f = 3`. -/
theorem source_native_endpoint_allocation_three [Nonempty V] (ρ : ι → Matrix V V ℂ)
    (hirr : ∀ W : Submodule ℂ (V → ℂ), (∀ j, ∀ x ∈ W, ρ j *ᵥ x ∈ W) → W = ⊥ ∨ W = ⊤)
    (X : ι → Matrix K K ℂ) (Yc Γ : Matrix K K ℂ) (y ε : ℂ) (ev : Matrix K (V × N) ℂ)
    (hev1 : evᴴ * ev = 1) (hev2 : ev * evᴴ = 1)
    (hX : ∀ j, X j * ev = ev * (ρ j ⊗ₖ (1 : Matrix N N ℂ)))
    (hY : Yc * ev = y • ev) (hΓ : Γ * ev = ε • ev) (Ξ : Matrix K (V × G) ℂ)
    (hdef : endpointAncDefect ρ X Yc Γ y ε Ξ = 0)
    (hpos : ((endpointAncCoefficient ev Ξ)ᴴ * endpointAncCoefficient ev Ξ).PosDef)
    (S : Matrix N E ℂ) (hS : Function.Surjective S.mulVec) (hG : Fintype.card G = 3) :
    ((allocationResidual S (endpointAncCoefficient ev Ξ)).trace = 0 ↔
      Function.Surjective Ξ.mulVec) ∧
    (Function.Surjective Ξ.mulVec ↔ Fintype.card N = 3) := by
  obtain ⟨-, h1, -, h3⟩ := source_native_endpoint_allocation ρ hirr X Yc Γ y ε ev hev1 hev2
    hX hY hΓ Ξ hdef hpos S hS
  have hGr : (Sᴴ * S).rank = Fintype.card N := by
    rw [Matrix.rank_conjTranspose_mul_self, ← endpointAlloc_surjective_iff_rank]
    exact hS
  rw [hGr, hG] at h3
  exact ⟨h1, h3⟩

end SourceNative

end EndpointAncestryAllocation
end RenewalGeometry
