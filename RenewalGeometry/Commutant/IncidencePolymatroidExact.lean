/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.Bicommutant
import RenewalGeometry.StandardModel.WeakResetGenerationExact

/-!
# The incidence rank polymatroid and source-minimal incidence skeletons

`thm:incidence-polymatroid` and `cor:minimal-incidence-skeleton` of the
spacetime–gauge duality paper.

## Abstract setting

The paper fixes a non-incidence algebra `𝒜₀`, a finite incidence bank `E` with
operators `Y_e`, and puts `M(S) = C*(𝒜₀, Y_e, Y_e^* : e ∈ S)'`.  Every such
commutant is of the form `M(S) = M₀ ⊓ ⨅_{e ∈ S} ker D_e` with `M₀ = 𝒜₀'` and
`D_e X = ([Y_e, X], [Y_e^*, X])` (the matrix bridge `matCommutant_union_eq` below
records this identity), and the polymatroid argument uses nothing else.  We therefore
work with an arbitrary finite-dimensional complex inner product space `H`, a subspace
`M₀`, and arbitrary linear constraint maps `D e : H →ₗ W e`:

* `enlargedCommutant M₀ D S = M₀ ⊓ constraintKer D S` is `M(S)`;
* `fullCommutant M₀ D = M(E)` (`S = univ`) and `residualSpace M₀ D = M₀ ⊓ M(E)ᗮ` is `V`;
* `residualMap M₀ D e` is `D_e` restricted to `V`; on `V` the constraint ranges
  `R_e = Ran D_e^*`, the rank function `f(S) = dim ∑_{e∈S} R_e` (`incidenceRank`) and the
  Gram operator `G_S = ∑_{e∈S} D_e^* D_e` (`incidenceGram`) are defined for any family
  of maps on a finite-dimensional inner product space.

## Results

* `ker_incidenceGram`: `Ker G_S = ⋂_{e∈S} Ker D_e`;
* `constraintKer_eq_orthogonal`: `⋂ Ker D_e = (∑ R_e)ᗮ`;
* `incidenceRank_eq_finrank_range_gram`: `f(S) = rank G_S`;
* `incidenceRank_add_finrank_constraintKer`: `f(S) = n − dim Ker G_S`;
* `incidenceRank_empty`, `incidenceRank_mono`, `incidenceRank_submodular`:
  `f` is normalized, monotone and submodular (`eq:incidence-submodular`);
* `enlargedCommutant_eq_sup`, `inner_fullCommutant_residual`,
  `enlargedCommutant_inf_residual_eq_map_ker`: `M(S) = M ⊕ Ker G_S` orthogonally
  (`eq:incidence-kernel`), with `M(S) ∩ V` the kernel of `G_S` on `V`;
* `incidence_polymatroid`: the assembled statement of `thm:incidence-polymatroid`;
* `essential_iff_incidenceRank_lt`: `e` essential (deleting it strictly enlarges the
  commutant) iff `f(E ∖ {e}) < n` (`eq:essential-incidence`);
* `exists_minimal_skeleton`: an inclusion-minimal `S` with `M(S) = M(E)` exists and
  has at most `n` members (`cor:minimal-incidence-skeleton`), via
  `card_le_incidenceRank` (a bank all of whose members are essential has at most
  `f(S)` members);
* `NonmatroidSkeleton`: the appendix example `ex:nonmatroid-skeleton` on `ℂ³`
  with `Y_a = E₁₂ + E₂₃`, `Y_b = E₁₂`, `Y_c = E₂₃`: `{a}` and `{b, c}` are both
  inclusion-minimal with scalar commutant, so minimal skeletons can have unequal
  cardinality (`minimal_skeletons_unequal_card`).
-/

open Module Submodule

namespace RenewalGeometry
namespace IncidencePolymatroid

variable {ι : Type*} [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {W : ι → Type*} [∀ e, NormedAddCommGroup (W e)] [∀ e, InnerProductSpace ℂ (W e)]
  [∀ e, FiniteDimensional ℂ (W e)]

/-! ### The rank polymatroid of a family of constraint maps -/

/-- The constraint range `R(S) = ∑_{e ∈ S} Ran D_e^*`. -/
noncomputable def constraintRange (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) : Submodule ℂ V :=
  S.sup fun e => LinearMap.range (LinearMap.adjoint (D e))

/-- The incidence rank function `f(S) = dim_ℂ R(S)` (`eq:incidence-rank`). -/
noncomputable def incidenceRank (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) : ℕ :=
  finrank ℂ (constraintRange D S)

/-- The incidence Gram operator `G_S = ∑_{e ∈ S} D_e^* D_e` (`eq:incidence-forms`,
without the immaterial factor `1/2`). -/
noncomputable def incidenceGram (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) : V →ₗ[ℂ] V :=
  ∑ e ∈ S, (LinearMap.adjoint (D e)) ∘ₗ (D e)

/-- The joint constraint kernel `⋂_{e ∈ S} Ker D_e`. -/
def constraintKer (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) : Submodule ℂ V :=
  S.inf fun e => LinearMap.ker (D e)

theorem mem_constraintKer {D : ∀ e, V →ₗ[ℂ] W e} {S : Finset ι} {x : V} :
    x ∈ constraintKer D S ↔ ∀ e ∈ S, D e x = 0 := by
  unfold constraintKer
  rw [Finset.inf_eq_iInf]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]

/-- Orthogonal complement of a finite supremum of subspaces. -/
theorem finset_sup_orthogonal (K : ι → Submodule ℂ V) (S : Finset ι) :
    (S.sup K)ᗮ = S.inf fun e => (K e)ᗮ := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.sup_empty, Finset.inf_empty, Submodule.bot_orthogonal_eq_top]
  | insert a s _ ih =>
    rw [Finset.sup_insert, Finset.inf_insert, ← Submodule.inf_orthogonal, ih]

/-- `Ker D_e = (Ran D_e^*)ᗮ`. -/
theorem ker_eq_orthogonal_range_adjoint {e : ι} (A : V →ₗ[ℂ] W e) :
    LinearMap.ker A = (LinearMap.range (LinearMap.adjoint A))ᗮ := by
  rw [LinearMap.orthogonal_range, LinearMap.adjoint_adjoint]

/-- `⋂_{e∈S} Ker D_e = (∑_{e∈S} Ran D_e^*)ᗮ`. -/
theorem constraintKer_eq_orthogonal (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) :
    constraintKer D S = (constraintRange D S)ᗮ := by
  rw [constraintRange, finset_sup_orthogonal, constraintKer]
  exact Finset.inf_congr rfl fun e _ => ker_eq_orthogonal_range_adjoint (D e)

/-- The quadratic form of `G_S` is `∑_{e∈S} ‖D_e x‖²`. -/
theorem inner_incidenceGram (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) (x : V) :
    inner ℂ x (incidenceGram D S x) = ∑ e ∈ S, ((‖D e x‖ : ℂ)) ^ 2 := by
  unfold incidenceGram
  rw [LinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  rfl

/-- `Ker G_S = ⋂_{e∈S} Ker D_e` (positive-semidefinite sum). -/
theorem ker_incidenceGram (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) :
    LinearMap.ker (incidenceGram D S) = constraintKer D S := by
  ext x
  rw [LinearMap.mem_ker, mem_constraintKer]
  constructor
  · intro h
    have h1 : inner ℂ x (incidenceGram D S x) = 0 := by rw [h, inner_zero_right]
    rw [inner_incidenceGram] at h1
    have h2 : ((∑ e ∈ S, ‖D e x‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [Complex.ofReal_sum]
      simp only [Complex.ofReal_pow]
      exact h1
    have h3 := Complex.ofReal_eq_zero.mp h2
    intro e he
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun e _ => sq_nonneg (‖D e x‖)).mp h3 e he
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)
  · intro h
    unfold incidenceGram
    rw [LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun e he => by rw [LinearMap.comp_apply, h e he, map_zero]

/-- `f(S) + dim ⋂ Ker D_e = n` (`eq:incidence-kernel`, rank form). -/
theorem incidenceRank_add_finrank_constraintKer (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) :
    incidenceRank D S + finrank ℂ (constraintKer D S) = finrank ℂ V := by
  rw [constraintKer_eq_orthogonal]
  exact Submodule.finrank_add_finrank_orthogonal _

/-- `f(S) = rank G_S`. -/
theorem incidenceRank_eq_finrank_range_gram (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) :
    incidenceRank D S = finrank ℂ (LinearMap.range (incidenceGram D S)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (incidenceGram D S)
  rw [ker_incidenceGram] at h1
  have h2 := incidenceRank_add_finrank_constraintKer D S
  omega

theorem incidenceRank_le (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) :
    incidenceRank D S ≤ finrank ℂ V :=
  Submodule.finrank_le _

/-- `f(∅) = 0` (normalization). -/
theorem incidenceRank_empty (D : ∀ e, V →ₗ[ℂ] W e) : incidenceRank D ∅ = 0 := by
  unfold incidenceRank constraintRange
  rw [Finset.sup_empty, finrank_bot]

/-- Monotonicity of `f`. -/
theorem incidenceRank_mono (D : ∀ e, V →ₗ[ℂ] W e) {S T : Finset ι} (h : S ⊆ T) :
    incidenceRank D S ≤ incidenceRank D T :=
  Submodule.finrank_mono (Finset.sup_mono h)

theorem constraintRange_union (D : ∀ e, V →ₗ[ℂ] W e) (S T : Finset ι) :
    constraintRange D (S ∪ T) = constraintRange D S ⊔ constraintRange D T :=
  Finset.sup_union

theorem constraintRange_inter_le (D : ∀ e, V →ₗ[ℂ] W e) (S T : Finset ι) :
    constraintRange D (S ∩ T) ≤ constraintRange D S ⊓ constraintRange D T :=
  le_inf (Finset.sup_mono Finset.inter_subset_left) (Finset.sup_mono Finset.inter_subset_right)

/-- **Submodularity** `f(S) + f(T) ≥ f(S ∪ T) + f(S ∩ T)` (`eq:incidence-submodular`). -/
theorem incidenceRank_submodular (D : ∀ e, V →ₗ[ℂ] W e) (S T : Finset ι) :
    incidenceRank D (S ∪ T) + incidenceRank D (S ∩ T) ≤ incidenceRank D S + incidenceRank D T := by
  unfold incidenceRank
  have h := Submodule.finrank_sup_add_finrank_inf_eq (constraintRange D S) (constraintRange D T)
  rw [← h, constraintRange_union]
  exact Nat.add_le_add_left (Submodule.finrank_mono (constraintRange_inter_le D S T)) _

/-- The exactness criterion: the joint constraint kernel vanishes iff `f(S) = n`. -/
theorem constraintKer_eq_bot_iff (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι) :
    constraintKer D S = ⊥ ↔ incidenceRank D S = finrank ℂ V := by
  have h := incidenceRank_add_finrank_constraintKer D S
  rw [← Submodule.finrank_eq_zero]
  omega

/-- If `R_e ⊄ R(S ∖ {e})` for every `e ∈ S` (every member strictly raises the rank),
then `|S| ≤ f(S)`: the constraint ranges added one by one form a strictly increasing
chain of subspaces. -/
theorem card_le_incidenceRank (D : ∀ e, V →ₗ[ℂ] W e) (S : Finset ι)
    (h : ∀ e ∈ S, incidenceRank D (S.erase e) < incidenceRank D S) :
    S.card ≤ incidenceRank D S := by
  -- every `e ∈ S` has `R_e ⊄ R(S ∖ {e})`
  have hnot : ∀ e ∈ S,
      ¬ LinearMap.range (LinearMap.adjoint (D e)) ≤ constraintRange D (S.erase e) := by
    intro e he hle
    have heq : constraintRange D S = constraintRange D (S.erase e) := by
      unfold constraintRange
      conv_lhs => rw [← Finset.insert_erase he, Finset.sup_insert]
      exact sup_eq_right.mpr hle
    have := h e he
    unfold incidenceRank at this
    rw [heq] at this
    exact lt_irrefl _ this
  -- chain: for every `T ⊆ S`, `|T| ≤ f(T)`
  have key : ∀ T : Finset ι, T ⊆ S → T.card ≤ incidenceRank D T := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert a T haT ih =>
      intro hsub
      have haS : a ∈ S := hsub (Finset.mem_insert_self a T)
      have hTS : T ⊆ S := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hTS' : T ⊆ S.erase a := fun x hx =>
        Finset.mem_erase.mpr ⟨fun hxa => haT (hxa ▸ hx), hTS hx⟩
      have hlt : constraintRange D T < constraintRange D (insert a T) := by
        refine lt_of_le_of_ne (Finset.sup_mono (Finset.subset_insert a T)) ?_
        intro heq
        apply hnot a haS
        refine le_trans ?_ (Finset.sup_mono hTS')
        have heq' : constraintRange D (insert a T)
            = LinearMap.range (LinearMap.adjoint (D a)) ⊔ constraintRange D T :=
          Finset.sup_insert
        show LinearMap.range (LinearMap.adjoint (D a)) ≤ constraintRange D T
        rw [heq, heq']
        exact le_sup_left
      have := Submodule.finrank_lt_finrank_of_lt hlt
      rw [Finset.card_insert_of_notMem haT]
      unfold incidenceRank
      have := ih hTS
      unfold incidenceRank at this
      omega
  exact key S (Finset.Subset.refl S)

/-! ### The commutant decomposition `M(S) = M ⊕ Ker G_S` -/

section Commutant

variable [Fintype ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- The enlarged commutant `M(S) = M₀ ⊓ ⋂_{e ∈ S} Ker D_e`. -/
noncomputable def enlargedCommutant (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e) (S : Finset ι) :
    Submodule ℂ H :=
  M₀ ⊓ constraintKer D S

/-- The full commutant `M = M(E)`. -/
noncomputable def fullCommutant (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e) : Submodule ℂ H :=
  enlargedCommutant M₀ D Finset.univ

/-- The residual test space `V = M₀ ⊓ Mᗮ`. -/
noncomputable def residualSpace (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e) : Submodule ℂ H :=
  M₀ ⊓ (fullCommutant M₀ D)ᗮ

/-- The constraint map `D_e` restricted to the residual space `V`. -/
noncomputable def residualMap (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e) (e : ι) :
    residualSpace M₀ D →ₗ[ℂ] W e :=
  (D e).comp (residualSpace M₀ D).subtype

theorem mem_enlargedCommutant {M₀ : Submodule ℂ H} {D : ∀ e, H →ₗ[ℂ] W e} {S : Finset ι}
    {x : H} : x ∈ enlargedCommutant M₀ D S ↔ x ∈ M₀ ∧ ∀ e ∈ S, D e x = 0 := by
  rw [enlargedCommutant, Submodule.mem_inf, mem_constraintKer]

/-- `M ⊆ M(S)`. -/
theorem fullCommutant_le (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e) (S : Finset ι) :
    fullCommutant M₀ D ≤ enlargedCommutant M₀ D S :=
  inf_le_inf_left _ (Finset.inf_mono (Finset.subset_univ S))

theorem enlargedCommutant_le_base (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e)
    (S : Finset ι) : enlargedCommutant M₀ D S ≤ M₀ :=
  inf_le_left

/-- `M(S) ⊓ V = M(S) ⊓ Mᗮ`. -/
theorem enlargedCommutant_inf_residual (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e)
    (S : Finset ι) :
    enlargedCommutant M₀ D S ⊓ residualSpace M₀ D
      = enlargedCommutant M₀ D S ⊓ (fullCommutant M₀ D)ᗮ := by
  rw [residualSpace, ← inf_assoc, inf_eq_left.mpr (enlargedCommutant_le_base M₀ D S)]

/-- **The orthogonal decomposition** `M(S) = M ⊕ (M(S) ∩ V)` (`eq:incidence-kernel`). -/
theorem enlargedCommutant_eq_sup (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e) (S : Finset ι) :
    enlargedCommutant M₀ D S
      = fullCommutant M₀ D ⊔ (enlargedCommutant M₀ D S ⊓ residualSpace M₀ D) := by
  rw [enlargedCommutant_inf_residual, inf_comm (enlargedCommutant M₀ D S),
    ← sup_inf_assoc_of_le _ (fullCommutant_le M₀ D S),
    Submodule.sup_orthogonal_of_hasOrthogonalProjection, top_inf_eq]

/-- The two summands are orthogonal. -/
theorem inner_fullCommutant_residual (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e)
    (S : Finset ι) {x y : H} (hx : x ∈ fullCommutant M₀ D)
    (hy : y ∈ enlargedCommutant M₀ D S ⊓ residualSpace M₀ D) : inner ℂ x y = 0 :=
  Submodule.inner_right_of_mem_orthogonal hx hy.2.2

theorem fullCommutant_inf_residual_eq_bot (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e)
    (S : Finset ι) :
    fullCommutant M₀ D ⊓ (enlargedCommutant M₀ D S ⊓ residualSpace M₀ D) = ⊥ := by
  rw [enlargedCommutant_inf_residual]
  refine le_bot_iff.mp ?_
  calc fullCommutant M₀ D ⊓ (enlargedCommutant M₀ D S ⊓ (fullCommutant M₀ D)ᗮ)
      ≤ fullCommutant M₀ D ⊓ (fullCommutant M₀ D)ᗮ := inf_le_inf_left _ inf_le_right
    _ = ⊥ := Submodule.inf_orthogonal_eq_bot _

/-- `M(S) ∩ V` is the joint constraint kernel of the restricted maps, i.e. the kernel
of `G_S` on `V`. -/
theorem enlargedCommutant_inf_residual_eq_map_ker (M₀ : Submodule ℂ H)
    (D : ∀ e, H →ₗ[ℂ] W e) (S : Finset ι) :
    enlargedCommutant M₀ D S ⊓ residualSpace M₀ D
      = (constraintKer (residualMap M₀ D) S).map (residualSpace M₀ D).subtype := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨hxM, hxV⟩
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    rw [mem_constraintKer]
    intro e he
    exact (mem_enlargedCommutant.mp hxM).2 e he
  · rintro ⟨⟨y, hyV⟩, hy, rfl⟩
    refine ⟨mem_enlargedCommutant.mpr ⟨hyV.1, fun e he => ?_⟩, hyV⟩
    exact mem_constraintKer.mp hy e he

theorem enlargedCommutant_inf_residual_eq_map_ker_gram (M₀ : Submodule ℂ H)
    (D : ∀ e, H →ₗ[ℂ] W e) (S : Finset ι) :
    enlargedCommutant M₀ D S ⊓ residualSpace M₀ D
      = (LinearMap.ker (incidenceGram (residualMap M₀ D) S)).map
          (residualSpace M₀ D).subtype := by
  rw [ker_incidenceGram, enlargedCommutant_inf_residual_eq_map_ker]

/-- `dim (M(S) ∩ V) = dim Ker G_S`. -/
theorem finrank_enlargedCommutant_inf_residual (M₀ : Submodule ℂ H)
    (D : ∀ e, H →ₗ[ℂ] W e) (S : Finset ι) :
    finrank ℂ ↥(enlargedCommutant M₀ D S ⊓ residualSpace M₀ D)
      = finrank ℂ (constraintKer (residualMap M₀ D) S) := by
  rw [enlargedCommutant_inf_residual_eq_map_ker, Submodule.finrank_map_subtype_eq]

/-- **The incidence rank polymatroid** (`thm:incidence-polymatroid`, with
`n = dim V`, `f = incidenceRank`, `G_S = incidenceGram` of the restricted maps):
`f(S) = rank G_S = n − dim (M(S) ∩ V)`, `M(S) = M ⊕ (M(S) ∩ V)` orthogonally with
`M(S) ∩ V = Ker G_S`, and `f` is normalized, monotone and submodular. -/
theorem incidence_polymatroid (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e) (S : Finset ι) :
    incidenceRank (residualMap M₀ D) S
        = finrank ℂ (LinearMap.range (incidenceGram (residualMap M₀ D) S)) ∧
    incidenceRank (residualMap M₀ D) S
        + finrank ℂ ↥(enlargedCommutant M₀ D S ⊓ residualSpace M₀ D)
        = finrank ℂ (residualSpace M₀ D) ∧
    enlargedCommutant M₀ D S
        = fullCommutant M₀ D ⊔ (enlargedCommutant M₀ D S ⊓ residualSpace M₀ D) ∧
    enlargedCommutant M₀ D S ⊓ residualSpace M₀ D
        = (LinearMap.ker (incidenceGram (residualMap M₀ D) S)).map
            (residualSpace M₀ D).subtype ∧
    (∀ x ∈ fullCommutant M₀ D, ∀ y ∈ (enlargedCommutant M₀ D S ⊓ residualSpace M₀ D),
        inner ℂ x y = 0) ∧
    incidenceRank (residualMap M₀ D) ∅ = 0 ∧
    (∀ T : Finset ι, S ⊆ T →
        incidenceRank (residualMap M₀ D) S ≤ incidenceRank (residualMap M₀ D) T) ∧
    (∀ T : Finset ι, incidenceRank (residualMap M₀ D) (S ∪ T)
        + incidenceRank (residualMap M₀ D) (S ∩ T)
        ≤ incidenceRank (residualMap M₀ D) S + incidenceRank (residualMap M₀ D) T) :=
  ⟨incidenceRank_eq_finrank_range_gram _ S,
    by rw [finrank_enlargedCommutant_inf_residual]
       exact incidenceRank_add_finrank_constraintKer _ S,
    enlargedCommutant_eq_sup M₀ D S,
    enlargedCommutant_inf_residual_eq_map_ker_gram M₀ D S,
    fun _ hx _ hy => inner_fullCommutant_residual M₀ D S hx hy,
    incidenceRank_empty _,
    fun _ h => incidenceRank_mono _ h,
    fun T => incidenceRank_submodular _ S T⟩

/-- `M(S) = M` iff `M(S) ∩ V = 0` iff `f(S) = n`. -/
theorem enlargedCommutant_eq_full_iff (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e)
    (S : Finset ι) :
    enlargedCommutant M₀ D S = fullCommutant M₀ D
      ↔ incidenceRank (residualMap M₀ D) S = finrank ℂ (residualSpace M₀ D) := by
  rw [← constraintKer_eq_bot_iff (residualMap M₀ D) S]
  have h2 : constraintKer (residualMap M₀ D) S = ⊥
      ↔ enlargedCommutant M₀ D S ⊓ residualSpace M₀ D = ⊥ := by
    rw [← Submodule.finrank_eq_zero (S := constraintKer (residualMap M₀ D) S),
      ← Submodule.finrank_eq_zero (S := enlargedCommutant M₀ D S ⊓ residualSpace M₀ D),
      finrank_enlargedCommutant_inf_residual]
  rw [h2]
  constructor
  · intro h
    rw [h, ← fullCommutant_inf_residual_eq_bot M₀ D S, h]
    exact (inf_eq_right.mpr inf_le_left).symm
  · intro h
    rw [enlargedCommutant_eq_sup M₀ D S, h, sup_bot_eq]

/-- **The essentiality criterion** (`eq:essential-incidence`): deleting `e` strictly
enlarges the commutant iff `f(E ∖ {e}) < n`. -/
theorem essential_iff_incidenceRank_lt (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e) (e : ι) :
    enlargedCommutant M₀ D (Finset.univ.erase e) ≠ fullCommutant M₀ D
      ↔ incidenceRank (residualMap M₀ D) (Finset.univ.erase e)
          < finrank ℂ (residualSpace M₀ D) := by
  rw [Ne, enlargedCommutant_eq_full_iff]
  exact ⟨fun h => lt_of_le_of_ne (incidenceRank_le _ _) h, fun h => ne_of_lt h⟩

/-- **The finite source-minimal incidence skeleton** (`cor:minimal-incidence-skeleton`):
there is an inclusion-minimal `S ⊆ E` with `M(S) = M(E)`, and any such `S` has at most
`n = dim V` members. -/
theorem exists_minimal_skeleton (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e) :
    ∃ S : Finset ι, enlargedCommutant M₀ D S = fullCommutant M₀ D ∧
      (∀ T : Finset ι, T ⊂ S → enlargedCommutant M₀ D T ≠ fullCommutant M₀ D) ∧
      S.card ≤ finrank ℂ (residualSpace M₀ D) := by
  obtain ⟨S, hS, hmin⟩ := (wellFounded_lt (α := Finset ι)).has_min
    {S : Finset ι | enlargedCommutant M₀ D S = fullCommutant M₀ D} ⟨Finset.univ, rfl⟩
  refine ⟨S, hS, fun T hT hTeq => hmin T hTeq hT, ?_⟩
  have hn : incidenceRank (residualMap M₀ D) S = finrank ℂ (residualSpace M₀ D) :=
    (enlargedCommutant_eq_full_iff M₀ D S).mp hS
  rw [← hn]
  refine card_le_incidenceRank _ S fun e he => ?_
  have hne : enlargedCommutant M₀ D (S.erase e) ≠ fullCommutant M₀ D :=
    fun h => hmin _ h (Finset.erase_ssubset he)
  rw [Ne, enlargedCommutant_eq_full_iff] at hne
  rw [hn]
  exact lt_of_le_of_ne (incidenceRank_le _ _) hne

/-- Any inclusion-minimal sufficient bank has at most `n` members. -/
theorem card_le_of_minimal_skeleton (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e)
    (S : Finset ι) (hS : enlargedCommutant M₀ D S = fullCommutant M₀ D)
    (hmin : ∀ T : Finset ι, T ⊂ S → enlargedCommutant M₀ D T ≠ fullCommutant M₀ D) :
    S.card ≤ finrank ℂ (residualSpace M₀ D) := by
  have hn : incidenceRank (residualMap M₀ D) S = finrank ℂ (residualSpace M₀ D) :=
    (enlargedCommutant_eq_full_iff M₀ D S).mp hS
  rw [← hn]
  refine card_le_incidenceRank _ S fun e he => ?_
  have hne := hmin _ (Finset.erase_ssubset he)
  rw [Ne, enlargedCommutant_eq_full_iff] at hne
  rw [hn]
  exact lt_of_le_of_ne (incidenceRank_le _ _) hne

end Commutant

/-! ### The matrix bridge: `M(S)` is a base commutant cut by commutator kernels -/

section MatrixBridge

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutator pair `X ↦ ([Y, X], [Y^*, X])` (the paper's `D_e` up to the factor
`2^{-1/2}`, which does not affect kernels). -/
def commutatorPair (Y : Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ × Matrix n n ℂ where
  toFun X := (Y * X - X * Y, Yᴴ * X - X * Yᴴ)
  map_add' X Z := by
    ext <;> simp only [Matrix.mul_add, Matrix.add_mul, Prod.fst_add, Prod.snd_add,
      Matrix.sub_apply, Matrix.add_apply] <;> ring
  map_smul' c X := by
    ext <;> simp only [Matrix.mul_smul, Matrix.smul_mul, Prod.smul_fst, Prod.smul_snd,
      RingHom.id_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] <;> ring

theorem commutatorPair_eq_zero_iff (Y X : Matrix n n ℂ) :
    commutatorPair Y X = 0 ↔ Y * X = X * Y ∧ Yᴴ * X = X * Yᴴ := by
  simp only [commutatorPair, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_eq_zero, sub_eq_zero]

/-- The paper's `M(S) = C*(𝒜₀, Y_e, Y_e^* : e ∈ S)'` is the base commutant `𝒜₀'` cut
by the commutator kernels: `M(S) = M₀ ∩ ⋂_{e∈S} Ker D_e`. -/
theorem matCommutant_union_eq {ι : Type*} (A₀ : Set (Matrix n n ℂ)) (Y : ι → Matrix n n ℂ)
    (S : Finset ι) :
    matCommutant (A₀ ∪ ⋃ e ∈ S, {Y e, (Y e)ᴴ})
      = matCommutant A₀ ∩ {X | ∀ e ∈ S, commutatorPair (Y e) X = 0} := by
  ext X
  simp only [matCommutant, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union,
    Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop,
    commutatorPair_eq_zero_iff]
  constructor
  · intro h
    refine ⟨fun a ha => h a (Or.inl ha), fun e he => ⟨?_, ?_⟩⟩
    · exact (h (Y e) (Or.inr ⟨e, he, Or.inl rfl⟩)).symm
    · exact (h (Y e)ᴴ (Or.inr ⟨e, he, Or.inr rfl⟩)).symm
  · rintro ⟨h0, h1⟩ a (ha | ⟨e, he, rfl | rfl⟩)
    · exact h0 a ha
    · exact (h1 e he).1.symm
    · exact (h1 e he).2.symm

end MatrixBridge

/-! ### Scalar commutants from generation -/

section ScalarCommutant

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Scalars commute with everything. -/
theorem scalar_mem_matCommutant (G : Set (Matrix n n ℂ)) (c : ℂ) :
    Matrix.scalar n c ∈ matCommutant G :=
  fun a _ => (Matrix.scalar_commute c (fun _ => Commute.all _ _) a).eq

/-- If a set of matrices generates the full matrix algebra, its commutant is the
scalars. -/
theorem matCommutant_eq_scalars_of_adjoin_eq_top {G : Set (Matrix n n ℂ)}
    (h : Algebra.adjoin ℂ G = ⊤) :
    matCommutant G = Set.range (Matrix.scalar n) := by
  ext X
  constructor
  · intro hX
    have hle : Algebra.adjoin ℂ G ≤ Subalgebra.centralizer ℂ {X} := by
      refine Algebra.adjoin_le fun a ha => ?_
      show a ∈ Subalgebra.centralizer ℂ {X}
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact hX a ha
    rw [h] at hle
    refine Matrix.mem_range_scalar_of_commute_single fun i j _ => ?_
    have hm : Matrix.single i j (1 : ℂ) ∈ Subalgebra.centralizer ℂ {X} := hle Algebra.mem_top
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact (hm X (Set.mem_singleton X)).symm
  · rintro ⟨c, rfl⟩
    exact scalar_mem_matCommutant G c

end ScalarCommutant

/-! ### The appendix example: minimal skeletons of unequal cardinality -/

namespace NonmatroidSkeleton

open Matrix

/-- `Y_a = E₁₂ + E₂₃`. -/
def Ya : Matrix (Fin 3) (Fin 3) ℂ := Matrix.single 0 1 1 + Matrix.single 1 2 1
/-- `Y_b = E₁₂`. -/
def Yb : Matrix (Fin 3) (Fin 3) ℂ := Matrix.single 0 1 1
/-- `Y_c = E₂₃`. -/
def Yc : Matrix (Fin 3) (Fin 3) ℂ := Matrix.single 1 2 1

/-- The incidence bank `E = {a, b, c}` indexed by `Fin 3`. -/
def Y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ := ![Ya, Yb, Yc]

/-- The generators `{Y_e, Y_e^* : e ∈ S}`. -/
def gens (S : Finset (Fin 3)) : Set (Matrix (Fin 3) (Fin 3) ℂ) :=
  {X | ∃ e ∈ S, X = Y e ∨ X = (Y e)ᴴ}

/-- `M(S) = C*(Y_e, Y_e^* : e ∈ S)'` with scalar base algebra. -/
def skel (S : Finset (Fin 3)) : Set (Matrix (Fin 3) (Fin 3) ℂ) :=
  matCommutant (gens S)

/-- The scalar matrices. -/
def scalars : Set (Matrix (Fin 3) (Fin 3) ℂ) := Set.range (Matrix.scalar (Fin 3))

theorem mem_skel {S : Finset (Fin 3)} {X : Matrix (Fin 3) (Fin 3) ℂ} :
    X ∈ skel S ↔ ∀ e ∈ S, X * Y e = Y e * X ∧ X * (Y e)ᴴ = (Y e)ᴴ * X := by
  constructor
  · intro h e he
    exact ⟨h (Y e) ⟨e, he, Or.inl rfl⟩, h (Y e)ᴴ ⟨e, he, Or.inr rfl⟩⟩
  · rintro h a ⟨e, he, rfl | rfl⟩
    · exact (h e he).1
    · exact (h e he).2

/-- Fewer incidences, larger commutant. -/
theorem skel_antitone {S T : Finset (Fin 3)} (h : S ⊆ T) : skel T ⊆ skel S := by
  intro X hX
  rw [mem_skel] at hX ⊢
  exact fun e he => hX e (h he)

theorem Y_mem_gens {S : Finset (Fin 3)} {e : Fin 3} (he : e ∈ S) : Y e ∈ gens S :=
  ⟨e, he, Or.inl rfl⟩

theorem Y_star_mem_gens {S : Finset (Fin 3)} {e : Fin 3} (he : e ∈ S) : (Y e)ᴴ ∈ gens S :=
  ⟨e, he, Or.inr rfl⟩

theorem Y_zero : Y 0 = Ya := rfl
theorem Y_one : Y 1 = Yb := rfl
theorem Y_two : Y 2 = Yc := rfl

/-- `{Y_a, Y_a^*}` generates `M₃(ℂ)`. -/
theorem adjoin_a : Algebra.adjoin ℂ (gens {0}) = ⊤ := by
  set A := Algebra.adjoin ℂ (gens {0}) with hA
  have hY : Ya ∈ A := Algebra.subset_adjoin (Y_mem_gens (Finset.mem_singleton_self 0))
  have hYs : Yaᴴ ∈ A := Algebra.subset_adjoin (Y_star_mem_gens (Finset.mem_singleton_self 0))
  -- E₁₁ = (Y Y*)(Y* Y)
  have h11 : Matrix.single 1 1 (1 : ℂ) = Ya * Yaᴴ * (Yaᴴ * Ya) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ya, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
        Matrix.conjTranspose_apply]
  have h00 : Matrix.single 0 0 (1 : ℂ) = Ya * Yaᴴ - Matrix.single 1 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ya, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
        Matrix.conjTranspose_apply]
  have h22 : Matrix.single 2 2 (1 : ℂ) = Yaᴴ * Ya - Matrix.single 1 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ya, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
        Matrix.conjTranspose_apply]
  have h01 : Matrix.single 0 1 (1 : ℂ) = Matrix.single 0 0 1 * Ya := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ya, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
  have h12 : Matrix.single 1 2 (1 : ℂ) = Matrix.single 1 1 1 * Ya := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ya, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
  have h10 : Matrix.single 1 0 (1 : ℂ) = Matrix.single 1 1 1 * Yaᴴ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ya, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
        Matrix.conjTranspose_apply]
  have h21 : Matrix.single 2 1 (1 : ℂ) = Matrix.single 2 2 1 * Yaᴴ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ya, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
        Matrix.conjTranspose_apply]
  have m11 : Matrix.single 1 1 (1 : ℂ) ∈ A := by
    rw [h11]; exact mul_mem (mul_mem hY hYs) (mul_mem hYs hY)
  have m00 : Matrix.single 0 0 (1 : ℂ) ∈ A := by
    rw [h00]; exact sub_mem (mul_mem hY hYs) m11
  have m22 : Matrix.single 2 2 (1 : ℂ) ∈ A := by
    rw [h22]; exact sub_mem (mul_mem hYs hY) m11
  have m01 : Matrix.single 0 1 (1 : ℂ) ∈ A := by rw [h01]; exact mul_mem m00 hY
  have m12 : Matrix.single 1 2 (1 : ℂ) ∈ A := by rw [h12]; exact mul_mem m11 hY
  have m10 : Matrix.single 1 0 (1 : ℂ) ∈ A := by rw [h10]; exact mul_mem m11 hYs
  have m21 : Matrix.single 2 1 (1 : ℂ) ∈ A := by rw [h21]; exact mul_mem m22 hYs
  have m02 : Matrix.single 0 2 (1 : ℂ) ∈ A := by
    have := mul_mem m01 m12
    rwa [Matrix.single_mul_single_same, one_mul] at this
  have m20 : Matrix.single 2 0 (1 : ℂ) ∈ A := by
    have := mul_mem m21 m10
    rwa [Matrix.single_mul_single_same, one_mul] at this
  refine WeakReset.top_of_units fun i j => ?_
  fin_cases i <;> fin_cases j <;> assumption

/-- `{Y_b, Y_b^*, Y_c, Y_c^*}` generates `M₃(ℂ)`. -/
theorem adjoin_bc : Algebra.adjoin ℂ (gens {1, 2}) = ⊤ := by
  set A := Algebra.adjoin ℂ (gens {1, 2}) with hA
  have h1 : (1 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by decide
  have h2 : (2 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by decide
  have m01 : Matrix.single 0 1 (1 : ℂ) ∈ A := Algebra.subset_adjoin (Y_mem_gens h1)
  have m12 : Matrix.single 1 2 (1 : ℂ) ∈ A := Algebra.subset_adjoin (Y_mem_gens h2)
  have m10 : Matrix.single 1 0 (1 : ℂ) ∈ A := by
    have := Algebra.subset_adjoin (R := ℂ) (Y_star_mem_gens h1)
    rwa [Y_one, Yb, Matrix.conjTranspose_single, star_one] at this
  have m21 : Matrix.single 2 1 (1 : ℂ) ∈ A := by
    have := Algebra.subset_adjoin (R := ℂ) (Y_star_mem_gens h2)
    rwa [Y_two, Yc, Matrix.conjTranspose_single, star_one] at this
  have m00 : Matrix.single 0 0 (1 : ℂ) ∈ A := by
    have := mul_mem m01 m10
    rwa [Matrix.single_mul_single_same, one_mul] at this
  have m11 : Matrix.single 1 1 (1 : ℂ) ∈ A := by
    have := mul_mem m10 m01
    rwa [Matrix.single_mul_single_same, one_mul] at this
  have m22 : Matrix.single 2 2 (1 : ℂ) ∈ A := by
    have := mul_mem m21 m12
    rwa [Matrix.single_mul_single_same, one_mul] at this
  have m02 : Matrix.single 0 2 (1 : ℂ) ∈ A := by
    have := mul_mem m01 m12
    rwa [Matrix.single_mul_single_same, one_mul] at this
  have m20 : Matrix.single 2 0 (1 : ℂ) ∈ A := by
    have := mul_mem m21 m10
    rwa [Matrix.single_mul_single_same, one_mul] at this
  refine WeakReset.top_of_units fun i j => ?_
  fin_cases i <;> fin_cases j <;> assumption

theorem skel_a : skel {0} = scalars :=
  matCommutant_eq_scalars_of_adjoin_eq_top adjoin_a

theorem skel_bc : skel {1, 2} = scalars :=
  matCommutant_eq_scalars_of_adjoin_eq_top adjoin_bc

theorem scalars_subset_skel (S : Finset (Fin 3)) : scalars ⊆ skel S := by
  rintro _ ⟨c, rfl⟩
  exact scalar_mem_matCommutant _ c

/-- The full bank has scalar commutant (the bank is exact). -/
theorem skel_univ : skel Finset.univ = scalars :=
  Set.Subset.antisymm (skel_a ▸ skel_antitone (Finset.subset_univ _))
    (scalars_subset_skel _)

/-- `E₃₃` commutes with `Y_b = E₁₂` and its adjoint. -/
theorem E22_mem_skel_b : Matrix.single 2 2 (1 : ℂ) ∈ skel {1} := by
  rw [mem_skel]
  intro e he
  rw [Finset.mem_singleton] at he
  subst he
  rw [Y_one, Yb, Matrix.conjTranspose_single, star_one]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

/-- `E₁₁` commutes with `Y_c = E₂₃` and its adjoint. -/
theorem E00_mem_skel_c : Matrix.single 0 0 (1 : ℂ) ∈ skel {2} := by
  rw [mem_skel]
  intro e he
  rw [Finset.mem_singleton] at he
  subst he
  rw [Y_two, Yc, Matrix.conjTranspose_single, star_one]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

/-- A diagonal matrix unit is not scalar. -/
theorem single_diag_not_scalar (i j : Fin 3) (hij : i ≠ j) :
    Matrix.single i i (1 : ℂ) ∉ scalars := by
  rintro ⟨c, hc⟩
  have h1 := congrFun (congrFun hc i) i
  have h2 := congrFun (congrFun hc j) j
  have h3 : Matrix.single i i (1 : ℂ) j j = 0 :=
    Matrix.single_apply_of_ne i i 1 j j (fun h => hij h.1)
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.single_apply_same] at h1
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, h3] at h2
  rw [h1] at h2
  exact one_ne_zero h2

/-- Every proper subset of `{a}` fails to be sufficient. -/
theorem not_sufficient_of_ssubset_a {T : Finset (Fin 3)} (hT : T ⊂ ({0} : Finset (Fin 3))) :
    skel T ≠ skel Finset.univ := by
  intro heq
  have h0 : (0 : Fin 3) ∉ T := fun h => hT.2 (Finset.singleton_subset_iff.mpr h)
  have hsub : T ⊆ {1} := by
    intro x hx
    have := hT.1 hx
    rw [Finset.mem_singleton] at this
    exact absurd (this ▸ hx) h0
  have hmem : Matrix.single 2 2 (1 : ℂ) ∈ skel T := skel_antitone hsub E22_mem_skel_b
  rw [heq, skel_univ] at hmem
  exact single_diag_not_scalar 2 0 (by decide) hmem

/-- Every proper subset of `{b, c}` fails to be sufficient. -/
theorem not_sufficient_of_ssubset_bc {T : Finset (Fin 3)}
    (hT : T ⊂ ({1, 2} : Finset (Fin 3))) : skel T ≠ skel Finset.univ := by
  intro heq
  have hmiss : (1 : Fin 3) ∉ T ∨ (2 : Fin 3) ∉ T := by
    by_contra h
    have h1 : (1 : Fin 3) ∈ T := by_contra fun h1 => h (Or.inl h1)
    have h2 : (2 : Fin 3) ∈ T := by_contra fun h2 => h (Or.inr h2)
    exact hT.2 (Finset.insert_subset h1 (Finset.singleton_subset_iff.mpr h2))
  rcases hmiss with h1 | h2
  · have hsub : T ⊆ {2} := by
      intro x hx
      have hx' := hT.1 hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl
      · exact absurd hx h1
      · exact Finset.mem_singleton_self _
    have hmem : Matrix.single 0 0 (1 : ℂ) ∈ skel T := skel_antitone hsub E00_mem_skel_c
    rw [heq, skel_univ] at hmem
    exact single_diag_not_scalar 0 1 (by decide) hmem
  · have hsub : T ⊆ {1} := by
      intro x hx
      have hx' := hT.1 hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact absurd hx h2
    have hmem : Matrix.single 2 2 (1 : ℂ) ∈ skel T := skel_antitone hsub E22_mem_skel_b
    rw [heq, skel_univ] at hmem
    exact single_diag_not_scalar 2 0 (by decide) hmem

/-- **Minimal incidence skeletons need not form matroid bases**
(`ex:nonmatroid-skeleton`): `{a}` and `{b, c}` are both inclusion-minimal sufficient
banks (`M(S) = M(E)` = scalars), of cardinalities `1 ≠ 2`. -/
theorem minimal_skeletons_unequal_card :
    skel {0} = skel Finset.univ ∧ skel {1, 2} = skel Finset.univ ∧
    (∀ T : Finset (Fin 3), T ⊂ {0} → skel T ≠ skel Finset.univ) ∧
    (∀ T : Finset (Fin 3), T ⊂ {1, 2} → skel T ≠ skel Finset.univ) ∧
    ({0} : Finset (Fin 3)).card ≠ ({1, 2} : Finset (Fin 3)).card :=
  ⟨by rw [skel_a, skel_univ], by rw [skel_bc, skel_univ],
    fun _ hT => not_sufficient_of_ssubset_a hT,
    fun _ hT => not_sufficient_of_ssubset_bc hT, by decide⟩

end NonmatroidSkeleton

end IncidencePolymatroid
end RenewalGeometry
