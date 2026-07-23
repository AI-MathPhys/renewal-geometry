/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact linear predictive retracts: classification

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:linear-predictive-presentation` — a finite linear predictive
  presentation is a surjective linear map `q : X → Q_lin` between
  finite-dimensional spaces; `K_pred = ker q` is the observationally
  null subspace and `r = dim Q_lin`;
* `def:exact-linear-retract` — exact predictive projections
  (`P² = P`, `qP = q`) and minimality (`rank P = r`);
* `thm:linear-retract-classification` — the full classification:
  rank bound and kernel inclusion, the equivalences characterising
  minimality, the bijection between minimal exact projections and
  linear complements of `K_pred`, and the unique quotient-fixed
  conjugacy between any two of them.

The classification is purely linear-algebraic, so it is proved over
an arbitrary field (the normed structure of the notes' presentation
enters only in the stability theorem, in
`NCG.Upstream.LinearStability`).
-/

namespace NCG.Upstream

open Module Submodule

variable {𝕜 : Type*} [Field 𝕜]
variable {X Q : Type*} [AddCommGroup X] [Module 𝕜 X]
  [AddCommGroup Q] [Module 𝕜 Q]
variable [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Q]

/-- **Definition `def:linear-predictive-presentation`**: the
observationally null subspace `K_pred = ker q` of a finite linear
predictive presentation (a surjective `q` between finite-dimensional
spaces; surjectivity is carried as a hypothesis below). -/
abbrev nullSpace (q : X →ₗ[𝕜] Q) : Submodule 𝕜 X :=
  LinearMap.ker q

/-- **Definition `def:exact-linear-retract`**: an exact predictive
projection for the presentation `q` — idempotent and exactly
future-sufficient (`qP = q`). -/
def IsExactProjection (q : X →ₗ[𝕜] Q) (P : X →ₗ[𝕜] X) : Prop :=
  P ∘ₗ P = P ∧ q ∘ₗ P = q

/-- **Definition `def:exact-linear-retract` (minimality)**:
`rank P = r = dim Q_lin`. -/
def IsMinimalProjection (q : X →ₗ[𝕜] Q) (P : X →ₗ[𝕜] X) : Prop :=
  IsExactProjection q P ∧
    finrank 𝕜 (LinearMap.range P) = finrank 𝕜 Q

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
theorem IsExactProjection.apply_apply {q : X →ₗ[𝕜] Q}
    {P : X →ₗ[𝕜] X} (hP : IsExactProjection q P) (x : X) :
    P (P x) = P x :=
  congrFun (congrArg DFunLike.coe hP.1) x

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
theorem IsExactProjection.q_apply {q : X →ₗ[𝕜] Q}
    {P : X →ₗ[𝕜] X} (hP : IsExactProjection q P) (x : X) :
    q (P x) = q x :=
  congrFun (congrArg DFunLike.coe hP.2) x

omit [FiniteDimensional 𝕜 Q] in
/-- **Theorem `thm:linear-retract-classification` (i, rank bound)**:
`rank P ≥ r` for every exact predictive projection. -/
theorem exactProjection_rank_ge {q : X →ₗ[𝕜] Q}
    (hq : Function.Surjective q) {P : X →ₗ[𝕜] X}
    (hP : IsExactProjection q P) :
    finrank 𝕜 Q ≤ finrank 𝕜 (LinearMap.range P) := by
  have hrange : Submodule.map q (LinearMap.range P) = ⊤ := by
    rw [← LinearMap.range_comp, hP.2, LinearMap.range_eq_top]
    exact hq
  calc finrank 𝕜 Q
      = finrank 𝕜 (Submodule.map q (LinearMap.range P)) := by
        rw [hrange]; exact (finrank_top 𝕜 Q).symm
    _ ≤ finrank 𝕜 (LinearMap.range P) := finrank_map_le q _

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
/-- **Theorem `thm:linear-retract-classification` (i, kernel
inclusion)**: `ker P ⊆ K_pred`. -/
theorem exactProjection_ker_le {q : X →ₗ[𝕜] Q} {P : X →ₗ[𝕜] X}
    (hP : IsExactProjection q P) :
    LinearMap.ker P ≤ LinearMap.ker q := by
  intro x hx
  have h1 : q (P x) = q x := hP.q_apply x
  rw [LinearMap.mem_ker.mp hx, map_zero] at h1
  exact LinearMap.mem_ker.mpr h1.symm

omit [FiniteDimensional 𝕜 Q] in
/-- **Theorem `thm:linear-retract-classification` (ii, rank =
kernel)**: for an exact predictive projection, `rank P = r` iff
`ker P = K_pred`. -/
theorem minimal_iff_ker_eq {q : X →ₗ[𝕜] Q}
    (hq : Function.Surjective q) {P : X →ₗ[𝕜] X}
    (hP : IsExactProjection q P) :
    finrank 𝕜 (LinearMap.range P) = finrank 𝕜 Q ↔
      LinearMap.ker P = LinearMap.ker q := by
  have hX : finrank 𝕜 (LinearMap.range P) + finrank 𝕜 (LinearMap.ker P)
      = finrank 𝕜 X := LinearMap.finrank_range_add_finrank_ker P
  have hXq : finrank 𝕜 (LinearMap.range q) + finrank 𝕜 (LinearMap.ker q)
      = finrank 𝕜 X := LinearMap.finrank_range_add_finrank_ker q
  have hrq : finrank 𝕜 (LinearMap.range q) = finrank 𝕜 Q := by
    rw [LinearMap.range_eq_top.mpr hq]; exact finrank_top 𝕜 Q
  constructor
  · intro hr
    refine Submodule.eq_of_le_of_finrank_le
      (exactProjection_ker_le hP) ?_
    omega
  · intro hker
    rw [hker] at hX
    omega

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
/-- **Theorem `thm:linear-retract-classification` (ii, restricted
surjectivity)**: `q` restricted to `im P` is always surjective. -/
theorem exactProjection_domRestrict_surjective {q : X →ₗ[𝕜] Q}
    (hq : Function.Surjective q) {P : X →ₗ[𝕜] X}
    (hP : IsExactProjection q P) :
    Function.Surjective (q.domRestrict (LinearMap.range P)) := by
  intro y
  obtain ⟨x, rfl⟩ := hq y
  exact ⟨⟨P x, LinearMap.mem_range_self P x⟩, hP.q_apply x⟩

omit [FiniteDimensional 𝕜 Q] in
/-- **Theorem `thm:linear-retract-classification` (ii,
isomorphism)**: for an exact predictive projection, `rank P = r` iff
`q|_{im P} : im P → Q_lin` is an isomorphism. -/
theorem minimal_iff_bijective {q : X →ₗ[𝕜] Q}
    (hq : Function.Surjective q) {P : X →ₗ[𝕜] X}
    (hP : IsExactProjection q P) :
    finrank 𝕜 (LinearMap.range P) = finrank 𝕜 Q ↔
      Function.Bijective (q.domRestrict (LinearMap.range P)) := by
  constructor
  · intro hr
    have hsurj := exactProjection_domRestrict_surjective hq hP
    refine ⟨?_, hsurj⟩
    have hsum := LinearMap.finrank_range_add_finrank_ker
      (q.domRestrict (LinearMap.range P))
    have hrng : finrank 𝕜
        (LinearMap.range (q.domRestrict (LinearMap.range P)))
        = finrank 𝕜 Q := by
      rw [LinearMap.range_eq_top.mpr hsurj]; exact finrank_top 𝕜 Q
    have hker0 : finrank 𝕜
        (LinearMap.ker (q.domRestrict (LinearMap.range P))) = 0 := by
      omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker0)
  · intro hbij
    exact (LinearEquiv.ofBijective _ hbij).finrank_eq

section Complement

variable (q : X →ₗ[𝕜] Q) (hq : Function.Surjective q)
variable (M : Submodule 𝕜 X) (hM : IsCompl M (LinearMap.ker q))

include hq hM

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
/-- For a complement `M` of the null space, `q|_M` is bijective. -/
theorem domRestrict_bijective_of_isCompl :
    Function.Bijective (q.domRestrict M) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hq' : q x = q y := hxy
    have hx0 : x - y = 0 :=
      Submodule.disjoint_def.mp hM.disjoint _ (M.sub_mem hx hy)
        (by simp [LinearMap.mem_ker, map_sub, hq'])
    exact Subtype.ext (sub_eq_zero.mp hx0)
  · intro y
    obtain ⟨x, rfl⟩ := hq y
    have hx : x ∈ M ⊔ LinearMap.ker q := by
      rw [hM.sup_eq_top]; trivial
    obtain ⟨m, hm, k, hk, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨m, hm⟩, ?_⟩
    change q m = q (m + k)
    rw [map_add, LinearMap.mem_ker.mp hk, add_zero]

/-- The isomorphism `q|_M : M ≃ Q_lin` for a complement `M`. -/
noncomputable def complEquiv : M ≃ₗ[𝕜] Q :=
  LinearEquiv.ofBijective (q.domRestrict M)
    (domRestrict_bijective_of_isCompl q hq M hM)

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
theorem q_complEquiv_symm (y : Q) :
    q ((complEquiv q hq M hM).symm y : X) = y :=
  (complEquiv q hq M hM).apply_symm_apply y

/-- **Theorem `thm:linear-retract-classification` (iii, corestricted
projection)**: `m ∘ q : X → M` with `m = (q|_M)^{-1}`. -/
noncomputable def projToCompl : X →ₗ[𝕜] M :=
  (complEquiv q hq M hM).symm.toLinearMap ∘ₗ q

/-- **Theorem `thm:linear-retract-classification` (iii, the
projection)**: `P_M = m ∘ q : X → X`. -/
noncomputable def projOfCompl : X →ₗ[𝕜] X :=
  M.subtype ∘ₗ projToCompl q hq M hM

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
theorem projOfCompl_mem (x : X) : projOfCompl q hq M hM x ∈ M :=
  ((complEquiv q hq M hM).symm (q x)).2

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
theorem q_projOfCompl (x : X) :
    q (projOfCompl q hq M hM x) = q x :=
  q_complEquiv_symm q hq M hM (q x)

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
theorem projOfCompl_of_mem {m : X} (hm : m ∈ M) :
    projOfCompl q hq M hM m = m :=
  congrArg Subtype.val
    ((complEquiv q hq M hM).symm_apply_apply ⟨m, hm⟩)

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
theorem projOfCompl_range :
    LinearMap.range (projOfCompl q hq M hM) = M := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact projOfCompl_mem q hq M hM y
  · intro m hm
    exact ⟨m, projOfCompl_of_mem q hq M hM hm⟩

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
/-- **Theorem `thm:linear-retract-classification` (iii, exactness
and minimality)**: `P_M` is a minimal exact predictive
projection. -/
theorem projOfCompl_isMinimal :
    IsMinimalProjection q (projOfCompl q hq M hM) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact LinearMap.ext fun x =>
      projOfCompl_of_mem q hq M hM (projOfCompl_mem q hq M hM x)
  · exact LinearMap.ext fun x => q_projOfCompl q hq M hM x
  · rw [projOfCompl_range]
    exact (complEquiv q hq M hM).finrank_eq

omit [FiniteDimensional 𝕜 Q] in
/-- **Theorem `thm:linear-retract-classification` (iii, kernel)**:
`ker P_M = K_pred`. -/
theorem projOfCompl_ker :
    LinearMap.ker (projOfCompl q hq M hM) = LinearMap.ker q :=
  (minimal_iff_ker_eq hq (projOfCompl_isMinimal q hq M hM).1).mp
    (projOfCompl_isMinimal q hq M hM).2

end Complement

omit [FiniteDimensional 𝕜 Q] in
/-- **Theorem `thm:linear-retract-classification` (iii, converse)**:
the image of every minimal exact predictive projection is a linear
complement of `K_pred`. -/
theorem isCompl_range_of_minimal {q : X →ₗ[𝕜] Q}
    (hq : Function.Surjective q) {P : X →ₗ[𝕜] X}
    (hP : IsMinimalProjection q P) :
    IsCompl (LinearMap.range P) (LinearMap.ker q) := by
  have hbij := (minimal_iff_bijective hq hP.1).mp hP.2
  constructor
  · rw [disjoint_iff]
    ext x
    simp only [Submodule.mem_inf, Submodule.mem_bot]
    constructor
    · rintro ⟨hxP, hxq⟩
      have h1 : q.domRestrict (LinearMap.range P) ⟨x, hxP⟩
          = q.domRestrict (LinearMap.range P) 0 := by
        change q x = q 0
        rw [LinearMap.mem_ker.mp hxq, map_zero]
      exact congrArg Subtype.val (hbij.1 h1)
    · rintro rfl
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hker : x - P x ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, hP.1.q_apply, sub_self]
    have hx2 : x = P x + (x - P x) := by abel
    rw [hx2]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self P x) hker

omit [FiniteDimensional 𝕜 Q] in
/-- **Theorem `thm:linear-retract-classification` (iii, bijection)**:
a minimal exact predictive projection equals the projection built
from its own image — so `P ↦ im P` and `M ↦ P_M` are mutually
inverse, and minimal exact projections are in bijection with linear
complements of `K_pred`. -/
theorem eq_projOfCompl_range {q : X →ₗ[𝕜] Q}
    (hq : Function.Surjective q) {P : X →ₗ[𝕜] X}
    (hP : IsMinimalProjection q P) :
    P = projOfCompl q hq (LinearMap.range P)
      (isCompl_range_of_minimal hq hP) := by
  have hcompl := isCompl_range_of_minimal hq hP
  have hbij := (minimal_iff_bijective hq hP.1).mp hP.2
  apply LinearMap.ext
  intro x
  have h1 : q.domRestrict (LinearMap.range P)
        ⟨P x, LinearMap.mem_range_self P x⟩
      = q.domRestrict (LinearMap.range P)
        ⟨projOfCompl q hq (LinearMap.range P) hcompl x,
          projOfCompl_mem q hq (LinearMap.range P) hcompl x⟩ := by
    change q (P x) = q (projOfCompl q hq (LinearMap.range P) hcompl x)
    rw [hP.1.q_apply, q_projOfCompl]
  exact congrArg Subtype.val (hbij.1 h1)

section Conjugacy

variable (q : X →ₗ[𝕜] Q) (hq : Function.Surjective q)
variable (M N : Submodule 𝕜 X)
variable (hM : IsCompl M (LinearMap.ker q))
variable (hN : IsCompl N (LinearMap.ker q))

include hq hM hN

/-- **Theorem `thm:linear-retract-classification` (iv, the
conjugacy)**: `U = (q|_N)^{-1} ∘ q|_M : M ≃ N`. -/
noncomputable def transferCompl : M ≃ₗ[𝕜] N :=
  (complEquiv q hq M hM).trans (complEquiv q hq N hN).symm

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
/-- **Theorem `thm:linear-retract-classification` (iv, quotient
fixed)**: `q ∘ U = q|_M` — the conjugacy acts trivially on the
predictive quotient. -/
theorem transferCompl_q (m : M) :
    q (transferCompl q hq M N hM hN m : X) = q (m : X) :=
  q_complEquiv_symm q hq N hN ((complEquiv q hq M hM) m)

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
/-- **Theorem `thm:linear-retract-classification` (iv,
uniqueness)**: `U` is the unique quotient-fixed linear map
`M → N`. -/
theorem transferCompl_unique (F : M →ₗ[𝕜] N)
    (hF : ∀ m : M, q (F m : X) = q (m : X)) (m : M) :
    F m = transferCompl q hq M N hM hN m :=
  (complEquiv q hq N hN).injective
    ((hF m).trans (transferCompl_q q hq M N hM hN m).symm)

omit [FiniteDimensional 𝕜 Q] [FiniteDimensional 𝕜 X] in
/-- **Theorem `thm:linear-retract-classification` (iv, conjugation
of the projections)**: `U ∘ (m_M ∘ q) = m_N ∘ q` — the conjugacy
intertwines the two minimal predictive carriers, so both realize the
same quotient dynamics. -/
theorem transferCompl_projToCompl (x : X) :
    transferCompl q hq M N hM hN (projToCompl q hq M hM x)
      = projToCompl q hq N hN x :=
  congrArg (fun y => (complEquiv q hq N hN).symm y)
    ((complEquiv q hq M hM).apply_symm_apply (q x))

end Conjugacy

end NCG.Upstream
