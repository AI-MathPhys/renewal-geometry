/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SmithPontryagin

/-!
# Smith-coordinate Pontryagin exact sequence

This file packages the circle-valued homomorphisms underlying
`thm:Smith-Pontryagin`.  A Smith diagonal with nonzero entries acts on the
paired torus coordinates, vanishes on the free source coordinates, and has a
free target quotient.  Its kernel is literally the product of the root groups
`μ_d` and the free source torus.
-/

namespace NCG
namespace SmithCoordinatePontryagin

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

/-- The circle subgroup `μ_d`, represented intrinsically as the kernel of
multiplication by `d`. -/
def RootGroup (d : ℤ) : AddSubgroup Circle :=
  AddMonoidHom.ker (d • AddMonoidHom.id Circle)

/-- Domain torus in Smith coordinates: paired coordinates followed by the
free cokernel-dual coordinates. -/
abbrev SmithDomain (paired freeSource : Type*) :=
  (paired → Circle) × (freeSource → Circle)

/-- Target torus in Smith coordinates: paired coordinates followed by the
free kernel-dual coordinates. -/
abbrev SmithCodomain (paired freeTarget : Type*) :=
  (paired → Circle) × (freeTarget → Circle)

/-- The Smith-diagonal torus homomorphism. -/
def diagonalTorusMap {paired freeSource freeTarget : Type*}
    (d : paired → ℤ) :
    SmithDomain paired freeSource →+
      SmithCodomain paired freeTarget where
  toFun x := (fun i => d i • x.1 i, 0)
  map_zero' := by ext <;> simp
  map_add' x y := by
    ext i <;> simp

/-- The Pontryagin dual of the Smith cokernel: one root group for every
nonzero Smith invariant, together with the free source torus. -/
abbrev DualCokernel (paired freeSource : Type*)
    (d : paired → ℤ) :=
  (∀ i, RootGroup (d i)) × (freeSource → Circle)

/-- Inclusion of the dual cokernel into the source torus. -/
def dualCokernelInclusion {paired freeSource : Type*}
    (d : paired → ℤ) :
    DualCokernel paired freeSource d →+
      SmithDomain paired freeSource where
  toFun x := (fun i => (x.1 i : Circle), x.2)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Projection onto the free target torus, representing the dual of the
integral kernel. -/
def dualKernelProjection {paired freeTarget : Type*} :
    SmithCodomain paired freeTarget →+ (freeTarget → Circle) where
  toFun x := x.2
  map_zero' := rfl
  map_add' _ _ := rfl

theorem circle_zsmul_surjective (d : ℤ) (hd : d ≠ 0) :
    Function.Surjective (fun x : Circle => d • x) :=
  smith_pontryagin.2.2 d hd

/-- Mathlib's PID classification supplies Smith diagonal coordinates for the
image of every integer constraint map. -/
theorem integerConstraintImage_hasSmithNormalForm {n m : ℕ}
    (A : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)) :
    Nonempty (Σ r : ℕ,
      Module.Basis.SmithNormalForm
        (LinearMap.range A) (Fin m) r) := by
  exact ⟨(LinearMap.range A).smithNormalForm
    (Pi.basisFun ℤ (Fin m))⟩

/-- A split surjection decomposes its source as kernel times target. -/
def splitSurjectionEquivKernelProd
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (s : N →ₗ[R] M)
    (hs : g.comp s = LinearMap.id) :
    M ≃ₗ[R] (LinearMap.ker g × N) where
  toFun x :=
    (⟨x - s (g x), by
      change g (x - s (g x)) = 0
      rw [map_sub, show g (s (g x)) = g x from by
        have h := LinearMap.congr_fun hs (g x)
        simpa using h]
      exact sub_self _⟩, g x)
  invFun y := y.1 + s y.2
  left_inv x := by
    dsimp
    abel
  right_inv y := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      have hgs : g (s y.2) = y.2 := by
        exact LinearMap.congr_fun hs y.2
      rw [map_add, y.1.property, zero_add, hgs]
      abel
    · dsimp
      rw [map_add, y.1.property, zero_add]
      exact LinearMap.congr_fun hs y.2
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      simp
      module
    · exact map_add g x y
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      simp
      module
    · exact map_smul g r x

/-- Since the image of an integer matrix is a free (hence projective) module,
the source splits canonically after choosing the projective right inverse. -/
noncomputable def integerConstraintSourceSplitting {n m : ℕ}
    (A : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)) :
    (Fin n → ℤ) ≃ₗ[ℤ]
      (LinearMap.ker A × LinearMap.range A) := by
  let g := A.rangeRestrict
  let hsplit :=
    g.exists_rightInverse_of_surjective A.range_rangeRestrict
  let s := Classical.choose hsplit
  let hs := Classical.choose_spec hsplit
  exact (splitSurjectionEquivKernelProd g s hs).trans
    ((LinearEquiv.ofEq (LinearMap.ker g) (LinearMap.ker A)
      (LinearMap.ker_rangeRestrict A)).prodCongr
      (LinearEquiv.refl ℤ (LinearMap.range A)))

@[simp] theorem integerConstraintSourceSplitting_snd {n m : ℕ}
    (A : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)) (x : Fin n → ℤ) :
    (integerConstraintSourceSplitting A x).2 = A.rangeRestrict x := by
  unfold integerConstraintSourceSplitting
  simp [splitSurjectionEquivKernelProd]

/-- Additive characters of a free integer module are exactly independent
circle coordinates on any chosen basis. -/
noncomputable def characterCoordinates
    {ι M : Type*} [AddCommGroup M]
    (b : Module.Basis ι ℤ M) :
    (M →+ Circle) ≃+ (ι → Circle) :=
  (addMonoidHomLequivInt (A := M) (B := Circle) ℤ).toAddEquiv.trans
    (b.constr (M' := Circle) ℤ).toAddEquiv.symm

@[simp] theorem characterCoordinates_apply
    {ι M : Type*} [AddCommGroup M]
    (b : Module.Basis ι ℤ M) (χ : M →+ Circle) (i : ι) :
    characterCoordinates b χ i = χ (b i) := by
  simp [characterCoordinates]

/-- Pontryagin duality is contravariant under an additive equivalence. -/
def characterContravariantEquiv
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) : (N →+ Circle) ≃+ (M →+ Circle) where
  toFun χ := χ.comp e.toAddMonoidHom
  invFun ψ := ψ.comp e.symm.toAddMonoidHom
  left_inv χ := by
    ext x
    simp
  right_inv ψ := by
    ext x
    simp
  map_add' _ _ := rfl

/-- Characters of a product split into the two factor characters. -/
def characterProdEquiv
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] :
    (M × N →+ Circle) ≃+ ((M →+ Circle) × (N →+ Circle)) := by
  refine
    { toFun := fun χ =>
        (χ.comp (AddMonoidHom.inl M N),
          χ.comp (AddMonoidHom.inr M N))
      invFun := fun χ =>
        { toFun := fun x => χ.1 x.1 + χ.2 x.2
          map_zero' := by simp
          map_add' := by
            intro x y
            dsimp
            rw [map_add, map_add]
            abel }
      left_inv := fun χ => by
        ext x
        change χ (x.1, 0) + χ (0, x.2) = χ x
        rw [← map_add]
        congr 1
        ext <;> simp
      right_inv := fun χ => by
        ext x <;> simp
      map_add' := fun _ _ => rfl }

/-- Split all functions on the codomain of an embedding into values on its
range and values on the complementary indices. -/
noncomputable def functionSplitAlongEmbedding
    {α β : Type*} (e : α ↪ β) :
    (β → Circle) ≃+
      ((α → Circle) × ({j : β // j ∉ Set.range e} → Circle)) := by
  classical
  refine
    { toFun := fun x => (fun i => x (e i), fun j => x j)
      invFun := fun x j => if h : j ∈ Set.range e then
          x.1 (Classical.choose h)
        else x.2 ⟨j, h⟩
      left_inv := fun x => by
        funext j
        by_cases h : j ∈ Set.range e
        · simp only [h, ↓reduceDIte]
          exact congrArg x (Classical.choose_spec h)
        · simp [h]
      right_inv := fun x => by
        apply Prod.ext
        · funext i
          simp only [Set.mem_range]
          split
          · rename_i h
            have heq := Classical.choose_spec h
            exact congrArg x.1 (e.injective heq)
          · rename_i h
            exact absurd ⟨i, rfl⟩ h
        · funext j
          simp [j.property]
      map_add' := fun x y => by
        apply Prod.ext <;> rfl }

/-- The transpose/Pontryagin-dual homomorphism induced by an integer linear
constraint map. -/
def integerConstraintDualMap {M N : Type*}
    [AddCommGroup M] [AddCommGroup N]
    (A : M →ₗ[ℤ] N) : (N →+ Circle) →+ (M →+ Circle) where
  toFun χ := χ.comp A.toAddMonoidHom
  map_zero' := rfl
  map_add' _ _ := rfl



theorem dualCokernelInclusion_injective
    {paired freeSource : Type*} (d : paired → ℤ) :
    Function.Injective
      (dualCokernelInclusion (freeSource := freeSource) d) := by
  intro x y hxy
  rcases x with ⟨x, u⟩
  rcases y with ⟨y, v⟩
  simp only [dualCokernelInclusion] at hxy
  have hfirst : (fun i => ((x i : RootGroup (d i)) : Circle)) =
      fun i => ((y i : RootGroup (d i)) : Circle) :=
    congrArg Prod.fst hxy
  have hsecond : u = v := congrArg Prod.snd hxy
  congr
  funext i
  exact Subtype.ext (congrFun hfirst i)

theorem range_dualCokernelInclusion_eq_kernel_diagonalTorusMap
    {paired freeSource freeTarget : Type*} (d : paired → ℤ) :
    Set.range (dualCokernelInclusion d) =
      {x : SmithDomain paired freeSource |
        diagonalTorusMap (freeTarget := freeTarget) d x = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    ext i
    · change d i • (y.1 i : Circle) = 0
      exact (y.1 i).property
    · rfl
  · intro hx
    have hpaired : ∀ i, d i • x.1 i = 0 := by
      intro i
      have h := congrArg (fun z => z.1 i) hx
      simpa [diagonalTorusMap] using h
    refine ⟨⟨fun i => ⟨x.1 i, ?_⟩, x.2⟩, ?_⟩
    · simpa [RootGroup] using hpaired i
    · rfl

theorem range_diagonalTorusMap_eq_kernel_dualKernelProjection
    {paired freeSource freeTarget : Type*}
    (d : paired → ℤ) (hd : ∀ i, d i ≠ 0) :
    Set.range (diagonalTorusMap
      (freeSource := freeSource) (freeTarget := freeTarget) d) =
      {y : SmithCodomain paired freeTarget |
        dualKernelProjection y = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hy
    have hyfree : y.2 = 0 := by simpa [dualKernelProjection] using hy
    choose x hx using fun i => circle_zsmul_surjective (d i) (hd i) (y.1 i)
    refine ⟨(x, 0), ?_⟩
    ext i
    · exact hx i
    · exact congrFun hyfree.symm i

theorem dualKernelProjection_surjective
    {paired freeTarget : Type*} :
    Function.Surjective
      (dualKernelProjection (paired := paired) (freeTarget := freeTarget)) := by
  intro y
  exact ⟨(0, y), rfl⟩

/-- The complete four-term exact sequence in Smith coordinates. -/
theorem smithCoordinatePontryaginExactSequence
    {paired freeSource freeTarget : Type*}
    (d : paired → ℤ) (hd : ∀ i, d i ≠ 0) :
    Function.Injective
      (dualCokernelInclusion (freeSource := freeSource) d)
    ∧ Set.range (dualCokernelInclusion (freeSource := freeSource) d) =
        {x : SmithDomain paired freeSource |
          diagonalTorusMap (freeTarget := freeTarget) d x = 0}
    ∧ Set.range (diagonalTorusMap
        (freeSource := freeSource) (freeTarget := freeTarget) d) =
        {y : SmithCodomain paired freeTarget |
          dualKernelProjection y = 0}
    ∧ Function.Surjective
        (dualKernelProjection (paired := paired)
          (freeTarget := freeTarget)) := by
  exact ⟨dualCokernelInclusion_injective d,
    range_dualCokernelInclusion_eq_kernel_diagonalTorusMap d,
    range_diagonalTorusMap_eq_kernel_dualKernelProjection d hd,
    dualKernelProjection_surjective⟩

/-- The kernel of the Smith torus map is canonically the displayed product
`T^(m-r) × Π μ_(d_i)`. -/
def diagonalKernelEquivDualCokernel
    {paired freeSource freeTarget : Type*} (d : paired → ℤ) :
    AddMonoidHom.ker
      (diagonalTorusMap
        (freeSource := freeSource) (freeTarget := freeTarget) d) ≃+
      DualCokernel paired freeSource d where
  toFun x :=
    (fun i => ⟨x.1.1 i, by
      have h := congrArg (fun z => z.1 i) x.2
      simpa [diagonalTorusMap, RootGroup] using h⟩, x.1.2)
  invFun y :=
    ⟨dualCokernelInclusion d y, by
      ext i
      · change d i • (y.1 i : Circle) = 0
        exact (y.1 i).property
      · rfl⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    rcases y with ⟨y, u⟩
    rfl
  map_add' _ _ := rfl

/-- Each root factor has the concrete manuscript description `x = k/d`. -/
theorem mem_rootGroup_iff_integer_division (d : ℤ) (hd : d ≠ 0)
    (x : Circle) :
    x ∈ RootGroup d ↔
      ∃ k : ℤ,
        x = (((k : ℝ) / (d : ℝ) : ℝ) : Circle) := by
  change d • x = 0 ↔ _
  exact smith_pontryagin.2.1 d x hd

/-- A Smith presentation of a torus homomorphism.  For an integer matrix this
is the torus map induced by the two unimodular Smith basis changes. -/
structure TorusSmithPresentation
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) where
  paired : Type
  freeSource : Type
  freeTarget : Type
  invariant : paired → ℤ
  invariant_ne_zero : ∀ i, invariant i ≠ 0
  sourceCoordinates : G ≃+ SmithDomain paired freeSource
  targetCoordinates : H ≃+ SmithCodomain paired freeTarget
  diagonalizes : ∀ x,
    targetCoordinates (f x) =
      diagonalTorusMap
        (freeSource := freeSource) (freeTarget := freeTarget)
        invariant (sourceCoordinates x)

/-- Every integer matrix induces the Smith torus presentation used by the
coordinate-free exact-sequence theorem. -/
noncomputable def integerConstraintTorusSmithPresentation {n m : ℕ}
    (A : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)) :
    TorusSmithPresentation (integerConstraintDualMap A) := by
  let snfData := (LinearMap.range A).smithNormalForm
    (Pi.basisFun ℤ (Fin m))
  let r := snfData.1
  let S := snfData.2
  let kerData := (LinearMap.ker A).basisOfPid
    (Pi.basisFun ℤ (Fin n))
  let k := kerData.1
  let bK := kerData.2
  let E := integerConstraintSourceSplitting A
  let sourceCoords :
      ((Fin m → ℤ) →+ Circle) ≃+
        ((Fin r → Circle) ×
          ({j : Fin m // j ∉ Set.range S.f} → Circle)) :=
    (characterCoordinates S.bM).trans
      (functionSplitAlongEmbedding S.f)
  let targetCoords :
      ((Fin n → ℤ) →+ Circle) ≃+
        ((Fin r → Circle) × (Fin k → Circle)) :=
    ((characterContravariantEquiv E.symm.toAddEquiv).trans
      characterProdEquiv).trans
      (((characterCoordinates bK).prodCongr
        (characterCoordinates S.bN)).trans
        (AddEquiv.prodComm
          (M := Fin k → Circle) (N := Fin r → Circle)))
  refine
    { paired := Fin r
      freeSource := {j : Fin m // j ∉ Set.range S.f}
      freeTarget := Fin k
      invariant := S.a
      invariant_ne_zero := ?_
      sourceCoordinates := sourceCoords
      targetCoordinates := targetCoords
      diagonalizes := ?_ }
  · intro i hi
    apply S.bN.ne_zero i
    apply Subtype.ext
    simpa [hi] using S.snf i
  · intro χ
    apply Prod.ext
    · funext i
      let x : Fin n → ℤ := E.symm (0, S.bN i)
      have hsplit := congrArg Prod.snd (E.apply_symm_apply (0, S.bN i))
      have hxrange : A.rangeRestrict x = S.bN i := by
        change (integerConstraintSourceSplitting A x).2 = S.bN i at hsplit
        rw [integerConstraintSourceSplitting_snd] at hsplit
        exact hsplit
      have hAx : A x = (S.bN i : Fin m → ℤ) :=
        congrArg Subtype.val hxrange
      change χ (A x) = S.a i • χ (S.bM (S.f i))
      rw [hAx, S.snf i, map_zsmul]
    · funext j
      let x : Fin n → ℤ := E.symm (bK j, 0)
      have hsplit := congrArg Prod.snd (E.apply_symm_apply (bK j, 0))
      have hxrange : A.rangeRestrict x = 0 := by
        change (integerConstraintSourceSplitting A x).2 = 0 at hsplit
        rw [integerConstraintSourceSplitting_snd] at hsplit
        exact hsplit
      have hAx : A x = 0 := congrArg Subtype.val hxrange
      change χ (A x) = 0
      rw [hAx, map_zero]

namespace TorusSmithPresentation

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
  {f : G →+ H} (P : TorusSmithPresentation f)

/-- Coordinate-free inclusion of the dual cokernel obtained from a Smith
presentation. -/
def dualCokernelMap :
    DualCokernel P.paired P.freeSource P.invariant →+ G :=
  P.sourceCoordinates.symm.toAddMonoidHom.comp
    (dualCokernelInclusion P.invariant)

/-- Coordinate-free terminal quotient map to the dual integral kernel. -/
def dualKernelMap : H →+ (P.freeTarget → Circle) :=
  dualKernelProjection.comp P.targetCoordinates.toAddMonoidHom

theorem dualCokernelMap_injective :
    Function.Injective P.dualCokernelMap := by
  intro x y hxy
  apply dualCokernelInclusion_injective P.invariant
  apply P.sourceCoordinates.symm.injective
  exact hxy

theorem range_dualCokernelMap_eq_kernel :
    Set.range P.dualCokernelMap = {x : G | f x = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply P.targetCoordinates.injective
    rw [P.diagonalizes, map_zero]
    change diagonalTorusMap P.invariant
      (P.sourceCoordinates
        (P.sourceCoordinates.symm (dualCokernelInclusion P.invariant y))) = 0
    rw [P.sourceCoordinates.apply_symm_apply]
    ext i
    · change P.invariant i • (y.1 i : Circle) = 0
      exact (y.1 i).property
    · rfl
  · intro hx
    have hcoord :
        diagonalTorusMap
          (freeTarget := P.freeTarget) P.invariant
          (P.sourceCoordinates x) = 0 := by
      rw [← P.diagonalizes, hx]
      exact map_zero P.targetCoordinates
    have hmem : P.sourceCoordinates x ∈
        Set.range (dualCokernelInclusion P.invariant) := by
      rw [range_dualCokernelInclusion_eq_kernel_diagonalTorusMap]
      exact hcoord
    rcases hmem with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply P.sourceCoordinates.injective
    simpa [dualCokernelMap] using hy

theorem range_eq_kernel_dualKernelMap :
    Set.range f = {y : H | P.dualKernelMap y = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change dualKernelProjection (P.targetCoordinates (f x)) = 0
    rw [P.diagonalizes]
    rfl
  · intro hy
    have hcoord : P.targetCoordinates y ∈
        Set.range (diagonalTorusMap
          (freeSource := P.freeSource) (freeTarget := P.freeTarget)
          P.invariant) := by
      rw [range_diagonalTorusMap_eq_kernel_dualKernelProjection
        P.invariant P.invariant_ne_zero]
      exact hy
    rcases hcoord with ⟨x, hx⟩
    refine ⟨P.sourceCoordinates.symm x, ?_⟩
    apply P.targetCoordinates.injective
    rw [P.diagonalizes]
    simpa using hx

theorem dualKernelMap_surjective :
    Function.Surjective P.dualKernelMap := by
  intro y
  refine ⟨P.targetCoordinates.symm (0, y), ?_⟩
  simp [dualKernelMap, dualKernelProjection]

/-- Coordinate-free exact sequence supplied by an integer Smith
presentation. -/
theorem pontryaginExactSequence :
    Function.Injective P.dualCokernelMap
    ∧ Set.range P.dualCokernelMap = {x : G | f x = 0}
    ∧ Set.range f = {y : H | P.dualKernelMap y = 0}
    ∧ Function.Surjective P.dualKernelMap := by
  exact ⟨P.dualCokernelMap_injective,
    P.range_dualCokernelMap_eq_kernel,
    P.range_eq_kernel_dualKernelMap,
    P.dualKernelMap_surjective⟩

/-- The coordinate-free kernel/product decomposition associated with a Smith
presentation. -/
def kernelEquivDualCokernel :
    AddMonoidHom.ker f ≃+
      DualCokernel P.paired P.freeSource P.invariant :=
  let E : AddMonoidHom.ker f ≃+
      AddMonoidHom.ker
        (diagonalTorusMap
          (freeSource := P.freeSource) (freeTarget := P.freeTarget)
          P.invariant) :=
    { toFun := fun x => ⟨P.sourceCoordinates x, by
          change diagonalTorusMap P.invariant (P.sourceCoordinates x) = 0
          rw [← P.diagonalizes, x.property]
          exact map_zero P.targetCoordinates⟩
      invFun := fun y => ⟨P.sourceCoordinates.symm y, by
          apply P.targetCoordinates.injective
          rw [P.diagonalizes, map_zero,
            P.sourceCoordinates.apply_symm_apply, y.property]⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact P.sourceCoordinates.symm_apply_apply x
      right_inv := fun y => by
        apply Subtype.ext
        exact P.sourceCoordinates.apply_symm_apply y
      map_add' := fun _ _ => by
        apply Subtype.ext
        exact map_add P.sourceCoordinates _ _ }
  E.trans (diagonalKernelEquivDualCokernel P.invariant)

/-- Full Smith--Pontryagin package once the unimodular Smith coordinates of
the integer constraint map have been supplied. -/
theorem smithPontryaginConstraintDuality :
    (Function.Injective P.dualCokernelMap
      ∧ Set.range P.dualCokernelMap = {x : G | f x = 0}
      ∧ Set.range f = {y : H | P.dualKernelMap y = 0}
      ∧ Function.Surjective P.dualKernelMap)
    ∧ Nonempty
      (AddMonoidHom.ker f ≃+
        DualCokernel P.paired P.freeSource P.invariant)
    ∧ (∀ i x, x ∈ RootGroup (P.invariant i) ↔
        ∃ k : ℤ,
          x = (((k : ℝ) / (P.invariant i : ℝ) : ℝ) : Circle)) := by
  refine ⟨P.pontryaginExactSequence,
    ⟨P.kernelEquivDualCokernel⟩, ?_⟩
  intro i x
  exact mem_rootGroup_iff_integer_division
    (P.invariant i) (P.invariant_ne_zero i) x

end TorusSmithPresentation

/-- `thm:Smith-Pontryagin` for an arbitrary integer constraint matrix.  The
Smith presentation is constructed internally rather than assumed. -/
theorem integerConstraintSmithPontryaginDuality {n m : ℕ}
    (A : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)) :
    let P := integerConstraintTorusSmithPresentation A
    (Function.Injective P.dualCokernelMap
      ∧ Set.range P.dualCokernelMap =
          {x : ((Fin m → ℤ) →+ Circle) |
            integerConstraintDualMap A x = 0}
      ∧ Set.range (integerConstraintDualMap A) =
          {y : ((Fin n → ℤ) →+ Circle) | P.dualKernelMap y = 0}
      ∧ Function.Surjective P.dualKernelMap)
    ∧ Nonempty
      (AddMonoidHom.ker (integerConstraintDualMap A) ≃+
        DualCokernel P.paired P.freeSource P.invariant)
    ∧ (∀ i x, x ∈ RootGroup (P.invariant i) ↔
        ∃ k : ℤ,
          x = (((k : ℝ) / (P.invariant i : ℝ) : ℝ) : Circle)) := by
  let P := integerConstraintTorusSmithPresentation A
  exact P.smithPontryaginConstraintDuality

end
end SmithCoordinatePontryagin
end NCG

