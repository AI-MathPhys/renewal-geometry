/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Rectangular fundamental theorem of calculus

Reusable Banach-valued calculus for physical shrinking intervention cubes.
The first lemma identifies a shrinking interval average with the derivative
of its integral primitive.  Iterating this construction is the analytic core
of the all-support Hellinger secant limit.
-/

open Filter MeasureTheory
open scoped Topology

namespace NCG

/-- The average of a continuous Banach-valued function over `[0,h]` converges
to its value at the endpoint as `h → 0`, with `h ≠ 0`.

The use of the punctured neighbourhood is intentional: it is exactly the
domain on which the normalized secant is defined. -/
theorem shrinkingIntervalAverage_tendsto
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → F) (hg : Continuous g) :
    Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, g t)
      (𝓝[≠] (0 : ℝ)) (𝓝 (g 0)) := by
  have hderiv : HasDerivAt (fun h : ℝ => ∫ t in (0 : ℝ)..h, g t)
      (g 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 0)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt
  simpa using hderiv.tendsto_slope_zero

/-- One-sided version used for physical positive side lengths. -/
theorem shrinkingIntervalAverage_tendsto_right
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → F) (hg : Continuous g) :
    Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, g t)
      (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
  (shrinkingIntervalAverage_tendsto g hg).mono_left (nhdsGT_le_nhdsNE 0)

/-- Rescaling a nondegenerate interval identifies its normalized integral with
an integral over the fixed unit interval.  This is the form that iterates over
a rectangular intervention cube. -/
theorem normalizedIntervalIntegral_eq_unit
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → F) (h : ℝ) (hh : h ≠ 0) :
    h⁻¹ • (∫ t in (0 : ℝ)..h, g t) =
      ∫ s in (0 : ℝ)..1, g (h * s) := by
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) g h
  rw [mul_zero, mul_one] at hscale
  rw [← hscale, ← smul_assoc]
  simp [hh]

/-- Iterated Bochner integral over the unit `n`-box.  `Fin.cons` exposes the
outer coordinate and leaves an `(n-1)`-box to the recursive call. -/
noncomputable def iteratedUnitBoxIntegral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :
    (n : ℕ) → ((Fin n → ℝ) → F) → F
  | 0, f => f Fin.elim0
  | n + 1, f => ∫ t in (0 : ℝ)..1,
      iteratedUnitBoxIntegral n (fun x => f (Fin.cases t x))

/-- Prepend one real coordinate to a finite real vector. -/
def prependCoordinate {n : ℕ} (head : ℝ) (tail : Fin n → ℝ) :
    Fin (n + 1) → ℝ :=
  Fin.cases head tail

@[simp]
theorem prependCoordinate_zero {n : ℕ} (head : ℝ) (tail : Fin n → ℝ) :
    prependCoordinate head tail 0 = head := rfl

@[simp]
theorem prependCoordinate_succ {n : ℕ} (head : ℝ) (tail : Fin n → ℝ)
    (i : Fin n) : prependCoordinate head tail i.succ = tail i := rfl

/-- Adjoining a continuous head coordinate to a continuous finite tail is
continuous.  Keeping this lemma explicit avoids expensive dependent-function
automation in the box-integral induction. -/
theorem continuous_prependCoordinate
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (head : X → ℝ) (tail : X → Fin n → ℝ)
    (hhead : Continuous head) (htail : Continuous tail) :
    Continuous (fun x => prependCoordinate (head x) (tail x)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa using hhead
  · intro j
    change Continuous (fun a => tail a j)
    exact (continuous_apply j).comp htail

/-- The unit box has volume one in every finite dimension. -/
@[simp]
theorem iteratedUnitBoxIntegral_const
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (c : F) :
    iteratedUnitBoxIntegral n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedUnitBoxIntegral]
      simp only [ih]
      simp

/-- A jointly continuous integrand has a continuous unit-box integral in its
external parameter. -/
theorem continuous_iteratedUnitBoxIntegral
    {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (f : X → (Fin n → ℝ) → F)
    (hf : Continuous (fun p : X × (Fin n → ℝ) => f p.1 p.2)) :
    Continuous (fun x => iteratedUnitBoxIntegral n (f x)) := by
  induction n generalizing X with
  | zero =>
      exact hf.comp (continuous_id.prodMk continuous_const)
  | succ n ih =>
      rw [show (fun x => iteratedUnitBoxIntegral (n + 1) (f x)) =
          fun x => ∫ t in (0 : ℝ)..1,
            iteratedUnitBoxIntegral n
              (fun y => f x (prependCoordinate t y)) by rfl]
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      apply ih (X := X × ℝ)
      have hmap : Continuous (fun p : (X × ℝ) × (Fin n → ℝ) =>
          (p.1.1, prependCoordinate p.1.2 p.2)) := by
        apply Continuous.prodMk
        · exact continuous_fst.comp continuous_fst
        · refine continuous_prependCoordinate _ _ ?_ ?_
          · exact continuous_snd.comp continuous_fst
          · exact continuous_snd
      change Continuous ((fun p : X × (Fin (n + 1) → ℝ) => f p.1 p.2) ∘
        fun p : (X × ℝ) × (Fin n → ℝ) =>
          (p.1.1, prependCoordinate p.1.2 p.2))
      exact hf.comp hmap

/-- Iterated unit-box integration commutes with addition. -/
theorem iteratedUnitBoxIntegral_add
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (f g : (Fin n → ℝ) → F)
    (hf : Continuous f) (hg : Continuous g) :
    iteratedUnitBoxIntegral n (fun x => f x + g x) =
      iteratedUnitBoxIntegral n f + iteratedUnitBoxIntegral n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedUnitBoxIntegral, iteratedUnitBoxIntegral,
        iteratedUnitBoxIntegral]
      have hpoint : ∀ t : ℝ,
          iteratedUnitBoxIntegral n
              (fun x => f (prependCoordinate t x) +
                g (prependCoordinate t x)) =
            iteratedUnitBoxIntegral n (fun x => f (prependCoordinate t x)) +
              iteratedUnitBoxIntegral n
                (fun x => g (prependCoordinate t x)) := by
        intro t
        have hcons : Continuous (fun x : Fin n → ℝ =>
            prependCoordinate t x) :=
          continuous_prependCoordinate (fun _ : Fin n → ℝ => t) id
            continuous_const continuous_id
        exact ih _ _ (hf.comp hcons) (hg.comp hcons)
      have heq :
          (fun t : ℝ => iteratedUnitBoxIntegral n
            (fun x => f (prependCoordinate t x) +
              g (prependCoordinate t x))) =
          fun t : ℝ =>
            iteratedUnitBoxIntegral n (fun x => f (prependCoordinate t x)) +
              iteratedUnitBoxIntegral n
                (fun x => g (prependCoordinate t x)) := funext hpoint
      change (∫ t in (0 : ℝ)..1,
          iteratedUnitBoxIntegral n
            (fun x => f (prependCoordinate t x) +
              g (prependCoordinate t x))) =
        (∫ t in (0 : ℝ)..1,
          iteratedUnitBoxIntegral n (fun x => f (prependCoordinate t x))) +
        ∫ t in (0 : ℝ)..1,
          iteratedUnitBoxIntegral n (fun x => g (prependCoordinate t x))
      rw [heq]
      rw [intervalIntegral.integral_add]
      · have hcons : Continuous (fun p : ℝ × (Fin n → ℝ) =>
            prependCoordinate p.1 p.2) :=
          continuous_prependCoordinate Prod.fst Prod.snd continuous_fst continuous_snd
        exact (continuous_iteratedUnitBoxIntegral n
          (fun t x => f (prependCoordinate t x))
          (by
            change Continuous (f ∘ fun p : ℝ × (Fin n → ℝ) =>
              prependCoordinate p.1 p.2)
            exact hf.comp hcons)).intervalIntegrable _ _
      · have hcons : Continuous (fun p : ℝ × (Fin n → ℝ) =>
            prependCoordinate p.1 p.2) :=
          continuous_prependCoordinate Prod.fst Prod.snd continuous_fst continuous_snd
        exact (continuous_iteratedUnitBoxIntegral n
          (fun t x => g (prependCoordinate t x))
          (by
            change Continuous (g ∘ fun p : ℝ × (Fin n → ℝ) =>
              prependCoordinate p.1 p.2)
            exact hg.comp hcons)).intervalIntegrable _ _

/-- Membership in the closed unit box. -/
def InUnitBox {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i, x i ∈ Set.uIcc (0 : ℝ) 1

/-- Iterated integration over a unit box has operator norm at most one for
the supremum norm. -/
theorem norm_iteratedUnitBoxIntegral_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (f : (Fin n → ℝ) → F) (C : ℝ)
    (hf : Continuous f) (hbound : ∀ x, InUnitBox x → ‖f x‖ ≤ C) :
    ‖iteratedUnitBoxIntegral n f‖ ≤ C := by
  induction n with
  | zero =>
      exact hbound Fin.elim0 (fun i => Fin.elim0 i)
  | succ n ih =>
      rw [iteratedUnitBoxIntegral]
      have houter : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          ‖iteratedUnitBoxIntegral n
            (fun x => f (prependCoordinate t x))‖ ≤ C := by
        intro t ht
        have hcons : Continuous (fun x : Fin n → ℝ =>
            prependCoordinate t x) :=
          continuous_prependCoordinate (fun _ : Fin n → ℝ => t) id
            continuous_const continuous_id
        apply ih (fun x => f (prependCoordinate t x)) (hf.comp hcons)
        intro x hx
        apply hbound (prependCoordinate t x)
        intro i
        refine Fin.cases ?_ ?_ i
        · exact ht
        · intro j
          exact hx j
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := C) (f := fun t =>
          iteratedUnitBoxIntegral n (fun x => f (prependCoordinate t x)))
        (fun t ht => houter t (Set.uIoc_subset_uIcc ht))
      change ‖∫ t in (0 : ℝ)..1,
        iteratedUnitBoxIntegral n (fun x => f (prependCoordinate t x))‖ ≤ C
      simpa only [sub_zero, abs_one, mul_one] using hi

/-- Unit-box average after independently scaling every coordinate. -/
noncomputable def scaledUnitBoxAverage
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {n : ℕ} (g : (Fin n → ℝ) → F) (h : Fin n → ℝ) : F :=
  iteratedUnitBoxIntegral n (fun s => g (fun i => h i * s i))

/-- A continuous integrand has a continuous independently scaled unit-box
average. -/
theorem continuous_scaledUnitBoxAverage
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {n : ℕ} (g : (Fin n → ℝ) → F) (hg : Continuous g) :
    Continuous (scaledUnitBoxAverage g) := by
  change Continuous (fun h : Fin n → ℝ =>
    iteratedUnitBoxIntegral n (fun s => g (fun i => h i * s i)))
  apply continuous_iteratedUnitBoxIntegral n
    (fun (h : Fin n → ℝ) (s : Fin n → ℝ) =>
      g (fun i => h i * s i))
  apply hg.comp
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp continuous_fst).mul
    ((continuous_apply i).comp continuous_snd)

/-- Arbitrary-side-length rectangular averaging converges to the mixed
derivative at the base point.  No bounded-aspect-ratio assumption is needed. -/
theorem scaledUnitBoxAverage_tendsto_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {n : ℕ} (g : (Fin n → ℝ) → F) (hg : Continuous g) :
    Tendsto (scaledUnitBoxAverage g)
      (𝓝 (0 : Fin n → ℝ)) (𝓝 (g 0)) := by
  have hc : Tendsto (scaledUnitBoxAverage g)
      (𝓝 (0 : Fin n → ℝ))
      (𝓝 (scaledUnitBoxAverage g (0 : Fin n → ℝ))) :=
    (continuous_scaledUnitBoxAverage g hg).continuousAt
  have hz : scaledUnitBoxAverage g (0 : Fin n → ℝ) = g 0 := by
    rw [scaledUnitBoxAverage]
    simp only [Pi.zero_apply, zero_mul, iteratedUnitBoxIntegral_const]
    apply congrArg g
    funext i
    rfl
  rw [hz] at hc
  exact hc

/-! ## Ordered mixed derivatives and recursive cube secants -/

/-- Remove the head coordinate of a finite real vector. -/
def dropHead {n : ℕ} (x : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => x i.succ

/-- The alternating secant of a coordinate box, recursively split along its
head coordinate.  This is the ordered form of the Boolean Möbius sum. -/
def orderedCubeSecant
    {F : Type*} [AddCommGroup F] :
    (n : ℕ) → ((Fin n → ℝ) → F) → (Fin n → ℝ) → F
  | 0, f, _h => f Fin.elim0
  | n + 1, f, h =>
      orderedCubeSecant n
          (fun y => f (prependCoordinate (h 0) y)) (dropHead h) -
      orderedCubeSecant n
          (fun y => f (prependCoordinate 0 y)) (dropHead h)

/-- Vertex of the coordinate cube selected by a Boolean indicator vector. -/
def booleanCubeVertex {n : ℕ} (h : Fin n → ℝ) (b : Fin n → Bool) :
    Fin n → ℝ :=
  fun i => if b i = true then h i else 0

/-- Boolean form of the top cube Möbius coefficient.  A selected coordinate
contributes sign `+1` and an unselected coordinate contributes sign `-1`. -/
def signedBooleanCubeSecant
    {F : Type*} [AddCommGroup F]
    (n : ℕ) (f : (Fin n → ℝ) → F) (h : Fin n → ℝ) : F :=
  ∑ b : Fin n → Bool,
    (∏ i, if b i = true then (1 : ℤ) else -1) •
      f (booleanCubeVertex h b)

/-- The recursively ordered cube secant is exactly its Boolean alternating
vertex sum. -/
theorem orderedCubeSecant_eq_signedBooleanCubeSecant
    {F : Type*} [AddCommGroup F]
    (n : ℕ) (f : (Fin n → ℝ) → F) (h : Fin n → ℝ) :
    orderedCubeSecant n f h = signedBooleanCubeSecant n f h := by
  induction n with
  | zero =>
      simp [orderedCubeSecant, signedBooleanCubeSecant, booleanCubeVertex]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      rw [orderedCubeSecant]
      rw [ih, ih]
      simp only [signedBooleanCubeSecant]
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))]
      simp only [Fintype.sum_prod_type, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, booleanCubeVertex,
        prependCoordinate, dropHead]
      simp [signedBooleanCubeSecant, sub_eq_add_neg]
      apply congrArg₂ (· + ·)
      · apply Fintype.sum_congr
        intro b
        apply congrArg ((∏ i, if b i = true then (1 : ℤ) else -1) • ·)
        apply congrArg f
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [booleanCubeVertex, prependCoordinate, Fin.consEquiv]
        · intro j
          simp [booleanCubeVertex, prependCoordinate, dropHead, Fin.consEquiv]
      · apply congrArg Neg.neg
        apply Fintype.sum_congr
        intro b
        apply congrArg ((∏ i, if b i = true then (1 : ℤ) else -1) • ·)
        apply congrArg f
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [booleanCubeVertex, prependCoordinate, Fin.consEquiv]
        · intro j
          simp [booleanCubeVertex, prependCoordinate, dropHead, Fin.consEquiv]

/-- The finite subset represented by a Boolean coordinate vector. -/
def trueCoordinateSet {n : ℕ} (b : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => b i = true)

/-- Boolean coordinate vectors and subsets of `Fin n` are canonically
equivalent. -/
def boolVectorFinsetEquiv (n : ℕ) :
    (Fin n → Bool) ≃ Finset (Fin n) where
  toFun := trueCoordinateSet
  invFun := fun B i => decide (i ∈ B)
  left_inv := by
    intro b
    funext i
    simp [trueCoordinateSet]
  right_inv := by
    intro B
    ext i
    simp [trueCoordinateSet]

/-- The product sign of a Boolean vertex is the usual Möbius sign determined
by the number of unselected coordinates. -/
theorem booleanCubeSign_eq_mobiusSign {n : ℕ} (b : Fin n → Bool) :
    (∏ i, if b i = true then (1 : ℤ) else -1) =
      (-1 : ℤ) ^ (n - (trueCoordinateSet b).card) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i => b i = true)
  have hfalse :
      ((Finset.univ : Finset (Fin n)).filter
          (fun i => ¬ b i = true)).card =
        n - (trueCoordinateSet b).card := by
    have hc : (trueCoordinateSet b).card +
        ((Finset.univ : Finset (Fin n)).filter
          (fun i => ¬ b i = true)).card = n := by
      simpa [trueCoordinateSet] using hcard
    omega
  rw [hfalse]

/-- Vertex of the coordinate cube indexed by an ordinary finite subset. -/
def finsetCubeVertex {n : ℕ} (h : Fin n → ℝ) (B : Finset (Fin n)) :
    Fin n → ℝ :=
  fun i => if i ∈ B then h i else 0

theorem booleanCubeVertex_eq_finsetCubeVertex {n : ℕ}
    (h : Fin n → ℝ) (b : Fin n → Bool) :
    booleanCubeVertex h b = finsetCubeVertex h (trueCoordinateSet b) := by
  funext i
  simp [booleanCubeVertex, finsetCubeVertex, trueCoordinateSet]

/-- The manuscript's top Boolean Möbius coefficient for the coordinate cube. -/
def finsetCubeMobiusSecant
    {F : Type*} [AddCommGroup F]
    (n : ℕ) (f : (Fin n → ℝ) → F) (h : Fin n → ℝ) : F :=
  ∑ B : Finset (Fin n),
    (-1 : ℤ) ^ (n - B.card) • f (finsetCubeVertex h B)

theorem signedBooleanCubeSecant_eq_finsetCubeMobiusSecant
    {F : Type*} [AddCommGroup F]
    (n : ℕ) (f : (Fin n → ℝ) → F) (h : Fin n → ℝ) :
    signedBooleanCubeSecant n f h = finsetCubeMobiusSecant n f h := by
  apply Fintype.sum_equiv (boolVectorFinsetEquiv n)
  intro b
  rw [booleanCubeSign_eq_mobiusSign]
  apply congrArg ((-1 : ℤ) ^ (n - (trueCoordinateSet b).card) • ·)
  apply congrArg f
  exact booleanCubeVertex_eq_finsetCubeVertex h b

/-- The ordered secant used by rectangular FTC is exactly the subset-indexed
Möbius coefficient appearing in the manuscript. -/
theorem orderedCubeSecant_eq_finsetCubeMobiusSecant
    {F : Type*} [AddCommGroup F]
    (n : ℕ) (f : (Fin n → ℝ) → F) (h : Fin n → ℝ) :
    orderedCubeSecant n f h = finsetCubeMobiusSecant n f h :=
  (orderedCubeSecant_eq_signedBooleanCubeSecant n f h).trans
    (signedBooleanCubeSecant_eq_finsetCubeMobiusSecant n f h)

/-- An ordered `C^n` mixed-derivative tower.  Layer `k+1` is the derivative of
layer `k` in coordinate `k`; the final layer is continuous.  This is precisely
the regularity consumed by repeated rectangular FTC. -/
structure OrderedDerivativeTower
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : (Fin n → ℝ) → F) where
  layer : Fin (n + 1) → (Fin n → ℝ) → F
  layer_zero : layer 0 = f
  hasDeriv_coordinate : ∀ (k : Fin n) (x : Fin n → ℝ),
    HasDerivAt
      (fun t => layer k.castSucc (Function.update x k t))
      (layer k.succ x) (x k)
  continuous_layer : ∀ k, Continuous (layer k)

/-- Scalar multiplication transports an ordered mixed-derivative tower layer
by layer. -/
def OrderedDerivativeTower.const_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : (Fin n → ℝ) → F}
    (D : OrderedDerivativeTower n f) (c : ℝ) :
    OrderedDerivativeTower n (fun x => c • f x) where
  layer := fun k x => c • D.layer k x
  layer_zero := by
    funext x
    rw [D.layer_zero]
  hasDeriv_coordinate := by
    intro k x
    convert HasDerivAt.const_smul c (D.hasDeriv_coordinate k x) using 1
    funext t
    rfl
  continuous_layer := by
    intro k
    exact (D.continuous_layer k).const_smul c

/-- The final mixed derivative carried by an ordered derivative tower. -/
def OrderedDerivativeTower.top
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : (Fin n → ℝ) → F}
    (D : OrderedDerivativeTower n f) : (Fin n → ℝ) → F :=
  D.layer (Fin.last n)

theorem OrderedDerivativeTower.continuousTop
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : (Fin n → ℝ) → F}
    (D : OrderedDerivativeTower n f) : Continuous D.top :=
  D.continuous_layer _

@[simp]
theorem OrderedDerivativeTower.top_const_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : (Fin n → ℝ) → F}
    (D : OrderedDerivativeTower n f) (c : ℝ) :
    (D.const_smul c).top = fun x => c • D.top x := rfl

theorem update_prependCoordinate_zero {n : ℕ}
    (head value : ℝ) (tail : Fin n → ℝ) :
    Function.update (prependCoordinate head tail) 0 value =
      prependCoordinate value tail := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp [Function.update]

theorem update_prependCoordinate_succ {n : ℕ}
    (head value : ℝ) (tail : Fin n → ℝ) (k : Fin n) :
    Function.update (prependCoordinate head tail) k.succ value =
      prependCoordinate head (Function.update tail k value) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · have hne : (0 : Fin (n + 1)) ≠ k.succ :=
      Ne.symm (Fin.succ_ne_zero k)
    simp [Function.update, hne]
  · intro j
    by_cases hj : j = k
    · subst j
      simp [Function.update]
    · have hs : j.succ ≠ k.succ := fun h => hj (Fin.succ_injective _ h)
      simp [Function.update, hj, hs]

/-- After differentiating the head coordinate, the remaining layers form the
ordered derivative tower on the tail coordinates. -/
def OrderedDerivativeTower.tail
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : (Fin (n + 1) → ℝ) → F}
    (D : OrderedDerivativeTower (n + 1) f) (head : ℝ) :
    OrderedDerivativeTower n
      (fun y => D.layer 1 (prependCoordinate head y)) where
  layer := fun j y => D.layer j.succ (prependCoordinate head y)
  layer_zero := by rfl
  hasDeriv_coordinate := by
    intro k y
    have hd := D.hasDeriv_coordinate k.succ
      (prependCoordinate head y)
    have hidx : k.castSucc.succ = k.succ.castSucc := by
      apply Fin.ext
      rfl
    simpa only [hidx, update_prependCoordinate_succ,
      prependCoordinate_succ] using hd
  continuous_layer := by
    intro j
    apply (D.continuous_layer j.succ).comp
    exact continuous_prependCoordinate (fun _ : Fin n → ℝ => head) id
      continuous_const continuous_id

/-- Differentiation commutes with a finite alternating cube secant. -/
theorem orderedCubeSecant_hasDerivAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f f' : ℝ → (Fin n → ℝ) → F)
    (h : Fin n → ℝ) (t : ℝ)
    (hderiv : ∀ y, HasDerivAt (fun s => f s y) (f' t y) t) :
    HasDerivAt (fun s => orderedCubeSecant n (f s) h)
      (orderedCubeSecant n (f' t) h) t := by
  induction n with
  | zero =>
      simpa [orderedCubeSecant] using hderiv Fin.elim0
  | succ n ih =>
      rw [show (fun s => orderedCubeSecant (n + 1) (f s) h) =
          fun s =>
            orderedCubeSecant n
                (fun y => f s (prependCoordinate (h 0) y)) (dropHead h) -
              orderedCubeSecant n
                (fun y => f s (prependCoordinate 0 y)) (dropHead h) by rfl]
      rw [show orderedCubeSecant (n + 1) (f' t) h =
          orderedCubeSecant n
              (fun y => f' t (prependCoordinate (h 0) y)) (dropHead h) -
            orderedCubeSecant n
              (fun y => f' t (prependCoordinate 0 y)) (dropHead h) by rfl]
      apply HasDerivAt.sub
      · apply ih
        intro y
        exact hderiv (prependCoordinate (h 0) y)
      · apply ih
        intro y
        exact hderiv (prependCoordinate 0 y)

/-- A finite cube secant of a jointly continuous family is continuous in its
external parameter. -/
theorem continuous_orderedCubeSecant
    {X F : Type*} [TopologicalSpace X]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F]
    (n : ℕ) (f : X → (Fin n → ℝ) → F) (h : Fin n → ℝ)
    (hf : Continuous (fun p : X × (Fin n → ℝ) => f p.1 p.2)) :
    Continuous (fun x => orderedCubeSecant n (f x) h) := by
  induction n generalizing X with
  | zero =>
      exact hf.comp (continuous_id.prodMk continuous_const)
  | succ n ih =>
      rw [show (fun x => orderedCubeSecant (n + 1) (f x) h) =
          fun x =>
            orderedCubeSecant n
                (fun y => f x (prependCoordinate (h 0) y)) (dropHead h) -
              orderedCubeSecant n
                (fun y => f x (prependCoordinate 0 y)) (dropHead h) by rfl]
      apply Continuous.sub
      · apply ih
        have hmap : Continuous (fun p : X × (Fin n → ℝ) =>
            (p.1, prependCoordinate (h 0) p.2)) := by
          apply Continuous.prodMk continuous_fst
          exact continuous_prependCoordinate (fun _ : X × (Fin n → ℝ) => h 0)
            Prod.snd continuous_const continuous_snd
        change Continuous ((fun p : X × (Fin (n + 1) → ℝ) => f p.1 p.2) ∘
          fun p : X × (Fin n → ℝ) =>
            (p.1, prependCoordinate (h 0) p.2))
        exact hf.comp hmap
      · apply ih
        have hmap : Continuous (fun p : X × (Fin n → ℝ) =>
            (p.1, prependCoordinate 0 p.2)) := by
          apply Continuous.prodMk continuous_fst
          exact continuous_prependCoordinate (fun _ : X × (Fin n → ℝ) => 0)
            Prod.snd continuous_const continuous_snd
        change Continuous ((fun p : X × (Fin (n + 1) → ℝ) => f p.1 p.2) ∘
          fun p : X × (Fin n → ℝ) =>
            (p.1, prependCoordinate 0 p.2))
        exact hf.comp hmap

/-- One step of repeated rectangular FTC: split the full secant at the head
coordinate and integrate the head derivative of the tail secant. -/
theorem orderedCubeSecant_succ_eq_integral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {n : ℕ} {f : (Fin (n + 1) → ℝ) → F}
    (D : OrderedDerivativeTower (n + 1) f) (h : Fin (n + 1) → ℝ) :
    orderedCubeSecant (n + 1) f h =
      ∫ t in (0 : ℝ)..h 0,
        orderedCubeSecant n
          (fun y => D.layer 1 (prependCoordinate t y)) (dropHead h) := by
  let q : ℝ → F := fun t =>
    orderedCubeSecant n (fun y => f (prependCoordinate t y)) (dropHead h)
  let q' : ℝ → F := fun t =>
    orderedCubeSecant n
      (fun y => D.layer 1 (prependCoordinate t y)) (dropHead h)
  have hqderiv : ∀ t : ℝ, HasDerivAt q (q' t) t := by
    intro t
    dsimp only [q, q']
    apply orderedCubeSecant_hasDerivAt n
      (fun s y => f (prependCoordinate s y))
      (fun s y => D.layer 1 (prependCoordinate s y))
      (dropHead h) t
    intro y
    have hd := D.hasDeriv_coordinate (0 : Fin (n + 1))
      (prependCoordinate t y)
    have hcast : (Fin.castSucc (0 : Fin (n + 1))) =
        (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hsucc : (Fin.succ (0 : Fin (n + 1))) =
        (1 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hcast, hsucc, D.layer_zero] at hd
    convert hd using 1
    · funext s
      rw [update_prependCoordinate_zero]
    · rw [prependCoordinate_zero]
  have hq'cont : Continuous q' := by
    apply continuous_orderedCubeSecant n
    have hprepend : Continuous (fun p : ℝ × (Fin n → ℝ) =>
        prependCoordinate p.1 p.2) :=
      continuous_prependCoordinate Prod.fst Prod.snd continuous_fst continuous_snd
    change Continuous ((D.layer 1) ∘ fun p : ℝ × (Fin n → ℝ) =>
      prependCoordinate p.1 p.2)
    exact (D.continuous_layer 1).comp hprepend
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := h 0)
    (fun t _ht => hqderiv t) (hq'cont.intervalIntegrable _ _)
  change q (h 0) - q 0 = ∫ t in (0 : ℝ)..h 0, q' t
  exact hFTC.symm

/-- Iterated integral over the coordinate box with side-length vector `h`. -/
noncomputable def iteratedBoxIntegral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :
    (n : ℕ) → ((Fin n → ℝ) → F) → (Fin n → ℝ) → F
  | 0, g, _h => g Fin.elim0
  | n + 1, g, h => ∫ t in (0 : ℝ)..h 0,
      iteratedBoxIntegral n
        (fun y => g (prependCoordinate t y)) (dropHead h)

/-- Rescaling each coordinate interval to `[0,1]` extracts exactly the
product of the signed side lengths.  This identity is valid even when some
side length is zero. -/
theorem iteratedBoxIntegral_eq_product_smul_scaledUnitBoxAverage
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (g : (Fin n → ℝ) → F) (h : Fin n → ℝ) :
    iteratedBoxIntegral n g h =
      (∏ i, h i) • scaledUnitBoxAverage g h := by
  induction n with
  | zero =>
      simp [iteratedBoxIntegral, scaledUnitBoxAverage]
      apply congrArg g
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      rw [iteratedBoxIntegral]
      have hinner :
          (fun t : ℝ => iteratedBoxIntegral n
            (fun y => g (prependCoordinate t y)) (dropHead h)) =
          fun t : ℝ => (∏ i, dropHead h i) •
            scaledUnitBoxAverage
              (fun y => g (prependCoordinate t y)) (dropHead h) := by
        funext t
        exact ih (fun y => g (prependCoordinate t y)) (dropHead h)
      rw [hinner, intervalIntegral.integral_smul]
      have hscale := intervalIntegral.smul_integral_comp_mul_left
        (a := (0 : ℝ)) (b := 1)
        (fun t : ℝ => scaledUnitBoxAverage
          (fun y => g (prependCoordinate t y)) (dropHead h)) (h 0)
      rw [mul_zero, mul_one] at hscale
      rw [← hscale]
      have havg :
          (∫ x : ℝ in (0 : ℝ)..1,
            scaledUnitBoxAverage
              (fun y => g (prependCoordinate (h 0 * x) y)) (dropHead h)) =
          scaledUnitBoxAverage g h := by
        simp only [scaledUnitBoxAverage, iteratedUnitBoxIntegral]
        apply intervalIntegral.integral_congr
        intro x hx
        change iteratedUnitBoxIntegral n
            (fun s => g (prependCoordinate (h 0 * x)
              (fun i => dropHead h i * s i))) =
          iteratedUnitBoxIntegral n
            (fun s => g (fun i => h i * prependCoordinate x s i))
        apply congrArg (iteratedUnitBoxIntegral n)
        funext s
        apply congrArg g
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [prependCoordinate]
        · intro j
          simp [prependCoordinate, dropHead]
      rw [havg]
      change (∏ i : Fin n, h i.succ) •
          (h 0 • scaledUnitBoxAverage g h) =
        (∏ i : Fin (n + 1), h i) • scaledUnitBoxAverage g h
      rw [← smul_assoc, Fin.prod_univ_succ]
      congr 1
      exact mul_comm _ _

/-- Repeated FTC: the alternating cube secant is exactly the nested box
integral of the final ordered mixed derivative. -/
theorem orderedCubeSecant_eq_iteratedBoxIntegral_top
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (f : (Fin n → ℝ) → F)
    (D : OrderedDerivativeTower n f) (h : Fin n → ℝ) :
    orderedCubeSecant n f h = iteratedBoxIntegral n D.top h := by
  induction n with
  | zero =>
      change f Fin.elim0 = D.layer 0 Fin.elim0
      rw [D.layer_zero]
  | succ n ih =>
      rw [orderedCubeSecant_succ_eq_integral D h]
      rw [iteratedBoxIntegral]
      apply intervalIntegral.integral_congr
      intro t ht
      change orderedCubeSecant n
          (fun y => D.layer 1 (prependCoordinate t y)) (dropHead h) =
        iteratedBoxIntegral n
          (fun y => D.top (prependCoordinate t y)) (dropHead h)
      calc
        orderedCubeSecant n
            (fun y => D.layer 1 (prependCoordinate t y)) (dropHead h) =
            iteratedBoxIntegral n (D.tail t).top (dropHead h) :=
          ih (fun y => D.layer 1 (prependCoordinate t y)) (D.tail t) (dropHead h)
        _ = iteratedBoxIntegral n
            (fun y => D.top (prependCoordinate t y)) (dropHead h) := by
          congr 1

/-- Exact rectangular FTC in normalized-average form. -/
theorem orderedCubeSecant_eq_product_smul_scaledUnitBoxAverage_top
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (f : (Fin n → ℝ) → F)
    (D : OrderedDerivativeTower n f) (h : Fin n → ℝ) :
    orderedCubeSecant n f h =
      (∏ i, h i) • scaledUnitBoxAverage D.top h := by
  rw [orderedCubeSecant_eq_iteratedBoxIntegral_top n f D h]
  exact iteratedBoxIntegral_eq_product_smul_scaledUnitBoxAverage n D.top h

/-- Away from coordinate hyperplanes, normalizing the cube secant by the
product of its side lengths leaves precisely the scaled unit-box average. -/
theorem normalized_orderedCubeSecant_eq_scaledUnitBoxAverage_top
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (f : (Fin n → ℝ) → F)
    (D : OrderedDerivativeTower n f) (h : Fin n → ℝ)
    (hne : ∀ i, h i ≠ 0) :
    (∏ i, h i)⁻¹ • orderedCubeSecant n f h =
      scaledUnitBoxAverage D.top h := by
  rw [orderedCubeSecant_eq_product_smul_scaledUnitBoxAverage_top n f D h]
  rw [← smul_assoc]
  have hp : (∏ i, h i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact hne i
  simp [hp]

/-- The normalized rectangular secant converges to the top ordered mixed
derivative as every side length tends to zero through nonzero coordinates. -/
theorem normalized_orderedCubeSecant_tendsto_top
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (f : (Fin n → ℝ) → F)
    (D : OrderedDerivativeTower n f) :
    Tendsto
      (fun h : Fin n → ℝ =>
        (∏ i, h i)⁻¹ • orderedCubeSecant n f h)
      (𝓝[{h | ∀ i, h i ≠ 0}] (0 : Fin n → ℝ))
      (𝓝 (D.top 0)) := by
  have hscaled : Tendsto (scaledUnitBoxAverage D.top)
      (𝓝[{h | ∀ i, h i ≠ 0}] (0 : Fin n → ℝ))
      (𝓝 (D.top 0)) :=
    (scaledUnitBoxAverage_tendsto_zero D.top D.continuousTop).mono_left
      inf_le_left
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (normalized_orderedCubeSecant_eq_scaledUnitBoxAverage_top
    n f D h hh).symm

end NCG
