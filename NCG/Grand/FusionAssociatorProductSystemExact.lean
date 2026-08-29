/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTFusionTower
import NCG.Grand.CanonicalSourceFusionExact

/-!
# Fusion associators and all-degree reconstruction

This file supplies the coherence step in `thm:GT-fusion-associativity`.
The analytic input constructing the binary unitary fusion maps is provided by
`CanonicalSourceFusion.gt_source_fusion_exact`, while their matrix-unitarity
propagation is provided by `gt_fusion_associativity`.  Here we prove the
previously missing associator induction: an associative graded fusion law and
its attach-one recursion imply the boxed identity at every pair of degrees.
-/

namespace NCG
namespace FusionAssociatorProductSystem

universe u

/-- The right-associated algebraic tensor power.  `snoc x a` represents
`x tensor a`; the index records the number of degree-one factors. -/
inductive TensorPower (E : Type u) : Nat -> Type u
  | unit : TensorPower E 0
  | snoc {n : Nat} : TensorPower E n -> E -> TensorPower E (n + 1)

/-- Canonical concatenation of finite tensor words. -/
def TensorPower.append {E : Type*} {r : Nat} :
    TensorPower E r -> {s : Nat} -> TensorPower E s -> TensorPower E (r + s)
  | x, 0, .unit => x
  | x, _ + 1, .snoc y a => .snoc (TensorPower.append x y) a

/-- An associative occurrence law on a single carrier, equipped with an exact
grading.  The carrier may be read as the disjoint graded union of the spaces
`H_n`; `degree` identifies its homogeneous summand. -/
structure GradedFusionLaw (A E : Type*) where
  degree : A -> Nat
  fuse : A -> A -> A
  unit : A
  atom : E -> A
  degree_unit : degree unit = 0
  degree_atom : forall a, degree (atom a) = 1
  degree_fuse : forall x y, degree (fuse x y) = degree x + degree y
  right_unit : forall x, fuse x unit = x
  associativity : forall x y z, fuse (fuse x y) z = fuse x (fuse y z)

variable {A E : Type*}

/-- Reconstruction from the degree-zero unit, degree-one source, and the
attach-one fusion. -/
def reconstruct (F : GradedFusionLaw A E) :
    {n : Nat} -> TensorPower E n -> A
  | 0, .unit => F.unit
  | _ + 1, .snoc x a => F.fuse (reconstruct F x) (F.atom a)

@[simp] theorem reconstruct_unit (F : GradedFusionLaw A E) :
    reconstruct F (.unit : TensorPower E 0) = F.unit := rfl

@[simp] theorem reconstruct_snoc (F : GradedFusionLaw A E)
    {n : Nat} (x : TensorPower E n) (a : E) :
    reconstruct F (.snoc x a) = F.fuse (reconstruct F x) (F.atom a) := rfl

/-- Every reconstructed tensor word lands in its declared homogeneous degree. -/
theorem reconstruct_degree (F : GradedFusionLaw A E) {n : Nat}
    (x : TensorPower E n) : F.degree (reconstruct F x) = n := by
  induction x with
  | unit => exact F.degree_unit
  | @snoc n x a ih =>
      rw [reconstruct_snoc, F.degree_fuse, ih, F.degree_atom]

/-- The boxed all-degree product-system identity.  It is obtained solely from
the vanishing associator residual (`F.associativity`) and the attach-one
recursion; no general-degree fusion identity is assumed. -/
theorem fuse_reconstruct_append (F : GradedFusionLaw A E)
    {r s : Nat} (x : TensorPower E r) (y : TensorPower E s) :
    F.fuse (reconstruct F x) (reconstruct F y) =
      reconstruct F (TensorPower.append x y) := by
  induction y with
  | unit => exact F.right_unit _
  | snoc y a ih =>
      rw [reconstruct_snoc, ← F.associativity, ih]
      rfl

/-- Uniqueness of the all-degree reconstruction from the degree-zero value and
the boxed attach-one recursion. -/
theorem reconstruct_unique (F : GradedFusionLaw A E)
    (V : {n : Nat} -> TensorPower E n -> A)
    (hzero : V (.unit : TensorPower E 0) = F.unit)
    (hstep : forall {n : Nat} (x : TensorPower E n) (a : E),
      V (.snoc x a) = F.fuse (V x) (F.atom a)) :
    forall {n : Nat} (x : TensorPower E n), V x = reconstruct F x := by
  intro n x
  induction x with
  | unit => exact hzero
  | snoc x a ih => rw [hstep, reconstruct_snoc, ih]

/-- Exact coherence package for `thm:GT-fusion-associativity`: recursion,
homogeneous landing, uniqueness, and the general binary fusion identity. -/
theorem fusion_associator_product_system_exact (F : GradedFusionLaw A E) :
    (forall {n : Nat} (x : TensorPower E n) (a : E),
      reconstruct F (.snoc x a) = F.fuse (reconstruct F x) (F.atom a))
    /\ (forall {n : Nat} (x : TensorPower E n),
      F.degree (reconstruct F x) = n)
    /\ (forall (V : {n : Nat} -> TensorPower E n -> A),
      V (.unit : TensorPower E 0) = F.unit ->
      (forall {n : Nat} (x : TensorPower E n) (a : E),
        V (.snoc x a) = F.fuse (V x) (F.atom a)) ->
      forall {n : Nat} (x : TensorPower E n), V x = reconstruct F x)
    /\ (forall {r s : Nat} (x : TensorPower E r) (y : TensorPower E s),
      F.fuse (reconstruct F x) (reconstruct F y) =
        reconstruct F (TensorPower.append x y)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n x a
    rfl
  · exact reconstruct_degree F
  · exact reconstruct_unique F
  · exact fuse_reconstruct_append F

end FusionAssociatorProductSystem
end NCG
