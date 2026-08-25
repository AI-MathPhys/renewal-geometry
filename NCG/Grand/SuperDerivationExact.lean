/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Even derivations on the super-algebra

Mixed-sector machinery for `thm:SM-common-action-integrability` (RG.1/RG.2).

Given a base derivation `d` of the even coefficient ring `R₀` (such as `pderiv i` on a
polynomial bank) and a compatible connection `co` on the odd generator module, the even
derivative lifts to the whole exterior super-algebra `⋀_{R₀} M` **with the Leibniz rule
for free**: `x ↦ (x, Dx)` is realized as the Clifford lift into the trivial square-zero
extension carrying the `d`-twisted `R₀`-algebra structure (`evenDeriv`, `evenDeriv_mul`,
`evenDeriv_algebraMap`, `evenDeriv_iota`).  No sign combinatorics or basis structure
constants are needed.  The twisted extension is a type synonym `TwistExt` so that the
twisted scalar action is the unique registered instance.
-/

open CliffordAlgebra TrivSqZeroExt

namespace NCG
namespace SuperDeriv

variable {R : Type*} [CommRing R]
variable {R₀ : Type*} [CommRing R₀] [Algebra R R₀]
variable {M : Type*} [AddCommGroup M] [Module R₀ M]

/-- A connection on the odd generator module over a base derivation: additive and
`d`-semilinear. -/
structure Connection (d : Derivation R R₀ R₀) (M : Type*) [AddCommGroup M]
    [Module R₀ M] where
  /-- the underlying map -/
  toFun : M → M
  /-- additivity -/
  map_add' : ∀ m n, toFun (m + n) = toFun m + toFun n
  /-- the Leibniz rule against scalars -/
  map_smul' : ∀ (r : R₀) (m : M), toFun (r • m) = d r • m + r • toFun m

instance (d : Derivation R R₀ R₀) : FunLike (Connection d M) M M where
  coe := Connection.toFun
  coe_injective := by
    rintro ⟨f, _, _⟩ ⟨g, _, _⟩ h
    simpa using h

/-- The square-zero extension of the super-algebra by itself, as a type synonym carrying
the `d`-twisted scalar action. -/
def TwistExt (_d : Derivation R R₀ R₀) (M : Type*) [AddCommGroup M] [Module R₀ M] :
    Type _ :=
  TrivSqZeroExt (ExteriorAlgebra R₀ M) (ExteriorAlgebra R₀ M)

variable (d : Derivation R R₀ R₀)

instance : Ring (TwistExt d M) :=
  inferInstanceAs (Ring (TrivSqZeroExt (ExteriorAlgebra R₀ M) (ExteriorAlgebra R₀ M)))

namespace TwistExt

/-- Build an element from the pair of components. -/
def mk (a b : ExteriorAlgebra R₀ M) : TwistExt d M := (inl a + inr b :
  TrivSqZeroExt (ExteriorAlgebra R₀ M) (ExteriorAlgebra R₀ M))

/-- The value component. -/
def val (x : TwistExt d M) : ExteriorAlgebra R₀ M :=
  TrivSqZeroExt.fst (R := ExteriorAlgebra R₀ M) (M := ExteriorAlgebra R₀ M) x

/-- The derivative component. -/
def der (x : TwistExt d M) : ExteriorAlgebra R₀ M :=
  TrivSqZeroExt.snd (R := ExteriorAlgebra R₀ M) (M := ExteriorAlgebra R₀ M) x

variable {d}

theorem ext' {x y : TwistExt d M} (h1 : val d x = val d y) (h2 : der d x = der d y) :
    x = y :=
  TrivSqZeroExt.ext h1 h2

@[simp] theorem val_mk (a b : ExteriorAlgebra R₀ M) : val d (mk d a b) = a := by
  change TrivSqZeroExt.fst
    (inl a + inr b : TrivSqZeroExt (ExteriorAlgebra R₀ M) (ExteriorAlgebra R₀ M)) = a
  rw [fst_add, fst_inl, fst_inr, add_zero]

@[simp] theorem der_mk (a b : ExteriorAlgebra R₀ M) : der d (mk d a b) = b := by
  change TrivSqZeroExt.snd
    (inl a + inr b : TrivSqZeroExt (ExteriorAlgebra R₀ M) (ExteriorAlgebra R₀ M)) = b
  rw [snd_add, snd_inl, snd_inr, zero_add]

@[simp] theorem val_mul (x y : TwistExt d M) : val d (x * y) = val d x * val d y :=
  TrivSqZeroExt.fst_mul _ _

@[simp] theorem der_mul (x y : TwistExt d M) :
    der d (x * y) = val d x * der d y + der d x * val d y := by
  have h := TrivSqZeroExt.snd_mul
    (R := ExteriorAlgebra R₀ M) (M := ExteriorAlgebra R₀ M) x y
  rwa [smul_eq_mul, op_smul_eq_mul] at h

@[simp] theorem val_add (x y : TwistExt d M) : val d (x + y) = val d x + val d y :=
  TrivSqZeroExt.fst_add _ _

@[simp] theorem der_add (x y : TwistExt d M) : der d (x + y) = der d x + der d y :=
  TrivSqZeroExt.snd_add _ _

@[simp] theorem val_one : val d (1 : TwistExt d M) = 1 := TrivSqZeroExt.fst_one

@[simp] theorem der_one : der d (1 : TwistExt d M) = 0 := TrivSqZeroExt.snd_one

@[simp] theorem val_zero : val d (0 : TwistExt d M) = 0 := TrivSqZeroExt.fst_zero

@[simp] theorem der_zero : der d (0 : TwistExt d M) = 0 := TrivSqZeroExt.snd_zero

theorem mk_mul (a b a' b' : ExteriorAlgebra R₀ M) :
    mk d a b * mk d a' b' = mk d (a * a') (a * b' + b * a') := by
  refine ext' ?_ ?_ <;> simp

end TwistExt

open TwistExt

/-- The `d`-twisted scalar embedding. -/
noncomputable def twistHom : R₀ →+* TwistExt d M where
  toFun r := mk d (algebraMap R₀ _ r) (algebraMap R₀ _ (d r))
  map_one' := by
    refine ext' ?_ ?_ <;>
      simp [Derivation.map_one_eq_zero]
  map_mul' r s := by
    rw [mk_mul]
    refine ext' ?_ ?_ <;> simp only [val_mk, der_mk, map_mul]
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
    congr 1
    rw [← map_mul, ← map_mul, mul_comm]
  map_zero' := by
    refine ext' ?_ ?_ <;> simp
  map_add' r s := by
    refine ext' ?_ ?_ <;> simp

theorem twistHom_val (r : R₀) : val d (twistHom (M := M) d r) = algebraMap R₀ _ r :=
  val_mk _ _

theorem twistHom_der (r : R₀) : der d (twistHom (M := M) d r) = algebraMap R₀ _ (d r) :=
  der_mk _ _

/-- The twisted embedding is central. -/
theorem twistHom_central (r : R₀) (x : TwistExt d M) :
    twistHom (M := M) d r * x = x * twistHom (M := M) d r := by
  refine ext' ?_ ?_
  · rw [val_mul, val_mul, twistHom_val]
    exact Algebra.commutes r (val d x)
  · rw [der_mul, der_mul, twistHom_val, twistHom_der,
      Algebra.commutes r (der d x), Algebra.commutes (d r) (val d x)]
    exact add_comm _ _

noncomputable instance : Algebra R₀ (TwistExt d M) :=
  (twistHom (M := M) d).toAlgebra' fun r x => twistHom_central d r x

theorem twist_algebraMap_eq (r : R₀) :
    algebraMap R₀ (TwistExt d M) r = twistHom (M := M) d r := rfl

theorem twist_smul_eq (r : R₀) (x : TwistExt d M) :
    r • x = twistHom (M := M) d r * x := rfl

variable (co : Connection d M)

/-- The generator pair `m ↦ (ιm, ι(co m))`. -/
noncomputable def pairFun (m : M) : TwistExt d M :=
  mk d (ExteriorAlgebra.ι R₀ m) (ExteriorAlgebra.ι R₀ (co.toFun m))

theorem pairFun_val (m : M) : val d (pairFun d co m) = ExteriorAlgebra.ι R₀ m :=
  val_mk _ _

theorem pairFun_der (m : M) :
    der d (pairFun d co m) = ExteriorAlgebra.ι R₀ (co m) :=
  der_mk _ _

theorem pairFun_add (m n : M) :
    pairFun d co (m + n) = pairFun d co m + pairFun d co n := by
  refine ext' ?_ ?_
  · rw [val_add, pairFun_val, pairFun_val, pairFun_val, map_add]
  · rw [der_add, pairFun_der, pairFun_der, pairFun_der]
    change ExteriorAlgebra.ι R₀ (co.toFun (m + n)) = _
    rw [co.map_add', map_add]
    rfl

theorem pairFun_smul (r : R₀) (m : M) :
    pairFun d co (r • m) = r • pairFun d co m := by
  rw [twist_smul_eq]
  refine ext' ?_ ?_
  · rw [val_mul, twistHom_val, pairFun_val, pairFun_val, map_smul, Algebra.smul_def]
  · rw [der_mul, twistHom_val, twistHom_der, pairFun_der, pairFun_der, pairFun_val]
    change ExteriorAlgebra.ι R₀ (co.toFun (r • m)) = _
    rw [co.map_smul', map_add, map_smul, map_smul, Algebra.smul_def, Algebra.smul_def]
    exact add_comm _ _

theorem pairFun_sq (m : M) : pairFun d co m * pairFun d co m = 0 := by
  refine ext' ?_ ?_
  · rw [val_mul, pairFun_val, val_zero]
    exact ExteriorAlgebra.ι_sq_zero m
  · rw [der_mul, pairFun_val, pairFun_der, der_zero]
    exact ExteriorAlgebra.ι_add_mul_swap m (co m)

/-- The twisted Clifford lift `x ↦ (x, Dx)`. -/
noncomputable def twistLift : ExteriorAlgebra R₀ M →ₐ[R₀] TwistExt d M :=
  CliffordAlgebra.lift (0 : QuadraticForm R₀ M)
    ⟨{ toFun := pairFun d co
       map_add' := fun m n => pairFun_add d co m n
       map_smul' := fun r m => by
         rw [RingHom.id_apply]
         exact pairFun_smul d co r m },
     fun m => by
       rw [show ((0 : QuadraticForm R₀ M) m) = 0 from rfl, map_zero]
       exact pairFun_sq d co m⟩

theorem twistLift_iota (m : M) :
    twistLift d co (ExteriorAlgebra.ι R₀ m) = pairFun d co m :=
  CliffordAlgebra.lift_ι_apply _ _ m

theorem twistLift_algebraMap (r : R₀) :
    twistLift d co (algebraMap R₀ _ r) = twistHom (M := M) d r := by
  rw [AlgHom.commutes]
  rfl

/-- The first component of the lift is the identity. -/
theorem val_twistLift (x : ExteriorAlgebra R₀ M) : val d (twistLift d co x) = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [twistLift_algebraMap, twistHom_val]
  | ι m => rw [twistLift_iota, pairFun_val]
  | mul a b ha hb => rw [map_mul, val_mul, ha, hb]
  | add a b ha hb => rw [map_add, val_add, ha, hb]

/-- **The even super-derivation** attached to a base derivation and a connection. -/
noncomputable def evenDeriv (x : ExteriorAlgebra R₀ M) : ExteriorAlgebra R₀ M :=
  der d (twistLift d co x)

theorem evenDeriv_add (x y : ExteriorAlgebra R₀ M) :
    evenDeriv d co (x + y) = evenDeriv d co x + evenDeriv d co y := by
  rw [evenDeriv, evenDeriv, evenDeriv, map_add, der_add]

/-- **The Leibniz rule holds for free** (no signs: the even derivation is degree zero). -/
theorem evenDeriv_mul (x y : ExteriorAlgebra R₀ M) :
    evenDeriv d co (x * y) = x * evenDeriv d co y + evenDeriv d co x * y := by
  rw [evenDeriv, evenDeriv, evenDeriv, map_mul, der_mul, val_twistLift, val_twistLift]

theorem evenDeriv_iota (m : M) :
    evenDeriv d co (ExteriorAlgebra.ι R₀ m) = ExteriorAlgebra.ι R₀ (co m) := by
  rw [evenDeriv, twistLift_iota, pairFun_der]

theorem evenDeriv_algebraMap (r : R₀) :
    evenDeriv d co (algebraMap R₀ _ r) = algebraMap R₀ _ (d r) := by
  rw [evenDeriv, twistLift_algebraMap, twistHom_der]

theorem evenDeriv_one : evenDeriv d co 1 = 0 := by
  have h := evenDeriv_algebraMap d co 1
  rwa [map_one, Derivation.map_one_eq_zero, map_zero] at h

end SuperDeriv
end NCG
