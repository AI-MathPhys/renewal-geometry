/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.SuperEvenPoincareExact
import NCG.Grand.GrassmannPoincareExact

/-!
# The graded (super) Poincaré lemma

The complete mixed-sector RG.1/RG.2 statement for `thm:SM-common-action-integrability`:
on the super-algebra of a finite graded coordinate bank (even polynomial coordinates and
odd Grassmann generators), a force family whose **complete mixed graded curl vanishes**
(even–even symmetric, odd–odd antisymmetric, even–odd commuting) is the gradient family
`F_A = ∂_A S` of a single action `S`, and conversely
(`super_curl_iff_exists_potential`).  The action is reconstructed by the two-step radial
homotopy: even integration first (`SuperPoincare.exists_even_potential`), then the odd
radial potential of the corrected odd forces (`OddPoincare.oddPotential`).
-/

open CliffordAlgebra MvPolynomial

namespace NCG
namespace SuperPoincare

open NCG.SuperDeriv

variable {σ : Type*} [Fintype σ] {R : Type*} [CommRing R] [Algebra ℚ R]
variable {ιo : Type*} [Fintype ιo] [LinearOrder ιo]
variable {M : Type*} [AddCommGroup M] [Module (MvPolynomial σ R) M]
variable (bM : Module.Basis ιo (MvPolynomial σ R) M)

omit [Fintype σ] [Algebra ℚ R] in
/-- The even derivations preserve the grading. -/
theorem evenDeriv_mem {d : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)}
    (co : Connection d M) :
    ∀ p : ℕ, ∀ x ∈ (⋀[MvPolynomial σ R]^p M :
      Submodule (MvPolynomial σ R) (ExteriorAlgebra (MvPolynomial σ R) M)),
      evenDeriv d co x ∈ (⋀[MvPolynomial σ R]^p M :
        Submodule (MvPolynomial σ R) (ExteriorAlgebra (MvPolynomial σ R) M)) := by
  intro p
  induction p with
  | zero =>
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
    rw [evenDeriv_algebraMap]
    exact Submodule.mem_one.mpr ⟨_, rfl⟩
  | succ p IH =>
    intro x hx
    have hx' : x ∈ LinearMap.range (ExteriorAlgebra.ι (MvPolynomial σ R) (M := M))
        * LinearMap.range (ExteriorAlgebra.ι (MvPolynomial σ R) (M := M)) ^ p := by
      rw [← pow_succ']
      exact hx
    refine Submodule.mul_induction_on hx' ?_ fun z w hz hw => by
      rw [evenDeriv_add]; exact Submodule.add_mem _ hz hw
    rintro m ⟨v, rfl⟩ y hy
    rw [evenDeriv_mul]
    refine Submodule.add_mem _ ?_ ?_
    · have h := SetLike.mul_mem_graded
        (show ExteriorAlgebra.ι (MvPolynomial σ R) v ∈ ⋀[MvPolynomial σ R]^1 M from by
          have : ExteriorAlgebra.ι (MvPolynomial σ R) v
              ∈ LinearMap.range (ExteriorAlgebra.ι (MvPolynomial σ R) (M := M)) :=
            ⟨v, rfl⟩
          rwa [← pow_one
            (LinearMap.range (ExteriorAlgebra.ι (MvPolynomial σ R) (M := M)))] at this)
        (IH y hy)
      rwa [show 1 + p = p + 1 from Nat.add_comm 1 p] at h
    · rw [evenDeriv_iota]
      have h := SetLike.mul_mem_graded
        (show ExteriorAlgebra.ι (MvPolynomial σ R) (co v) ∈ ⋀[MvPolynomial σ R]^1 M
          from by
          have : ExteriorAlgebra.ι (MvPolynomial σ R) (co v)
              ∈ LinearMap.range (ExteriorAlgebra.ι (MvPolynomial σ R) (M := M)) :=
            ⟨co v, rfl⟩
          rwa [← pow_one
            (LinearMap.range (ExteriorAlgebra.ι (MvPolynomial σ R) (M := M)))] at this)
        hy
      rwa [show 1 + p = p + 1 from Nat.add_comm 1 p] at h

omit [Fintype σ] [Algebra ℚ R] in
/-- The even derivations commute with the graded projections. -/
theorem evenDeriv_proj {d : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)}
    (co : Connection d M) (p : ℕ) (x : ExteriorAlgebra (MvPolynomial σ R) M) :
    evenDeriv d co
        (GradedAlgebra.proj (fun i : ℕ => ⋀[MvPolynomial σ R]^i M) p x)
      = GradedAlgebra.proj (fun i : ℕ => ⋀[MvPolynomial σ R]^i M) p
          (evenDeriv d co x) := by
  classical
  have hx : x = ∑ q ∈ (DirectSum.decompose
      (fun i : ℕ => ⋀[MvPolynomial σ R]^i M) x).support,
      (DirectSum.decompose (fun i : ℕ => ⋀[MvPolynomial σ R]^i M) x q
        : ExteriorAlgebra (MvPolynomial σ R) M) :=
    (DirectSum.sum_support_decompose _ x).symm
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  rw [map_sum, evenDeriv_finset_sum, evenDeriv_finset_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rcases eq_or_ne q p with rfl | hq
  · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same
      (ℳ := fun i : ℕ => ⋀[MvPolynomial σ R]^i M) (SetLike.coe_mem _),
      GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same
      (ℳ := fun i : ℕ => ⋀[MvPolynomial σ R]^i M)
      (evenDeriv_mem co q _ (SetLike.coe_mem _))]
  · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne
      (ℳ := fun i : ℕ => ⋀[MvPolynomial σ R]^i M) (SetLike.coe_mem _) hq,
      evenDeriv_zero, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne
      (ℳ := fun i : ℕ => ⋀[MvPolynomial σ R]^i M)
      (evenDeriv_mem co q _ (SetLike.coe_mem _)) hq]

omit [Fintype σ] in
/-- Rational scalars are flat for the even derivations. -/
theorem pderiv_ratCast (i : σ) (q : ℚ) :
    pderiv (R := R) i (algebraMap ℚ (MvPolynomial σ R) q) = 0 := by
  rw [IsScalarTower.algebraMap_apply ℚ R (MvPolynomial σ R), algebraMap_eq, pderiv_C]

omit [Fintype σ] [LinearOrder ιo] in
/-- The even derivations kill the odd radial potential of an even-flat family. -/
theorem evenDeriv_oddPotential (i : σ) (G : ιo → ExteriorAlgebra (MvPolynomial σ R) M)
    (hG : ∀ a, evenDeriv (pderiv i) (coordConn bM i) (G a) = 0) :
    evenDeriv (pderiv i) (coordConn bM i) (OddPoincare.oddPotential bM G) = 0 := by
  rw [OddPoincare.oddPotential, evenDeriv_finset_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [evenDeriv_smul, pderiv_ratCast, zero_smul, zero_add, evenDeriv_finset_sum]
  rw [Finset.sum_eq_zero fun a _ => ?_, smul_zero]
  rw [evenDeriv_mul, evenDeriv_proj, hG, map_zero, mul_zero, evenDeriv_iota]
  rw [show (coordConn bM i) (bM a) = (coordConn bM i).toFun (bM a) from rfl,
    coordConn_basis, map_zero, zero_mul, add_zero]

/-- The odd derivatives, as interior products by the coordinate duals. -/
noncomputable abbrev odd (a : ιo) :
    ExteriorAlgebra (MvPolynomial σ R) M →ₗ[MvPolynomial σ R]
      ExteriorAlgebra (MvPolynomial σ R) M :=
  OddPoincare.odiff bM a

/-- **The graded (super) Poincaré lemma**: a super-force family with vanishing complete
mixed graded curl is the gradient family of one action, reconstructed by the two-step
radial homotopy. -/
theorem exists_super_potential
    (Fe : σ → ExteriorAlgebra (MvPolynomial σ R) M)
    (Fo : ιo → ExteriorAlgebra (MvPolynomial σ R) M)
    (hee : ∀ i j, evenDeriv (pderiv i) (coordConn bM i) (Fe j)
      = evenDeriv (pderiv j) (coordConn bM j) (Fe i))
    (hoo : ∀ a c, odd bM a (Fo c) = -odd bM c (Fo a))
    (heo : ∀ i a, evenDeriv (pderiv i) (coordConn bM i) (Fo a)
      = odd bM a (Fe i)) :
    ∃ S : ExteriorAlgebra (MvPolynomial σ R) M,
      (∀ i, evenDeriv (pderiv i) (coordConn bM i) S = Fe i) ∧
      ∀ a, odd bM a S = Fo a := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_even_potential bM Fe hee
  set G : ιo → ExteriorAlgebra (MvPolynomial σ R) M :=
    fun a => Fo a - odd bM a S₀ with hGdef
  have hGflat : ∀ i a, evenDeriv (pderiv i) (coordConn bM i) (G a) = 0 := by
    intro i a
    have hcomm : evenDeriv (pderiv i) (coordConn bM i) (odd bM a S₀)
        = odd bM a (evenDeriv (pderiv i) (coordConn bM i) S₀) :=
      evenDeriv_contractLeft (pderiv i) (coordConn bM i) (bM.coord a)
        (fun m => coord_coordConn bM i a m) S₀
    rw [hGdef]
    rw [evenDeriv_sub, heo i a, hcomm, hS₀]
    exact sub_self _
  have hGcurl : ∀ a c, odd bM a (G c) = -odd bM c (G a) := by
    intro a c
    have hcc : odd bM a (odd bM c S₀) = -odd bM c (odd bM a S₀) :=
      contractLeft_comm (Q := (0 : QuadraticForm (MvPolynomial σ R) M))
        (bM.coord a) (bM.coord c) S₀
    rw [hGdef]
    simp only [map_sub]
    rw [hoo a c, hcc]
    abel
  refine ⟨S₀ + OddPoincare.oddPotential bM G, fun i => ?_, fun a => ?_⟩
  · rw [evenDeriv_add, hS₀, evenDeriv_oddPotential bM i G fun a => hGflat i a, add_zero]
  · rw [map_add, OddPoincare.odiff_oddPotential bM G hGcurl a]
    simp only [hGdef]
    abel

/-- **RG.1/RG.2, complete graded statement**: the complete mixed graded curl vanishes
exactly when the super-force family is the gradient family of one action.  Sectorwise
gauge, scalar, fermion, or Yukawa fits define one physical theory only when their complete
mixed graded curl vanishes. -/
theorem super_curl_iff_exists_potential
    (Fe : σ → ExteriorAlgebra (MvPolynomial σ R) M)
    (Fo : ιo → ExteriorAlgebra (MvPolynomial σ R) M) :
    ((∀ i j, evenDeriv (pderiv i) (coordConn bM i) (Fe j)
        = evenDeriv (pderiv j) (coordConn bM j) (Fe i)) ∧
      (∀ a c, odd bM a (Fo c) = -odd bM c (Fo a)) ∧
      ∀ i a, evenDeriv (pderiv i) (coordConn bM i) (Fo a) = odd bM a (Fe i)) ↔
    ∃ S : ExteriorAlgebra (MvPolynomial σ R) M,
      (∀ i, evenDeriv (pderiv i) (coordConn bM i) S = Fe i) ∧
      ∀ a, odd bM a S = Fo a := by
  constructor
  · rintro ⟨hee, hoo, heo⟩
    exact exists_super_potential bM Fe Fo hee hoo heo
  · rintro ⟨S, hSe, hSo⟩
    refine ⟨fun i j => ?_, fun a c => ?_, fun i a => ?_⟩
    · rw [← hSe i, ← hSe j]
      exact evenDeriv_comm bM i j S
    · rw [← hSo a, ← hSo c]
      exact contractLeft_comm _ _ S
    · rw [← hSo a, ← hSe i]
      exact evenDeriv_contractLeft (pderiv i) (coordConn bM i) (bM.coord a)
        (fun m => coord_coordConn bM i a m) S

end SuperPoincare
end NCG
