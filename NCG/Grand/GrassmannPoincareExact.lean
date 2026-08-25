/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Grassmann (odd-sector) Poincaré lemma

Odd-sector machinery for `thm:SM-common-action-integrability` (RG.1/RG.2).

On the exterior algebra of a finite free module, the odd derivatives are the interior
products `∂ₐ = δₐ⌋·` with the dual basis (`odiff`).  The number operator
`N = ∑ₐ θₐ ∂ₐ` acts as `p•` on grade `p` (`numberOp_grade` — the odd Euler identity),
and the odd curl condition `∂ₐF_c = -∂_cFₐ` holds exactly when `Fₐ = ∂ₐS` for a single
action `S` (`odd_curl_iff_exists_potential`), reconstructed by the same radial homotopy
as in the even sector; the converse direction is the anticommutation of interior products
(`CliffordAlgebra.contractLeft_comm`).
-/

open CliffordAlgebra

namespace NCG
namespace OddPoincare

variable {R : Type*} [CommRing R] [Algebra ℚ R]
variable {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M] [Module R M]

/-- The odd partial derivative `∂ₐ = δₐ⌋·` on the exterior algebra. -/
noncomputable def odiff (b : Module.Basis ι R M) (a : ι) :
    ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  contractLeft (Q := (0 : QuadraticForm R M)) (b.coord a)

/-- The odd number operator `N = ∑ₐ θₐ ∂ₐ`. -/
noncomputable def numberOp (b : Module.Basis ι R M) :
    ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  ∑ a, (LinearMap.mulLeft R (ExteriorAlgebra.ι R (b a))).comp (odiff b a)

omit [Algebra ℚ R] in
theorem numberOp_apply (b : Module.Basis ι R M) (x : ExteriorAlgebra R M) :
    numberOp b x = ∑ a, ExteriorAlgebra.ι R (b a) * odiff b a x := by
  rw [numberOp, LinearMap.sum_apply]
  rfl

omit [Algebra ℚ R] [Fintype ι] in
theorem odiff_iota_mul (b : Module.Basis ι R M) (a : ι) (v : M)
    (x : ExteriorAlgebra R M) :
    odiff b a (ExteriorAlgebra.ι R v * x)
      = b.repr v a • x - ExteriorAlgebra.ι R v * odiff b a x := by
  have h := contractLeft_ι_mul (Q := (0 : QuadraticForm R M)) (d := b.coord a) v x
  simpa [odiff, Module.Basis.coord_apply] using h

omit [Algebra ℚ R] [Fintype ι] in
theorem odiff_iota (b : Module.Basis ι R M) (a : ι) (v : M) :
    odiff b a (ExteriorAlgebra.ι R v) = algebraMap R _ (b.repr v a) := by
  simp [odiff, Module.Basis.coord_apply]

omit [Algebra ℚ R] [Fintype ι] in
theorem odiff_algebraMap (b : Module.Basis ι R M) (a : ι) (r : R) :
    odiff b a (algebraMap R (ExteriorAlgebra R M) r) = 0 := by
  simp [odiff]

omit [Algebra ℚ R] [Fintype ι] in
/-- Elements of grade zero are killed by every odd derivative. -/
theorem odiff_grade_zero (b : Module.Basis ι R M) (a : ι) {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^0 M) : odiff b a x = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
  exact odiff_algebraMap b a r

omit [Algebra ℚ R] in
/-- One-vectors anticommute (base-ring general version). -/
theorem iota_swap (v w : M) :
    ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w
      = -(ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R v) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v w)

omit [Algebra ℚ R] in
/-- The number operator satisfies the graded Leibniz recursion. -/
theorem numberOp_iota_mul (b : Module.Basis ι R M) (v : M) (x : ExteriorAlgebra R M) :
    numberOp b (ExteriorAlgebra.ι R v * x)
      = ExteriorAlgebra.ι R v * (x + numberOp b x) := by
  rw [numberOp_apply]
  have hterm : ∀ a : ι,
      ExteriorAlgebra.ι R (b a) * odiff b a (ExteriorAlgebra.ι R v * x)
        = b.repr v a • (ExteriorAlgebra.ι R (b a) * x)
          + ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R (b a) * odiff b a x) := by
    intro a
    rw [odiff_iota_mul, mul_sub, mul_smul_comm, ← mul_assoc, iota_swap (b a) v,
      neg_mul, mul_assoc, sub_neg_eq_add]
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_add_distrib]
  have hrepr : (∑ a, b.repr v a • (ExteriorAlgebra.ι R (b a) * x))
      = ExteriorAlgebra.ι R v * x := by
    calc ∑ a, b.repr v a • (ExteriorAlgebra.ι R (b a) * x)
        = (∑ a, b.repr v a • ExteriorAlgebra.ι R (b a)) * x := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => (smul_mul_assoc _ _ _).symm
      _ = ExteriorAlgebra.ι R v * x := by
          congr 1
          calc ∑ a, b.repr v a • ExteriorAlgebra.ι R (b a)
              = ∑ a, ExteriorAlgebra.ι R (b.repr v a • b a) :=
                Finset.sum_congr rfl fun a _ => (map_smul _ _ _).symm
            _ = ExteriorAlgebra.ι R (∑ a, b.repr v a • b a) := (map_sum _ _ _).symm
            _ = ExteriorAlgebra.ι R v := by rw [b.sum_repr]
  rw [hrepr, ← Finset.mul_sum, ← numberOp_apply, mul_add]

omit [Algebra ℚ R] in
/-- **The odd Euler identity**: the number operator acts as `p •` on grade `p`. -/
theorem numberOp_grade (b : Module.Basis ι R M) :
    ∀ p : ℕ, ∀ x ∈ ⋀[R]^p M, numberOp b x = p • x := by
  intro p
  induction p with
  | zero =>
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
    rw [numberOp_apply, Finset.sum_eq_zero fun a _ => by
      rw [odiff_algebraMap, mul_zero], zero_smul]
  | succ p IH =>
    intro x hx
    have hx' : x ∈ LinearMap.range (ExteriorAlgebra.ι R (M := M))
        * LinearMap.range (ExteriorAlgebra.ι R (M := M)) ^ p := by
      rw [← pow_succ']
      exact hx
    refine Submodule.mul_induction_on hx' ?_ fun z w hz hw => by
      rw [map_add, hz, hw, smul_add]
    rintro m ⟨v, rfl⟩ y hy
    rw [numberOp_iota_mul, IH y hy,
      show y + p • y = (p + 1) • y from by rw [succ_nsmul]; abel, mul_smul_comm]

omit [Algebra ℚ R] [Fintype ι] in
/-- The odd derivatives lower the grade by one. -/
theorem odiff_mem (b : Module.Basis ι R M) (a : ι) :
    ∀ p : ℕ, ∀ x ∈ ⋀[R]^(p + 1) M, odiff b a x ∈ ⋀[R]^p M := by
  intro p
  induction p with
  | zero =>
    intro x hx
    have hx' : x ∈ LinearMap.range (ExteriorAlgebra.ι R (M := M)) := by
      rw [← pow_one (LinearMap.range (ExteriorAlgebra.ι R (M := M)))]
      exact hx
    obtain ⟨v, rfl⟩ := hx'
    rw [odiff_iota]
    exact Submodule.mem_one.mpr ⟨_, rfl⟩
  | succ p IH =>
    intro x hx
    have hx' : x ∈ LinearMap.range (ExteriorAlgebra.ι R (M := M))
        * LinearMap.range (ExteriorAlgebra.ι R (M := M)) ^ (p + 1) := by
      rw [← pow_succ']
      exact hx
    refine Submodule.mul_induction_on hx' ?_ fun z w hz hw => by
      rw [map_add]; exact Submodule.add_mem _ hz hw
    rintro m ⟨v, rfl⟩ y hy
    rw [odiff_iota_mul]
    refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) ?_
    have hmul := SetLike.mul_mem_graded
      (show ExteriorAlgebra.ι R v ∈ ⋀[R]^1 M from by
        have : ExteriorAlgebra.ι R v ∈ LinearMap.range (ExteriorAlgebra.ι R (M := M)) :=
          ⟨v, rfl⟩
        rwa [← pow_one (LinearMap.range (ExteriorAlgebra.ι R (M := M)))] at this)
      (IH y hy)
    rwa [show 1 + p = p + 1 from Nat.add_comm 1 p] at hmul

omit [Algebra ℚ R] in
/-- The Euler homotopy step for a homogeneous odd curl-free force family. -/
theorem homogeneous_step (b : Module.Basis ι R M) (p : ℕ)
    (F : ι → ExteriorAlgebra R M) (hF : ∀ a, F a ∈ ⋀[R]^p M)
    (hcurl : ∀ a c, odiff b a (F c) = -odiff b c (F a)) (c : ι) :
    odiff b c (∑ a, ExteriorAlgebra.ι R (b a) * F a) = (p + 1) • F c := by
  classical
  rw [map_sum]
  have hterm : ∀ a, odiff b c (ExteriorAlgebra.ι R (b a) * F a)
      = b.repr (b a) c • F a + ExteriorAlgebra.ι R (b a) * odiff b a (F c) := by
    intro a
    rw [odiff_iota_mul, hcurl c a, mul_neg, sub_neg_eq_add]
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_add_distrib]
  have h1 : (∑ a, b.repr (b a) c • F a) = F c := by
    rw [Finset.sum_congr rfl fun a _ => by
      rw [Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul]]
    rw [Finset.sum_ite_eq' Finset.univ c F, if_pos (Finset.mem_univ c)]
  rw [h1, ← numberOp_apply, numberOp_grade b p (F c) (hF c), succ_nsmul, add_comm]

omit [Algebra ℚ R] [Fintype ι] in
/-- Interior products intertwine the graded projections: `∂ₐ ∘ proj_{p+1} = proj_p ∘ ∂ₐ`. -/
theorem odiff_proj (b : Module.Basis ι R M) (a : ι) (p : ℕ) (x : ExteriorAlgebra R M) :
    odiff b a (GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i M) (p + 1) x)
      = GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i M) p (odiff b a x) := by
  classical
  have hx : x = ∑ q ∈ (DirectSum.decompose (fun i : ℕ => ⋀[R]^i M) x).support,
      (DirectSum.decompose (fun i : ℕ => ⋀[R]^i M) x q : ExteriorAlgebra R M) :=
    (DirectSum.sum_support_decompose _ x).symm
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rcases eq_or_ne q (p + 1) with rfl | hq
  · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same
      (ℳ := fun i : ℕ => ⋀[R]^i M) (SetLike.coe_mem _),
      GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same
      (ℳ := fun i : ℕ => ⋀[R]^i M) (odiff_mem b a p _ (SetLike.coe_mem _))]
  · rcases q with _ | q'
    · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne
        (ℳ := fun i : ℕ => ⋀[R]^i M) (SetLike.coe_mem _) hq, map_zero,
        odiff_grade_zero b a (SetLike.coe_mem _), map_zero]
    · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne
        (ℳ := fun i : ℕ => ⋀[R]^i M) (SetLike.coe_mem _) hq, map_zero,
        GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne
        (ℳ := fun i : ℕ => ⋀[R]^i M) (odiff_mem b a q' _ (SetLike.coe_mem _))
        (by omega)]

omit [Algebra ℚ R] in
/-- Grades above the number of odd generators vanish. -/
theorem exteriorPower_eq_bot (b : Module.Basis ι R M) {p : ℕ}
    (hp : Fintype.card ι < p) :
    (⋀[R]^p M : Submodule R (ExteriorAlgebra R M)) = ⊥ := by
  classical
  obtain e := Fintype.equivFin ι
  letI : LinearOrder ι := LinearOrder.lift' e e.injective
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  have hb := b.exteriorPower (n := p)
  have h0 : hb.repr ⟨x, hx⟩ = hb.repr 0 := by
    ext s
    exfalso
    have hcard : (s : Finset ι).card = p := Set.powersetCard.card_eq s
    have hle : (s : Finset ι).card ≤ Fintype.card ι := Finset.card_le_univ _
    omega
  have h1 := hb.repr.injective h0
  exact congrArg Subtype.val h1

/-- **The odd radial homotopy potential**: the exact Grassmann analogue of radial
integration. -/
noncomputable def oddPotential (b : Module.Basis ι R M) (F : ι → ExteriorAlgebra R M) :
    ExteriorAlgebra R M :=
  ∑ p ∈ Finset.range (Fintype.card ι + 1), algebraMap ℚ R (((p : ℚ) + 1)⁻¹) •
    ∑ a, ExteriorAlgebra.ι R (b a)
      * GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i M) p (F a)

/-- **The Grassmann Poincaré lemma (homotopy form)**: the odd radial potential integrates
an odd curl-free force family. -/
theorem odiff_oddPotential (b : Module.Basis ι R M) (F : ι → ExteriorAlgebra R M)
    (hcurl : ∀ a c, odiff b a (F c) = -odiff b c (F a)) :
    ∀ c, odiff b c (oddPotential b F) = F c := by
  classical
  set n := Fintype.card ι with hn
  set P : ℕ → ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
    fun p => GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i M) p with hP
  have hPmem : ∀ p z, P p z ∈ ⋀[R]^p M := fun p z => by
    rw [hP, GradedAlgebra.proj_apply]
    exact SetLike.coe_mem _
  have hPcurl : ∀ p, ∀ a c, odiff b a (P p (F c)) = -odiff b c (P p (F a)) := by
    intro p a c
    rcases p with _ | p'
    · rw [odiff_grade_zero b a (hPmem 0 (F c)), odiff_grade_zero b c (hPmem 0 (F a)),
        neg_zero]
    · rw [hP, odiff_proj, odiff_proj, hcurl a c, map_neg]
  intro c
  rw [show oddPotential b F = ∑ p ∈ Finset.range (n + 1),
    algebraMap ℚ R (((p : ℚ) + 1)⁻¹) •
      ∑ a, ExteriorAlgebra.ι R (b a) * P p (F a) from rfl]
  have hstep : ∀ p : ℕ, odiff b c (algebraMap ℚ R (((p : ℚ) + 1)⁻¹) •
      ∑ a, ExteriorAlgebra.ι R (b a) * P p (F a)) = P p (F c) := by
    intro p
    rw [map_smul, homogeneous_step b p (fun a => P p (F a)) (fun a => hPmem p (F a))
      (hPcurl p) c, ← Nat.cast_smul_eq_nsmul R, smul_smul]
    have hcast : algebraMap ℚ R (((p : ℚ) + 1)⁻¹) * ((p + 1 : ℕ) : R) = 1 := by
      rw [show ((p + 1 : ℕ) : R) = algebraMap ℚ R ((p + 1 : ℕ) : ℚ) from
        (map_natCast (algebraMap ℚ R) (p + 1)).symm, ← map_mul]
      rw [show (((p : ℚ) + 1)⁻¹ * ((p + 1 : ℕ) : ℚ)) = 1 from by
        push_cast
        exact inv_mul_cancel₀ (by positivity)]
      exact map_one _
    rw [hcast, one_smul]
  rw [map_sum, Finset.sum_congr rfl fun p _ => hstep p]
  -- the graded components of `F c` up to the top grade sum back to `F c`
  conv_rhs => rw [← DirectSum.sum_support_decompose (fun i : ℕ => ⋀[R]^i M) (F c)]
  have hterm : ∀ p, P p (F c)
      = (DirectSum.decompose (fun i : ℕ => ⋀[R]^i M) (F c) p : ExteriorAlgebra R M) :=
    fun p => by rw [hP, GradedAlgebra.proj_apply]
  have hsupp : (DirectSum.decompose (fun i : ℕ => ⋀[R]^i M) (F c)).support
      ⊆ Finset.range (n + 1) := by
    intro q hq
    rw [Finset.mem_range]
    by_contra hq'
    have hbot : (⋀[R]^q M : Submodule R (ExteriorAlgebra R M)) = ⊥ :=
      exteriorPower_eq_bot b (by omega)
    have hzero : (DirectSum.decompose (fun i : ℕ => ⋀[R]^i M) (F c) q
        : ExteriorAlgebra R M) = 0 :=
      (Submodule.eq_bot_iff _).mp hbot _ (SetLike.coe_mem _)
    exact (DFinsupp.mem_support_iff.mp hq) (Subtype.ext hzero)
  rw [Finset.sum_congr rfl fun p _ => hterm p]
  refine (Finset.sum_subset hsupp fun q _ hq => ?_).symm
  rw [DFinsupp.notMem_support_iff.mp hq]
  rfl

/-- **The Grassmann Poincaré lemma (existence)**: an odd curl-free force family on a
finite Grassmann bank is the family of odd derivatives of a single action. -/
theorem exists_potential (b : Module.Basis ι R M) (F : ι → ExteriorAlgebra R M)
    (hcurl : ∀ a c, odiff b a (F c) = -odiff b c (F a)) :
    ∃ S : ExteriorAlgebra R M, ∀ c, odiff b c S = F c :=
  ⟨oddPotential b F, odiff_oddPotential b F hcurl⟩

/-- **RG.1/RG.2, odd sector**: the odd curl vanishes exactly when the odd force family is
the derivative family of one action; the converse is the anticommutation of interior
products. -/
theorem odd_curl_iff_exists_potential (b : Module.Basis ι R M)
    (F : ι → ExteriorAlgebra R M) :
    (∀ a c, odiff b a (F c) = -odiff b c (F a)) ↔
      ∃ S : ExteriorAlgebra R M, ∀ c, odiff b c S = F c := by
  constructor
  · exact exists_potential b F
  · rintro ⟨S, hS⟩ a c
    rw [← hS a, ← hS c]
    exact contractLeft_comm _ _ S

end OddPoincare
end NCG
