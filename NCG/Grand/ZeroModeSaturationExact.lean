/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.GrassmannPairCalculusExact
import NCG.Grand.FermionicExponentialExact

/-!
# Finite zero-mode factorization and saturation

Exact formalization for `thm:SMST-zero-mode-saturation` (SMQ.1–SMQ.3).

* **SMQ.1** (`det_line_dim_one`, `line_factorization`): each determinant line is
  one-dimensional (`finrank ⋀^d = (d).choose d = 1`), and on zero-mode-adapted generator
  families the top Grassmann monomial factors exactly into the kernel block times the
  regular block.
* **SMQ.2** (`reduced_determinant_norm`, `reduced_determinant_ne_zero`): the reduced
  determinant satisfies `‖det D'‖ = ∏ singular values` and is nonzero for invertible `D'`.
* **SMQ.3** (`saturated_projection`): the top-degree component of
  `e^{-ψ̄Dψ} ∏_{a≤k} ψ̄ₐψₐ` is exactly `det D'` times the top Grassmann monomial — the
  fermionic exponential saturates through its factorial-normalized top power and the
  Gaussian evaluates to the reduced determinant.  The **unsaturated vacuum integral
  vanishes** (`vacuum_vanishes`): without the zero-mode insertion the exponential never
  reaches top degree.
-/

open ExteriorAlgebra

namespace NCG
namespace ZeroMode

noncomputable section

/-! ### The `noncommProd`–`List.ofFn` bridge -/

theorem noncommProd_univ_fin {A : Type*} [Monoid A] {e : ℕ} (f : Fin e → A)
    (h : (↑(Finset.univ : Finset (Fin e)) : Set (Fin e)).Pairwise
      (Function.onFun Commute f)) :
    Finset.univ.noncommProd f h = (List.ofFn f).prod := by
  rw [List.ofFn_eq_map]
  exact Multiset.noncommProd_coe (List.map f (List.finRange e)) _

/-! ### Grading of pair products -/

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- A Grassmann pair lives in degree two. -/
theorem pair_mem_grade_two (x y : M) : ι ℂ x * ι ℂ y ∈ ⋀[ℂ]^2 M := by
  have h : ι ℂ x * ι ℂ y = ιMulti ℂ 2 ![x, y] := by
    rw [ιMulti_apply]
    simp
  rw [h]
  exact ιMulti_range ℂ 2 (Set.mem_range_self _)

/-- A product of `r` pairs lives in degree `2r`. -/
theorem prod_pairs_mem (r : ℕ) (a b : Fin r → M) :
    (List.ofFn fun i => ι ℂ (a i) * ι ℂ (b i)).prod ∈ ⋀[ℂ]^(2 * r) M := by
  induction r with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Nat.mul_zero]
    exact SetLike.GradedOne.one_mem
  | succ r IH =>
    rw [List.ofFn_succ, List.prod_cons]
    have h := SetLike.mul_mem_graded (pair_mem_grade_two (a 0) (b 0))
      (IH (fun i => a i.succ) (fun i => b i.succ))
    have he : 2 + 2 * r = 2 * (r + 1) := by ring
    rwa [he] at h

/-! ### The zero-mode-adapted fermionic integral -/

variable {k e : ℕ} (zb z : Fin k → M) (a : Fin e → M) (g : (Fin e → ℂ) →ₗ[ℂ] M)
  (D' : Matrix (Fin e) (Fin e) ℂ)

/-- The Gaussian pair field `βᵢ = ψ̄ᵢ ∧ χᵢ` of the regular block. -/
noncomputable def beta (i : Fin e) : ExteriorAlgebra ℂ M := ι ℂ (a i) * ι ℂ (g (D' i))

/-- The quadratic action element `ω = ∑ᵢ βᵢ = -ψ̄Dψ`. -/
noncomputable def omegaAct : ExteriorAlgebra ℂ M := ∑ i, beta a g D' i

/-- The zero-mode insertion `∏_{q<k} ψ̄_q ψ_q`. -/
noncomputable def insertionK : ExteriorAlgebra ℂ M :=
  (List.ofFn fun q => ι ℂ (zb q) * ι ℂ (z q)).prod

/-- The unit-normalized regular-block top monomial. -/
noncomputable def unitPairs : ExteriorAlgebra ℂ M :=
  (List.ofFn fun i => ι ℂ (a i) * ι ℂ (g (Pi.single i 1))).prod

/-- The fermionic exponential `e^ω` — a polynomial, by nilpotence. -/
noncomputable def fexp : ExteriorAlgebra ℂ M :=
  ∑ p ∈ Finset.range (e + 1), ((p.factorial : ℂ))⁻¹ • omegaAct a g D' ^ p

theorem beta_commute (i j : Fin e) : Commute (beta a g D' i) (beta a g D' j) :=
  Grassmann.pair_commute _ _ _ _

theorem beta_sq_zero (i : Fin e) : beta a g D' i * beta a g D' i = 0 := by
  have h := Grassmann.pair_mul_pair_same (a i) (a i) (g (D' i))
  exact h

/-- **Nilpotence**: `ω^p = 0` for `p > e`. -/
theorem omega_pow_eq_zero {p : ℕ} (hp : e < p) : omegaAct a g D' ^ p = 0 := by
  have h := Fermionic.sum_pow_eq_zero_of_card_lt (beta a g D')
    (beta_commute a g D') (beta_sq_zero a g D') Finset.univ
    (by rwa [Finset.card_univ, Fintype.card_fin])
  exact h

/-- **Factorial saturation**: `ω^e = e! • ∏ᵢ βᵢ`. -/
theorem omega_pow_card :
    omegaAct a g D' ^ e = e.factorial • (List.ofFn (beta a g D')).prod := by
  have h := Fermionic.sum_pow_card (beta a g D')
    (beta_commute a g D') (beta_sq_zero a g D') Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [show omegaAct a g D' = ∑ i ∈ Finset.univ, beta a g D' i from rfl, h]
  congr 1
  exact noncommProd_univ_fin _ _

/-- **The Gaussian evaluates to the reduced determinant**: `∏ᵢ βᵢ = det D' • ∏ᵢ ψ̄ᵢψᵢ`. -/
theorem gaussian_eval :
    (List.ofFn (beta a g D')).prod = D'.det • unitPairs a g := by
  have h := Grassmann.fermionic_gaussian_general a g D'
  exact h

theorem omega_mem : omegaAct a g D' ∈ ⋀[ℂ]^2 M :=
  Submodule.sum_mem _ fun _ _ => pair_mem_grade_two _ _

theorem omega_pow_mem (p : ℕ) : omegaAct a g D' ^ p ∈ ⋀[ℂ]^(2 * p) M := by
  have h := SetLike.pow_mem_graded p (omega_mem a g D')
  rwa [show p • 2 = 2 * p from by rw [smul_eq_mul, Nat.mul_comm]] at h

theorem insertionK_mem : insertionK zb z ∈ ⋀[ℂ]^(2 * k) M := prod_pairs_mem k zb z

theorem unitPairs_mem : unitPairs a g ∈ ⋀[ℂ]^(2 * e) M := prod_pairs_mem e a _

/-- **SMQ.3, saturation**: the top-degree component of `e^ω ∏_{q<k} ψ̄_q ψ_q` is exactly
`det D'` times the top Grassmann monomial: the insertion supplies exactly the missing
zero-mode degree, the fermionic exponential saturates through its factorial-normalized
top power, and the Gaussian evaluates to the reduced determinant. -/
theorem saturated_projection :
    GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i M) (2 * e + 2 * k)
        (fexp a g D' * insertionK zb z)
      = D'.det • (unitPairs a g * insertionK zb z) := by
  classical
  rw [fexp, Finset.sum_mul, map_sum]
  rw [Finset.sum_eq_single e]
  · have hval : ((e.factorial : ℂ))⁻¹ • omegaAct a g D' ^ e * insertionK zb z
        = D'.det • (unitPairs a g * insertionK zb z) := by
      rw [omega_pow_card, gaussian_eval, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr e.factorial_ne_zero),
        one_mul, smul_mul_assoc]
    have hmem : unitPairs a g * insertionK zb z ∈ ⋀[ℂ]^(2 * e + 2 * k) M :=
      SetLike.mul_mem_graded (unitPairs_mem a g) (insertionK_mem zb z)
    rw [hval, LinearMap.map_smul, GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_same (ℳ := fun i : ℕ => ⋀[ℂ]^i M) hmem]
  · intro p hp hpe
    have hplt : p < e := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)) hpe
    rw [smul_mul_assoc, LinearMap.map_smul]
    have hmem : omegaAct a g D' ^ p * insertionK zb z ∈ ⋀[ℂ]^(2 * p + 2 * k) M :=
      SetLike.mul_mem_graded (omega_pow_mem a g D' p) (insertionK_mem zb z)
    rw [GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_ne (ℳ := fun i : ℕ => ⋀[ℂ]^i M) hmem (by omega)]
    rw [smul_zero]
  · intro h
    exact absurd (Finset.self_mem_range_succ e) h

/-- **SMQ.3, vacuum vanishing**: without the zero-mode insertion the fermionic exponential
never reaches top degree — the unsaturated vacuum integral vanishes. -/
theorem vacuum_vanishes (hk : 0 < k) :
    GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i M) (2 * e + 2 * k) (fexp a g D') = 0 := by
  classical
  rw [fexp, map_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpe : p ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  rw [LinearMap.map_smul, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_ne (ℳ := fun i : ℕ => ⋀[ℂ]^i M)
      (omega_pow_mem a g D' p) (by omega), smul_zero]

/-! ### SMQ.1: the determinant lines and the adapted factorization -/

/-- Every determinant line is one-dimensional: `dim ⋀^d W = C(d,d) = 1`. -/
theorem det_line_dim_one {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] :
    Module.finrank ℂ (⋀[ℂ]^(Module.finrank ℂ W) W) = 1 := by
  rw [exteriorPower.finrank_eq]
  exact Nat.choose_self _

/-- The determinant line of a finite-dimensional complex carrier. -/
abbrev DetLine (W : Type*) [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] :=
  ⋀[ℂ]^(Module.finrank ℂ W) W

/-- The chiral amplitude line `(det Hplus)^* tensor det Hminus`. -/
abbrev ChiralAmplitudeLine (Hplus Hminus : Type*)
    [AddCommGroup Hplus] [Module ℂ Hplus] [FiniteDimensional ℂ Hplus]
    [AddCommGroup Hminus] [Module ℂ Hminus] [FiniteDimensional ℂ Hminus] :=
  TensorProduct ℂ (Module.Dual ℂ (DetLine Hplus)) (DetLine Hminus)

/-- The zero-mode determinant line `det Kminus tensor (det Kplus)^*`. -/
abbrev ZeroModeLine (Kplus Kminus : Type*)
    [AddCommGroup Kplus] [Module ℂ Kplus] [FiniteDimensional ℂ Kplus]
    [AddCommGroup Kminus] [Module ℂ Kminus] [FiniteDimensional ℂ Kminus] :=
  TensorProduct ℂ (DetLine Kminus) (Module.Dual ℂ (DetLine Kplus))

/-- The reduced determinant line `det Eminus tensor (det Eplus)^*`. -/
abbrev ReducedLine (Eplus Eminus : Type*)
    [AddCommGroup Eplus] [Module ℂ Eplus] [FiniteDimensional ℂ Eplus]
    [AddCommGroup Eminus] [Module ℂ Eminus] [FiniteDimensional ℂ Eminus] :=
  TensorProduct ℂ (DetLine Eminus) (Module.Dual ℂ (DetLine Eplus))

/-- **SMQ.1 as an actual line isomorphism.**  For the orthogonal direct-sum
carriers `Hplus = Kplus x Eplus` and `Hminus = Kminus x Eminus`, the chiral
amplitude line is linearly isomorphic to the tensor product of the zero-mode
and reduced determinant lines.  `line_factorization` below identifies this
isomorphism on every zero-mode-adapted top generator. -/
theorem determinant_line_factorization
    {Kplus Kminus Eplus Eminus : Type*}
    [AddCommGroup Kplus] [Module ℂ Kplus] [FiniteDimensional ℂ Kplus]
    [AddCommGroup Kminus] [Module ℂ Kminus] [FiniteDimensional ℂ Kminus]
    [AddCommGroup Eplus] [Module ℂ Eplus] [FiniteDimensional ℂ Eplus]
    [AddCommGroup Eminus] [Module ℂ Eminus] [FiniteDimensional ℂ Eminus] :
    Nonempty
      (ChiralAmplitudeLine (Kplus × Eplus) (Kminus × Eminus) ≃ₗ[ℂ]
        TensorProduct ℂ (ZeroModeLine Kplus Kminus)
          (ReducedLine Eplus Eminus)) := by
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  simp [ChiralAmplitudeLine, ZeroModeLine, ReducedLine, DetLine,
    Module.finrank_tensorProduct, Subspace.dual_finrank_eq,
    det_line_dim_one]

/-- **SMQ.1, adapted factorization**: on zero-mode-adapted generator families the top
Grassmann monomial factors exactly as (kernel block) × (regular block) — the canonical
factorization of the determinant line realized on adapted generators. -/
theorem line_factorization (c d : Fin k → M) (u v : Fin e → M) :
    (List.ofFn fun p : Fin (k + e) =>
        ι ℂ (Fin.append c u p) * ι ℂ (Fin.append d v p)).prod
      = (List.ofFn fun q => ι ℂ (c q) * ι ℂ (d q)).prod
        * (List.ofFn fun i => ι ℂ (u i) * ι ℂ (v i)).prod := by
  have hfun : (fun p : Fin (k + e) => ι ℂ (Fin.append c u p) * ι ℂ (Fin.append d v p))
      = Fin.append (fun q => ι ℂ (c q) * ι ℂ (d q)) (fun i => ι ℂ (u i) * ι ℂ (v i)) := by
    funext p
    rcases p with ⟨pv, hpv⟩
    by_cases hcase : pv < k
    · rw [show (⟨pv, hpv⟩ : Fin (k + e)) = Fin.castAdd e ⟨pv, hcase⟩ from rfl,
        Fin.append_left, Fin.append_left, Fin.append_left]
    · have hle : k ≤ pv := Nat.le_of_not_lt hcase
      obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [show (⟨k + q, hpv⟩ : Fin (k + e)) = Fin.natAdd k ⟨q, by omega⟩ from rfl,
        Fin.append_right, Fin.append_right, Fin.append_right]
  rw [hfun, List.ofFn_fin_append, List.prod_append]

/-! ### SMQ.2: the reduced determinant and singular values -/

/-- **SMQ.2**: `‖det D'‖` is the product of the singular values of the reduced map. -/
theorem reduced_determinant_norm (D' : Matrix (Fin e) (Fin e) ℂ) :
    ‖D'.det‖ = ∏ i ∈ Finset.range e,
      (Matrix.toEuclideanLin D' : EuclideanSpace ℂ (Fin e) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin e)).singularValues i := by
  have h1 : (Matrix.toEuclideanLin D' : EuclideanSpace ℂ (Fin e) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin e)).normDet = ‖D'.det‖ := by
    rw [LinearMap.normDet_eq_norm_det]
    congr 1
    have heq : Matrix.toEuclideanLin D' = Matrix.toLin (PiLp.basisFun 2 ℂ (Fin e))
        (PiLp.basisFun 2 ℂ (Fin e)) D' := rfl
    rw [heq, LinearMap.det_toLin]
  have h2 := LinearMap.normDet_eq_prod_singularValues
    (Matrix.toEuclideanLin D' : EuclideanSpace ℂ (Fin e) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin e))
  rw [h1] at h2
  rw [h2]
  congr 1
  simp [finrank_euclideanSpace]

/-- The reduced determinant is nonzero for an invertible regular block. -/
theorem reduced_determinant_ne_zero {D' : Matrix (Fin e) (Fin e) ℂ}
    (hD' : IsUnit D'.det) : ‖D'.det‖ ≠ 0 :=
  norm_ne_zero_iff.mpr hD'.ne_zero

/-- **Bundle for `thm:SMST-zero-mode-saturation`**: SMQ.1 (one-dimensional determinant
lines, adapted top-monomial factorization), SMQ.2 (reduced determinant norm = product of
singular values, nonvanishing), SMQ.3 (top-degree saturation with insertion equals
`det D'` times the top monomial; the unsaturated vacuum vanishes). -/
theorem smst_zero_mode_saturation {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (hk : 0 < k)
    {D' : Matrix (Fin e) (Fin e) ℂ} (hD' : IsUnit D'.det) :
    Module.finrank ℂ (⋀[ℂ]^(Module.finrank ℂ W) W) = 1 ∧
    ‖D'.det‖ = (∏ i ∈ Finset.range e,
      (Matrix.toEuclideanLin D' : EuclideanSpace ℂ (Fin e) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin e)).singularValues i) ∧
    ‖D'.det‖ ≠ 0 ∧
    GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i M) (2 * e + 2 * k)
        (fexp a g D' * insertionK zb z)
      = D'.det • (unitPairs a g * insertionK zb z) ∧
    GradedAlgebra.proj (fun i : ℕ => ⋀[ℂ]^i M) (2 * e + 2 * k) (fexp a g D') = 0 :=
  ⟨det_line_dim_one, reduced_determinant_norm D', reduced_determinant_ne_zero hD',
   saturated_projection zb z a g D', vacuum_vanishes a g D' hk⟩

end
end ZeroMode
end NCG
