/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Grassmann pair calculus and the fermionic Gaussian determinant

Machinery for `thm:SMST-zero-mode-saturation` (SMQ.3) and other Berezin-integral records.

Inside the exterior algebra `⋀ M`, degree-two "pairs" `ι a * ι b` pairwise commute
(`pair_commute`), and a product containing two pairs with a common second leg vanishes
(`pair_mul_pair_same`).  A product of slots `ψ̄ᵢ ∧ vᵢ` is therefore an alternating
multilinear function of the second legs (`pairProd`), and every alternating map from an
`m`-dimensional space in `m` slots is `det`-proportional to its basis value
(`AlternatingMap.eq_det_smul_of_basis`).  Together these give the exact fermionic Gaussian:

`∏ᵢ (ψ̄ᵢ ∧ χᵢ) = det D • ∏ᵢ (ψ̄ᵢ ∧ ψᵢ)`   where  `χᵢ = ∑ⱼ Dᵢⱼ ψⱼ`

(`fermionic_gaussian`) — the Grassmann–Gaussian integral evaluates to the determinant,
with no permutation-sign bookkeeping.
-/

open ExteriorAlgebra

namespace NCG
namespace Grassmann

/-! ### Generic zero-product extraction in a ring -/

/-- If a list contains, at positions `i < j`, elements whose ordered product is zero, and the
`j`-th element commutes with everything in the list, the whole product vanishes. -/
theorem list_prod_eq_zero_of_pair {A : Type*} [Ring A] (l : List A) (i j : ℕ)
    (hij : i < j) (hj : j < l.length)
    (hcomm : ∀ a ∈ l, Commute a l[j]) (h0 : l[i] * l[j] = 0) : l.prod = 0 := by
  have hi : i < l.length := hij.trans hj
  -- split at position i
  have hsplit1 : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i l]
    congr 1
    exact List.drop_eq_getElem_cons hi
  -- position of j inside the tail
  have hjd : j - (i + 1) < (l.drop (i + 1)).length := by
    rw [List.length_drop]
    omega
  have hgetj : (l.drop (i + 1))[j - (i + 1)] = l[j] := by
    rw [List.getElem_drop]
    congr 1
    omega
  have hsplit2 : l.drop (i + 1)
      = (l.drop (i + 1)).take (j - (i + 1)) ++ l[j] :: (l.drop (i + 1)).drop (j - i) := by
    conv_lhs => rw [← List.take_append_drop (j - (i + 1)) (l.drop (i + 1))]
    congr 1
    rw [List.drop_eq_getElem_cons hjd, hgetj]
    congr 2
    omega
  set mid := (l.drop (i + 1)).take (j - (i + 1)) with hmid
  have hmemmid : ∀ a ∈ mid, Commute a l[j] := fun a ha =>
    hcomm a (List.mem_of_mem_drop (List.mem_of_mem_take ha))
  have hcm : Commute l[j] mid.prod :=
    (Commute.list_prod_right _ _ fun b hb => (hmemmid b hb).symm)
  calc l.prod
      = (l.take i).prod * (l[i] * (mid.prod * (l[j]
          * ((l.drop (i + 1)).drop (j - i)).prod))) := by
        conv_lhs => rw [hsplit1]
        rw [List.prod_append, List.prod_cons]
        congr 1
        conv_lhs => rw [hsplit2]
        rw [List.prod_append, List.prod_cons]
    _ = (l.take i).prod * ((l[i] * l[j]) * (mid.prod
          * ((l.drop (i + 1)).drop (j - i)).prod)) := by
        congr 1
        rw [← mul_assoc mid.prod, ← hcm.eq, mul_assoc, ← mul_assoc]
    _ = 0 := by rw [h0, zero_mul, mul_zero]

/-! ### Pair calculus in the exterior algebra -/

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- One-vectors anticommute. -/
theorem iota_swap (x y : M) : ι ℂ x * ι ℂ y = -(ι ℂ y * ι ℂ x) :=
  eq_neg_of_add_eq_zero_left (ι_add_mul_swap x y)

/-- Moving a one-vector past another inside a right-associated product flips the sign. -/
theorem iota_move (x y : M) (z : ExteriorAlgebra ℂ M) :
    ι ℂ x * (ι ℂ y * z) = -(ι ℂ y * (ι ℂ x * z)) := by
  rw [← mul_assoc, iota_swap x y, neg_mul, mul_assoc]

/-- Degree-two pairs commute with each other. -/
theorem pair_commute (a b c d : M) :
    Commute (ι ℂ a * ι ℂ b) (ι ℂ c * ι ℂ d) := by
  unfold Commute SemiconjBy
  simp only [mul_assoc]
  calc ι ℂ a * (ι ℂ b * (ι ℂ c * ι ℂ d))
      = ι ℂ a * (-(ι ℂ c * (ι ℂ b * ι ℂ d))) := by rw [iota_move b c]
    _ = -(ι ℂ a * (ι ℂ c * (ι ℂ b * ι ℂ d))) := by rw [mul_neg]
    _ = -(-(ι ℂ c * (ι ℂ a * (ι ℂ b * ι ℂ d)))) := by rw [iota_move a c]
    _ = ι ℂ c * (ι ℂ a * (ι ℂ b * ι ℂ d)) := by rw [neg_neg]
    _ = ι ℂ c * (ι ℂ a * (-(ι ℂ d * ι ℂ b))) := by rw [iota_swap b d]
    _ = -(ι ℂ c * (ι ℂ a * (ι ℂ d * ι ℂ b))) := by rw [mul_neg, mul_neg]
    _ = -(-(ι ℂ c * (ι ℂ d * (ι ℂ a * ι ℂ b)))) := by rw [iota_move a d, mul_neg]
    _ = ι ℂ c * (ι ℂ d * (ι ℂ a * ι ℂ b)) := by rw [neg_neg]

/-- Two pairs with the same second leg multiply to zero. -/
theorem pair_mul_pair_same (a b w : M) :
    (ι ℂ a * ι ℂ w) * (ι ℂ b * ι ℂ w) = 0 := by
  simp only [mul_assoc]
  rw [iota_move w b, ι_sq_zero, mul_zero, neg_zero, mul_zero]

/-! ### The pair-product alternating map -/

variable {m : ℕ}

/-- The pair product `∏ᵢ (ψ̄ᵢ ∧ vᵢ)` as a multilinear map in the second legs. -/
noncomputable def pairProd (a : Fin m → M) :
    MultilinearMap ℂ (fun _ : Fin m => M) (ExteriorAlgebra ℂ M) :=
  (MultilinearMap.mkPiAlgebraFin ℂ m (ExteriorAlgebra ℂ M)).compLinearMap
    fun i => LinearMap.mulLeft ℂ (ι ℂ (a i)) ∘ₗ ι ℂ

theorem pairProd_apply (a v : Fin m → M) :
    pairProd a v = (List.ofFn fun i => ι ℂ (a i) * ι ℂ (v i)).prod := by
  simp [pairProd, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply]

/-- The pair product is alternating in the second legs. -/
noncomputable def pairProdAlt (a : Fin m → M) :
    M [⋀^Fin m]→ₗ[ℂ] ExteriorAlgebra ℂ M where
  toMultilinearMap := pairProd a
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    change pairProd a v = 0
    rw [pairProd_apply]
    rcases lt_or_gt_of_ne hij with h | h
    · refine list_prod_eq_zero_of_pair _ i j h (by simp) ?_ ?_
      · intro x hx
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
        simp only [List.getElem_ofFn]
        exact pair_commute _ _ _ _
      · simp only [List.getElem_ofFn]
        rw [show v ⟨j, by simp⟩ = v ⟨i, by simp⟩ from by simpa using hv.symm]
        exact pair_mul_pair_same _ _ _
    · refine list_prod_eq_zero_of_pair _ j i h (by simp) ?_ ?_
      · intro x hx
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
        simp only [List.getElem_ofFn]
        exact pair_commute _ _ _ _
      · simp only [List.getElem_ofFn]
        rw [show v ⟨i, by simp⟩ = v ⟨j, by simp⟩ from by simpa using hv]
        exact pair_mul_pair_same _ _ _

theorem pairProdAlt_apply (a v : Fin m → M) :
    pairProdAlt a v = (List.ofFn fun i => ι ℂ (a i) * ι ℂ (v i)).prod :=
  pairProd_apply a v

/-! ### Alternating maps are determinant-proportional -/

/-- **Every alternating map from an `m`-dimensional space in `m` slots is
`det`-proportional to its value on a basis.** -/
theorem _root_.AlternatingMap.eq_det_smul_of_basis {W N : Type*} [AddCommGroup W]
    [Module ℂ W] [AddCommGroup N] [Module ℂ N]
    (e : Module.Basis (Fin m) ℂ W) (f : W [⋀^Fin m]→ₗ[ℂ] N) (v : Fin m → W) :
    f v = e.det v • f e := by
  have hf : f = AlternatingMap.smulRight e.det (f e) := by
    refine Module.Basis.ext_alternating e fun w hw => ?_
    have hbij : Function.Bijective w := Finite.injective_iff_bijective.mp hw
    set σ : Equiv.Perm (Fin m) := Equiv.ofBijective w hbij with hσ
    have hwσ : (fun i => e (w i)) = (fun i => e i) ∘ σ := rfl
    rw [hwσ, AlternatingMap.map_perm, AlternatingMap.smulRight_apply,
      AlternatingMap.map_perm, Module.Basis.det_self]
    simp
  conv_lhs => rw [hf]
  simp [AlternatingMap.smulRight_apply]

/-! ### The fermionic Gaussian -/

/-- The doubled coefficient module carrying `ψ̄` (left) and `ψ` (right) generators. -/
abbrev Doubled (m : ℕ) := (Fin m → ℂ) × (Fin m → ℂ)

/-- The `ψ̄` generators. -/
noncomputable def psibar (i : Fin m) : ExteriorAlgebra ℂ (Doubled m) :=
  ι ℂ (Pi.single i 1, 0)

/-- The `ψ` generators. -/
noncomputable def psi (j : Fin m) : ExteriorAlgebra ℂ (Doubled m) :=
  ι ℂ (0, Pi.single j 1)

/-- The right-leg embedding. -/
noncomputable def psiEmbed : (Fin m → ℂ) →ₗ[ℂ] Doubled m := LinearMap.inr ℂ _ _

/-- **The general fermionic Gaussian**: for any `ψ̄`-family `a` and any linear embedding `g`
of the coefficient space into the fermion module, `∏ᵢ (ι(aᵢ) ∧ ι(g(Dᵢ))) = det D • ∏ᵢ
(ι(aᵢ) ∧ ι(g(eᵢ)))`.  The Grassmann–Gaussian pairing evaluates to the determinant. -/
theorem fermionic_gaussian_general (a : Fin m → M) (g : (Fin m → ℂ) →ₗ[ℂ] M)
    (D : Matrix (Fin m) (Fin m) ℂ) :
    (List.ofFn fun i => ι ℂ (a i) * ι ℂ (g (D i))).prod
      = D.det • (List.ofFn fun i => ι ℂ (a i) * ι ℂ (g (Pi.single i 1))).prod := by
  set G : (Fin m → ℂ) [⋀^Fin m]→ₗ[ℂ] ExteriorAlgebra ℂ M :=
    (pairProdAlt a).compLinearMap g with hG
  have hGapply : ∀ v : Fin m → Fin m → ℂ,
      G v = (List.ofFn fun i => ι ℂ (a i) * ι ℂ (g (v i))).prod := by
    intro v
    rw [hG, AlternatingMap.compLinearMap_apply, pairProdAlt_apply]
  have h1 : G (fun i => D i) = (Pi.basisFun ℂ (Fin m)).det (fun i => D i)
      • G (Pi.basisFun ℂ (Fin m)) :=
    AlternatingMap.eq_det_smul_of_basis (Pi.basisFun ℂ (Fin m)) G _
  have hdet : (Pi.basisFun ℂ (Fin m)).det (fun i => D i) = D.det := by
    rw [Pi.basisFun_det_apply]
    rfl
  have hbasis : G (Pi.basisFun ℂ (Fin m))
      = (List.ofFn fun i => ι ℂ (a i) * ι ℂ (g (Pi.single i 1))).prod := by
    rw [hGapply]
    simp only [Pi.basisFun_apply]
  calc (List.ofFn fun i => ι ℂ (a i) * ι ℂ (g (D i))).prod
      = G fun i => D i := (hGapply fun i => D i).symm
    _ = D.det • G (Pi.basisFun ℂ (Fin m)) := by rw [h1, hdet]
    _ = D.det • (List.ofFn fun i => ι ℂ (a i) * ι ℂ (g (Pi.single i 1))).prod := by
        rw [hbasis]

/-- **The fermionic Gaussian** on the doubled module: `∏ᵢ (ψ̄ᵢ ∧ χᵢ) = det D • ∏ᵢ (ψ̄ᵢ ∧ ψᵢ)`
where `χᵢ = ∑ⱼ Dᵢⱼ ψⱼ` is the row field of the action matrix. -/
theorem fermionic_gaussian (D : Matrix (Fin m) (Fin m) ℂ) :
    (List.ofFn fun i => psibar i * ι ℂ (psiEmbed (D i))).prod
      = D.det • (List.ofFn fun i => psibar i * psi i).prod := by
  have h := fermionic_gaussian_general (M := Doubled m)
    (fun i => (Pi.single i 1, 0)) psiEmbed D
  simpa [psibar, psi, psiEmbed, LinearMap.inr_apply] using h

end Grassmann
end NCG
