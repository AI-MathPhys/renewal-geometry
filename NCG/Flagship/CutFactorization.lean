/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.ChronologyLeakage

/-!
# Complete renewal-cut factorization
  (`thm:complete-cut-factorization-master`,
   `cor:resolved-memory-factorization-master`,
   flagship manuscript)

At a complete renewal cut with irreducible loaded past action
(irreducibility rendered as the scalar-commutant property, the
finite-dimensional Schur characterization — disclosed):

* every natural post-cut control factorizes,
  `W_y = I_past ⊗ V_y` (`cut_commutant_factorizes`, by the block
  computation `{U_g ⊗ I}' = I ⊗ B(F)`);
* applied to the past–fresh split, the complete polarized source
  factors, `Ξ(x,y) = ξ_past(x) ⊗ ξ_fut(y)`
  (`cut_source_product`);
* hence the boxed kernel product
  `K((x,y),(x',y')) = K((x,0),(x',0))·K((0,y),(0,y'))` for unit
  basepoints (`complete_cut_kernel_factorization`);
* `cor:resolved-memory-factorization-master`: on each resolved
  orthogonal sector the boxed conditional product
  `K_z = K_z^past·K_z^fut` holds, and the unconditional kernel is
  the finite direct sum of the sector products
  (`resolved_memory_factorization`).

Slot transitivity, the identical serial root, and the isotypic
location of residual memory in the reducible case are prose
(disclosed).  Vectors are finite tuples with the sesquilinear
`star ⬝ᵥ` pairing and `kronVec` tensors.
-/

open Matrix Kronecker Finset

namespace NCG

variable {P F : Type*} [Fintype P] [Fintype F] [DecidableEq P]
  [DecidableEq F]

/-- Schur-commutant factorization: a tensor operator commuting
with an irreducible past action `U_g ⊗ I` is `I ⊗ V`. -/
theorem cut_commutant_factorizes {G : Type*} (U : G → Matrix P P ℂ)
    (hirr : ∀ M : Matrix P P ℂ,
      (∀ g, U g * M = M * U g) → ∃ c : ℂ, M = c • 1)
    (W : Matrix (P × F) (P × F) ℂ)
    (hnat : ∀ g, W * (U g ⊗ₖ (1 : Matrix F F ℂ))
      = (U g ⊗ₖ (1 : Matrix F F ℂ)) * W) :
    ∃ V : Matrix F F ℂ, W = (1 : Matrix P P ℂ) ⊗ₖ V := by
  have hL : ∀ (g : G) (p : P) (f : F) (q' : P) (e' : F),
      (W * (U g ⊗ₖ (1 : Matrix F F ℂ))) (p, f) (q', e')
        = ∑ q, W (p, f) (q, e') * U g q q' := by
    intro g p f q' e'
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single e']
    · simp
    · intro ee _ hee
      simp [hee]
    · intro h
      exact absurd (Finset.mem_univ e') h
  have hR : ∀ (g : G) (p : P) (f : F) (q' : P) (e' : F),
      ((U g ⊗ₖ (1 : Matrix F F ℂ)) * W) (p, f) (q', e')
        = ∑ q, U g p q * W (q, f) (q', e') := by
    intro g p f q' e'
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single f]
    · simp
    · intro ee _ hee
      simp [Ne.symm hee]
    · intro h
      exact absurd (Finset.mem_univ f) h
  have hblock : ∀ f e : F, ∃ c : ℂ,
      (Matrix.of fun p q => W (p, f) (q, e)) = c • 1 := by
    intro f e
    refine hirr _ fun g => ?_
    ext p p'
    have h := congrArg (fun M => M (p, f) (p', e)) (hnat g)
    rw [hL, hR] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply]
    exact h.symm
  choose v hv using hblock
  refine ⟨Matrix.of fun f e => v f e, ?_⟩
  ext ⟨p, f⟩ ⟨q, e⟩
  have h := congrArg (fun M => M p q) (hv f e)
  simp only [Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul] at h
  rw [Matrix.kroneckerMap_apply, Matrix.of_apply, h,
    Matrix.one_apply]
  by_cases hpq : p = q <;> simp [hpq, mul_comm]

omit [DecidableEq F] in
/-- The factored control acts only on the fresh factor:
`Ξ(x,y) = ξ_past(x) ⊗ ξ_fut(y)`. -/
lemma cut_source_product (V : Matrix F F ℂ) (a : P → ℂ)
    (Ω : F → ℂ) :
    ((1 : Matrix P P ℂ) ⊗ₖ V) *ᵥ kronVec a Ω
      = kronVec a (V *ᵥ Ω) := by
  rw [mulVec_kronVec, Matrix.one_mulVec]

omit [DecidableEq P] [DecidableEq F] in
/-- `thm:complete-cut-factorization-master`, boxed kernel
product: with unit basepoints,
`K((x,y),(x',y')) = K((x,0),(x',0))·K((0,y),(0,y'))`. -/
theorem complete_cut_kernel_factorization
    {Xt Yt : Type*} (ξp : Xt → (P → ℂ)) (ξf : Yt → (F → ℂ))
    (x0 : Xt) (y0 : Yt)
    (hp0 : star (ξp x0) ⬝ᵥ ξp x0 = 1)
    (hf0 : star (ξf y0) ⬝ᵥ ξf y0 = 1)
    (x x' : Xt) (y y' : Yt) :
    star (kronVec (ξp x) (ξf y)) ⬝ᵥ kronVec (ξp x') (ξf y')
      = (star (kronVec (ξp x) (ξf y0))
          ⬝ᵥ kronVec (ξp x') (ξf y0))
        * (star (kronVec (ξp x0) (ξf y))
            ⬝ᵥ kronVec (ξp x0) (ξf y')) := by
  rw [star_kronVec_dotProduct, star_kronVec_dotProduct,
    star_kronVec_dotProduct, hp0, hf0]
  ring

omit [DecidableEq P] [DecidableEq F] in
/-- `cor:resolved-memory-factorization-master`, boxed sector
product and the direct-sum mixture: on every resolved sector
`K_z = K_z^past·K_z^fut`, and the unconditional kernel is the
finite sum of the sector products. -/
theorem resolved_memory_factorization
    {Z Xt Yt : Type*} [Fintype Z]
    (ξp : Z → Xt → (P → ℂ)) (ξf : Z → Yt → (F → ℂ))
    (x x' : Xt) (y y' : Yt) :
    (∀ z, star (kronVec (ξp z x) (ξf z y))
        ⬝ᵥ kronVec (ξp z x') (ξf z y')
      = (star (ξp z x) ⬝ᵥ ξp z x')
        * (star (ξf z y) ⬝ᵥ ξf z y'))
    ∧ ∑ z, star (kronVec (ξp z x) (ξf z y))
        ⬝ᵥ kronVec (ξp z x') (ξf z y')
      = ∑ z, (star (ξp z x) ⬝ᵥ ξp z x')
          * (star (ξf z y) ⬝ᵥ ξf z y') := by
  refine ⟨fun z => star_kronVec_dotProduct _ _ _ _, ?_⟩
  exact Finset.sum_congr rfl fun z _ =>
    star_kronVec_dotProduct _ _ _ _

end NCG
