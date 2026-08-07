/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.DetDerivative

/-!
# Boundary spectral-shift identity
  (`thm:boundary-spectral-shift`, Gran-Tensor manuscript)

* `boundary_det_ratio`: for two boundary loads over one common
  interior, `det(𝔸ᵢ - z) = det(D - z)·det(Λᵢ(z))`, hence the
  determinant ratio `𝒟₁₀(z)` equals the response-determinant
  ratio `det Λ₁(z)/det Λ₀(z)`.
* `boundary_spectral_shift_deriv`: the boxed log-derivative
  identity `𝒟₁₀' = 𝒟₁₀ · (-Tr[(𝔸₁-z)⁻¹ - (𝔸₀-z)⁻¹])`, from the
  complex-parameter Jacobi formula (`hasDerivAt_det_holo`).
* `boundary_contour_count`: the boxed contour count — for a
  circle avoiding both spectra, `∮ d/dz log 𝒟₁₀ = 2πi(N₁ - N₀)`
  with `Nᵢ` the number of eigenvalues (with multiplicity) inside;
  the integrand is the trace-resolvent difference of the first
  boxed identity, converted on the circle to eigenvalue sums by
  `trace_resolvent_eq_sum`.

Supporting machinery (public): `hasDerivAt_det_holo` (Jacobi
derivative of `det` along a holomorphic family — the
complex-parameter port of `NCG.hasDerivAt_det`),
`hasDerivAt_det_affine`/`_inv`, `det_affine_eq_prod_roots`
(charpoly factorization of `det(M - z)` over `ℂ`),
`multiset_prod_hasDerivAt`, `trace_resolvent_eq_sum`
(`Tr(M - z)⁻¹ = Σ_μ (μ - z)⁻¹`, obtained by derivative
uniqueness — no triangularization needed), and the circle
integrals `circleIntegrable_root_sum`/`circleIntegral_root_sum`.

Rendering disclosed: the contour domain is a metric disc (circle
contour), the counting functions are root multiset counts of the
characteristic polynomials, and `d/dz log 𝒟₁₀` in the contour
clause is rendered by its value `Tr R₀ - Tr R₁` established in
the derivative clause.
-/

open Matrix Polynomial Metric
open scoped Real

namespace NCG

variable {n : ℕ}

/-- The Jacobi derivative formula along a holomorphic matrix
family: `(det U)' = tr(adj(U)·V)` where `V` is the entrywise
`z`-derivative. -/
theorem hasDerivAt_det_holo {U : ℂ → Matrix (Fin n) (Fin n) ℂ}
    {V : Matrix (Fin n) (Fin n) ℂ} {t : ℂ}
    (hU : ∀ i j, HasDerivAt (fun s => U s i j) (V i j) t) :
    HasDerivAt (fun s => (U s).det)
      (Matrix.trace (adjugate (U t) * V)) t := by
  have hfun : (fun s => (U s).det)
      = fun s => ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, U s (σ i) i := by
    funext s
    rw [Matrix.det_apply']
  rw [hfun]
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      HasDerivAt (fun s => ∏ i, U s (σ i) i)
        (∑ i, (∏ j ∈ Finset.univ.erase i, U t (σ j) j) • V (σ i) i)
        t := by
    intro σ
    exact HasDerivAt.fun_finsetProd (fun i _ => hU (σ i) i)
  have hsum : HasDerivAt (fun s => ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, U s (σ i) i)
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, U t (σ j) j) • V (σ i) i)
      t := by
    apply HasDerivAt.fun_sum
    intro σ _
    exact ((hprod σ).const_mul _)
  have hval : (∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, U t (σ j) j) • V (σ i) i)
      = Matrix.trace (adjugate (U t) * V) := by
    have hswap : (∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∑ i, (∏ j ∈ Finset.univ.erase i, U t (σ j) j) • V (σ i) i)
        = ∑ i, ∑ σ : Equiv.Perm (Fin n),
            ((Equiv.Perm.sign σ : ℤ) : ℂ) *
              ((∏ j ∈ Finset.univ.erase i, U t (σ j) j) * V (σ i) i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_eq_mul]
    have hdet_i : ∀ i, (∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ((∏ j ∈ Finset.univ.erase i, U t (σ j) j) * V (σ i) i))
        = ((U t).updateCol i (fun k => V k i)).det := by
      intro i
      rw [Matrix.det_apply']
      apply Finset.sum_congr rfl
      intro σ _
      have hp : (∏ j, ((U t).updateCol i (fun k => V k i)) (σ j) j)
          = V (σ i) i * ∏ j ∈ Finset.univ.erase i, U t (σ j) j := by
        rw [← Finset.mul_prod_erase Finset.univ
          (fun j => ((U t).updateCol i (fun k => V k i)) (σ j) j)
          (Finset.mem_univ i)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro j hj
          simp [(Finset.mem_erase.mp hj).1]
      rw [hp]
      ring
    rw [hswap]
    calc ∑ i, ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ((∏ j ∈ Finset.univ.erase i, U t (σ j) j) * V (σ i) i)
        = ∑ i, ((U t).updateCol i (fun k => V k i)).det :=
          Finset.sum_congr rfl fun i _ => hdet_i i
    _ = ∑ i, ∑ k, adjugate (U t) i k * V k i :=
          Finset.sum_congr rfl fun i _ =>
            det_updateCol_expand (U t) i (fun k => V k i)
    _ = Matrix.trace (adjugate (U t) * V) := by
          simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [← hval]
  exact hsum

/-- Derivative of `det(M - z)` in the spectral parameter:
`-tr(adj(M - t))`. -/
lemma hasDerivAt_det_affine (M : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    HasDerivAt
      (fun z => (M - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det)
      (-Matrix.trace (adjugate (M - t • 1))) t := by
  have hU : ∀ i j, HasDerivAt
      (fun s : ℂ => (M - s • (1 : Matrix (Fin n) (Fin n) ℂ)) i j)
      ((-(1 : Matrix (Fin n) (Fin n) ℂ)) i j) t := by
    intro i j
    have hfun : (fun s : ℂ =>
        (M - s • (1 : Matrix (Fin n) (Fin n) ℂ)) i j)
        = fun s => M i j
            - s * (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
      funext s
      simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hfun]
    have h := ((hasDerivAt_id t).mul_const
      ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).const_sub (M i j)
    simpa [Matrix.neg_apply] using h
  have h := hasDerivAt_det_holo hU
  rw [Matrix.mul_neg, Matrix.mul_one, Matrix.trace_neg] at h
  exact h

/-- Jacobi in resolvent form: at an invertible point,
`(det(M - z))' = -det(M - t)·tr((M - t)⁻¹)`. -/
lemma hasDerivAt_det_affine_inv (M : Matrix (Fin n) (Fin n) ℂ)
    (t : ℂ) [Invertible (M - t • 1)] :
    HasDerivAt
      (fun z => (M - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det)
      (-((M - t • 1).det * Matrix.trace (M - t • 1)⁻¹)) t := by
  have h := hasDerivAt_det_affine M t
  have hadj : adjugate (M - t • 1)
      = (M - t • 1).det • (M - t • 1)⁻¹ := by
    have h1 := Matrix.mul_adjugate (M - t • 1)
    have h2 := congrArg (fun X => (M - t • 1)⁻¹ * X) h1
    simp only [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at h2
    exact h2
  rw [hadj, Matrix.trace_smul, smul_eq_mul] at h
  exact h

section Ratio

variable {b ii : Type*} [Fintype b] [Fintype ii]
  [DecidableEq b] [DecidableEq ii]

/-- `thm:boundary-spectral-shift`, ratio clause: both boundary
determinants factor through the common interior, so the
determinant ratio equals the response-determinant ratio. -/
theorem boundary_det_ratio
    (A1 A0 : Matrix b b ℂ) (B1 B0 : Matrix b ii ℂ)
    (C1 C0 : Matrix ii b ℂ) (D : Matrix ii ii ℂ) (z : ℂ)
    [Invertible (D - z • 1)] :
    (Matrix.fromBlocks A1 B1 C1 D - z • 1).det
      = (D - z • 1).det
        * ((A1 - z • 1) - B1 * (D - z • 1)⁻¹ * C1).det
    ∧ (Matrix.fromBlocks A1 B1 C1 D - z • 1).det
        * ((A0 - z • 1) - B0 * (D - z • 1)⁻¹ * C0).det
      = (Matrix.fromBlocks A0 B0 C0 D - z • 1).det
        * ((A1 - z • 1) - B1 * (D - z • 1)⁻¹ * C1).det := by
  have hblock : ∀ (A : Matrix b b ℂ) (B : Matrix b ii ℂ)
      (C : Matrix ii b ℂ),
      Matrix.fromBlocks A B C D
          - z • (1 : Matrix (b ⊕ ii) (b ⊕ ii) ℂ)
        = Matrix.fromBlocks (A - z • 1) B C (D - z • 1) := by
    intro A B C
    ext ij kl
    cases ij <;> cases kl <;>
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  have hdet : ∀ (A : Matrix b b ℂ) (B : Matrix b ii ℂ)
      (C : Matrix ii b ℂ),
      (Matrix.fromBlocks A B C D - z • 1).det
        = (D - z • 1).det
          * ((A - z • 1) - B * (D - z • 1)⁻¹ * C).det := by
    intro A B C
    rw [hblock, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  refine ⟨hdet A1 B1 C1, ?_⟩
  rw [hdet A1 B1 C1, hdet A0 B0 C0]
  ring

end Ratio

/-- `thm:boundary-spectral-shift`, boxed derivative clause:
`𝒟₁₀' = 𝒟₁₀ · (-Tr[(𝔸₁ - z)⁻¹ - (𝔸₀ - z)⁻¹])` — the logarithmic
derivative of the determinant ratio is minus the trace of the
resolvent difference. -/
theorem boundary_spectral_shift_deriv
    (M1 M0 : Matrix (Fin n) (Fin n) ℂ) (t : ℂ)
    [Invertible (M1 - t • 1)] [Invertible (M0 - t • 1)] :
    HasDerivAt
      (fun z => (M1 - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det
        / (M0 - z • 1).det)
      (((M1 - t • 1).det / (M0 - t • 1).det)
        * (-(Matrix.trace (M1 - t • 1)⁻¹
            - Matrix.trace (M0 - t • 1)⁻¹))) t := by
  have h1 := hasDerivAt_det_affine_inv M1 t
  have h0 := hasDerivAt_det_affine_inv M0 t
  have hd0 : (M0 - t • 1).det ≠ 0 :=
    (Matrix.isUnit_det_of_invertible _).ne_zero
  have h := h1.div h0 hd0
  refine h.congr_deriv ?_
  field_simp
  ring

/-- Charpoly factorization of the spectral determinant:
`det(M - z) = Π_{μ ∈ spec M} (μ - z)` with multiplicity. -/
lemma det_affine_eq_prod_roots (M : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) :
    (M - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det
      = (M.charpoly.roots.map (fun μ => μ - z)).prod := by
  have hcard : Multiset.card M.charpoly.roots
      = M.charpoly.natDegree :=
    (Polynomial.splits_iff_card_roots.mp
      (IsAlgClosed.splits M.charpoly))
  have hfac : (M.charpoly.roots.map (fun a => X - C a)).prod
      = M.charpoly := by
    have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      (p := M.charpoly) hcard
    rwa [M.charpoly_monic.leadingCoeff, map_one, one_mul] at h
  have hscalar : Matrix.scalar (Fin n) z
      = z • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.smul_apply]
    · simp [Matrix.smul_apply, h]
  have heval : (z • (1 : Matrix (Fin n) (Fin n) ℂ) - M).det
      = (M.charpoly.roots.map (fun μ => z - μ)).prod := by
    rw [← hscalar, ← Matrix.eval_charpoly]
    conv_lhs => rw [← hfac]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro μ _
    simp
  have hneg : M - z • (1 : Matrix (Fin n) (Fin n) ℂ)
      = -(z • (1 : Matrix (Fin n) (Fin n) ℂ) - M) :=
    (neg_sub _ _).symm
  rw [hneg, Matrix.det_neg, heval]
  have hmapneg : (M.charpoly.roots.map (fun μ => μ - z))
      = (M.charpoly.roots.map (fun μ => z - μ)).map Neg.neg := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro μ _
    simp
  rw [hmapneg, Multiset.prod_map_neg, Multiset.card_map, hcard,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- Derivative of the spectral product
`z ↦ Π (μ - z)` at a regular point. -/
lemma multiset_prod_hasDerivAt (s : Multiset ℂ) (t : ℂ)
    (hs : ∀ μ ∈ s, μ - t ≠ 0) :
    HasDerivAt (fun z => (s.map (fun μ => μ - z)).prod)
      (-((s.map (fun μ => μ - t)).prod
          * (s.map (fun μ => (μ - t)⁻¹)).sum)) t := by
  induction s using Multiset.induction with
  | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero,
        Multiset.sum_zero, mul_zero, neg_zero]
      exact hasDerivAt_const t 1
  | cons a s ih =>
      have ha : a - t ≠ 0 := hs a (Multiset.mem_cons_self a s)
      have hs' : ∀ μ ∈ s, μ - t ≠ 0 :=
        fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ)
      have hfun : (fun z =>
          ((a ::ₘ s).map (fun μ => μ - z)).prod)
          = fun z => (a - z) * (s.map (fun μ => μ - z)).prod := by
        funext z
        rw [Multiset.map_cons, Multiset.prod_cons]
      rw [hfun]
      have hf : HasDerivAt (fun z : ℂ => a - z) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub a
      have hmul := hf.mul (ih hs')
      have heq : -1 * (s.map (fun μ => μ - t)).prod
          + (a - t) * -((s.map (fun μ => μ - t)).prod
              * (s.map (fun μ => (μ - t)⁻¹)).sum)
          = -((((a ::ₘ s).map (fun μ => μ - t)).prod
              * (((a ::ₘ s).map (fun μ => (μ - t)⁻¹)).sum))) := by
        rw [Multiset.map_cons, Multiset.prod_cons,
          Multiset.map_cons, Multiset.sum_cons]
        field_simp
        ring
      exact hmul.congr_deriv heq

/-- The trace of the resolvent is the eigenvalue sum
`Tr((M - z)⁻¹) = Σ_μ (μ - z)⁻¹` — by uniqueness of the
derivative of the spectral determinant. -/
theorem trace_resolvent_eq_sum (M : Matrix (Fin n) (Fin n) ℂ)
    (t : ℂ) [Invertible (M - t • 1)] :
    Matrix.trace (M - t • 1)⁻¹
      = (M.charpoly.roots.map (fun μ => (μ - t)⁻¹)).sum := by
  have hdet : (M - t • 1).det ≠ 0 :=
    (Matrix.isUnit_det_of_invertible _).ne_zero
  have hroots : ∀ μ ∈ M.charpoly.roots, μ - t ≠ 0 := by
    intro μ hμ h0
    apply hdet
    rw [det_affine_eq_prod_roots]
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨μ, hμ, h0⟩)
  have h1 := hasDerivAt_det_affine_inv M t
  have h2 : HasDerivAt
      (fun z => (M - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det)
      (-((M.charpoly.roots.map (fun μ => μ - t)).prod
          * (M.charpoly.roots.map (fun μ => (μ - t)⁻¹)).sum))
      t := by
    have h := multiset_prod_hasDerivAt M.charpoly.roots t hroots
    have hfun : (fun z =>
        (M.charpoly.roots.map (fun μ => μ - z)).prod)
        = fun z =>
            (M - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det := by
      funext z
      rw [det_affine_eq_prod_roots]
    rw [hfun] at h
    exact h
  have huniq := h1.unique h2
  rw [det_affine_eq_prod_roots] at huniq
  have hprod0 : (M.charpoly.roots.map (fun μ => μ - t)).prod
      ≠ 0 := by
    rw [← det_affine_eq_prod_roots]
    exact hdet
  exact mul_left_cancel₀ hprod0 (neg_inj.mp huniq)

/-- Root sums `Σ_μ (μ - z)⁻¹` are circle integrable off the
spectrum. -/
lemma circleIntegrable_root_sum (s : Multiset ℂ) (c : ℂ)
    (R : ℝ) (hR : 0 < R) (hs : ∀ μ ∈ s, μ ∉ sphere c R) :
    CircleIntegrable
      (fun z => (s.map (fun μ => (μ - z)⁻¹)).sum) c R := by
  induction s using Multiset.induction with
  | empty =>
      simp only [Multiset.map_zero, Multiset.sum_zero]
      exact circleIntegrable_const 0 c R
  | cons a s ih =>
      have ha : a ∉ sphere c R := hs a (Multiset.mem_cons_self a s)
      have hs' : ∀ μ ∈ s, μ ∉ sphere c R :=
        fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ)
      have hfun : (fun z =>
          ((a ::ₘ s).map (fun μ => (μ - z)⁻¹)).sum)
          = fun z => (a - z)⁻¹
              + (s.map (fun μ => (μ - z)⁻¹)).sum := by
        funext z
        rw [Multiset.map_cons, Multiset.sum_cons]
      rw [hfun]
      refine CircleIntegrable.add ?_ (ih hs')
      have hbase : CircleIntegrable (fun z => (z - a)⁻¹) c R := by
        rw [circleIntegrable_sub_inv_iff]
        right
        rwa [abs_of_pos hR]
      have hfun2 : (fun z : ℂ => (a - z)⁻¹)
          = -(fun z : ℂ => (z - a)⁻¹) := by
        funext z
        rw [Pi.neg_apply, ← inv_neg, neg_sub]
      rw [hfun2]
      exact hbase.neg

open Classical in
/-- Circle integral of a root sum: each eigenvalue inside the
disc contributes `-2πi` to `∮ Σ_μ (μ - z)⁻¹ dz`. -/
lemma circleIntegral_root_sum (s : Multiset ℂ) (c : ℂ)
    (R : ℝ) (hR : 0 < R) (hs : ∀ μ ∈ s, μ ∉ sphere c R) :
    (∮ z in C(c, R), (s.map (fun μ => (μ - z)⁻¹)).sum)
      = -(2 * π * Complex.I)
          * (s.countP (· ∈ ball c R) : ℂ) := by
  induction s using Multiset.induction with
  | empty =>
      simp [circleIntegral]
  | cons a s ih =>
      have ha : a ∉ sphere c R := hs a (Multiset.mem_cons_self a s)
      have hs' : ∀ μ ∈ s, μ ∉ sphere c R :=
        fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ)
      have hfun : (fun z =>
          ((a ::ₘ s).map (fun μ => (μ - z)⁻¹)).sum)
          = fun z => (a - z)⁻¹
              + (s.map (fun μ => (μ - z)⁻¹)).sum := by
        funext z
        rw [Multiset.map_cons, Multiset.sum_cons]
      have hint_a : CircleIntegrable (fun z => (a - z)⁻¹) c R := by
        have h := circleIntegrable_root_sum {a} c R hR
          (fun μ hμ => by
            rw [Multiset.mem_singleton.mp hμ]; exact ha)
        simpa using h
      have hatom : (∮ z in C(c, R), (a - z)⁻¹)
          = if a ∈ ball c R then -(2 * π * Complex.I)
            else 0 := by
        have hneg : (fun z : ℂ => (a - z)⁻¹)
            = fun z => (-1 : ℂ) • (z - a)⁻¹ := by
          funext z
          rw [smul_eq_mul, neg_one_mul, ← inv_neg, neg_sub]
        rw [hneg, circleIntegral.integral_smul]
        by_cases hmem : a ∈ ball c R
        · rw [if_pos hmem,
            circleIntegral.integral_sub_inv_of_mem_ball hmem]
          rw [smul_eq_mul]
          ring
        · rw [if_neg hmem]
          have hout : ∀ w ∈ closedBall c R, w ≠ a := by
            intro w hw hwa
            rcases lt_or_eq_of_le (mem_closedBall.mp hw) with h | h
            · exact hmem (hwa ▸ mem_ball.mpr h)
            · exact ha (hwa ▸ mem_sphere.mpr h)
          have hdiff : DifferentiableOn ℂ
              (fun z : ℂ => (z - a)⁻¹) (closedBall c R) := by
            apply DifferentiableOn.inv
            · exact (differentiable_id.sub
                (differentiable_const a)).differentiableOn
            · intro w hw
              exact sub_ne_zero.mpr (hout w hw)
          have hzero := DiffContOnCl.circleIntegral_eq_zero
            hR.le (hdiff.diffContOnCl_ball
              (le_refl (closedBall c R)))
          rw [hzero, smul_zero]
      rw [hfun, circleIntegral.integral_add hint_a
        (circleIntegrable_root_sum s c R hR hs'), hatom, ih hs',
        Multiset.countP_cons]
      by_cases hmem : a ∈ ball c R
      · rw [if_pos hmem, if_pos hmem]
        push_cast
        ring
      · rw [if_neg hmem, if_neg hmem]
        push_cast
        ring

open Classical in
/-- `thm:boundary-spectral-shift`, boxed contour clause: for a
circle avoiding both spectra, the contour integral of
`d/dz log 𝒟₁₀ = Tr R₀ - Tr R₁` counts the eigenvalue difference:
`∮ = 2πi (N₁ - N₀)`. -/
theorem boundary_contour_count
    (M1 M0 : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 < R)
    (h1 : ∀ μ ∈ M1.charpoly.roots, μ ∉ sphere c R)
    (h0 : ∀ μ ∈ M0.charpoly.roots, μ ∉ sphere c R) :
    (∮ z in C(c, R),
        (Matrix.trace
            ((M0 - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹)
          - Matrix.trace ((M1 - z • 1)⁻¹)))
      = 2 * π * Complex.I
        * ((M1.charpoly.roots.countP (· ∈ ball c R) : ℂ)
            - (M0.charpoly.roots.countP (· ∈ ball c R) : ℂ)) := by
  have hinv : ∀ (M : Matrix (Fin n) (Fin n) ℂ)
      (hM : ∀ μ ∈ M.charpoly.roots, μ ∉ sphere c R)
      (z : ℂ) (hz : z ∈ sphere c R),
      Matrix.trace ((M - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹)
        = (M.charpoly.roots.map (fun μ => (μ - z)⁻¹)).sum := by
    intro M hM z hz
    have hdet : (M - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det
        ≠ 0 := by
      rw [det_affine_eq_prod_roots]
      intro hp
      obtain ⟨μ, hμ, hμ0⟩ := Multiset.mem_map.mp
        (Multiset.prod_eq_zero_iff.mp hp)
      have : μ = z := by linear_combination hμ0
      exact hM μ hμ (this ▸ hz)
    haveI := Matrix.invertibleOfIsUnitDet _
      (isUnit_iff_ne_zero.mpr hdet)
    exact trace_resolvent_eq_sum M z
  have hcong : Set.EqOn
      (fun z =>
        Matrix.trace
            ((M0 - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹)
          - Matrix.trace ((M1 - z • 1)⁻¹))
      (fun z =>
        (M0.charpoly.roots.map (fun μ => (μ - z)⁻¹)).sum
          - (M1.charpoly.roots.map (fun μ => (μ - z)⁻¹)).sum)
      (sphere c R) := by
    intro z hz
    simp only
    rw [hinv M0 h0 z hz, hinv M1 h1 z hz]
  rw [circleIntegral.integral_congr hR.le hcong,
    circleIntegral.integral_sub
      (circleIntegrable_root_sum _ c R hR h0)
      (circleIntegrable_root_sum _ c R hR h1),
    circleIntegral_root_sum _ c R hR h0,
    circleIntegral_root_sum _ c R hR h1]
  ring

end NCG
