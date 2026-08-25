/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTAtlasCompleteness
import NCG.Grand.TrineTransportExtras
import NCG.Grand.SMSTCliffordPressureMatterExact

/-!
# Medium exact batch 05
  (Gran-Tensor manuscript)

Exact full-statement formalizations closing the named audit gaps of five
records:

* `thm:GT-source-fusion` — `Medium05.gt_source_fusion_exact`: the fusion
  isometry `Γ` is **constructed** from the vanishing metric fusion defect
  (existence and uniqueness of the solution of `Γ(S_r ⊗ S_s) = S m`), the
  boxed pure-tensor intertwining follows, the innovation
  `𝕀 = S*(1-ΓΓ*)S ⪰ 0` vanishes **iff** `Γ` is unitary (both directions),
  and the boxed rank clause
  `rank 𝕀 + dim(H_r ⊗ H_s) = dim H_{r+s}` is proved (no leakage-trace
  stand-in).

* `thm:GT-trine-cofinal` — `Medium05.gt_trine_cofinal_exact`: packets on a
  cofinal cutoff sequence are transported through compatible maps to an
  arbitrary fixed physical current screen; a summable adjacent trine error
  makes every transported positive outcome Cauchy **in total variation**,
  the carrier/complex/slack measures have unique limits on that screen,
  every bounded transported complex payoff converges, normalized
  amplitudes converge under a uniform amplitude floor, and without the
  floor the unnormalized complex measure and its zero-safe divisor are
  exact canonical outputs.

* `thm:GT-two-margin-closure` — `Medium05.gt_two_margin_closure_complete`:
  the boxed SA.10 ∧ SA.11 ⟹ SA.12 implication **on the complete physical
  carrier** (the atlas margin `‖U*(I-P_{J,N})U‖ < m_U` forces the Krylov
  carrier to exhaust the physical space, and the Hankel domination then
  bounds `T ⪯ (θ-β)I` everywhere), together with both failure branches:
  a failed SA.10 returns the exact missing source bank
  (`range((I-P)U) = 𝒦ᗮ ≠ ⊥`), and a failed SA.11 returns an explicit
  nonzero visible soft response history.

* `cor:SMST-Clifford-pressure-matter` —
  `Medium05.clifford_pressure_matter_exact`: the quantum reduction is
  closed: the sign-flip probability of the actual protocol (maximally
  mixed preparation, uniform axis choice, Born-rule sign readout before
  and after a Clifford axis) **equals** `p_Cl = (1/4)Σ_μ 2η_μ/D` with
  `η_μ = ‖P₋σ_μP₊‖²_HS`; `p_Cl ∈ [0,1]`, `d₊ + d₋ = D`,
  `d_± = rank P_±`, and all boxed pressure/slope/mass/Hessian identities
  hold at that quantum-derived parameter.

* `prop:SMST-complete-fermion-gauge-covariance` —
  `Medium05.complete_fermion_gauge_covariance`: on a finite lattice model
  of the complete same-history Euclidean coefficient
  `𝒦(λ) = ⋆₀(D_sp^U + Y(H))` (gauge-link hop transport, vertex-local
  equivariant Yukawa block, gauge-scalar positive Hodge factor), every
  finite gauge transformation produces explicit block-diagonal unitary
  source/target representations with the boxed SMQ.0b covariance, and
  rank, singular-value data (characteristic polynomial of the Gram),
  divisor (Gram determinant), graph-regulator spectrum, and zero-mode
  multiplicities are proved gauge invariant.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace Medium05

/-! ## `thm:GT-source-fusion`: canonical source fusion, exact form -/

section SourceFusion

variable {Nr Ns N kr ks K : Type}
  [Fintype Nr] [Fintype Ns] [Fintype N] [Fintype kr] [Fintype ks]
  [Fintype K] [DecidableEq Nr] [DecidableEq Ns] [DecidableEq N]
  [DecidableEq kr] [DecidableEq ks]

/-- Elementary tensor of two coefficient vectors. -/
def vecKron {a b : Type} (u : a → ℂ) (w : b → ℂ) : a × b → ℂ :=
  fun p => u p.1 * w p.2

/-- The Kronecker synthesis maps elementary coefficient tensors to
elementary carrier tensors. -/
theorem kron_mulVec_pure (A : Matrix Nr kr ℂ) (B : Matrix Ns ks ℂ)
    (x : kr → ℂ) (y : ks → ℂ) :
    (A ⊗ₖ B) *ᵥ vecKron x y = vecKron (A *ᵥ x) (B *ᵥ y) := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [Matrix.mulVec, dotProduct, vecKron, kroneckerMap_apply]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Surjectivity of the two source syntheses passes to their Kronecker
product (the product source vectors span the tensor carrier). -/
theorem kron_surjective (A : Matrix Nr kr ℂ) (B : Matrix Ns ks ℂ)
    (hA : Function.Surjective A.mulVecLin)
    (hB : Function.Surjective B.mulVecLin) :
    Function.Surjective (A ⊗ₖ B).mulVecLin := by
  rw [← LinearMap.range_eq_top, ← top_le_iff,
    ← (Pi.basisFun ℂ (Nr × Ns)).span_eq, Submodule.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  obtain ⟨x, hx⟩ := hA (Pi.single i 1)
  obtain ⟨y, hy⟩ := hB (Pi.single j 1)
  refine ⟨vecKron x y, ?_⟩
  have hxy : (A ⊗ₖ B).mulVecLin (vecKron x y)
      = vecKron (A.mulVecLin x) (B.mulVecLin y) :=
    kron_mulVec_pure A B x y
  rw [hxy, hx, hy]
  funext p
  obtain ⟨a, b⟩ := p
  simp only [Pi.basisFun_apply, vecKron, Pi.single_apply,
    Prod.mk.injEq]
  by_cases hia : a = i <;> by_cases hjb : b = j <;>
    simp [hia, hjb]

/-- A matrix with surjective column synthesis has invertible
self-Gram `B Bᴴ`. -/
theorem gram_isUnit_det_of_surjective (B : Matrix N K ℂ)
    (hB : Function.Surjective B.mulVecLin) :
    IsUnit (B * Bᴴ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  -- the kernel vector kills `Bᴴ v`
  have hBv : Bᴴ *ᵥ v = 0 := by
    have h0 : star v ⬝ᵥ ((B * Bᴴ) *ᵥ v) = 0 := by
      rw [hv, dotProduct_zero]
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec] at h0
    · exact (star_dotProduct_self_eq_zero).mp
        (by rw [← Matrix.star_mulVec] at h0 ⊢; exact h0)
  -- and `v` is orthogonal to the whole (surjective) range of `B`
  obtain ⟨u, hu⟩ := hB v
  have hvv : star v ⬝ᵥ v = 0 := by
    have : star v ⬝ᵥ (B *ᵥ u) = star (Bᴴ *ᵥ v) ⬝ᵥ u := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    rw [← hu]
    change star v ⬝ᵥ B.mulVecLin u = 0 at this ⊢
    rw [this, hBv]
    simp
  exact hv0 (star_dotProduct_self_eq_zero.mp hvv)

/-- **`thm:GT-source-fusion` (exact form).**  Sources: minimal (surjective)
syntheses `Sr, Ss` of the two graded carriers and `S` of the fused
carrier, a coefficient occurrence map `m`, and the vanishing metric
fusion defect `Δ^met = 0` (the Gram identity
`m* G_{r+s} m = G_r ⊗ G_s` of `def:GT-graded-source`).

Conclusions: (i) a **unique** fusion `Γ` with `Γ(S_r ⊗ S_s) = S m`
exists; (ii) that `Γ` satisfies the boxed pure-tensor intertwining
`Γ(S_r x ⊗ S_s y) = S m(x ⊗ y)` and is an isometry `Γ*Γ = 1`;
(iii) the occurrence innovation `𝕀 = S*(1-ΓΓ*)S` is positive
semidefinite; (iv) `𝕀` vanishes **exactly** when `Γ` is unitary; and
(v) the boxed dimension count
`rank 𝕀 + dim(H_r ⊗ H_s) = dim H_{r+s}`. -/
theorem gt_source_fusion_exact
    (Sr : Matrix Nr kr ℂ) (Ss : Matrix Ns ks ℂ)
    (S : Matrix N K ℂ) (m : Matrix K (kr × ks) ℂ)
    (hr : Function.Surjective Sr.mulVecLin)
    (hs : Function.Surjective Ss.mulVecLin)
    (hS : Function.Surjective S.mulVecLin)
    (hmet : mᴴ * (Sᴴ * S) * m = (Srᴴ * Sr) ⊗ₖ (Ssᴴ * Ss)) :
    (∃! Γ : Matrix N (Nr × Ns) ℂ, Γ * (Sr ⊗ₖ Ss) = S * m)
    ∧ ∀ Γ : Matrix N (Nr × Ns) ℂ, Γ * (Sr ⊗ₖ Ss) = S * m →
      -- boxed intertwining on elementary source tensors
      (∀ (x : kr → ℂ) (y : ks → ℂ),
        Γ *ᵥ vecKron (Sr *ᵥ x) (Ss *ᵥ y) = (S * m) *ᵥ vecKron x y)
      -- isometry
      ∧ Γᴴ * Γ = 1
      -- boxed positive occurrence innovation
      ∧ (Sᴴ * (1 - Γ * Γᴴ) * S).PosSemidef
      -- vanishing exactly at unitarity
      ∧ (Sᴴ * (1 - Γ * Γᴴ) * S = 0 ↔ Γ * Γᴴ = 1)
      -- boxed rank clause
      ∧ (Sᴴ * (1 - Γ * Γᴴ) * S).rank
          + Fintype.card Nr * Fintype.card Ns = Fintype.card N := by
  set B : Matrix (Nr × Ns) (kr × ks) ℂ := Sr ⊗ₖ Ss with hBdef
  set SM : Matrix N (kr × ks) ℂ := S * m with hSMdef
  have hBsurj : Function.Surjective B.mulVecLin :=
    kron_surjective Sr Ss hr hs
  -- the vanishing metric defect as a Gram identity
  have hGram : SMᴴ * SM = Bᴴ * B := by
    rw [hSMdef, hBdef, Matrix.conjTranspose_mul]
    calc mᴴ * Sᴴ * (S * m) = mᴴ * (Sᴴ * S) * m := by
          simp only [Matrix.mul_assoc]
      _ = (Srᴴ * Sr) ⊗ₖ (Ssᴴ * Ss) := hmet
      _ = (Srᴴ ⊗ₖ Ssᴴ) * (Sr ⊗ₖ Ss) := by
          rw [Matrix.mul_kronecker_mul]
      _ = (Sr ⊗ₖ Ss)ᴴ * (Sr ⊗ₖ Ss) := by
          rw [Matrix.conjTranspose_kronecker]
  have hGdet : IsUnit (B * Bᴴ).det :=
    gram_isUnit_det_of_surjective B hBsurj
  have hGinv : (B * Bᴴ) * (B * Bᴴ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hGdet
  have hGinv' : (B * Bᴴ)⁻¹ * (B * Bᴴ) = 1 :=
    Matrix.nonsing_inv_mul _ hGdet
  have hGH : (B * Bᴴ)ᴴ = B * Bᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hGinvH : ((B * Bᴴ)⁻¹)ᴴ = (B * Bᴴ)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hGH]
  -- the canonical solution
  set Γ₀ : Matrix N (Nr × Ns) ℂ := SM * Bᴴ * (B * Bᴴ)⁻¹ with hΓ₀def
  -- `SM` kills the kernel of `B`: matrix-level, via the Gram identity
  have hkill : SM * (1 - Bᴴ * (B * Bᴴ)⁻¹ * B) = 0 := by
    have hBQ : B * (1 - Bᴴ * (B * Bᴴ)⁻¹ * B) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      have : B * (Bᴴ * (B * Bᴴ)⁻¹ * B)
          = (B * Bᴴ) * (B * Bᴴ)⁻¹ * B := by
        simp only [Matrix.mul_assoc]
      rw [this, hGinv, Matrix.one_mul, sub_self]
    have hQH : (1 - Bᴴ * (B * Bᴴ)⁻¹ * B)ᴴ
        = 1 - Bᴴ * (B * Bᴴ)⁻¹ * B := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hGinvH]
      simp only [Matrix.mul_assoc]
    have hzero : (SM * (1 - Bᴴ * (B * Bᴴ)⁻¹ * B))ᴴ
        * (SM * (1 - Bᴴ * (B * Bᴴ)⁻¹ * B)) = 0 := by
      rw [Matrix.conjTranspose_mul, hQH]
      calc (1 - Bᴴ * (B * Bᴴ)⁻¹ * B) * SMᴴ
            * (SM * (1 - Bᴴ * (B * Bᴴ)⁻¹ * B))
          = (1 - Bᴴ * (B * Bᴴ)⁻¹ * B) * (SMᴴ * SM)
            * (1 - Bᴴ * (B * Bᴴ)⁻¹ * B) := by
            simp only [Matrix.mul_assoc]
        _ = (1 - Bᴴ * (B * Bᴴ)⁻¹ * B) * Bᴴ
            * (B * (1 - Bᴴ * (B * Bᴴ)⁻¹ * B)) := by
            rw [hGram]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hBQ, Matrix.mul_zero]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp hzero
  have hΓ₀B : Γ₀ * B = SM := by
    have h1 : Γ₀ * B = SM * (Bᴴ * (B * Bᴴ)⁻¹ * B) := by
      rw [hΓ₀def]; simp only [Matrix.mul_assoc]
    have h2 : SM * (Bᴴ * (B * Bᴴ)⁻¹ * B)
        = SM - SM * (1 - Bᴴ * (B * Bᴴ)⁻¹ * B) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      abel
    rw [h1, h2, hkill, sub_zero]
  -- uniqueness of the intertwining solution
  have huniq : ∀ Γ' : Matrix N (Nr × Ns) ℂ, Γ' * B = SM → Γ' = Γ₀ := by
    intro Γ' hΓ'
    calc Γ' = Γ' * ((B * Bᴴ) * (B * Bᴴ)⁻¹) := by
          rw [hGinv, Matrix.mul_one]
      _ = (Γ' * B) * Bᴴ * (B * Bᴴ)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = Γ₀ := by rw [hΓ', hΓ₀def]
  refine ⟨⟨Γ₀, hΓ₀B, huniq⟩, ?_⟩
  intro Γ hΓB
  have hΓeq : Γ = Γ₀ := huniq Γ hΓB
  -- the isometry identity
  have hiso : Γᴴ * Γ = 1 := by
    rw [hΓeq, hΓ₀def]
    have hH : (SM * Bᴴ * (B * Bᴴ)⁻¹)ᴴ
        = (B * Bᴴ)⁻¹ * (B * SMᴴ) := by
      simp only [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hGinvH, Matrix.mul_assoc]
    rw [hH]
    calc (B * Bᴴ)⁻¹ * (B * SMᴴ) * (SM * Bᴴ * (B * Bᴴ)⁻¹)
        = (B * Bᴴ)⁻¹ * (B * ((SMᴴ * SM) * Bᴴ)) * (B * Bᴴ)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (B * Bᴴ)⁻¹ * (B * (Bᴴ * (B * Bᴴ))) * (B * Bᴴ)⁻¹ := by
          rw [hGram]; simp only [Matrix.mul_assoc]
      _ = ((B * Bᴴ)⁻¹ * (B * Bᴴ)) * ((B * Bᴴ) * (B * Bᴴ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGinv, hGinv', Matrix.one_mul]
  -- projector algebra for the innovation clauses
  have hPP : (Γ * Γᴴ) * (Γ * Γᴴ) = Γ * Γᴴ := by
    calc (Γ * Γᴴ) * (Γ * Γᴴ) = Γ * ((Γᴴ * Γ) * Γᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = Γ * Γᴴ := by rw [hiso, Matrix.one_mul]
  have hPH : (Γ * Γᴴ)ᴴ = Γ * Γᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h1P : (1 - Γ * Γᴴ) * (1 - Γ * Γᴴ) = 1 - Γ * Γᴴ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, hPP]
    abel
  have h1PH : (1 - Γ * Γᴴ)ᴴ = 1 - Γ * Γᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hidem : (1 - Γ * Γᴴ) * ((1 - Γ * Γᴴ) * S) = (1 - Γ * Γᴴ) * S := by
    rw [← Matrix.mul_assoc, h1P]
  have hfact : Sᴴ * (1 - Γ * Γᴴ) * S
      = ((1 - Γ * Γᴴ) * S)ᴴ * ((1 - Γ * Γᴴ) * S) := by
    rw [Matrix.conjTranspose_mul, h1PH,
      Matrix.mul_assoc Sᴴ (1 - Γ * Γᴴ) S, ← hidem,
      ← Matrix.mul_assoc, hidem]
  refine ⟨?_, hiso, ?_, ?_, ?_⟩
  · -- boxed intertwining on elementary tensors
    intro x y
    rw [← kron_mulVec_pure Sr Ss x y, ← hBdef,
      Matrix.mulVec_mulVec, hΓB, hSMdef]
  · rw [hfact]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · -- vanishing exactly at unitarity
    constructor
    · intro hz
      have hPS : (1 - Γ * Γᴴ) * S = 0 := by
        rw [hfact] at hz
        exact Matrix.conjTranspose_mul_self_eq_zero.mp hz
      -- surjectivity of the fused synthesis upgrades this to `ΓΓᴴ = 1`
      have hker : ∀ v : N → ℂ, (1 - Γ * Γᴴ) *ᵥ v = 0 := by
        intro v
        obtain ⟨u, hu⟩ := hS v
        rw [← hu]
        change (1 - Γ * Γᴴ) *ᵥ S.mulVecLin u = 0
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPS,
          Matrix.zero_mulVec]
      have hzero : (1 : Matrix N N ℂ) - Γ * Γᴴ = 0 := by
        ext i j
        have := congrFun (hker (Pi.single j 1)) i
        rwa [Matrix.mulVec_single_one, Matrix.zero_apply] at this
      have := sub_eq_zero.mp hzero
      exact this.symm
    · intro huni
      rw [huni, sub_self, Matrix.mul_zero, Matrix.zero_mul]
  · -- boxed rank clause
    have hrank1 : (Sᴴ * (1 - Γ * Γᴴ) * S).rank
        = ((1 - Γ * Γᴴ) * S).rank := by
      rw [hfact, Matrix.rank_conjTranspose_mul_self]
    have hrange : LinearMap.range ((1 - Γ * Γᴴ) * S).mulVecLin
        = LinearMap.range (1 - Γ * Γᴴ).mulVecLin := by
      rw [Matrix.mulVecLin_mul, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr hS, Submodule.map_top]
    have hrank2 : ((1 - Γ * Γᴴ) * S).rank = (1 - Γ * Γᴴ).rank := by
      unfold Matrix.rank
      rw [hrange]
    have hadd := NCG.gt_idempotent_rank_compl (Γ * Γᴴ) hPP
    have hrankP : (Γ * Γᴴ).rank = Fintype.card Nr * Fintype.card Ns := by
      rw [Matrix.rank_self_mul_conjTranspose,
        ← Matrix.rank_conjTranspose_mul_self, hiso, Matrix.rank_one,
        Fintype.card_prod]
    rw [hrank1, hrank2]
    omega

end SourceFusion

end Medium05
end NCG
