/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.DescriptorDirectSum

/-!
# Descriptor realizations in Weierstrass primary form

Paper `predictive_spectral_geometry`, `cor:supp-all-rational` (partial: the primary-form side of
`eq:supp-all-rational-equivalence`).

* `PontryaginRealization.infinityChainOf`: any finite Pontryagin realization `(A, Γ, J)` with
  nilpotent `A` read as a descriptor realization with the roles of the pencil exchanged
  (`E = A` nilpotent, `A = 1`); its transfer function is the Hermitian polynomial
  `∑_{k < n} z^k M_k` of its Markov parameters (`infinityChainOf_transfer`).
* `PrimaryDescriptor`: a regular Pontryagin descriptor realization **in Weierstrass primary form**,
  the direct sum (`toDescriptor`) of an infinity chain and an ordinary Pontryagin realization;
  `IsMinimal` = both blocks source-cyclic; `toDescriptor_transfer` = polynomial part plus strictly
  proper part.
* `FiniteRationalHermitianData.primary`: the canonical primary realization of `Q = P + Q₀` is
  minimal (`primary_isMinimal`) and its descriptor is `FiniteRationalHermitianData.descriptor`.
* `PrimaryDescriptor.exists_sourceFixing_unitary`: two minimal primary realizations with the same
  jet Markov parameters and the same proper Markov parameters are related by a source-fixing
  descriptor Pontryagin unitary (a linear isomorphism fixing the source, intertwining both pencil
  operators and preserving the indefinite forms) — the direct sum of the unique block unitaries of
  `thm:supp-complete-rational-Krein`.
-/

open scoped InnerProductSpace InnerProduct
open Module

noncomputable section

namespace RenewalGeometry

namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (P : PontryaginRealization H N)

/-- **The infinity chain** of a Pontryagin realization: the descriptor realization with
`E = A`, `A = 1`, same source and Gram operator (used for nilpotent `A`). -/
def infinityChainOf : DescriptorRealization H N where
  E := P.A
  A := 1
  Γ := P.Γ
  J := P.J
  J_selfAdjoint := P.J_selfAdjoint
  J_isUnit := P.J_isUnit
  J_mul_A := by simp
  J_mul_E := P.J_mul_A
  regular := ⟨0, by simp⟩

theorem isUnit_infinityChainOf_pencil {n : ℕ} (hn : P.A ^ n = 0) (z : ℂ) :
    IsUnit (P.infinityChainOf.A - z • P.infinityChainOf.E) :=
  show IsUnit (1 - z • P.A) from
    IsNilpotent.isUnit_one_sub ⟨n, by rw [smul_pow, hn, smul_zero]⟩

/-- The finite Neumann series of a nilpotent pencil. -/
theorem inverse_one_sub_smul_of_pow_eq_zero {n : ℕ} (hn : P.A ^ n = 0) (z : ℂ) :
    Ring.inverse (1 - z • P.A) = ∑ k ∈ Finset.range n, z ^ k • P.A ^ k := by
  set x := z • P.A with hx
  have hpow : x ^ n = 0 := by rw [hx, smul_pow, hn, smul_zero]
  have hsum : ∑ k ∈ Finset.range n, z ^ k • P.A ^ k = ∑ k ∈ Finset.range n, x ^ k :=
    Finset.sum_congr rfl fun k _ => by rw [hx, smul_pow]
  have h1 : (1 - x) * ∑ k ∈ Finset.range n, x ^ k = 1 := by
    rw [mul_neg_geom_sum, hpow, sub_zero]
  have h2 : (∑ k ∈ Finset.range n, x ^ k) * (1 - x) = 1 := by
    rw [geom_sum_mul_neg, hpow, sub_zero]
  rw [hsum]
  exact Ring.inverse_unit (⟨1 - x, _, h1, h2⟩ : (N →L[ℂ] N)ˣ)

/-- **The infinity chain realizes the Hermitian polynomial of the Markov parameters**:
`Γ* J (1 - z A)⁻¹ Γ = ∑_{k < n} z^k M_k` for every `z` when `A^n = 0`. -/
theorem infinityChainOf_transfer {n : ℕ} (hn : P.A ^ n = 0) (z : ℂ) :
    P.infinityChainOf.transfer z = ∑ k ∈ Finset.range n, z ^ k • P.markov k := by
  unfold DescriptorRealization.transfer infinityChainOf
  simp only
  rw [P.inverse_one_sub_smul_of_pow_eq_zero hn z]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, smul_apply, map_sum,
    map_smul, markov]

end PontryaginRealization

/-- The canonical infinity chain of a jet is the infinity chain of its canonical realization. -/
theorem NormalizedRationalHermitianData.infinityChain_eq_infinityChainOf {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (Q : NormalizedRationalHermitianData H) :
    Q.infinityChain = Q.canonical.infinityChainOf := rfl

/-! ## Primary form -/

/-- **A regular Pontryagin descriptor realization in Weierstrass primary form**: an infinity block
(a Pontryagin realization with nilpotent state operator, read as the infinity chain `E = A_∞`,
`A = 1`) and a finite block (an ordinary Pontryagin realization). -/
structure PrimaryDescriptor (H Ninf Nfin : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup Ninf] [InnerProductSpace ℂ Ninf] [CompleteSpace Ninf]
    [NormedAddCommGroup Nfin] [InnerProductSpace ℂ Nfin] [CompleteSpace Nfin] where
  /-- The infinity block. -/
  inf : PontryaginRealization H Ninf
  /-- Its state operator is nilpotent. -/
  inf_nilpotent : ∃ n : ℕ, inf.A ^ n = 0
  /-- The finite block. -/
  fin : PontryaginRealization H Nfin

namespace PrimaryDescriptor

variable {H Ninf Nfin : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Ninf] [InnerProductSpace ℂ Ninf] [CompleteSpace Ninf]
  [NormedAddCommGroup Nfin] [InnerProductSpace ℂ Nfin] [CompleteSpace Nfin]
variable [FiniteDimensional ℂ H] [FiniteDimensional ℂ Ninf] [FiniteDimensional ℂ Nfin]
variable (R : PrimaryDescriptor H Ninf Nfin)

theorem isUnit_fin_pencil {z : ℂ} (hz : ‖R.fin.A‖ < ‖z‖) :
    IsUnit (R.fin.toDescriptor.A - z • R.fin.toDescriptor.E) := by
  show IsUnit (R.fin.A - z • 1)
  rw [← Algebra.algebraMap_eq_smul_one]
  exact isUnit_sub_algebraMap_of_norm_lt _ hz

theorem exists_common_regular :
    ∃ z : ℂ, IsUnit (R.inf.infinityChainOf.A - z • R.inf.infinityChainOf.E) ∧
      IsUnit (R.fin.toDescriptor.A - z • R.fin.toDescriptor.E) := by
  obtain ⟨n, hn⟩ := R.inf_nilpotent
  obtain ⟨t, ht⟩ := exists_gt ‖R.fin.A‖
  refine ⟨t, R.inf.isUnit_infinityChainOf_pencil hn t, R.isUnit_fin_pencil ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt (norm_nonneg _) ht)]
  exact ht

/-- The descriptor realization of a primary form: the direct sum of the infinity chain and the
finite block. -/
def toDescriptor : DescriptorRealization H (WithLp 2 (Ninf × Nfin)) :=
  R.inf.infinityChainOf.prod R.fin.toDescriptor R.exists_common_regular

/-- **Minimality in primary form**: both blocks are source-cyclic. -/
def IsMinimal : Prop := R.inf.IsCyclic ∧ R.fin.IsCyclic

/-- The transfer function of a primary form is the Hermitian polynomial of the infinity block plus
the strictly proper transfer function of the finite block. -/
theorem toDescriptor_transfer {n : ℕ} (hn : R.inf.A ^ n = 0) {z : ℂ} (hz : ‖R.fin.A‖ < ‖z‖) :
    R.toDescriptor.transfer z =
      ∑ k ∈ Finset.range n, z ^ k • R.inf.markov k + R.fin.transfer z := by
  rw [toDescriptor, DescriptorRealization.prod_transfer _ _ _
    (R.inf.isUnit_infinityChainOf_pencil hn z) (R.isUnit_fin_pencil hz),
    R.inf.infinityChainOf_transfer hn z, PontryaginRealization.toDescriptor_transfer]

theorem toDescriptor_Γ_apply (h : H) :
    R.toDescriptor.Γ h = WithLp.toLp 2 (R.inf.Γ h, R.fin.Γ h) := rfl

theorem toDescriptor_E_apply (x : WithLp 2 (Ninf × Nfin)) :
    R.toDescriptor.E x = WithLp.toLp 2 (R.inf.A x.fst, x.snd) := rfl

theorem toDescriptor_A_apply (x : WithLp 2 (Ninf × Nfin)) :
    R.toDescriptor.A x = WithLp.toLp 2 (x.fst, R.fin.A x.snd) := rfl

theorem toDescriptor_form (x y : WithLp 2 (Ninf × Nfin)) :
    R.toDescriptor.form x y = R.inf.form x.fst y.fst + R.fin.form x.snd y.snd :=
  DescriptorRealization.prod_form _ _ _ x y

end PrimaryDescriptor

/-! ## The canonical primary realization of a general `Q` -/

namespace FiniteRationalHermitianData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable (Q : FiniteRationalHermitianData H)

/-- **The canonical primary realization** of `Q = P + Q₀`: the canonical realization of the jet as
the infinity block and the canonical realization of the strictly proper part as the finite block. -/
def primary : PrimaryDescriptor H Q.jet.Carrier Q.proper.Carrier where
  inf := Q.jet.canonical
  inf_nilpotent := ⟨Q.deg + 1, Q.jet.canonical_A_pow_eq_zero Q.jet_isJet⟩
  fin := Q.proper.canonical

theorem primary_toDescriptor : Q.primary.toDescriptor = Q.descriptor := rfl

/-- The canonical primary realization is minimal (both blocks are source-cyclic). -/
theorem primary_isMinimal : Q.primary.IsMinimal :=
  ⟨Q.jet.canonical_isCyclic, Q.proper.canonical_isCyclic⟩

end FiniteRationalHermitianData

/-! ## Source-fixing descriptor unitaries between minimal primary forms -/

namespace PrimaryDescriptor

variable {H Ninf Nfin Ninf' Nfin' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Ninf] [InnerProductSpace ℂ Ninf] [CompleteSpace Ninf]
  [NormedAddCommGroup Nfin] [InnerProductSpace ℂ Nfin] [CompleteSpace Nfin]
  [NormedAddCommGroup Ninf'] [InnerProductSpace ℂ Ninf'] [CompleteSpace Ninf']
  [NormedAddCommGroup Nfin'] [InnerProductSpace ℂ Nfin'] [CompleteSpace Nfin']
variable [FiniteDimensional ℂ H] [FiniteDimensional ℂ Ninf] [FiniteDimensional ℂ Nfin]
  [FiniteDimensional ℂ Ninf'] [FiniteDimensional ℂ Nfin']

/-- A **source-fixing descriptor Pontryagin unitary** between two descriptor realizations: a linear
isomorphism of the state spaces fixing the source, intertwining both pencil operators and
preserving the indefinite forms. -/
def IsSourceFixingUnitary {N N' : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    [CompleteSpace N] [NormedAddCommGroup N'] [InnerProductSpace ℂ N'] [CompleteSpace N']
    (D : DescriptorRealization H N) (D' : DescriptorRealization H N') (S : N ≃ₗ[ℂ] N') : Prop :=
  (∀ h, S (D.Γ h) = D'.Γ h) ∧ (∀ x, S (D.E x) = D'.E (S x)) ∧ (∀ x, S (D.A x) = D'.A (S x)) ∧
    (∀ x y, D'.form (S x) (S y) = D.form x y)

/-- **Existence of the source-fixing descriptor unitary between minimal primary forms** with the
same jet Markov parameters and the same proper Markov parameters: the direct sum of the unique
block unitaries of `thm:supp-complete-rational-Krein` (`cor:supp-all-rational`, primary-form
side of `eq:supp-all-rational-equivalence`). -/
theorem exists_sourceFixing_unitary (R : PrimaryDescriptor H Ninf Nfin) (R' : PrimaryDescriptor H Ninf' Nfin')
    (hR : R.IsMinimal) (hR' : R'.IsMinimal) (hinf : ∀ n, R.inf.markov n = R'.inf.markov n)
    (hfin : ∀ n, R.fin.markov n = R'.fin.markov n) :
    ∃ S : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin'),
      IsSourceFixingUnitary R.toDescriptor R'.toDescriptor S := by
  obtain ⟨S₁, ⟨hΓ₁, hA₁, hform₁⟩, -⟩ :=
    R.inf.existsUnique_sourceFixing_unitary R'.inf hR.1 hR'.1 hinf
  obtain ⟨S₂, ⟨hΓ₂, hA₂, hform₂⟩, -⟩ :=
    R.fin.existsUnique_sourceFixing_unitary R'.fin hR.2 hR'.2 hfin
  refine ⟨L2Prod.blockEquiv S₁ S₂, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [toDescriptor_Γ_apply, toDescriptor_Γ_apply, L2Prod.blockEquiv_apply]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, hΓ₁, hΓ₂]
  · intro x
    rw [toDescriptor_E_apply, toDescriptor_E_apply, L2Prod.blockEquiv_apply,
      L2Prod.blockEquiv_apply]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, hA₁]
  · intro x
    rw [toDescriptor_A_apply, toDescriptor_A_apply, L2Prod.blockEquiv_apply,
      L2Prod.blockEquiv_apply]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, hA₂]
  · intro x y
    rw [toDescriptor_form, toDescriptor_form, L2Prod.blockEquiv_apply_fst,
      L2Prod.blockEquiv_apply_fst, L2Prod.blockEquiv_apply_snd, L2Prod.blockEquiv_apply_snd,
      hform₁, hform₂]

/-! ### Block structure of a source-fixing unitary -/

theorem prod_ext {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {x y : WithLp 2 (E × F)}
    (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := by
  rw [← WithLp.toLp_ofLp 2 x, ← WithLp.toLp_ofLp 2 y]
  exact congrArg _ (Prod.ext h1 h2)

theorem toLp_add_toLp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (a : E) (b : F) :
    WithLp.toLp 2 (a, b) = WithLp.toLp 2 (a, 0) + WithLp.toLp 2 (0, b) := by
  rw [← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]

variable (R : PrimaryDescriptor H Ninf Nfin)

theorem toDescriptor_E_pow_apply (k : ℕ) (a : Ninf) (b : Nfin) :
    (R.toDescriptor.E ^ k) (WithLp.toLp 2 (a, b)) = WithLp.toLp 2 ((R.inf.A ^ k) a, b) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, toDescriptor_E_apply, WithLp.toLp_fst,
        WithLp.toLp_snd, pow_succ', mul_apply_eq_comp]

variable {R} {R' : PrimaryDescriptor H Ninf' Nfin'}

theorem map_E_pow_of_isSourceFixingUnitary
    {G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')}
    (hG : IsSourceFixingUnitary R.toDescriptor R'.toDescriptor G) (k : ℕ)
    (x : WithLp 2 (Ninf × Nfin)) :
    G ((R.toDescriptor.E ^ k) x) = (R'.toDescriptor.E ^ k) (G x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, hG.2.1, ih, pow_succ', mul_apply_eq_comp]

/-- A source-fixing unitary maps the infinity block into the infinity block. -/
theorem snd_map_inl_of_isSourceFixingUnitary
    {G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')}
    (hG : IsSourceFixingUnitary R.toDescriptor R'.toDescriptor G) (a : Ninf) :
    (G (WithLp.toLp 2 (a, 0))).snd = 0 := by
  obtain ⟨n, hn⟩ := R.inf_nilpotent
  obtain ⟨n', hn'⟩ := R'.inf_nilpotent
  have h1 : (R.inf.A ^ (n + n')) a = 0 := by
    rw [add_comm, pow_add, mul_apply_eq_comp, hn]; simp
  have h2 := map_E_pow_of_isSourceFixingUnitary hG (n + n') (WithLp.toLp 2 (a, 0))
  rw [toDescriptor_E_pow_apply, h1, show ((0 : Ninf), (0 : Nfin)) = 0 from rfl, WithLp.toLp_zero,
    map_zero] at h2
  have h3 := congrArg WithLp.snd h2
  rw [← WithLp.toLp_ofLp 2 (G (WithLp.toLp 2 (a, 0))), toDescriptor_E_pow_apply] at h3
  simpa using h3.symm

/-- A source-fixing unitary maps the finite block into the finite block. -/
theorem fst_map_inr_of_isSourceFixingUnitary
    {G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')}
    (hG : IsSourceFixingUnitary R.toDescriptor R'.toDescriptor G) (b : Nfin) :
    (G (WithLp.toLp 2 (0, b))).fst = 0 := by
  obtain ⟨n, hn⟩ := R.inf_nilpotent
  obtain ⟨n', hn'⟩ := R'.inf_nilpotent
  have h2 := map_E_pow_of_isSourceFixingUnitary hG (n + n') (WithLp.toLp 2 (0, b))
  rw [toDescriptor_E_pow_apply, map_zero] at h2
  have h3 := congrArg WithLp.fst h2
  rw [← WithLp.toLp_ofLp 2 (G (WithLp.toLp 2 (0, b))), toDescriptor_E_pow_apply] at h3
  simp only [WithLp.toLp_ofLp, WithLp.toLp_fst] at h3
  rw [h3, pow_add, mul_apply_eq_comp, hn']
  simp

/-- The infinity block of a source-fixing unitary. -/
def infBlock (G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')) : Ninf →ₗ[ℂ] Ninf' :=
  WithLp.fstₗ 2 ℂ Ninf' Nfin' ∘ₗ (G : WithLp 2 (Ninf × Nfin) →ₗ[ℂ] WithLp 2 (Ninf' × Nfin')) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Ninf × Nfin)).symm.toLinearMap ∘ₗ LinearMap.inl ℂ Ninf Nfin

/-- The finite block of a source-fixing unitary. -/
def finBlock (G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')) : Nfin →ₗ[ℂ] Nfin' :=
  WithLp.sndₗ 2 ℂ Ninf' Nfin' ∘ₗ (G : WithLp 2 (Ninf × Nfin) →ₗ[ℂ] WithLp 2 (Ninf' × Nfin')) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Ninf × Nfin)).symm.toLinearMap ∘ₗ LinearMap.inr ℂ Ninf Nfin

theorem infBlock_apply (G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')) (a : Ninf) :
    infBlock G a = (G (WithLp.toLp 2 (a, 0))).fst := rfl

theorem finBlock_apply (G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')) (b : Nfin) :
    finBlock G b = (G (WithLp.toLp 2 (0, b))).snd := rfl

/-- **A source-fixing unitary between primary forms is block diagonal.** -/
theorem apply_eq_of_isSourceFixingUnitary
    {G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')}
    (hG : IsSourceFixingUnitary R.toDescriptor R'.toDescriptor G) (x : WithLp 2 (Ninf × Nfin)) :
    G x = WithLp.toLp 2 (infBlock G x.fst, finBlock G x.snd) := by
  have hx : x = WithLp.toLp 2 (x.fst, 0) + WithLp.toLp 2 (0, x.snd) := by
    rw [← toLp_add_toLp]; rfl
  conv_lhs => rw [hx, map_add]
  refine prod_ext ?_ ?_
  · change (G (WithLp.toLp 2 (x.fst, 0))).fst + (G (WithLp.toLp 2 (0, x.snd))).fst = _
    rw [fst_map_inr_of_isSourceFixingUnitary hG, add_zero, infBlock_apply]
    rfl
  · change (G (WithLp.toLp 2 (x.fst, 0))).snd + (G (WithLp.toLp 2 (0, x.snd))).snd = _
    rw [snd_map_inl_of_isSourceFixingUnitary hG, zero_add, finBlock_apply]
    rfl

theorem infBlock_bijective {G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')}
    (hG : IsSourceFixingUnitary R.toDescriptor R'.toDescriptor G) :
    Function.Bijective (infBlock G) := by
  constructor
  · intro a a' h
    have : G (WithLp.toLp 2 (a, 0)) = G (WithLp.toLp 2 (a', 0)) := by
      rw [apply_eq_of_isSourceFixingUnitary hG, apply_eq_of_isSourceFixingUnitary hG]
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, h]
    have := congrArg WithLp.fst (G.injective this)
    simpa using this
  · intro a'
    refine ⟨(G.symm (WithLp.toLp 2 (a', 0))).fst, ?_⟩
    have h := apply_eq_of_isSourceFixingUnitary hG (G.symm (WithLp.toLp 2 (a', 0)))
    rw [G.apply_symm_apply] at h
    have := congrArg WithLp.fst h
    simpa using this.symm

theorem finBlock_bijective {G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')}
    (hG : IsSourceFixingUnitary R.toDescriptor R'.toDescriptor G) :
    Function.Bijective (finBlock G) := by
  constructor
  · intro b b' h
    have : G (WithLp.toLp 2 (0, b)) = G (WithLp.toLp 2 (0, b')) := by
      rw [apply_eq_of_isSourceFixingUnitary hG, apply_eq_of_isSourceFixingUnitary hG]
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, h]
    have := congrArg WithLp.snd (G.injective this)
    simpa using this
  · intro b'
    refine ⟨(G.symm (WithLp.toLp 2 (0, b'))).snd, ?_⟩
    have h := apply_eq_of_isSourceFixingUnitary hG (G.symm (WithLp.toLp 2 (0, b')))
    rw [G.apply_symm_apply] at h
    have := congrArg WithLp.snd h
    simpa using this.symm

/-- The infinity block of a source-fixing unitary is a source-fixing unitary of the infinity
blocks. -/
theorem infBlock_spec {G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')}
    (hG : IsSourceFixingUnitary R.toDescriptor R'.toDescriptor G) :
    (∀ h, infBlock G (R.inf.Γ h) = R'.inf.Γ h) ∧
      (∀ a, infBlock G (R.inf.A a) = R'.inf.A (infBlock G a)) ∧
      (∀ a a', R'.inf.form (infBlock G a) (infBlock G a') = R.inf.form a a') := by
  obtain ⟨hΓ, hE, -, hform⟩ := id hG
  refine ⟨fun h => ?_, fun a => ?_, fun a a' => ?_⟩
  · have := congrArg WithLp.fst (hΓ h)
    rw [toDescriptor_Γ_apply, toDescriptor_Γ_apply, apply_eq_of_isSourceFixingUnitary hG] at this
    simpa using this
  · have := congrArg WithLp.fst (hE (WithLp.toLp 2 (a, 0)))
    rw [toDescriptor_E_apply, apply_eq_of_isSourceFixingUnitary hG, toDescriptor_E_apply,
      apply_eq_of_isSourceFixingUnitary hG] at this
    simpa using this
  · have := hform (WithLp.toLp 2 (a, 0)) (WithLp.toLp 2 (a', 0))
    rw [toDescriptor_form, toDescriptor_form, apply_eq_of_isSourceFixingUnitary hG,
      apply_eq_of_isSourceFixingUnitary hG] at this
    simpa using this

/-- The finite block of a source-fixing unitary is a source-fixing unitary of the finite blocks. -/
theorem finBlock_spec {G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin')}
    (hG : IsSourceFixingUnitary R.toDescriptor R'.toDescriptor G) :
    (∀ h, finBlock G (R.fin.Γ h) = R'.fin.Γ h) ∧
      (∀ b, finBlock G (R.fin.A b) = R'.fin.A (finBlock G b)) ∧
      (∀ b b', R'.fin.form (finBlock G b) (finBlock G b') = R.fin.form b b') := by
  obtain ⟨hΓ, -, hA, hform⟩ := id hG
  refine ⟨fun h => ?_, fun b => ?_, fun b b' => ?_⟩
  · have := congrArg WithLp.snd (hΓ h)
    rw [toDescriptor_Γ_apply, toDescriptor_Γ_apply, apply_eq_of_isSourceFixingUnitary hG] at this
    simpa using this
  · have := congrArg WithLp.snd (hA (WithLp.toLp 2 (0, b)))
    rw [toDescriptor_A_apply, apply_eq_of_isSourceFixingUnitary hG, toDescriptor_A_apply,
      apply_eq_of_isSourceFixingUnitary hG] at this
    simpa using this
  · have := hform (WithLp.toLp 2 (0, b)) (WithLp.toLp 2 (0, b'))
    rw [toDescriptor_form, toDescriptor_form, apply_eq_of_isSourceFixingUnitary hG,
      apply_eq_of_isSourceFixingUnitary hG] at this
    simpa using this

/-- **Uniqueness of the source-fixing descriptor unitary between minimal primary forms**
(`cor:supp-all-rational`, "the unique source-fixing unitaries on the finite and infinity blocks
combine to the unique descriptor equivalence"): two minimal primary realizations with the same jet
and proper Markov parameters are related by a unique source-fixing descriptor Pontryagin unitary,
the direct sum of the block unitaries of `thm:supp-complete-rational-Krein`. -/
theorem existsUnique_sourceFixing_unitary (R : PrimaryDescriptor H Ninf Nfin)
    (R' : PrimaryDescriptor H Ninf' Nfin') (hR : R.IsMinimal) (hR' : R'.IsMinimal)
    (hinf : ∀ n, R.inf.markov n = R'.inf.markov n)
    (hfin : ∀ n, R.fin.markov n = R'.fin.markov n) :
    ∃! S : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin'),
      IsSourceFixingUnitary R.toDescriptor R'.toDescriptor S := by
  obtain ⟨S₁, -, huniq₁⟩ := R.inf.existsUnique_sourceFixing_unitary R'.inf hR.1 hR'.1 hinf
  obtain ⟨S₂, -, huniq₂⟩ := R.fin.existsUnique_sourceFixing_unitary R'.fin hR.2 hR'.2 hfin
  obtain ⟨S, hS⟩ := exists_sourceFixing_unitary R R' hR hR' hinf hfin
  refine ⟨S, hS, fun G hG => ?_⟩
  have key : ∀ (G : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin'))
      (hG : IsSourceFixingUnitary R.toDescriptor R'.toDescriptor G),
      (∀ a, infBlock G a = S₁ a) ∧ (∀ b, finBlock G b = S₂ b) := by
    intro G hG
    have h₁ := huniq₁ (LinearEquiv.ofBijective (infBlock G) (infBlock_bijective hG))
      (by simpa only [LinearEquiv.ofBijective_apply] using infBlock_spec hG)
    have h₂ := huniq₂ (LinearEquiv.ofBijective (finBlock G) (finBlock_bijective hG))
      (by simpa only [LinearEquiv.ofBijective_apply] using finBlock_spec hG)
    refine ⟨fun a => ?_, fun b => ?_⟩
    · have := LinearEquiv.congr_fun h₁ a
      rwa [LinearEquiv.ofBijective_apply] at this
    · have := LinearEquiv.congr_fun h₂ b
      rwa [LinearEquiv.ofBijective_apply] at this
  obtain ⟨eG₁, eG₂⟩ := key G hG
  obtain ⟨eS₁, eS₂⟩ := key S hS
  refine LinearEquiv.ext fun x => ?_
  rw [apply_eq_of_isSourceFixingUnitary hG, apply_eq_of_isSourceFixingUnitary hS, eG₁, eG₂, eS₁,
    eS₂]

end PrimaryDescriptor

end RenewalGeometry

end
