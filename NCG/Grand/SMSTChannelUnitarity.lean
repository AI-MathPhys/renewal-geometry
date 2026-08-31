/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.RobustChoiPurityUnitary

/-!
# Exact inverse and Choi-purity branches
  (`thm:SMST-channel-unitarity-branches`,
  Gran-Tensor manuscript)

* `smst_channel_unitarity_branches`: the exact-inverse
  branch, proved in full.  For channels `Φ, Ψ` presented
  by Kraus branch families `(A i)`, `(B j)` with the
  trace-preservation identities `∑ Aᵢᴴ Aᵢ = 1`,
  `∑ Bⱼᴴ Bⱼ = 1`, if the boxed inverse residual vanishes,
  `Δ_inv = ‖J_{Ψ∘Φ} − J_id‖²_HS + ‖J_{Φ∘Ψ} − J_id‖²_HS
  = 0` (rendered literally through the Choi matrices and
  the entrywise squared Hilbert–Schmidt norm), then there
  is **one unitary** `U` with `Φ = Ad_U` and `Ψ = Ad_{U*}`
  — and moreover every Kraus branch of `Φ` is a scalar
  multiple of `U` and every branch of `Ψ` a scalar
  multiple of `Uᴴ`.

The proof is the manuscript's: vanishing residuals force
every composite branch `Bⱼ Aᵢ` to be a scalar multiple of
the identity (the identity channel has Choi rank one —
here rendered as the eigenvector-everywhere argument:
each composite branch maps every vector into its own
line), trace preservation of `Ψ` turns `Aᵢ₀ᴴ Aᵢ₀` into a
positive multiple of `1` for any nonzero branch, whose
normalization is the unitary `U`, and all remaining
branches are recovered as scalar multiples through the
explicit inverse `s⁻¹ Aᵢ₀ᴴ`.

The robust branch — `‖J − J_{Ad_U}‖₁ ≤ 2√δ + δ/d` for
`δ = d² − Tr J²` via the leading Choi eigenvector, the
polar partial isometry, and the rank-one trace-norm
estimate — is proved in
`RobustChoiPurityUnitary.exists_unitary_of_choi_purity`.
Together the two named theorems formalize both branches of
the manuscript statement.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The (unnormalized) Choi matrix of a map on `M_d`,
`J(f) (a,i) (b,j) = f(E_{ab}) i j`. -/
noncomputable def branchChoiMatrix (f : Matrix n n ℂ → Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ :=
  Matrix.of fun p q => f (Matrix.single p.1 q.1 1) p.2 q.2

/-- The Kraus-branch channel `X ↦ ∑ i, Aᵢ X Aᵢᴴ` as a
linear map. -/
noncomputable def krausMap {ι : Type} [Fintype ι]
    (A : ι → Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := ∑ i, A i * X * (A i)ᴴ
  map_add' X Y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [mul_add, add_mul]
  map_smul' c X := by
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem krausMap_apply {ι : Type} [Fintype ι]
    (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    krausMap A X = ∑ i, A i * X * (A i)ᴴ := rfl

private theorem matrix_expand (X : Matrix n n ℂ) :
    X = ∑ a, ∑ b, X a b • Matrix.single a b (1 : ℂ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  refine Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

omit [DecidableEq n] in
private theorem star_dot_comm (a b : n → ℂ) :
    star a ⬝ᵥ b = star (star b ⬝ᵥ a) := by
  simp only [dotProduct, Pi.star_apply]
  rw [star_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [star_mul', star_star, mul_comm]

omit [DecidableEq n] in
private theorem star_dot_self_zero {v : n → ℂ}
    (h : star v ⬝ᵥ v = 0) : v = 0 := by
  have hn : ∀ i, star v i * v i =
      ((Complex.normSq (v i) : ℝ) : ℂ) := fun i => by
    rw [Pi.star_apply, Complex.star_def, mul_comm,
      Complex.mul_conj]
  have hsum : ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) = 0 := by
    push_cast
    rw [← h]
    exact (Finset.sum_congr rfl fun i _ => (hn i).symm)
  rw [Complex.ofReal_eq_zero] at hsum
  have hz : ∀ i ∈ Finset.univ, Complex.normSq (v i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      fun i _ => Complex.normSq_nonneg (v i)).mp hsum
  funext i
  exact Complex.normSq_eq_zero.mp (hz i (Finset.mem_univ i))

omit [DecidableEq n] in
private theorem sandwich_vecMulVec (C : Matrix n n ℂ)
    (u : n → ℂ) :
    C * vecMulVec u (star u) * Cᴴ
      = vecMulVec (C.mulVec u) (star (C.mulVec u)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Pi.star_apply]
  rw [star_sum, Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [star_mul']
  ring

omit [DecidableEq n] in
private theorem dot_vecMulVec (w v : n → ℂ) :
    star v ⬝ᵥ (vecMulVec w (star w)).mulVec v
      = (star v ⬝ᵥ w) * star (star v ⬝ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec,
    Matrix.vecMulVec_apply, Pi.star_apply]
  rw [star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', star_star]
  ring

private theorem eigen_all_scalar [Nonempty n]
    (M : Matrix n n ℂ)
    (h : ∀ u : n → ℂ, ∃ c : ℂ, M.mulVec u = c • u) :
    ∃ c : ℂ, M = c • (1 : Matrix n n ℂ) := by
  classical
  have hb : ∀ a : n, ∃ c : ℂ,
      M.mulVec (Pi.single a 1) = c • Pi.single a 1 :=
    fun a => h _
  choose c hc using hb
  obtain ⟨a₀⟩ := ‹Nonempty n›
  refine ⟨c a₀, ?_⟩
  have hagree : ∀ a, c a = c a₀ := by
    intro a
    by_cases ha : a = a₀
    · rw [ha]
    · obtain ⟨d, hd⟩ := h (Pi.single a 1 + Pi.single a₀ 1)
      rw [Matrix.mulVec_add, hc a, hc a₀] at hd
      have h1 := congrFun hd a
      have h2 := congrFun hd a₀
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_same, Pi.single_eq_of_ne ha,
        Pi.single_eq_of_ne (Ne.symm ha),
        mul_one, mul_zero, add_zero, zero_add] at h1 h2
      rw [h1, h2]
  ext i j
  have hcol := congrFun (hc j) i
  have hMij : M.mulVec (Pi.single j 1) i = M i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hMij] at hcol
  rw [hcol]
  by_cases hij : i = j
  · subst hij
    simp only [Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one, Matrix.smul_apply,
      Matrix.one_apply_eq]
    exact hagree i
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hij,
      Matrix.smul_apply, Matrix.one_apply_ne hij,
      smul_zero, smul_zero]

private theorem kraus_identity_scalar [Nonempty n]
    {ι : Type} [Fintype ι] (C : ι → Matrix n n ℂ)
    (hC : ∀ X, ∑ k, C k * X * (C k)ᴴ = X) (k : ι) :
    ∃ c : ℂ, C k = c • (1 : Matrix n n ℂ) := by
  classical
  apply eigen_all_scalar
  intro u
  -- every `v ⊥ u` is orthogonal to `C k *ᵥ u`
  have horth : ∀ v : n → ℂ, star v ⬝ᵥ u = 0 →
      star v ⬝ᵥ (C k).mulVec u = 0 := by
    intro v hv
    have hs := congrArg
      (fun M : Matrix n n ℂ => star v ⬝ᵥ M.mulVec v)
      (hC (vecMulVec u (star u)))
    have hlhs : (∑ k', C k' * vecMulVec u (star u) * (C k')ᴴ)
        = ∑ k', vecMulVec ((C k').mulVec u)
            (star ((C k').mulVec u)) :=
      Finset.sum_congr rfl fun k' _ =>
        sandwich_vecMulVec _ _
    rw [hlhs, Matrix.sum_mulVec, dotProduct_sum] at hs
    simp only [dot_vecMulVec] at hs
    rw [hv, zero_mul] at hs
    -- real sum of `normSq` terms is zero
    have hcast : ∀ z : ℂ, z * star z =
        ((Complex.normSq z : ℝ) : ℂ) := fun z => by
      rw [Complex.star_def, Complex.mul_conj]
    have hsum0 : ((∑ k', Complex.normSq
        (star v ⬝ᵥ (C k').mulVec u) : ℝ) : ℂ) = 0 := by
      push_cast
      rw [← hs]
      exact Finset.sum_congr rfl fun k' _ =>
        (hcast _).symm
    rw [Complex.ofReal_eq_zero] at hsum0
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      fun k' _ => Complex.normSq_nonneg _).mp hsum0
    exact Complex.normSq_eq_zero.mp
      (hz k (Finset.mem_univ k))
  -- decompose `C k *ᵥ u` along `u`
  by_cases hu : u = 0
  · exact ⟨0, by rw [hu, Matrix.mulVec_zero, smul_zero]⟩
  · set w := (C k).mulVec u with hw
    have hd : star u ⬝ᵥ u ≠ 0 := fun h0 =>
      hu (star_dot_self_zero h0)
    set cc : ℂ := (star u ⬝ᵥ w) / (star u ⬝ᵥ u) with hcc
    have hstarcc : star cc =
        star (star u ⬝ᵥ w) / (star u ⬝ᵥ u) := by
      rw [hcc, star_div₀]
      congr 1
      exact (star_dot_comm u u).symm
    have hv0 : star (w - cc • u) ⬝ᵥ u = 0 := by
      rw [star_sub, star_smul, sub_dotProduct,
        smul_dotProduct, smul_eq_mul, star_dot_comm w u]
      rw [hstarcc, div_mul_cancel₀ _ hd, sub_self]
    have hvw := horth _ hv0
    have hself : star (w - cc • u) ⬝ᵥ (w - cc • u) = 0 := by
      rw [dotProduct_sub, dotProduct_smul,
        smul_eq_mul, hvw, hv0, mul_zero, sub_zero]
    have hzero := star_dot_self_zero hself
    refine ⟨cc, ?_⟩
    rw [sub_eq_zero] at hzero
    exact hzero

/-- `thm:SMST-channel-unitarity-branches` (exact-inverse
branch): if both boxed Choi residuals vanish,
`‖J_{Ψ∘Φ} − J_id‖²_HS + ‖J_{Φ∘Ψ} − J_id‖²_HS = 0`, then
`Φ = Ad_U` and `Ψ = Ad_{U*}` for one unitary `U`, and
every Kraus branch of `Φ` (resp. `Ψ`) is a scalar
multiple of `U` (resp. `Uᴴ`). -/
theorem smst_channel_unitarity_branches [Nonempty n]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1)
    (hB : ∑ j, (B j)ᴴ * B j = 1)
    (hΔ : (∑ p, ∑ q, Complex.normSq
        ((branchChoiMatrix (fun X => krausMap B (krausMap A X))
          - branchChoiMatrix (id : Matrix n n ℂ → Matrix n n ℂ)) p q))
      + (∑ p, ∑ q, Complex.normSq
        ((branchChoiMatrix (fun X => krausMap A (krausMap B X))
          - branchChoiMatrix (id : Matrix n n ℂ → Matrix n n ℂ)) p q)) = 0) :
    ∃ U : Matrix n n ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1
      ∧ (∀ X, krausMap A X = U * X * Uᴴ)
      ∧ (∀ X, krausMap B X = Uᴴ * X * U)
      ∧ (∀ i, ∃ lam : ℂ, A i = lam • U)
      ∧ (∀ j, ∃ mu : ℂ, B j = mu • Uᴴ) := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty n›
  -- ── the vanishing residual gives the exact inverse law
  have hnn : ∀ (f : Matrix n n ℂ → Matrix n n ℂ),
      0 ≤ ∑ p, ∑ q, Complex.normSq
        ((branchChoiMatrix f
          - branchChoiMatrix (id : Matrix n n ℂ → Matrix n n ℂ)) p q) :=
    fun f => Finset.sum_nonneg fun p _ =>
      Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _
  have hzero1 : ∑ p, ∑ q, Complex.normSq
      ((branchChoiMatrix (fun X => krausMap B (krausMap A X))
        - branchChoiMatrix (id : Matrix n n ℂ → Matrix n n ℂ)) p q) = 0 := by
    have h1 := hnn (fun X => krausMap B (krausMap A X))
    have h2 := hnn (fun X => krausMap A (krausMap B X))
    linarith
  have hentries : ∀ p q,
      (branchChoiMatrix (fun X => krausMap B (krausMap A X))) p q
        = (branchChoiMatrix (id : Matrix n n ℂ → Matrix n n ℂ)) p q := by
    intro p q
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      fun p' (_ : p' ∈ Finset.univ) =>
        Finset.sum_nonneg fun q' _ =>
          Complex.normSq_nonneg _).mp hzero1 p
      (Finset.mem_univ p)
    have hzq := (Finset.sum_eq_zero_iff_of_nonneg
      fun q' (_ : q' ∈ Finset.univ) =>
        Complex.normSq_nonneg _).mp hz q
      (Finset.mem_univ q)
    have := Complex.normSq_eq_zero.mp hzq
    rw [Matrix.sub_apply, sub_eq_zero] at this
    exact this
  have hE : ∀ a b : n,
      krausMap B (krausMap A (Matrix.single a b (1 : ℂ)))
        = Matrix.single a b 1 := by
    intro a b
    ext i j
    have := hentries (a, i) (b, j)
    simpa [branchChoiMatrix, Matrix.of_apply] using this
  have hid : ∀ X : Matrix n n ℂ,
      krausMap B (krausMap A X) = X := by
    intro X
    conv_lhs => rw [matrix_expand X]
    simp only [map_sum, map_smul]
    simp only [hE]
    exact (matrix_expand X).symm
  -- ── composite Kraus family and its scalar branches
  have hcomp : ∀ X : Matrix n n ℂ,
      ∑ p : κ × ι, (B p.1 * A p.2) * X * (B p.1 * A p.2)ᴴ
        = X := by
    intro X
    rw [Fintype.sum_prod_type]
    have hterm : ∀ (j : κ) (i : ι),
        (B j * A i) * X * (B j * A i)ᴴ
          = B j * (A i * X * (A i)ᴴ) * (B j)ᴴ := by
      intro j i
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    simp only [hterm]
    have hj : ∀ j : κ,
        ∑ i, B j * (A i * X * (A i)ᴴ) * (B j)ᴴ
          = B j * (∑ i, A i * X * (A i)ᴴ) * (B j)ᴴ := by
      intro j
      rw [Finset.mul_sum, Finset.sum_mul]
    simp only [hj]
    have := hid X
    simp only [krausMap_apply] at this
    exact this
  have hscal : ∀ (j : κ) (i : ι),
      ∃ c : ℂ, B j * A i = c • (1 : Matrix n n ℂ) := by
    intro j i
    exact kraus_identity_scalar
      (fun p : κ × ι => B p.1 * A p.2) hcomp (j, i)
  choose c hc using hscal
  -- ── a nonzero branch of `Φ`
  have hone : (1 : Matrix n n ℂ) ≠ 0 := by
    intro h
    have := congrFun (congrFun h a₀) a₀
    rw [Matrix.one_apply_eq, Matrix.zero_apply] at this
    exact one_ne_zero this
  have hex : ∃ i, A i ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hone
    rw [← hA]
    exact Finset.sum_eq_zero fun i _ => by
      rw [hno i, Matrix.mul_zero]
  obtain ⟨i₀, hi₀⟩ := hex
  -- ── `Aᵢ₀ᴴ Aᵢ₀` is a positive multiple of `1`
  have hAA : (A i₀)ᴴ * A i₀
      = (∑ j, star (c j i₀) * c j i₀) •
        (1 : Matrix n n ℂ) := by
    have h1 : (A i₀)ᴴ * A i₀
        = ∑ j, (B j * A i₀)ᴴ * (B j * A i₀) := by
      have : (A i₀)ᴴ * A i₀
          = (A i₀)ᴴ * (∑ j, (B j)ᴴ * B j) * A i₀ := by
        rw [hB, Matrix.mul_one]
      rw [this, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    rw [h1, Finset.sum_smul]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hc j i₀, Matrix.conjTranspose_smul,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.conjTranspose_one, Matrix.one_mul]
  set s : ℂ := ∑ j, star (c j i₀) * c j i₀ with hsdef
  have hsr : s = ((∑ j, Complex.normSq (c j i₀) : ℝ) : ℂ) := by
    rw [hsdef]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
  have hs0 : s ≠ 0 := by
    intro h0
    apply hi₀
    have hz : (A i₀)ᴴ * A i₀ = 0 := by
      rw [hAA, h0, zero_smul]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp hz
  set r : ℝ := ∑ j, Complex.normSq (c j i₀) with hrdef
  have hr0 : 0 < r := by
    have hrn : 0 ≤ r := Finset.sum_nonneg
      fun j _ => Complex.normSq_nonneg _
    rcases hrn.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hsr, ← h]; simp) hs0
  have hsqrt : Real.sqrt r ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hr0)
  -- ── the unitary
  set a : ℂ := (((Real.sqrt r)⁻¹ : ℝ) : ℂ) with hadef
  set U : Matrix n n ℂ := a • A i₀ with hUdef
  have hstara : star a = a := by
    rw [hadef, Complex.star_def, Complex.conj_ofReal]
  have haas : star a * a * s = 1 := by
    rw [hstara, hadef, hsr, Complex.ofReal_inv, ← mul_inv,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hr0.le,
      inv_mul_cancel₀
        (show (r : ℂ) ≠ 0 from by exact_mod_cast hr0.ne')]
  have hUU : Uᴴ * U = 1 := by
    rw [hUdef, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hAA, smul_smul,
      haas, one_smul]
  have hUUc : U * Uᴴ = 1 := mul_eq_one_comm.mp hUU
  -- `A i₀` in terms of `U`
  have ha0 : a ≠ 0 := by
    rw [hadef]
    exact_mod_cast inv_ne_zero hsqrt
  have hAi₀U : A i₀ = ((Real.sqrt r : ℝ) : ℂ) • U := by
    rw [hUdef, smul_smul, hadef]
    rw [show ((Real.sqrt r : ℝ) : ℂ) *
        (((Real.sqrt r)⁻¹ : ℝ) : ℂ) = 1 from by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hsqrt,
        Complex.ofReal_one]]
    rw [one_smul]
  -- ── every branch of `Ψ` is a multiple of `Uᴴ`
  have hBprop : ∀ j : κ, B j
      = (c j i₀ * s⁻¹ * ((Real.sqrt r : ℝ) : ℂ)) • Uᴴ := by
    intro j
    have hinv : A i₀ * (s⁻¹ • (A i₀)ᴴ) = 1 := by
      apply mul_eq_one_comm.mp
      rw [Matrix.smul_mul, hAA, smul_smul,
        inv_mul_cancel₀ hs0, one_smul]
    calc B j = B j * (A i₀ * (s⁻¹ • (A i₀)ᴴ)) := by
          rw [hinv, Matrix.mul_one]
      _ = (B j * A i₀) * (s⁻¹ • (A i₀)ᴴ) := by
          rw [Matrix.mul_assoc]
      _ = (c j i₀ • (1 : Matrix n n ℂ))
            * (s⁻¹ • (A i₀)ᴴ) := by rw [hc]
      _ = (c j i₀ * s⁻¹) • (A i₀)ᴴ := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
            Matrix.one_mul]
      _ = (c j i₀ * s⁻¹ * ((Real.sqrt r : ℝ) : ℂ)) • Uᴴ := by
          rw [hAi₀U, Matrix.conjTranspose_smul, smul_smul]
          congr 1
          rw [Complex.star_def, Complex.conj_ofReal]
  -- ── a composite scalar that does not vanish
  have hj₀ : ∃ j₀, c j₀ i₀ ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hs0
    rw [hsdef]
    exact Finset.sum_eq_zero fun j _ => by
      rw [hno j, mul_zero]
  obtain ⟨j₀, hj₀ne⟩ := hj₀
  set mu₀ : ℂ := c j₀ i₀ * s⁻¹ * ((Real.sqrt r : ℝ) : ℂ)
    with hmu₀
  have hmu₀ne : mu₀ ≠ 0 := by
    rw [hmu₀]
    refine mul_ne_zero (mul_ne_zero hj₀ne
      (inv_ne_zero hs0)) ?_
    exact_mod_cast hsqrt
  -- ── every branch of `Φ` is a multiple of `U`
  have hAprop : ∀ i : ι, ∃ lam : ℂ, A i = lam • U := by
    intro i
    refine ⟨mu₀⁻¹ * c j₀ i, ?_⟩
    have h1 : (mu₀ • Uᴴ) * A i = c j₀ i • 1 := by
      rw [← hBprop j₀]
      exact hc j₀ i
    rw [Matrix.smul_mul] at h1
    have h2 : Uᴴ * A i = (mu₀⁻¹ * c j₀ i) • 1 := by
      have := congrArg (fun M => mu₀⁻¹ • M) h1
      simp only [smul_smul, inv_mul_cancel₀ hmu₀ne,
        one_smul] at this
      exact this
    calc A i = (U * Uᴴ) * A i := by
          rw [hUUc, Matrix.one_mul]
      _ = U * (Uᴴ * A i) := by rw [Matrix.mul_assoc]
      _ = U * ((mu₀⁻¹ * c j₀ i) • 1) := by rw [h2]
      _ = (mu₀⁻¹ * c j₀ i) • U := by
          rw [Matrix.mul_smul, Matrix.mul_one]
  choose lam hlam using hAprop
  -- ── scalar normalizations from trace preservation
  have hscalar_of : ∀ t : ℂ,
      t • (1 : Matrix n n ℂ) = 1 → t = 1 := by
    intro t ht
    have := congrFun (congrFun ht a₀) a₀
    rw [Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at this
    exact this
  have hadj : ∀ (m : ℂ) (V X : Matrix n n ℂ),
      (m • V) * X * (m • V)ᴴ
        = (star m * m) • (V * X * Vᴴ) := by
    intro m V X
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_comm m (star m)]
  have hadj2 : ∀ (m : ℂ) (V : Matrix n n ℂ),
      (m • V)ᴴ * (m • V) = (star m * m) • (Vᴴ * V) := by
    intro m V
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
  have hAsum : ∑ i, (A i)ᴴ * A i
      = (∑ i, star (lam i) * lam i) •
        (1 : Matrix n n ℂ) := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hlam i, hadj2, hUU]
  have hBsum : ∑ j, (B j)ᴴ * B j
      = (∑ j, star (c j i₀ * s⁻¹
          * ((Real.sqrt r : ℝ) : ℂ))
        * (c j i₀ * s⁻¹ * ((Real.sqrt r : ℝ) : ℂ))) •
        (1 : Matrix n n ℂ) := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hBprop j, hadj2,
      Matrix.conjTranspose_conjTranspose, hUUc]
  have hlamsum : (∑ i, star (lam i) * lam i) = 1 :=
    hscalar_of _ (by rw [← hAsum, hA])
  have hmusum : (∑ j, star (c j i₀ * s⁻¹
      * ((Real.sqrt r : ℝ) : ℂ))
      * (c j i₀ * s⁻¹ * ((Real.sqrt r : ℝ) : ℂ))) = 1 :=
    hscalar_of _ (by rw [← hBsum, hB])
  -- ── the channel identities
  refine ⟨U, hUU, hUUc, ?_, ?_, fun i => ⟨lam i, hlam i⟩,
    fun j => ⟨_, hBprop j⟩⟩
  · intro X
    rw [krausMap_apply]
    have hterm : ∀ i, A i * X * (A i)ᴴ
        = (star (lam i) * lam i) • (U * X * Uᴴ) :=
      fun i => by rw [hlam i, hadj]
    simp only [hterm]
    rw [← Finset.sum_smul, hlamsum, one_smul]
  · intro X
    rw [krausMap_apply]
    have hterm : ∀ j, B j * X * (B j)ᴴ
        = (star (c j i₀ * s⁻¹ * ((Real.sqrt r : ℝ) : ℂ))
            * (c j i₀ * s⁻¹ * ((Real.sqrt r : ℝ) : ℂ)))
          • (Uᴴ * X * U) :=
      fun j => by
        rw [hBprop j, hadj,
          Matrix.conjTranspose_conjTranspose]
    simp only [hterm]
    rw [← Finset.sum_smul, hmusum, one_smul]

end NCG
