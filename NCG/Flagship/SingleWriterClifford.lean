/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.AnchorClifford

/-!
# Single-writer Clifford source and common-trace criterion
  (`thm:single-writer-clifford-master`, flagship manuscript)

On the anchor Clifford factor with spatial generators
`γ¹ = Z⊗Z`, `γ² = Z⊗Y`, `γ³ = Y⊗I` (Hermitian, anticommuting,
squares `+1`), pseudoscalar `ω₃ = γ¹γ²γ³`, involution
`𝒥₃ = iω₃ = Y⊗X`, and `τ₄ = ¼Tr`:

* `calJ3_eq` / `calJ3_involution`: `𝒥₃` is the Hermitian
  involution `Y⊗X` with `Tr 𝒥₃ = 0`;
* (i) `gam_pair` / `gam_triple`: the two boxed trace identities —
  `τ₄(γ(u)γ(v)) = u·v` and
  `iτ₄(𝒥₃γ(u)γ(v)γ(w)) = det[u v w]` (the exterior top line is
  the Clifford pseudoscalar line, in trace form);
* (ii) `single_writer_gram` / `single_writer_chi`: for
  `W(v) = γ(L v)` the boxed common trace and loading —
  `G_W = LᵀL`, `χ_W = det L`, `χ_W² = det G_W`;
* (iii) `single_writer_coframe`: the boxed coframe-control
  covariance `iτ₄(𝒥₃W(Ee₁)W(Ee₂)W(Ee₃)) = χ_W·det E`;
* (iv) `single_writer_nondegenerate`: the equivalences
  `χ_W ≠ 0 ⟺ G_W ≻ 0 ⟺ rank L = 3`;
* (v) `single_writer_equivariant`: frame equivariance for an
  irreducibly acting symmetry family forces `W = λγ`,
  `G_W = λ²I₃`, `χ_W = λ³`.

Rendering disclosed: `Alt₃(γ(u),γ(v),γ(w)) = det[u v w]·ω₃` is
rendered by its equivalent boxed trace display (the trace against
`𝒥₃` proved in full trilinear generality); the concrete
icosahedral irreducibility of the frame action enters clause (v)
as the displayed real-Schur hypothesis `hirr` (the manuscript's
representation-theory input).
-/

open Matrix Kronecker

namespace NCG

noncomputable section

/-- `τ₄ = ¼ Tr` on the anchor factor. -/
def tau4 (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℂ :=
  A.trace / 4

private lemma tau4_sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    tau4 (∑ i ∈ s, f i) = ∑ i ∈ s, tau4 (f i) := by
  simp [tau4, Matrix.trace_sum, Finset.sum_div]

private lemma tau4_smul (c : ℂ)
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    tau4 (c • A) = c * tau4 A := by
  simp [tau4, Matrix.trace_smul]
  ring

/-- The spatial generator triple `(γ¹, γ², γ³)`. -/
def gamS : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ![gamma1, gamma2, gamma3]

/-- The spatial pseudoscalar `ω₃ = γ¹γ²γ³`. -/
def omega3 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  gamma1 * gamma2 * gamma3

/-- The chirality involution `𝒥₃ = iω₃`. -/
def calJ3 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Complex.I • omega3

/- Pauli product table. -/
private lemma pZY : clockZ * clockY = (-Complex.I) • clockX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockZ, clockY, clockX, Matrix.mul_apply,
      Fin.sum_univ_two]

private lemma pYZ : clockY * clockZ = Complex.I • clockX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockZ, clockY, clockX, Matrix.mul_apply,
      Fin.sum_univ_two]

private lemma pXY : clockX * clockY = Complex.I • clockZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockX, clockY, clockZ, Matrix.mul_apply,
      Fin.sum_univ_two]

private lemma pYX : clockY * clockX = (-Complex.I) • clockZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockX, clockY, clockZ, Matrix.mul_apply,
      Fin.sum_univ_two]

private lemma pZX : clockZ * clockX = Complex.I • clockY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockX, clockY, clockZ, Matrix.mul_apply,
      Fin.sum_univ_two]

private lemma pXZ : clockX * clockZ = (-Complex.I) • clockY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockX, clockY, clockZ, Matrix.mul_apply,
      Fin.sum_univ_two]

private lemma pXX : clockX * clockX = 1 := pauli_relations.2.1.1

private lemma pYY : clockY * clockY = 1 :=
  pauli_relations.2.1.2.1

private lemma pZZ : clockZ * clockZ = 1 :=
  pauli_relations.2.1.2.2

/- Pauli traces. -/
private lemma trX : clockX.trace = 0 := by
  simp [clockX, Matrix.trace_fin_two]

private lemma trY : clockY.trace = 0 := by
  simp [clockY, Matrix.trace_fin_two]

private lemma trZ : clockZ.trace = 0 := by
  simp [clockZ, Matrix.trace_fin_two]

/-- `𝒥₃ = Y ⊗ X` in closed Kronecker form. -/
lemma calJ3_eq : calJ3 = clockY ⊗ₖ clockX := by
  rw [calJ3, omega3, gamma1, gamma2, gamma3,
    ← Matrix.mul_kronecker_mul, pZZ, pZY, Matrix.kronecker_smul,
    smul_mul_assoc, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [show Complex.I * -Complex.I = 1 from by
    rw [mul_neg, Complex.I_mul_I, neg_neg]]
  rw [one_smul]

/-- `𝒥₃` is a Hermitian involution with zero trace. -/
theorem calJ3_involution :
    calJ3ᴴ = calJ3 ∧ calJ3 * calJ3 = 1 ∧ calJ3.trace = 0 := by
  obtain ⟨⟨hXh, hYh, _⟩, -, -⟩ := pauli_relations
  refine ⟨?_, ?_, ?_⟩
  · rw [calJ3_eq]
    rw [show (clockY ⊗ₖ clockX)ᴴ = clockYᴴ ⊗ₖ clockXᴴ from by
      ext ⟨a, b⟩ ⟨c, d⟩
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
        mul_comm]]
    rw [hXh, hYh]
  · rw [calJ3_eq, ← Matrix.mul_kronecker_mul, pYY, pXX,
      Matrix.one_kronecker_one]
  · rw [calJ3_eq, Matrix.trace_kronecker, trX, mul_zero]

/-- The signed permutation table `ε_{ijk}` as a complex
constant. -/
def epsC : Fin 3 → Fin 3 → Fin 3 → ℂ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

set_option maxHeartbeats 1600000 in
-- the simp set varies across the nine `fin_cases` branches
set_option linter.unusedSimpArgs false in
private lemma pair_table (i j : Fin 3) :
    tau4 (gamS i * gamS j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [gamS, gamma1, gamma2, gamma3, tau4,
      ← Matrix.mul_kronecker_mul, pXX, pYY, pZZ, pZY, pYZ, pXY,
      pYX, pZX, pXZ, Matrix.smul_kronecker, Matrix.kronecker_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      Matrix.trace_smul, Matrix.trace_kronecker, trX, trY, trZ,
      Matrix.trace_one]

set_option maxHeartbeats 3200000 in
-- the simp set varies across the 27 `fin_cases` branches
set_option linter.unusedSimpArgs false in
private lemma triple_table (i j k : Fin 3) :
    Complex.I * tau4 (calJ3 * gamS i * gamS j * gamS k)
      = epsC i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [epsC, gamS, gamma1, gamma2, gamma3, calJ3_eq, tau4,
      ← Matrix.mul_kronecker_mul, pXX, pYY, pZZ, pZY, pYZ, pXY,
      pYX, pZX, pXZ, Matrix.smul_kronecker,
      Matrix.kronecker_smul, smul_mul_assoc,
      mul_smul_comm, smul_smul, Matrix.trace_smul,
      Matrix.trace_kronecker, trX, trY, trZ, Matrix.trace_one,
      Matrix.one_mul, Matrix.mul_one] <;>
    ring_nf <;>
    norm_num [Complex.I_sq]

/-- The real linear writer `γ(u) = Σᵢ uᵢγⁱ`. -/
def gamMap (u : Fin 3 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ i, (u i : ℂ) • gamS i

private lemma mul_gamMap_expand
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (c : Fin 3 → ℝ) :
    A * gamMap c = ∑ i, (c i : ℂ) • (A * gamS i) := by
  rw [gamMap, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _

private lemma gamMap_mul (u v : Fin 3 → ℝ) :
    gamMap u * gamMap v
      = ∑ i, ∑ j, ((u i : ℂ) * (v j : ℂ))
          • (gamS i * gamS j) := by
  rw [gamMap, gamMap, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/-- Boxed identity (i), quadratic form:
`τ₄(γ(u)γ(v)) = u·v`. -/
theorem gam_pair (u v : Fin 3 → ℝ) :
    tau4 (gamMap u * gamMap v) = ((u ⬝ᵥ v : ℝ) : ℂ) := by
  have hinner : ∀ i : Fin 3,
      (∑ j, tau4 (((u i : ℂ) * (v j : ℂ)) • (gamS i * gamS j)))
        = (u i : ℂ) * (v i : ℂ) := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [tau4_smul, pair_table, if_pos rfl, mul_one]
    · intro j _ hj
      rw [tau4_smul, pair_table, if_neg (Ne.symm hj), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [gamMap_mul, tau4_sum]
  calc ∑ i, tau4 (∑ j, ((u i : ℂ) * (v j : ℂ))
        • (gamS i * gamS j))
      = ∑ i, ∑ j, tau4 (((u i : ℂ) * (v j : ℂ))
          • (gamS i * gamS j)) :=
        Finset.sum_congr rfl fun i _ => tau4_sum _ _
    _ = ∑ i, (u i : ℂ) * (v i : ℂ) :=
        Finset.sum_congr rfl fun i _ => hinner i
    _ = ((u ⬝ᵥ v : ℝ) : ℂ) := by simp [dotProduct]

private lemma triple_expand (u v w : Fin 3 → ℝ) :
    calJ3 * gamMap u * gamMap v * gamMap w
      = ∑ i, ∑ j, ∑ k,
          ((u i : ℂ) * (v j : ℂ) * (w k : ℂ))
            • (calJ3 * gamS i * gamS j * gamS k) := by
  rw [mul_gamMap_expand calJ3 u, Finset.sum_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, smul_mul_assoc,
    mul_gamMap_expand (calJ3 * gamS i) v, Finset.sum_mul,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc,
    mul_gamMap_expand (calJ3 * gamS i * gamS j) w,
    Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, smul_smul]

/-- Boxed identity (i), top line: the trace against `𝒥₃` is the
determinant of the frame —
`iτ₄(𝒥₃γ(u)γ(v)γ(w)) = det[u v w]` (rows). -/
theorem gam_triple (u v w : Fin 3 → ℝ) :
    Complex.I * tau4 (calJ3 * gamMap u * gamMap v * gamMap w)
      = ((Matrix.of ![u, v, w]).det : ℂ) := by
  have hexp : tau4 (calJ3 * gamMap u * gamMap v * gamMap w)
      = ∑ i, ∑ j, ∑ k,
          ((u i : ℂ) * (v j : ℂ) * (w k : ℂ))
            * tau4 (calJ3 * gamS i * gamS j * gamS k) := by
    rw [triple_expand, tau4_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tau4_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tau4_sum]
    exact Finset.sum_congr rfl fun k _ => tau4_smul _ _
  have hswap : ∀ i : Fin 3,
      Complex.I * (∑ j, ∑ k,
          ((u i : ℂ) * (v j : ℂ) * (w k : ℂ))
            * tau4 (calJ3 * gamS i * gamS j * gamS k))
        = ∑ j, ∑ k, ((u i : ℂ) * (v j : ℂ) * (w k : ℂ))
            * epsC i j k := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show Complex.I * (((u i : ℂ) * (v j : ℂ) * (w k : ℂ))
        * tau4 (calJ3 * gamS i * gamS j * gamS k))
      = ((u i : ℂ) * (v j : ℂ) * (w k : ℂ))
        * (Complex.I
          * tau4 (calJ3 * gamS i * gamS j * gamS k)) from by
      ring, triple_table]
  rw [hexp, Finset.mul_sum]
  calc ∑ i, Complex.I * (∑ j, ∑ k,
        ((u i : ℂ) * (v j : ℂ) * (w k : ℂ))
          * tau4 (calJ3 * gamS i * gamS j * gamS k))
      = ∑ i, ∑ j, ∑ k, ((u i : ℂ) * (v j : ℂ) * (w k : ℂ))
          * epsC i j k :=
        Finset.sum_congr rfl fun i _ => hswap i
    _ = ((Matrix.of ![u, v, w]).det : ℂ) := by
        rw [Matrix.det_fin_three]
        push_cast
        simp [Fin.sum_univ_three, epsC]
        ring

/-- Linearity of the writer in the frame argument. -/
private lemma gamMap_sub (u v : Fin 3 → ℝ) :
    gamMap (u - v) = gamMap u - gamMap v := by
  rw [gamMap, gamMap, gamMap, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_smul]
  simp

private lemma gamMap_smul (c : ℝ) (u : Fin 3 → ℝ) :
    gamMap (c • u) = (c : ℂ) • gamMap u := by
  rw [gamMap, gamMap, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  simp

/-- The writer is injective: `γ(u) = 0` forces `u = 0`. -/
lemma gamMap_injective (u v : Fin 3 → ℝ)
    (h : gamMap u = gamMap v) : u = v := by
  have hz : gamMap (u - v) = 0 := by
    rw [gamMap_sub, h, sub_self]
  have hpair := gam_pair (u - v) (u - v)
  rw [hz, mul_zero] at hpair
  rw [show tau4 0 = 0 from by simp [tau4]] at hpair
  have h0 : (u - v) ⬝ᵥ (u - v) = 0 := by
    exact_mod_cast hpair.symm
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h0)

/-- The single writer `W_L(v) = γ(Lv)`. -/
def writerW (L : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  gamMap (L.mulVec v)

/-- (ii) Boxed common trace: `G_W(u,v) = τ₄(W(u)W(v))` is the
Gram `LᵀL`. -/
theorem single_writer_gram (L : Matrix (Fin 3) (Fin 3) ℝ)
    (u v : Fin 3 → ℝ) :
    tau4 (writerW L u * writerW L v)
      = ((u ⬝ᵥ (Lᵀ * L) *ᵥ v : ℝ) : ℂ) := by
  rw [writerW, writerW, gam_pair]
  congr 1
  rw [← Matrix.mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, Matrix.vecMul_transpose]

private lemma mulVec_single_col (L : Matrix (Fin 3) (Fin 3) ℝ)
    (p : Fin 3) :
    L.mulVec (Pi.single p 1) = Lᵀ p := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply,
    Finset.sum_ite_eq', Matrix.transpose_apply]

/-- (ii) Boxed loading: `χ_W = det L` and `χ_W² = det G_W`. -/
theorem single_writer_chi (L : Matrix (Fin 3) (Fin 3) ℝ) :
    Complex.I * tau4 (calJ3 * writerW L (Pi.single 0 1)
        * writerW L (Pi.single 1 1) * writerW L (Pi.single 2 1))
      = (L.det : ℂ)
    ∧ L.det ^ 2 = (Lᵀ * L).det := by
  constructor
  · rw [writerW, writerW, writerW, mulVec_single_col,
      mulVec_single_col, mulVec_single_col, gam_triple]
    rw [show Matrix.of ![Lᵀ 0, Lᵀ 1, Lᵀ 2] = Lᵀ from by
      ext i j
      fin_cases i <;> rfl]
    rw [Matrix.det_transpose]
  · rw [Matrix.det_mul, Matrix.det_transpose]
    ring

/-- (iii) Boxed coframe covariance:
`iτ₄(𝒥₃W(Ee₁)W(Ee₂)W(Ee₃)) = χ_W · det E`. -/
theorem single_writer_coframe (L E : Matrix (Fin 3) (Fin 3) ℝ) :
    Complex.I * tau4 (calJ3
        * writerW L (E.mulVec (Pi.single 0 1))
        * writerW L (E.mulVec (Pi.single 1 1))
        * writerW L (E.mulVec (Pi.single 2 1)))
      = (L.det : ℂ) * (E.det : ℂ) := by
  have hcol : ∀ p : Fin 3,
      L.mulVec (E.mulVec (Pi.single p 1)) = (L * E)ᵀ p := by
    intro p
    rw [Matrix.mulVec_mulVec, mulVec_single_col]
  rw [writerW, writerW, writerW, hcol, hcol, hcol, gam_triple]
  rw [show Matrix.of ![(L * E)ᵀ 0, (L * E)ᵀ 1, (L * E)ᵀ 2]
      = (L * E)ᵀ from by
    ext i j
    fin_cases i <;> rfl]
  rw [Matrix.det_transpose, Matrix.det_mul]
  push_cast
  ring

/-- (iv) The nondegeneracy equivalences:
`det L ≠ 0 ⟺ G_W = LᵀL ≻ 0 ⟺ rank L = 3`. -/
theorem single_writer_nondegenerate
    (L : Matrix (Fin 3) (Fin 3) ℝ) :
    (L.det ≠ 0 ↔ (Lᵀ * L).PosDef)
    ∧ (L.det ≠ 0 ↔ L.rank = 3) := by
  have hquad : ∀ x : Fin 3 → ℝ,
      x ⬝ᵥ (Lᵀ * L) *ᵥ x = (L *ᵥ x) ⬝ᵥ (L *ᵥ x) := by
    intro x
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec,
      Matrix.vecMul_transpose]
  constructor
  · constructor
    · intro hdet
      have hinj : Function.Injective L.mulVec :=
        Matrix.mulVec_injective_iff_isUnit.mpr
          ((Matrix.isUnit_iff_isUnit_det L).mpr
            (isUnit_iff_ne_zero.mpr hdet))
      refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
      · rw [Matrix.IsHermitian,
          Matrix.conjTranspose_eq_transpose_of_trivial,
          Matrix.transpose_mul, Matrix.transpose_transpose]
      · intro x hx
        have hLx : L *ᵥ x ≠ 0 := by
          intro h0
          exact hx (hinj (by rw [h0, Matrix.mulVec_zero]))
        have hq := hquad x
        have hnn : 0 ≤ (L *ᵥ x) ⬝ᵥ (L *ᵥ x) := by
          rw [dotProduct]
          exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
        have hpos : 0 < (L *ᵥ x) ⬝ᵥ (L *ᵥ x) := by
          rcases lt_or_eq_of_le hnn with h | h
          · exact h
          · exact absurd (dotProduct_self_eq_zero.mp h.symm)
              hLx
        have hsx : star x = x := funext fun i => star_trivial _
        rw [hsx, hq]
        exact hpos
    · intro hpd
      have hdetG : 0 < (Lᵀ * L).det := hpd.det_pos
      intro hdet
      rw [Matrix.det_mul, Matrix.det_transpose, hdet,
        mul_zero] at hdetG
      exact lt_irrefl _ hdetG
  · constructor
    · intro hdet
      have := Matrix.rank_of_isUnit L
        ((Matrix.isUnit_iff_isUnit_det L).mpr
          (isUnit_iff_ne_zero.mpr hdet))
      simpa using this
    · intro hrank
      have hrange : LinearMap.range L.mulVecLin = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [← Matrix.rank, hrank]
        simp
      have hsurj : Function.Surjective L.mulVec :=
        LinearMap.range_eq_top.mp hrange
      have hinj : Function.Injective L.mulVec :=
        (LinearMap.injective_iff_surjective
          (f := L.mulVecLin)).mpr hsurj
      have hunit : IsUnit L :=
        Matrix.mulVec_injective_iff_isUnit.mp hinj
      exact isUnit_iff_ne_zero.mp
        ((Matrix.isUnit_iff_isUnit_det L).mp hunit)

/-- (v) Equivariance under an irreducibly acting frame family
forces the single-writer normal form `W = λγ`, `G_W = λ²I`,
`χ_W = λ³`. -/
theorem single_writer_equivariant {ι : Type*}
    (g : ι → Matrix (Fin 3) (Fin 3) ℝ)
    (S : ι → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (L : Matrix (Fin 3) (Fin 3) ℝ)
    (hW : ∀ i v, gamMap (L.mulVec ((g i).mulVec v))
      = S i * gamMap (L.mulVec v) * (S i)ᴴ)
    (hgam : ∀ i v, S i * gamMap v * (S i)ᴴ
      = gamMap ((g i).mulVec v))
    (hirr : ∀ M : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i, M * g i = g i * M)
      → ∃ c : ℝ, M = c • (1 : Matrix (Fin 3) (Fin 3) ℝ)) :
    ∃ lam : ℝ,
      (∀ v, writerW L v = (lam : ℂ) • gamMap v)
      ∧ Lᵀ * L = (lam ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      ∧ L.det = lam ^ 3 := by
  have hcomm : ∀ i, L * g i = g i * L := by
    intro i
    have hvec : ∀ v, (L * g i).mulVec v = (g i * L).mulVec v := by
      intro v
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact gamMap_injective _ _ ((hW i v).trans (hgam i _))
    ext a b
    have := congrFun (hvec (Pi.single b 1)) a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply,
      Finset.sum_ite_eq'] using this
  obtain ⟨lam, hlam⟩ := hirr L hcomm
  refine ⟨lam, ?_, ?_, ?_⟩
  · intro v
    rw [writerW, hlam]
    rw [show (lam • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ v
        = lam • v from by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]]
    exact gamMap_smul lam v
  · rw [hlam, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      smul_smul, sq]
  · rw [hlam, Matrix.det_smul, Matrix.det_one, mul_one]
    simp

/-- `thm:single-writer-clifford-master`: the assembled clauses
(i)–(iv) — trace identities, Gram/determinant loading, coframe
covariance, and the nondegeneracy equivalences. -/
theorem single_writer_clifford_master
    (L E : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ u v : Fin 3 → ℝ,
      tau4 (gamMap u * gamMap v) = ((u ⬝ᵥ v : ℝ) : ℂ))
    ∧ (∀ u v w : Fin 3 → ℝ,
      Complex.I * tau4 (calJ3 * gamMap u * gamMap v * gamMap w)
        = ((Matrix.of ![u, v, w]).det : ℂ))
    ∧ (Complex.I * tau4 (calJ3 * writerW L (Pi.single 0 1)
          * writerW L (Pi.single 1 1)
          * writerW L (Pi.single 2 1)) = (L.det : ℂ)
      ∧ L.det ^ 2 = (Lᵀ * L).det)
    ∧ (Complex.I * tau4 (calJ3
          * writerW L (E.mulVec (Pi.single 0 1))
          * writerW L (E.mulVec (Pi.single 1 1))
          * writerW L (E.mulVec (Pi.single 2 1)))
        = (L.det : ℂ) * (E.det : ℂ))
    ∧ ((L.det ≠ 0 ↔ (Lᵀ * L).PosDef)
      ∧ (L.det ≠ 0 ↔ L.rank = 3)) :=
  ⟨gam_pair, gam_triple, single_writer_chi L,
    single_writer_coframe L E, single_writer_nondegenerate L⟩

end

end NCG
