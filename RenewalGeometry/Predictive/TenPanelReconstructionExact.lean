/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.FiniteAnchorOperatorNormExact

/-!
# Ten-panel reconstruction and the robust commutant stopping test

`prop:ten-panel-reconstruction` and `prop:reconstruction-error` of the spacetime–gauge
duality manuscript (appendix *Source identifiability and finite system tomography*),
together with the Heisenberg complementary pullback identity `eq:complementary-pullback`.

## The frame

* Six edge coefficients `K_e ∈ B(H_E)`, four record projections `Q_a` on `H_R` with
  `∑_a Q_a = I`, and the twenty-four accepted operators `A_{e,a} = K_e ⊗ Q_a`
  (`TenPanel.acceptedOp`).
* The coefficient Gram `M_ϑ = ϑ I + (1 − ϑ) c c*` with `c = 𝟏/√2 ∈ ℂ^24`
  (`TenPanel.coefficientGram`) and its positive square root.  We give it explicitly,
  `M_ϑ^{1/2} = √ϑ (I − P) + √h P` with `P = 𝟏𝟏ᵀ/24` and `h = 12 − 11ϑ`
  (`TenPanel.coefficientGramSqrt`), and identify it with Mathlib's continuous-functional-
  calculus square root (`TenPanel.cfc_sqrt_coefficientGram`).
* The frame coefficients `C_ν = ∑_j (M_ϑ^{1/2})_{jν} A_j` (`TenPanel.frameCoefficient`), the
  Stinespring isometry `V = ∑_ν C_ν ⊗ |ν⟩` (`stinespringIsometry`), the pulled coefficient
  `C(z) = (I ⊗ ⟨z|) V` (`pulledCoefficient`), and the Heisenberg pullback of the
  complementary channel `𝒫*(F) = V* (I ⊗ F) V` (`complementaryPullback`).
* `eq:complementary-pullback`: `𝒫*(|z⟩⟨w|) = C(z)* C(w)` (`complementaryPullback_vecMulVec`),
  proved for an arbitrary finite family `C_ν`.
* The ten Hermitian quadratures `X_μ = |u⟩⟨r_μ| + |r_μ⟩⟨u|`,
  `Y_μ = −i|u⟩⟨r_μ| + i|r_μ⟩⟨u|` (`eq:ten-quadratures`) with `u = 𝟏/√24`,
  `(r_μ)_{e,a} = O_{eμ}/2` for a real Helmert frame `O` (`eq:helmert-frame`), and the
  contrasts `D_μ = ∑_e O_{eμ} K_e` (`edgeContrast`).

## Results

* `TenPanel.ten_panel_reconstruction` (`prop:ten-panel-reconstruction`):
  `D_μ ⊗ I = (2√3/√(ϑh)) (𝒫*(X_μ) + i 𝒫*(Y_μ))` and `K_e = I/√18 + ∑_μ O_{eμ} D_μ`.
  The intermediate claims of the manuscript's proof, `C(u) = √(h/12) I` and
  `C(r_μ) = (√ϑ/2) D_μ ⊗ I`, are `pulledCoefficient_uniformEnv` and
  `pulledCoefficient_contrastEnv`.  `ten_panel_determines_coefficients` records the
  "determines" clause: two coefficient families with the same ten pullbacks coincide.
* `TenPanel.reconstruction_error` (`prop:reconstruction-error`): with measured panels
  `X̂_μ, Ŷ_μ` of Hilbert–Schmidt errors `ε_{X,μ}, ε_{Y,μ}`, the linear reconstruction
  `D̂_μ = (2√3/√(ϑh))(X̂_μ + iŶ_μ)`, `K̂_e = I/√18 + ∑_μ O_{eμ} D̂_μ` satisfies
  `(∑_e ‖K̂_e − K_e ⊗ I‖²_HS)^{1/2} ≤ e_K` (`eq:appendix-reconstruction-error`), the
  star-closed stacked commutator map moves by at most `2√2 e_K` in `2 → 2` norm
  (`eq:appendix-commutator-error`), and a measured least singular value `ŝ > 2√2 e_K`
  on a protected complement `W` leaves no commutant direction in `W`.
* The generic ingredients: `l2_opNorm_le_matrixL2_norm` (`‖A‖_op ≤ ‖A‖_HS`),
  `helmert_sum_norm_sq` (orthonormal columns preserve the sum of squared errors),
  `starClosedStack_commutator_perturbation` (the `2√2` bound) and
  `robust_commutant_stopping_test` / `robust_commutant_stopping_test_ker` (the least
  singular value perturbation argument, on an arbitrary finite carrier).

Scoped hypotheses (disclosed): the edge system and record factor are finite-dimensional,
modelled as matrix spaces `Matrix E E ℂ`, `Matrix R R ℂ`; the reconstruction lives on the
common carrier `E × R`, so the reconstructed coefficient is compared with `K_e ⊗ I_R`; the
"measured least singular value on the protected complement `W`" is taken as the bound
`ŝ ‖x‖ ≤ ‖𝒟̂ x‖` for `x ∈ W`.  Only the parts of `eq:six-edge-normalization` and
`eq:helmert-frame` that the manuscript's proof uses are assumed (`∑_e K_e = √2 I`,
`∑_a Q_a = I`, `OᵀO = I`, `Oᵀ𝟏 = 0`, `OOᵀ = I − 𝟏𝟏ᵀ/6`).
-/

open Matrix
open scoped Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder

namespace RenewalGeometry

noncomputable section

/-! ### Hilbert–Schmidt linear structure and `‖A‖_op ≤ ‖A‖_HS` -/

section HilbertSchmidt

variable {m k : Type*} [Fintype m] [Fintype k]

/-- `matrixL2` as a linear map. -/
def matrixL2Linear : Matrix m k ℂ →ₗ[ℂ] EuclideanSpace ℂ (m × k) where
  toFun := matrixL2
  map_add' A B := by ext ij; simp [matrixL2]
  map_smul' a A := by ext ij; simp [matrixL2]

@[simp] theorem matrixL2Linear_apply (A : Matrix m k ℂ) : matrixL2Linear A = matrixL2 A := rfl

theorem matrixL2_add (A B : Matrix m k ℂ) : matrixL2 (A + B) = matrixL2 A + matrixL2 B :=
  map_add matrixL2Linear A B

theorem matrixL2_smul (a : ℂ) (A : Matrix m k ℂ) : matrixL2 (a • A) = a • matrixL2 A :=
  map_smul matrixL2Linear a A

theorem matrixL2_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix m k ℂ) :
    matrixL2 (∑ i ∈ s, f i) = ∑ i ∈ s, matrixL2 (f i) :=
  map_sum matrixL2Linear f s

theorem matrixL2_zero : matrixL2 (0 : Matrix m k ℂ) = 0 :=
  map_zero matrixL2Linear

end HilbertSchmidt

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `ℓ²` operator norm is dominated by the Hilbert–Schmidt norm: `‖A‖_op ≤ ‖A‖_HS`. -/
theorem l2_opNorm_le_matrixL2_norm (A : Matrix n n ℂ) : ‖A‖ ≤ ‖matrixL2 A‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have hsq : ‖toEuclideanCLM (𝕜 := ℂ) A x‖ ^ 2 ≤ (‖matrixL2 A‖ * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq (matrixL2 A),
      EuclideanSpace.norm_sq_eq x]
    simp only [ofLp_toEuclideanCLM, matrixL2, WithLp.ofLp_toLp, Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    calc ‖(A *ᵥ x.ofLp) i‖ ^ 2 = ‖∑ j, A i j * x.ofLp j‖ ^ 2 := by
          simp [Matrix.mulVec, dotProduct]
      _ ≤ (∑ j, ‖A i j‖ * ‖x.ofLp j‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (le_of_eq (by simp))
      _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-! ### Helmert isometry: orthonormal columns preserve the sum of squared errors -/

/-- For a real matrix `O` with orthonormal columns (`OᵀO = I`) and vectors `v_μ` of a complex
inner product space, `∑_e ‖∑_μ O_{eμ} v_μ‖² = ∑_μ ‖v_μ‖²`. -/
theorem helmert_sum_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (O : Matrix ι κ ℝ) (hO : Oᵀ * O = 1) (v : κ → F) :
    ∑ e, ‖∑ μ, ((O e μ : ℝ) : ℂ) • v μ‖ ^ 2 = ∑ μ, ‖v μ‖ ^ 2 := by
  have key : ∀ μ μ', (∑ e, ((O e μ : ℝ) : ℂ) * ((O e μ' : ℝ) : ℂ))
      = if μ = μ' then (1 : ℂ) else 0 := by
    intro μ μ'
    have h := congrFun (congrFun hO μ) μ'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    by_cases hμ : μ = μ'
    · simp only [hμ, ite_true] at h ⊢
      exact_mod_cast h
    · simp only [hμ, ite_false] at h ⊢
      exact_mod_cast h
  have h1 : ∀ e, inner ℂ (∑ μ, ((O e μ : ℝ) : ℂ) • v μ) (∑ μ, ((O e μ : ℝ) : ℂ) • v μ)
      = ∑ μ, ∑ μ', (((O e μ : ℝ) : ℂ) * ((O e μ' : ℝ) : ℂ)) * inner ℂ (v μ) (v μ') := by
    intro e
    rw [sum_inner]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun μ' _ => ?_
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    ring
  have hw : ∑ e, inner ℂ (∑ μ, ((O e μ : ℝ) : ℂ) • v μ) (∑ μ, ((O e μ : ℝ) : ℂ) • v μ)
      = ∑ μ, inner ℂ (v μ) (v μ) := by
    simp only [h1]
    calc ∑ e, ∑ μ, ∑ μ', (((O e μ : ℝ) : ℂ) * ((O e μ' : ℝ) : ℂ)) * inner ℂ (v μ) (v μ')
        = ∑ μ, ∑ μ', (∑ e, ((O e μ : ℝ) : ℂ) * ((O e μ' : ℝ) : ℂ)) * inner ℂ (v μ) (v μ') := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun μ' _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ μ, inner ℂ (v μ) (v μ) := by
          refine Finset.sum_congr rfl fun μ _ => ?_
          simp [key]
  have hre : ∀ x : F, ‖x‖ ^ 2 = (inner ℂ x x).re := fun x =>
    (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
  simp only [hre, ← Complex.re_sum, hw]

/-! ### The star-closed stack and the `2√2` commutator perturbation bound -/

/-- The star-closed stacking `(K_1, …, K_s, K_1^*, …, K_s^*)` of a coefficient tuple. -/
def starClosedStack {s : ℕ} (K : Fin s → Matrix n n ℂ) (j : Fin (s + s)) : Matrix n n ℂ :=
  if h : (j : ℕ) < s then K ⟨j, h⟩ else (K ⟨j - s, by have := j.2; omega⟩)ᴴ

theorem starClosedStack_castAdd {s : ℕ} (K : Fin s → Matrix n n ℂ) (i : Fin s) :
    starClosedStack K (Fin.castAdd s i) = K i := by
  have h : ((Fin.castAdd s i : Fin (s + s)) : ℕ) < s := by simp
  have e : (⟨(Fin.castAdd s i : Fin (s + s)), h⟩ : Fin s) = i := Fin.ext (by simp)
  unfold starClosedStack
  rw [dif_pos h]
  try rw [e]

theorem starClosedStack_natAdd {s : ℕ} (K : Fin s → Matrix n n ℂ) (i : Fin s) :
    starClosedStack K (Fin.natAdd s i) = (K i)ᴴ := by
  unfold starClosedStack
  rw [dif_neg (by simp)]
  congr 2
  ext
  simp

theorem starClosedStack_sub {s : ℕ} (K K' : Fin s → Matrix n n ℂ) :
    starClosedStack K - starClosedStack K' = starClosedStack (K - K') := by
  funext j
  simp only [Pi.sub_apply, starClosedStack]
  split_ifs <;> simp [Matrix.conjTranspose_sub]

/-- The Hilbert–Schmidt coefficient error `(∑_e ‖K̂_e − K_e‖²_HS)^{1/2}`. -/
noncomputable def hsCoefficientError {s : ℕ} (K' K : Fin s → Matrix n n ℂ) : ℝ :=
  Real.sqrt (∑ e, ‖matrixL2 (K' e - K e)‖ ^ 2)

theorem hsCoefficientError_nonneg {s : ℕ} (K' K : Fin s → Matrix n n ℂ) :
    0 ≤ hsCoefficientError K' K := Real.sqrt_nonneg _

/-- The operator-norm displacement of the star-closed stack is at most `√2` times the
Hilbert–Schmidt coefficient error. -/
theorem opNormDisplacement_starClosedStack_le {s : ℕ} (K' K : Fin s → Matrix n n ℂ) :
    opNormDisplacement (starClosedStack K') (starClosedStack K)
      ≤ Real.sqrt 2 * hsCoefficientError K' K := by
  unfold opNormDisplacement opNormBudget hsCoefficientError
  rw [starClosedStack_sub, ← Real.sqrt_mul (by norm_num)]
  refine Real.sqrt_le_sqrt ?_
  rw [Fin.sum_univ_add]
  simp only [starClosedStack_castAdd, starClosedStack_natAdd, Pi.sub_apply,
    Matrix.l2_opNorm_conjTranspose]
  have h : ∑ e, ‖K' e - K e‖ ^ 2 ≤ ∑ e, ‖matrixL2 (K' e - K e)‖ ^ 2 :=
    Finset.sum_le_sum fun e _ =>
      pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_le_matrixL2_norm _) 2
  linarith

/-- **`eq:appendix-commutator-error`**: the star-closed stacked commutator map changes by at
most `2√2 e_K` in `2 → 2` norm, for any `e_K` dominating the Hilbert–Schmidt coefficient
error. -/
theorem starClosedStack_commutator_perturbation {s : ℕ} (K' K : Fin s → Matrix n n ℂ)
    (eK : ℝ) (he : hsCoefficientError K' K ≤ eK) (x : EuclideanSpace ℂ (n × n)) :
    ‖jointCommutatorL2 (starClosedStack K') x - jointCommutatorL2 (starClosedStack K) x‖
      ≤ 2 * Real.sqrt 2 * eK * ‖x‖ := by
  refine (jointCommutatorL2_sub_norm_le _ _ x).trans ?_
  have h1 := opNormDisplacement_starClosedStack_le K' K
  have h2 : Real.sqrt 2 * hsCoefficientError K' K ≤ Real.sqrt 2 * eK :=
    mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)
  have hx := norm_nonneg x
  nlinarith [h1, h2, hx]

/-! ### The robust stopping test on a protected complement -/

/-- **Least-singular-value stability** (`prop:reconstruction-error`, last clause).  If the
measured stacked commutator map `𝒟̂` has least singular value at least `ŝ` on a subspace `W`
(`ŝ ‖x‖ ≤ ‖𝒟̂ x‖` for `x ∈ W`) and `ŝ > 2√2 e_K`, then the true map `𝒟` has least singular
value at least `ŝ − 2√2 e_K > 0` on `W`; in particular `W` carries no commutant direction. -/
theorem robust_commutant_stopping_test {s : ℕ} (K' K : Fin s → Matrix n n ℂ)
    (eK : ℝ) (he : hsCoefficientError K' K ≤ eK)
    (W : Submodule ℂ (EuclideanSpace ℂ (n × n))) (ŝ : ℝ)
    (hŝ : ∀ x ∈ W, ŝ * ‖x‖ ≤ ‖jointCommutatorL2 (starClosedStack K') x‖)
    (hgap : 2 * Real.sqrt 2 * eK < ŝ) :
    (∀ x ∈ W, (ŝ - 2 * Real.sqrt 2 * eK) * ‖x‖
        ≤ ‖jointCommutatorL2 (starClosedStack K) x‖)
    ∧ (∀ x ∈ W, jointCommutatorL2 (starClosedStack K) x = 0 → x = 0)
    ∧ (∀ X : Matrix n n ℂ, matrixL2 X ∈ W → (∀ e, K e * X = X * K e) →
        (∀ e, (K e)ᴴ * X = X * (K e)ᴴ) → X = 0) := by
  have hlow : ∀ x ∈ W, (ŝ - 2 * Real.sqrt 2 * eK) * ‖x‖
      ≤ ‖jointCommutatorL2 (starClosedStack K) x‖ := by
    intro x hx
    have h1 := hŝ x hx
    have h2 := starClosedStack_commutator_perturbation K' K eK he x
    have h3 := norm_sub_norm_le (jointCommutatorL2 (starClosedStack K') x)
      (jointCommutatorL2 (starClosedStack K) x)
    nlinarith [h1, h2, h3]
  have hker : ∀ x ∈ W, jointCommutatorL2 (starClosedStack K) x = 0 → x = 0 := by
    intro x hx h0
    have h := hlow x hx
    rw [h0, norm_zero] at h
    by_contra hne
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
    have := mul_pos (sub_pos.mpr hgap) hpos
    linarith
  refine ⟨hlow, hker, ?_⟩
  intro X hX hc hc'
  have hcomm : ∀ j, starClosedStack K j * X = X * starClosedStack K j := by
    intro j
    unfold starClosedStack
    split_ifs
    · exact hc _
    · exact hc' _
  have h0 : jointCommutatorL2 (starClosedStack K) (matrixL2 X) = 0 :=
    LinearMap.mem_ker.mp ((matrixL2_mem_jointCommutator_ker_iff _ X).2 hcomm)
  have hz := hker _ hX h0
  have := congrArg l2Matrix hz
  rwa [l2Matrix_matrixL2] at this

/-- The kernel form of the stopping test: if a verified protected subspace `M` lies in the
commutant kernel and the measured map has least singular value `ŝ > 2√2 e_K` on `Mᗮ`, then
the true commutant kernel is exactly `M` (no additional commutant direction). -/
theorem robust_commutant_stopping_test_ker {s : ℕ} (K' K : Fin s → Matrix n n ℂ)
    (eK : ℝ) (he : hsCoefficientError K' K ≤ eK)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (hM : M ≤ LinearMap.ker (jointCommutatorL2 (starClosedStack K))) (ŝ : ℝ)
    (hŝ : ∀ x ∈ Mᗮ, ŝ * ‖x‖ ≤ ‖jointCommutatorL2 (starClosedStack K') x‖)
    (hgap : 2 * Real.sqrt 2 * eK < ŝ) :
    LinearMap.ker (jointCommutatorL2 (starClosedStack K)) = M := by
  obtain ⟨_, hker, _⟩ := robust_commutant_stopping_test K' K eK he Mᗮ ŝ hŝ hgap
  refine le_antisymm ?_ hM
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := M.exists_add_mem_mem_orthogonal x
  have hzker : jointCommutatorL2 (starClosedStack K) z = 0 := by
    have := LinearMap.mem_ker.mp hx
    rw [map_add, LinearMap.mem_ker.mp (hM hy), zero_add] at this
    exact this
  rw [hker z hz hzker, add_zero]
  exact hy

/-! ### The coherent frame of the six-edge source class -/

namespace TenPanel

/-- The twenty-four coefficient labels `(e, a)`. -/
abbrev Label := Fin 6 × Fin 4

section Frame

variable {ι : Type*} [Fintype ι]

/-- The Stinespring map `V = ∑_ν C_ν ⊗ |ν⟩` of a finite coefficient family, as a matrix
`H → H ⊗ ℂ^ι`: `V_{(x,ν),y} = (C_ν)_{xy}`. -/
def stinespringIsometry (C : ι → Matrix n n ℂ) : Matrix (n × ι) n ℂ :=
  of fun p y => C p.2 p.1 y

/-- The pulled coefficient `C(z) = (I ⊗ ⟨z|) V = ∑_ν \bar z_ν C_ν`. -/
def pulledCoefficient (C : ι → Matrix n n ℂ) (z : ι → ℂ) : Matrix n n ℂ :=
  ∑ ν, star (z ν) • C ν

/-- The Heisenberg pullback of the complementary channel, `𝒫*(F) = V* (I ⊗ F) V`. -/
def complementaryPullback (C : ι → Matrix n n ℂ) (F : Matrix ι ι ℂ) : Matrix n n ℂ :=
  (stinespringIsometry C)ᴴ * ((1 : Matrix n n ℂ) ⊗ₖ F) * stinespringIsometry C

theorem complementaryPullback_add (C : ι → Matrix n n ℂ) (F G : Matrix ι ι ℂ) :
    complementaryPullback C (F + G)
      = complementaryPullback C F + complementaryPullback C G := by
  simp only [complementaryPullback, kronecker_add, Matrix.mul_add, Matrix.add_mul]

theorem complementaryPullback_smul (C : ι → Matrix n n ℂ) (a : ℂ) (F : Matrix ι ι ℂ) :
    complementaryPullback C (a • F) = a • complementaryPullback C F := by
  simp only [complementaryPullback, kronecker_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- `𝒫*(F) = ∑_{ν ν'} F_{νν'} C_ν^* C_{ν'}`. -/
theorem complementaryPullback_eq_sum (C : ι → Matrix n n ℂ) (F : Matrix ι ι ℂ) :
    complementaryPullback C F = ∑ ν, ∑ ν', F ν ν' • ((C ν)ᴴ * C ν') := by
  have hstep : ((1 : Matrix n n ℂ) ⊗ₖ F) * stinespringIsometry C
      = of fun p y => ∑ ν', F p.2 ν' * C ν' p.1 y := by
    ext ⟨p, ν⟩ y
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, kronecker_apply, Matrix.one_apply,
      stinespringIsometry, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  rw [complementaryPullback, Matrix.mul_assoc, hstep]
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stinespringIsometry, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  calc ∑ p, ∑ ν, ∑ ν', star (C ν p x) * (F ν ν' * C ν' p y)
      = ∑ ν, ∑ ν', ∑ p, star (C ν p x) * (F ν ν' * C ν' p y) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ ν, ∑ ν', ∑ p, F ν ν' * (star (C ν p x) * C ν' p y) := by
        refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ν' _ =>
          Finset.sum_congr rfl fun p _ => ?_
        ring

/-- **`eq:complementary-pullback`**: `𝒫*(|z⟩⟨w|) = C(z)^* C(w)`. -/
theorem complementaryPullback_vecMulVec (C : ι → Matrix n n ℂ) (z w : ι → ℂ) :
    complementaryPullback C (vecMulVec z (star w))
      = (pulledCoefficient C z)ᴴ * pulledCoefficient C w := by
  rw [complementaryPullback_eq_sum]
  simp only [pulledCoefficient, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    star_star, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, vecMulVec_apply,
    Pi.star_apply]
  exact Finset.sum_comm

end Frame

variable {E R : Type*} [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

/-- The accepted operators `A_{e,a} = K_e ⊗ Q_a`. -/
def acceptedOp (K : Fin 6 → Matrix E E ℂ) (Q : Fin 4 → Matrix R R ℂ) (j : Label) :
    Matrix (E × R) (E × R) ℂ :=
  K j.1 ⊗ₖ Q j.2

/-- `c = 𝟏/√2 ∈ ℂ^24`. -/
def uniformC : Label → ℂ := fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

/-- The coefficient Gram `M_ϑ = ϑ I + (1 − ϑ) c c*`. -/
def coefficientGram (ϑ : ℝ) : Matrix Label Label ℂ :=
  (ϑ : ℂ) • 1 + ((1 - ϑ : ℝ) : ℂ) • vecMulVec uniformC (star uniformC)

/-- The orthogonal projection onto the global uniform direction, `P = 𝟏𝟏ᵀ/24 = cc*/12`. -/
def uniformProj : Matrix Label Label ℂ := (((24 : ℝ)⁻¹ : ℝ) : ℂ) • of fun _ _ => (1 : ℂ)

/-- `h = 12 − 11ϑ`, the eigenvalue of `M_ϑ` on the uniform direction. -/
def hParam (ϑ : ℝ) : ℝ := 12 - 11 * ϑ

/-- The explicit positive square root `M_ϑ^{1/2} = √ϑ (I − P) + √h P`. -/
def coefficientGramSqrt (ϑ : ℝ) : Matrix Label Label ℂ :=
  ((Real.sqrt ϑ : ℝ) : ℂ) • (1 - uniformProj) + ((Real.sqrt (hParam ϑ) : ℝ) : ℂ) • uniformProj

theorem card_label : Fintype.card Label = 24 := by
  simp [Label]

theorem uniformProj_mul_self : uniformProj * uniformProj = uniformProj := by
  ext i j
  simp [uniformProj, Matrix.mul_apply, Finset.sum_const, Finset.card_univ]

theorem uniformProj_conjTranspose : uniformProjᴴ = uniformProj := by
  ext i j
  simp [uniformProj]

theorem vecMulVec_uniformC : vecMulVec uniformC (star uniformC) = (12 : ℂ) • uniformProj := by
  ext i j
  simp only [vecMulVec_apply, uniformC, uniformProj, Pi.star_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, mul_one, Complex.star_def, Complex.conj_ofReal]
  have h : ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 12 * (24 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  exact_mod_cast h

theorem uniformProj_posSemidef : uniformProj.PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self uniformProj
  rwa [uniformProj_conjTranspose, uniformProj_mul_self] at h

theorem one_sub_uniformProj_posSemidef : (1 - uniformProj).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (1 - uniformProj)
  have e : (1 - uniformProj)ᴴ * (1 - uniformProj) = 1 - uniformProj := by
    simp only [conjTranspose_sub, conjTranspose_one, uniformProj_conjTranspose, sub_mul,
      mul_sub, Matrix.one_mul, Matrix.mul_one, uniformProj_mul_self]
    abel
  rwa [e] at h

/-- `(M_ϑ^{1/2})² = M_ϑ`. -/
theorem coefficientGramSqrt_mul_self {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (hh : 0 ≤ hParam ϑ) :
    coefficientGramSqrt ϑ * coefficientGramSqrt ϑ = coefficientGram ϑ := by
  set a : ℂ := ((Real.sqrt ϑ : ℝ) : ℂ) with ha_def
  set b : ℂ := ((Real.sqrt (hParam ϑ) : ℝ) : ℂ) with hb_def
  have ha : a * a = (ϑ : ℂ) := by
    rw [ha_def, ← Complex.ofReal_mul, Real.mul_self_sqrt hϑ]
  have hb : b * b = ((hParam ϑ : ℝ) : ℂ) := by
    rw [hb_def, ← Complex.ofReal_mul, Real.mul_self_sqrt hh]
  have hS : coefficientGramSqrt ϑ = a • (1 : Matrix Label Label ℂ) + (b - a) • uniformProj := by
    simp only [coefficientGramSqrt, smul_sub, sub_smul, ← ha_def, ← hb_def]
    abel
  rw [hS, coefficientGram, vecMulVec_uniformC]
  have hP := uniformProj_mul_self
  have hexp : (a • (1 : Matrix Label Label ℂ) + (b - a) • uniformProj)
      * (a • 1 + (b - a) • uniformProj)
      = (a * a) • (1 : Matrix Label Label ℂ) + (b * b - a * a) • uniformProj := by
    simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hP]
    module
  have hcoef : b * b - a * a = ((1 - ϑ : ℝ) : ℂ) * 12 := by
    rw [hb, ha, hParam]
    push_cast
    ring
  rw [hexp, hcoef, ha, smul_smul]

theorem coefficientGramSqrt_posSemidef {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (hh : 0 ≤ hParam ϑ) :
    (coefficientGramSqrt ϑ).PosSemidef := by
  unfold coefficientGramSqrt
  refine PosSemidef.add ?_ ?_
  · exact one_sub_uniformProj_posSemidef.smul (Complex.zero_le_real.mpr (Real.sqrt_nonneg _))
  · exact uniformProj_posSemidef.smul (Complex.zero_le_real.mpr (Real.sqrt_nonneg _))

/-- The explicit square root is Mathlib's positive square root of `M_ϑ`. -/
theorem cfc_sqrt_coefficientGram {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (hh : 0 ≤ hParam ϑ) :
    CFC.sqrt (coefficientGram ϑ) = coefficientGramSqrt ϑ :=
  CFC.sqrt_unique (coefficientGramSqrt_mul_self hϑ hh)
    (coefficientGramSqrt_posSemidef hϑ hh).nonneg

/-- The frame coefficients `C_ν = ∑_j (M_ϑ^{1/2})_{jν} A_j` (columns of `𝖡 M_ϑ^{1/2}`). -/
def frameCoefficient (ϑ : ℝ) (K : Fin 6 → Matrix E E ℂ) (Q : Fin 4 → Matrix R R ℂ)
    (ν : Label) : Matrix (E × R) (E × R) ℂ :=
  ∑ j, coefficientGramSqrt ϑ j ν • acceptedOp K Q j

theorem pulledCoefficient_frame (ϑ : ℝ) (K : Fin 6 → Matrix E E ℂ) (Q : Fin 4 → Matrix R R ℂ)
    (z : Label → ℂ) :
    pulledCoefficient (frameCoefficient ϑ K Q) z
      = ∑ j, (∑ ν, coefficientGramSqrt ϑ j ν * star (z ν)) • acceptedOp K Q j := by
  simp only [pulledCoefficient, frameCoefficient, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [mul_comm]

theorem coefficientGramSqrt_apply (ϑ : ℝ) (j ν : Label) :
    coefficientGramSqrt ϑ j ν
      = ((Real.sqrt ϑ : ℝ) : ℂ) * ((if j = ν then 1 else 0) - (((24 : ℝ)⁻¹ : ℝ) : ℂ))
        + ((Real.sqrt (hParam ϑ) : ℝ) : ℂ) * (((24 : ℝ)⁻¹ : ℝ) : ℂ) := by
  simp [coefficientGramSqrt, uniformProj, Matrix.one_apply]

/-- The row action of `M_ϑ^{1/2}`: `(M_ϑ^{1/2} z)_j = √ϑ (z_j − P z) + √h P z`. -/
theorem coefficientGramSqrt_row_sum (ϑ : ℝ) (j : Label) (z : Label → ℂ) :
    ∑ ν, coefficientGramSqrt ϑ j ν * z ν
      = ((Real.sqrt ϑ : ℝ) : ℂ) * (z j - (((24 : ℝ)⁻¹ : ℝ) : ℂ) * ∑ ν, z ν)
        + ((Real.sqrt (hParam ϑ) : ℝ) : ℂ) * ((((24 : ℝ)⁻¹ : ℝ) : ℂ) * ∑ ν, z ν) := by
  simp only [coefficientGramSqrt_apply, add_mul, sub_mul, mul_assoc, ite_mul, one_mul,
    zero_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- `u = 𝟏/√24`, the uniform environment vector. -/
def uniformEnv : Label → ℂ := fun _ => (((Real.sqrt 24)⁻¹ : ℝ) : ℂ)

/-- `(r_μ)_{e,a} = O_{eμ}/2`, the contrast environment vectors. -/
def contrastEnv (O : Matrix (Fin 6) (Fin 5) ℝ) (μ : Fin 5) : Label → ℂ :=
  fun j => ((O j.1 μ / 2 : ℝ) : ℂ)

/-- `X_μ = |u⟩⟨r_μ| + |r_μ⟩⟨u|` (`eq:ten-quadratures`). -/
def quadratureX (O : Matrix (Fin 6) (Fin 5) ℝ) (μ : Fin 5) : Matrix Label Label ℂ :=
  vecMulVec uniformEnv (star (contrastEnv O μ)) + vecMulVec (contrastEnv O μ) (star uniformEnv)

/-- `Y_μ = −i|u⟩⟨r_μ| + i|r_μ⟩⟨u|` (`eq:ten-quadratures`). -/
def quadratureY (O : Matrix (Fin 6) (Fin 5) ℝ) (μ : Fin 5) : Matrix Label Label ℂ :=
  (-Complex.I) • vecMulVec uniformEnv (star (contrastEnv O μ))
    + Complex.I • vecMulVec (contrastEnv O μ) (star uniformEnv)

/-- `D_μ = ∑_e O_{eμ} K_e`. -/
def edgeContrast (O : Matrix (Fin 6) (Fin 5) ℝ) (K : Fin 6 → Matrix E E ℂ) (μ : Fin 5) :
    Matrix E E ℂ :=
  ∑ e, ((O e μ : ℝ) : ℂ) • K e

/-- The reconstruction scale `2√3/√(ϑh)`. -/
def reconstructionScale (ϑ : ℝ) : ℝ := 2 * Real.sqrt 3 / Real.sqrt (ϑ * hParam ϑ)

theorem star_uniformEnv (j : Label) : star (uniformEnv j) = uniformEnv j := by
  simp [uniformEnv]

theorem star_contrastEnv (O : Matrix (Fin 6) (Fin 5) ℝ) (μ : Fin 5) (j : Label) :
    star (contrastEnv O μ j) = contrastEnv O μ j := by
  simp [contrastEnv]

theorem sum_uniformEnv : ∑ ν, uniformEnv ν = (24 : ℂ) * (((Real.sqrt 24)⁻¹ : ℝ) : ℂ) := by
  simp [uniformEnv, Finset.sum_const, Finset.card_univ, card_label]

theorem sum_contrastEnv {O : Matrix (Fin 6) (Fin 5) ℝ} (hcol : ∀ μ, ∑ e, O e μ = 0)
    (μ : Fin 5) : ∑ ν, contrastEnv O μ ν = 0 := by
  have h : ((∑ e, O e μ : ℝ) : ℂ) = 0 := by rw [hcol μ]; simp
  rw [Fintype.sum_prod_type]
  simp only [contrastEnv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast at h ⊢
  calc ∑ e, (4 : ℂ) * ((O e μ : ℂ) / 2) = 2 * ∑ e, (O e μ : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
    _ = 0 := by rw [h, mul_zero]

/-- `X_μ + i Y_μ = 2 |u⟩⟨r_μ|`. -/
theorem quadratureX_add_I_smul_quadratureY (O : Matrix (Fin 6) (Fin 5) ℝ) (μ : Fin 5) :
    quadratureX O μ + Complex.I • quadratureY O μ
      = (2 : ℂ) • vecMulVec uniformEnv (star (contrastEnv O μ)) := by
  simp only [quadratureX, quadratureY, smul_add, smul_smul, mul_neg, Complex.I_mul_I,
    neg_neg, one_smul, neg_one_smul]
  abel_nf
  simp [two_smul]

/-- `∑_{e,a} f_e A_{e,a} = (∑_e f_e K_e) ⊗ (∑_a Q_a)`. -/
theorem sum_smul_acceptedOp (K : Fin 6 → Matrix E E ℂ) (Q : Fin 4 → Matrix R R ℂ)
    (f : Fin 6 → ℂ) :
    ∑ j : Label, f j.1 • acceptedOp K Q j = (∑ e, f e • K e) ⊗ₖ (∑ a, Q a) := by
  ext ⟨x, r⟩ ⟨y, s⟩
  simp only [acceptedOp, Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    kronecker_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- `C(u) = √(h/12) I` (first intermediate claim of the manuscript's proof). -/
theorem pulledCoefficient_uniformEnv (ϑ : ℝ) {K : Fin 6 → Matrix E E ℂ}
    {Q : Fin 4 → Matrix R R ℂ} (hK : ∑ e, K e = ((Real.sqrt 2 : ℝ) : ℂ) • 1)
    (hQ : ∑ a, Q a = 1) :
    pulledCoefficient (frameCoefficient ϑ K Q) uniformEnv
      = ((Real.sqrt (hParam ϑ) / Real.sqrt 12 : ℝ) : ℂ) • 1 := by
  rw [pulledCoefficient_frame]
  simp only [star_uniformEnv]
  have hrow : ∀ j : Label, (∑ ν, coefficientGramSqrt ϑ j ν * uniformEnv ν)
      = ((Real.sqrt (hParam ϑ) * (Real.sqrt 24)⁻¹ : ℝ) : ℂ) := by
    intro j
    rw [coefficientGramSqrt_row_sum, sum_uniformEnv]
    simp only [uniformEnv]
    push_cast
    ring
  simp only [hrow]
  rw [sum_smul_acceptedOp K Q (fun _ => ((Real.sqrt (hParam ϑ) * (Real.sqrt 24)⁻¹ : ℝ) : ℂ)),
    ← Finset.smul_sum, hK, hQ, smul_smul, smul_kronecker, one_kronecker_one]
  congr 1
  have h24 : Real.sqrt 24 = Real.sqrt 12 * Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  rw [← Complex.ofReal_mul, h24]
  congr 1
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have h12 : Real.sqrt 12 ≠ 0 := by positivity
  field_simp

/-- `C(r_μ) = (√ϑ/2) D_μ ⊗ I` (second intermediate claim of the manuscript's proof). -/
theorem pulledCoefficient_contrastEnv (ϑ : ℝ) {K : Fin 6 → Matrix E E ℂ}
    {Q : Fin 4 → Matrix R R ℂ} {O : Matrix (Fin 6) (Fin 5) ℝ}
    (hQ : ∑ a, Q a = 1) (hcol : ∀ μ, ∑ e, O e μ = 0) (μ : Fin 5) :
    pulledCoefficient (frameCoefficient ϑ K Q) (contrastEnv O μ)
      = ((Real.sqrt ϑ / 2 : ℝ) : ℂ) • (edgeContrast O K μ ⊗ₖ (1 : Matrix R R ℂ)) := by
  rw [pulledCoefficient_frame]
  simp only [star_contrastEnv]
  have hrow : ∀ j : Label, (∑ ν, coefficientGramSqrt ϑ j ν * contrastEnv O μ ν)
      = ((Real.sqrt ϑ / 2 : ℝ) : ℂ) * ((O j.1 μ : ℝ) : ℂ) := by
    intro j
    rw [coefficientGramSqrt_row_sum, sum_contrastEnv hcol]
    simp only [contrastEnv]
    push_cast
    ring
  simp only [hrow]
  rw [sum_smul_acceptedOp K Q (fun e => ((Real.sqrt ϑ / 2 : ℝ) : ℂ) * ((O e μ : ℝ) : ℂ)), hQ,
    ← smul_kronecker]
  congr 1
  rw [edgeContrast, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [smul_smul]

/-- `(√18)⁻¹ = √2/6`. -/
theorem inv_sqrt_eighteen : (Real.sqrt 18)⁻¹ = Real.sqrt 2 / 6 := by
  have h18 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    rw [show (18 : ℝ) = 3 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h18]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  norm_num

/-- The Helmert inversion `K_e = I/√18 + ∑_μ O_{eμ} D_μ` (second formula of
`eq:ten-panel-reconstruction`). -/
theorem helmert_inversion {K : Fin 6 → Matrix E E ℂ} {O : Matrix (Fin 6) (Fin 5) ℝ}
    (hK : ∑ e, K e = ((Real.sqrt 2 : ℝ) : ℂ) • 1)
    (hproj : O * Oᵀ = 1 - ((6 : ℝ)⁻¹ : ℝ) • of fun _ _ => (1 : ℝ)) (e : Fin 6) :
    K e = (((Real.sqrt 18)⁻¹ : ℝ) : ℂ) • 1 + ∑ μ, ((O e μ : ℝ) : ℂ) • edgeContrast O K μ := by
  have hOO : ∀ f, (∑ μ, ((O e μ : ℝ) : ℂ) * ((O f μ : ℝ) : ℂ))
      = (if e = f then (1 : ℂ) else 0) - (((6 : ℝ)⁻¹ : ℝ) : ℂ) := by
    intro f
    have h := congrFun (congrFun hproj e) f
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one] at h
    by_cases hef : e = f
    · simp only [hef, ite_true] at h ⊢
      exact_mod_cast h
    · simp only [hef, ite_false] at h ⊢
      exact_mod_cast h
  have hsum : ∑ μ, ((O e μ : ℝ) : ℂ) • edgeContrast O K μ
      = K e - (((6 : ℝ)⁻¹ : ℝ) : ℂ) • ∑ f, K f := by
    simp only [edgeContrast, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hOO, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.smul_sum]
  rw [hsum, hK, smul_smul]
  have hc : (((Real.sqrt 18)⁻¹ : ℝ) : ℂ) = (((6 : ℝ)⁻¹ : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, inv_sqrt_eighteen]
    congr 1
    ring
  rw [hc]
  abel

/-- **`prop:ten-panel-reconstruction` (Explicit ten-panel reconstruction).**  For the
normalized six-edge source class with `∑_e K_e = √2 I`, `∑_a Q_a = I`, `0 < ϑ < 1` and a
Helmert frame `O` (`Oᵀ𝟏 = 0`, `OOᵀ = I − 𝟏𝟏ᵀ/6`), the ten Hermitian operator-valued pullbacks
`𝖷_μ = 𝒫*_ϑ(X_μ)`, `𝖸_μ = 𝒫*_ϑ(Y_μ)` determine all six coefficients through

`D_μ ⊗ I = (2√3/√(ϑh)) (𝖷_μ + i 𝖸_μ)`,  `K_e = I/√18 + ∑_μ O_{eμ} D_μ`. -/
theorem ten_panel_reconstruction {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ < 1)
    {K : Fin 6 → Matrix E E ℂ} {Q : Fin 4 → Matrix R R ℂ} {O : Matrix (Fin 6) (Fin 5) ℝ}
    (hK : ∑ e, K e = ((Real.sqrt 2 : ℝ) : ℂ) • 1) (hQ : ∑ a, Q a = 1)
    (hcol : ∀ μ, ∑ e, O e μ = 0)
    (hproj : O * Oᵀ = 1 - ((6 : ℝ)⁻¹ : ℝ) • of fun _ _ => (1 : ℝ)) :
    (∀ μ, edgeContrast O K μ ⊗ₖ (1 : Matrix R R ℂ)
        = ((reconstructionScale ϑ : ℝ) : ℂ)
          • (complementaryPullback (frameCoefficient ϑ K Q) (quadratureX O μ)
              + Complex.I • complementaryPullback (frameCoefficient ϑ K Q) (quadratureY O μ)))
    ∧ ∀ e, K e = (((Real.sqrt 18)⁻¹ : ℝ) : ℂ) • 1
        + ∑ μ, ((O e μ : ℝ) : ℂ) • edgeContrast O K μ := by
  refine ⟨fun μ => ?_, helmert_inversion hK hproj⟩
  have hh : 0 < hParam ϑ := by unfold hParam; linarith
  have hpull : complementaryPullback (frameCoefficient ϑ K Q) (quadratureX O μ)
      + Complex.I • complementaryPullback (frameCoefficient ϑ K Q) (quadratureY O μ)
      = ((Real.sqrt (hParam ϑ) * Real.sqrt ϑ / Real.sqrt 12 : ℝ) : ℂ)
          • (edgeContrast O K μ ⊗ₖ (1 : Matrix R R ℂ)) := by
    rw [← complementaryPullback_smul, ← complementaryPullback_add,
      quadratureX_add_I_smul_quadratureY, complementaryPullback_smul,
      complementaryPullback_vecMulVec, pulledCoefficient_uniformEnv ϑ hK hQ,
      pulledCoefficient_contrastEnv ϑ hQ hcol, conjTranspose_smul, conjTranspose_one,
      smul_mul_smul_comm, one_mul, smul_smul]
    congr 1
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [hpull, smul_smul]
  have hscale : ((reconstructionScale ϑ : ℝ) : ℂ)
      * ((Real.sqrt (hParam ϑ) * Real.sqrt ϑ / Real.sqrt 12 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    have h12 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
      rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    rw [reconstructionScale, Real.sqrt_mul hϑ.le, h12]
    have h3 : Real.sqrt 3 ≠ 0 := by positivity
    have hϑ' : Real.sqrt ϑ ≠ 0 := by positivity
    have hh' : Real.sqrt (hParam ϑ) ≠ 0 := by positivity
    field_simp
  rw [hscale, one_smul]

theorem kronecker_one_injective [Nonempty R] {A B : Matrix E E ℂ}
    (h : A ⊗ₖ (1 : Matrix R R ℂ) = B ⊗ₖ 1) : A = B := by
  obtain ⟨r⟩ := ‹Nonempty R›
  ext x y
  have := congrFun (congrFun h (x, r)) (y, r)
  simpa [kronecker_apply] using this

/-- The "determines" clause of `prop:ten-panel-reconstruction`: two coefficient families of
the six-edge source class with the same ten operator-valued pullbacks coincide (hence have
the same represented system algebra and commutant). -/
theorem ten_panel_determines_coefficients [Nonempty R] {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ < 1)
    {K K' : Fin 6 → Matrix E E ℂ} {Q : Fin 4 → Matrix R R ℂ} {O : Matrix (Fin 6) (Fin 5) ℝ}
    (hK : ∑ e, K e = ((Real.sqrt 2 : ℝ) : ℂ) • 1) (hK' : ∑ e, K' e = ((Real.sqrt 2 : ℝ) : ℂ) • 1)
    (hQ : ∑ a, Q a = 1) (hcol : ∀ μ, ∑ e, O e μ = 0)
    (hproj : O * Oᵀ = 1 - ((6 : ℝ)⁻¹ : ℝ) • of fun _ _ => (1 : ℝ))
    (hX : ∀ μ, complementaryPullback (frameCoefficient ϑ K Q) (quadratureX O μ)
      = complementaryPullback (frameCoefficient ϑ K' Q) (quadratureX O μ))
    (hY : ∀ μ, complementaryPullback (frameCoefficient ϑ K Q) (quadratureY O μ)
      = complementaryPullback (frameCoefficient ϑ K' Q) (quadratureY O μ)) :
    K = K' := by
  obtain ⟨h1, h2⟩ := ten_panel_reconstruction (Q := Q) hϑ hϑ1 hK hQ hcol hproj
  obtain ⟨h1', h2'⟩ := ten_panel_reconstruction (Q := Q) hϑ hϑ1 hK' hQ hcol hproj
  have hD : ∀ μ, edgeContrast O K μ = edgeContrast O K' μ := fun μ =>
    kronecker_one_injective (by rw [h1 μ, h1' μ, hX μ, hY μ])
  funext e
  rw [h2 e, h2' e]
  simp only [hD]

/-! ### `prop:reconstruction-error` in the ten-panel frame -/

/-- The linear reconstruction of a contrast from measured panels,
`D̂_μ = (2√3/√(ϑh)) (X̂_μ + i Ŷ_μ)`. -/
def reconstructedContrast (ϑ : ℝ) (X' Y' : Fin 5 → Matrix n n ℂ) (μ : Fin 5) :
    Matrix n n ℂ :=
  ((reconstructionScale ϑ : ℝ) : ℂ) • (X' μ + Complex.I • Y' μ)

/-- The reconstructed coefficients `K̂_e = I/√18 + ∑_μ O_{eμ} D̂_μ`. -/
def reconstructedCoefficient (ϑ : ℝ) (O : Matrix (Fin 6) (Fin 5) ℝ)
    (X' Y' : Fin 5 → Matrix n n ℂ) (e : Fin 6) : Matrix n n ℂ :=
  (((Real.sqrt 18)⁻¹ : ℝ) : ℂ) • 1 + ∑ μ, ((O e μ : ℝ) : ℂ) • reconstructedContrast ϑ X' Y' μ

/-- The error budget `e_K = (2√3/√(ϑh)) (∑_μ (ε_{X,μ} + ε_{Y,μ})²)^{1/2}` of
`eq:appendix-reconstruction-error`. -/
def panelErrorBudget (ϑ : ℝ) (εX εY : Fin 5 → ℝ) : ℝ :=
  reconstructionScale ϑ * Real.sqrt (∑ μ, (εX μ + εY μ) ^ 2)

theorem reconstructionScale_nonneg (ϑ : ℝ) : 0 ≤ reconstructionScale ϑ := by
  unfold reconstructionScale
  positivity

theorem sum_kronecker_one {ι : Type*} [Fintype ι] (f : ι → Matrix E E ℂ) :
    (∑ i, f i) ⊗ₖ (1 : Matrix R R ℂ) = ∑ i, f i ⊗ₖ (1 : Matrix R R ℂ) := by
  ext ⟨x, r⟩ ⟨y, s⟩
  simp [kronecker_apply, Matrix.sum_apply, Finset.sum_mul]

/-- **`prop:reconstruction-error` (Robust commutant stopping test).**  If the ten measured
panels `X̂_μ, Ŷ_μ` have Hilbert–Schmidt errors `ε_{X,μ}, ε_{Y,μ}` relative to the true pullbacks
`𝒫*_ϑ(X_μ), 𝒫*_ϑ(Y_μ)`, then the linear reconstruction `K̂_e` satisfies

* `(∑_e ‖K̂_e − K_e ⊗ I‖²_HS)^{1/2} ≤ e_K` (`eq:appendix-reconstruction-error`);
* `‖𝒟̂ − 𝒟‖_{2→2} ≤ 2√2 e_K` for the star-closed stacked commutator maps
  (`eq:appendix-commutator-error`);
* a measured least singular value `ŝ > 2√2 e_K` of `𝒟̂` on a protected complement `W`
  certifies that `W` carries no commutant direction of the true coefficients.

The reconstruction lives on the common carrier `E × R`, so the true coefficient is
`K_e ⊗ I_R`. -/
theorem reconstruction_error {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ < 1)
    {K : Fin 6 → Matrix E E ℂ} {Q : Fin 4 → Matrix R R ℂ} {O : Matrix (Fin 6) (Fin 5) ℝ}
    (hK : ∑ e, K e = ((Real.sqrt 2 : ℝ) : ℂ) • 1) (hQ : ∑ a, Q a = 1)
    (hO : Oᵀ * O = 1) (hcol : ∀ μ, ∑ e, O e μ = 0)
    (hproj : O * Oᵀ = 1 - ((6 : ℝ)⁻¹ : ℝ) • of fun _ _ => (1 : ℝ))
    (X' Y' : Fin 5 → Matrix (E × R) (E × R) ℂ) (εX εY : Fin 5 → ℝ)
    (hX : ∀ μ, ‖matrixL2 (X' μ
      - complementaryPullback (frameCoefficient ϑ K Q) (quadratureX O μ))‖ ≤ εX μ)
    (hY : ∀ μ, ‖matrixL2 (Y' μ
      - complementaryPullback (frameCoefficient ϑ K Q) (quadratureY O μ))‖ ≤ εY μ) :
    hsCoefficientError (reconstructedCoefficient ϑ O X' Y')
        (fun e => K e ⊗ₖ (1 : Matrix R R ℂ)) ≤ panelErrorBudget ϑ εX εY
    ∧ (∀ x : EuclideanSpace ℂ ((E × R) × (E × R)),
        ‖jointCommutatorL2 (starClosedStack (reconstructedCoefficient ϑ O X' Y')) x
          - jointCommutatorL2 (starClosedStack fun e => K e ⊗ₖ (1 : Matrix R R ℂ)) x‖
          ≤ 2 * Real.sqrt 2 * panelErrorBudget ϑ εX εY * ‖x‖)
    ∧ (∀ (W : Submodule ℂ (EuclideanSpace ℂ ((E × R) × (E × R)))) (ŝ : ℝ),
        (∀ x ∈ W, ŝ * ‖x‖
          ≤ ‖jointCommutatorL2 (starClosedStack (reconstructedCoefficient ϑ O X' Y')) x‖) →
        2 * Real.sqrt 2 * panelErrorBudget ϑ εX εY < ŝ →
        ∀ x ∈ W, jointCommutatorL2 (starClosedStack fun e => K e ⊗ₖ (1 : Matrix R R ℂ)) x = 0
          → x = 0) := by
  set κ : ℝ := reconstructionScale ϑ with hκ_def
  have hκ : 0 ≤ κ := reconstructionScale_nonneg ϑ
  obtain ⟨h1, h2⟩ := ten_panel_reconstruction (Q := Q) hϑ hϑ1 hK hQ hcol hproj
  set PX : Fin 5 → Matrix (E × R) (E × R) ℂ :=
    fun μ => complementaryPullback (frameCoefficient ϑ K Q) (quadratureX O μ) with hPX
  set PY : Fin 5 → Matrix (E × R) (E × R) ℂ :=
    fun μ => complementaryPullback (frameCoefficient ϑ K Q) (quadratureY O μ) with hPY
  have hΔ : ∀ μ, reconstructedContrast ϑ X' Y' μ - edgeContrast O K μ ⊗ₖ (1 : Matrix R R ℂ)
      = (κ : ℂ) • ((X' μ - PX μ) + Complex.I • (Y' μ - PY μ)) := by
    intro μ
    rw [reconstructedContrast, h1 μ, ← smul_sub]
    congr 1
    simp only [smul_sub]
    abel
  have hΔnorm : ∀ μ, ‖matrixL2 (reconstructedContrast ϑ X' Y' μ
      - edgeContrast O K μ ⊗ₖ (1 : Matrix R R ℂ))‖ ≤ κ * (εX μ + εY μ) := by
    intro μ
    rw [hΔ, matrixL2_smul, norm_smul, matrixL2_add, matrixL2_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hκ]
    refine mul_le_mul_of_nonneg_left ?_ hκ
    calc ‖matrixL2 (X' μ - PX μ) + Complex.I • matrixL2 (Y' μ - PY μ)‖
        ≤ ‖matrixL2 (X' μ - PX μ)‖ + ‖Complex.I • matrixL2 (Y' μ - PY μ)‖ := norm_add_le _ _
      _ = ‖matrixL2 (X' μ - PX μ)‖ + ‖matrixL2 (Y' μ - PY μ)‖ := by
          rw [norm_smul, Complex.norm_I, one_mul]
      _ ≤ εX μ + εY μ := add_le_add (hX μ) (hY μ)
  have hKe : ∀ e, reconstructedCoefficient ϑ O X' Y' e - K e ⊗ₖ (1 : Matrix R R ℂ)
      = ∑ μ, ((O e μ : ℝ) : ℂ) • (reconstructedContrast ϑ X' Y' μ
          - edgeContrast O K μ ⊗ₖ (1 : Matrix R R ℂ)) := by
    intro e
    rw [reconstructedCoefficient, h2 e, add_kronecker, smul_kronecker, one_kronecker_one,
      sum_kronecker_one]
    simp only [smul_kronecker, smul_sub, Finset.sum_sub_distrib]
    abel
  have hsum : ∑ e, ‖matrixL2 (reconstructedCoefficient ϑ O X' Y' e
      - K e ⊗ₖ (1 : Matrix R R ℂ))‖ ^ 2 ≤ κ ^ 2 * ∑ μ, (εX μ + εY μ) ^ 2 := by
    simp only [hKe, matrixL2_sum, matrixL2_smul]
    rw [helmert_sum_norm_sq O hO (fun μ => matrixL2 (reconstructedContrast ϑ X' Y' μ
      - edgeContrast O K μ ⊗ₖ (1 : Matrix R R ℂ))), Finset.mul_sum]
    refine Finset.sum_le_sum fun μ _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hΔnorm μ) 2
  have hfirst : hsCoefficientError (reconstructedCoefficient ϑ O X' Y')
      (fun e => K e ⊗ₖ (1 : Matrix R R ℂ)) ≤ panelErrorBudget ϑ εX εY := by
    unfold hsCoefficientError panelErrorBudget
    calc Real.sqrt (∑ e, ‖matrixL2 (reconstructedCoefficient ϑ O X' Y' e
          - K e ⊗ₖ (1 : Matrix R R ℂ))‖ ^ 2)
        ≤ Real.sqrt (κ ^ 2 * ∑ μ, (εX μ + εY μ) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = κ * Real.sqrt (∑ μ, (εX μ + εY μ) ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ]
  refine ⟨hfirst, fun x => starClosedStack_commutator_perturbation _ _ _ hfirst x,
    fun W ŝ hŝ hgap => (robust_commutant_stopping_test _ _ _ hfirst W ŝ hŝ hgap).2.1⟩

end TenPanel

end

end RenewalGeometry
