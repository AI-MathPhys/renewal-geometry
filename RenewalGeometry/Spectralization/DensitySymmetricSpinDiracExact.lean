/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.CovariantWilsonCoreConsistencyExact
import RenewalGeometry.Algebra.DetDerivative

/-!
# The density-symmetric spin Dirac identity on a coordinate chart

Paper `predictive_spectral_geometry`, label `lem:supp-density-symmetric`
(`eq:supp-clifford-coeff`, `eq:supp-geometric-dirac`, `eq:supp-density-symmetric`), proved for
the actual geometric data rather than for an abstract algebra in which the contracted
metric-compatibility identity is assumed.

**Data.**  On an open chart `Q ⊆ ℝ^d`: an inverse coframe (frame) `E(y) = (E_a{}^j)` and the
coframe `e(y) = (e^a{}_j)` with `E(y) e(y) = 1` on `Q`, entrywise differentiable at the point
`x`, oriented (`det e(x) > 0`); Clifford matrices `γ_a` (Hermiticity is not needed) with
`γ_a γ_b + γ_b γ_a = 2 δ_{ab}`.

**Derived objects** (all defined from the data, nothing assumed):

* the inverse metric `g^{jk} = Σ_a E_a^j E_a^k` (`ginv`), the metric `g = e eᵀ` (`metric`), its
  derivative `∂_l g = (∂_l e) eᵀ + e (∂_l e)ᵀ` (`metricDeriv`);
* the Levi-Civita Christoffel symbols
  `Γ^k_{jl} = ½ g^{kn}(∂_j g_{nl} + ∂_l g_{nj} - ∂_n g_{jl})` (`christoffel`);
* the Levi-Civita spin connection `ω_{j}{}^a{}_b = e^a_m(∂_j E_b^m + Γ^m_{jl} E_b^l)`
  (`frameConnection`) and its spinor form `Ω_j = ¼ Σ_{a,b} ω_{jab} γ_a γ_b`
  (`spinorConnection`);
* the Clifford coefficients `c^j = E_a{}^j γ_a` (`cliffordCoeff`) and the Riemannian density
  `ρ = det e = √(det g)` (`det_metric`).

**Results.**

* `cliffordCoeff_anticomm` (`eq:supp-clifford-coeff`): `c^j c^k + c^k c^j = 2 g^{jk} I`.
* `metric_mul_christoffel_add` : `∇g = 0` for the Christoffel symbols;
  `frameConnection_antisymm` : `ω_{jab} = -ω_{jba}`;
* `metric_compatibility` (the first display of the paper's proof):
  `∂_j c^k + [Ω_j, c^k] + Γ^k_{jl} c^l = 0`;
* `sum_christoffel_trace` + `hasDerivAt_det_coframe` (Jacobi): `Γ^j_{jl} = ∂_l log ρ`;
* `contracted_identity`: `Σ_j (∂_j c^j + [Ω_j, c^j]) = -Σ_j c^j ∂_j log ρ`;
* `densitySymmetric_identity` (**`eq:supp-density-symmetric`**): for every spinor field `ψ`
  differentiable at `x`,
  `ρ^{1/2}(x) · D_g(ρ^{-1/2} ψ)(x) = -(i/2) Σ_j (c^j ∇_j ψ + ∇_j (c^j ψ))(x)`
  with `D_g = -i Σ_j c^j (∂_j + Ω_j)` (`geometricDirac`) and the right side
  `CovariantWilsonCoreConsistency.densitySymmetricDirac` (the continuum operator of
  `lem:supp-general-core`).
* `densitySymmetric_nonvacuous`: the identity for the non-flat conformal metric
  `g = e^{2 y_0²} δ` in `d = 2` with Pauli matrices.

The identity is pointwise (it is an identity between differential operators); the operators act
on spinor fields `ψ : ℝ^d → ℂ^N` differentiable at the point, as in `eq:supp-geometric-dirac`.
-/

open Matrix Finset Filter Topology
open RenewalGeometry.FrozenWilsonCoreConsistency RenewalGeometry.CovariantWilsonCoreConsistency

namespace RenewalGeometry.DensitySymmetricSpinDirac

variable {d N : ℕ}

/-! ### First-order frame data at a point -/

section jet

variable (E e : Matrix (Fin d) (Fin d) ℝ) (dE de : Fin d → Matrix (Fin d) (Fin d) ℝ)

/-- The inverse metric `g^{jk} = Σ_a E_a^j E_a^k`. -/
def ginv : Matrix (Fin d) (Fin d) ℝ := Eᵀ * E

/-- The metric `g_{jk} = Σ_a e^a_j e^a_k`. -/
def metric : Matrix (Fin d) (Fin d) ℝ := e * eᵀ

/-- `∂_l g = (∂_l e) eᵀ + e (∂_l e)ᵀ`. -/
def metricDeriv (l : Fin d) : Matrix (Fin d) (Fin d) ℝ := de l * eᵀ + e * (de l)ᵀ

/-- The lowered Christoffel symbols `Γ_{n,jl} = ½(∂_j g_{nl} + ∂_l g_{nj} - ∂_n g_{jl})`, as the
matrix `(n, l) ↦ Γ_{n,jl}` for fixed `j`. -/
noncomputable def christoffelLower (j : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  fun n l => (1 / 2 : ℝ) * (metricDeriv e de j n l + metricDeriv e de l n j - metricDeriv e de n j l)

/-- The Levi-Civita Christoffel symbols `Γ^k_{jl} = g^{kn} Γ_{n,jl}`, as the matrix
`(k, l) ↦ Γ^k_{jl}` for fixed `j`. -/
noncomputable def christoffel (j : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  ginv E * christoffelLower e de j

/-- The Levi-Civita frame connection `ω_{jab} = e^a_m (∂_j E_b^m + Γ^m_{jl} E_b^l)`. -/
noncomputable def frameConnection (j : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  eᵀ * (dE j)ᵀ + eᵀ * christoffel E e de j * Eᵀ

variable (γ : Fin d → Matrix (Fin N) (Fin N) ℂ)

/-- `M ↦ Σ_a M_a{}^k γ_a`. -/
noncomputable def cliffordMap (M : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ a, ((M a k : ℝ) : ℂ) • γ a

/-- The Clifford coefficients `c^k = E_a{}^k γ_a` of `eq:supp-clifford-coeff`. -/
noncomputable def cliffordCoeff (k : Fin d) : Matrix (Fin N) (Fin N) ℂ := cliffordMap γ E k

/-- The spinor Levi-Civita connection `Ω_j = ¼ Σ_{a,b} ω_{jab} γ_a γ_b`. -/
noncomputable def spinorConnection (j : Fin d) : Matrix (Fin N) (Fin N) ℂ :=
  (1 / 4 : ℂ) • ∑ a, ∑ b, ((frameConnection E e dE de j a b : ℝ) : ℂ) • (γ a * γ b)

/-- The Clifford relations `γ_a γ_b + γ_b γ_a = 2 δ_{ab}`. -/
def IsClifford : Prop :=
  ∀ a b, γ a * γ b + γ b * γ a = (if a = b then (2 : ℂ) else 0) • (1 : Matrix (Fin N) (Fin N) ℂ)

end jet

section algebra

variable {E e : Matrix (Fin d) (Fin d) ℝ} {dE de : Fin d → Matrix (Fin d) (Fin d) ℝ}

theorem coframe_mul_frame (hEe : E * e = 1) : e * E = 1 := mul_eq_one_comm.mp hEe

theorem transpose_coframe_mul (hEe : E * e = 1) : eᵀ * Eᵀ = 1 := by
  rw [← Matrix.transpose_mul, hEe, Matrix.transpose_one]

theorem ginv_transpose : (ginv E)ᵀ = ginv E := by
  rw [ginv, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem metric_transpose : (metric e)ᵀ = metric e := by
  rw [metric, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem metricDeriv_transpose (l : Fin d) : (metricDeriv e de l)ᵀ = metricDeriv e de l := by
  rw [metricDeriv, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose, add_comm]

theorem metricDeriv_symm (l n m : Fin d) : metricDeriv e de l n m = metricDeriv e de l m n := by
  have := congrFun (congrFun (metricDeriv_transpose (e := e) (de := de) l) m) n
  simpa [Matrix.transpose_apply] using this

/-- `g g⁻¹ = 1`. -/
theorem metric_mul_ginv (hEe : E * e = 1) : metric e * ginv E = 1 := by
  rw [metric, ginv, Matrix.mul_assoc, ← Matrix.mul_assoc eᵀ, transpose_coframe_mul hEe,
    Matrix.one_mul, coframe_mul_frame hEe]

theorem ginv_mul_metric (hEe : E * e = 1) : ginv E * metric e = 1 :=
  mul_eq_one_comm.mp (metric_mul_ginv hEe)

/-- `g Γ_j = Γ♭_j`. -/
theorem metric_mul_christoffel (hEe : E * e = 1) (j : Fin d) :
    metric e * christoffel E e de j = christoffelLower e de j := by
  rw [christoffel, ← Matrix.mul_assoc, metric_mul_ginv hEe, Matrix.one_mul]

/-- **Metric compatibility of the Levi-Civita symbols**, `∇g = 0`:
`g Γ_j + Γ_jᵀ g = ∂_j g`. -/
theorem metric_mul_christoffel_add (hEe : E * e = 1) (j : Fin d) :
    metric e * christoffel E e de j + (christoffel E e de j)ᵀ * metric e =
      metricDeriv e de j := by
  have h2 : (christoffel E e de j)ᵀ * metric e = (christoffelLower e de j)ᵀ := by
    rw [← metric_mul_christoffel (de := de) hEe j, Matrix.transpose_mul, metric_transpose]
  rw [metric_mul_christoffel hEe, h2]
  ext n l
  simp only [Matrix.add_apply, Matrix.transpose_apply, christoffelLower]
  rw [metricDeriv_symm (e := e) (de := de) l n j, metricDeriv_symm (e := e) (de := de) n j l,
    metricDeriv_symm (e := e) (de := de) j l n]
  ring

/-- **Antisymmetry of the Levi-Civita frame connection**: `ω_j + ω_jᵀ = 0`, from `∇g = 0`
and the differentiated frame relation `∂E e + E ∂e = 0`. -/
theorem frameConnection_antisymm (hEe : E * e = 1) (hd : ∀ l, dE l * e + E * de l = 0)
    (j : Fin d) : frameConnection E e dE de j + (frameConnection E e dE de j)ᵀ = 0 := by
  set Γ := christoffel E e de j
  have hEe' : ∀ Y : Matrix (Fin d) (Fin d) ℝ, E * (e * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hEe, Matrix.one_mul]
  have heE' : ∀ Y : Matrix (Fin d) (Fin d) ℝ, eᵀ * (Eᵀ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, transpose_coframe_mul hEe, Matrix.one_mul]
  have hdE : dE j * e = -(E * de j) := eq_neg_of_add_eq_zero_left (hd j)
  have hdEt : eᵀ * (dE j)ᵀ = -((de j)ᵀ * Eᵀ) := by
    rw [← Matrix.transpose_mul, hdE, Matrix.transpose_neg, Matrix.transpose_mul]
  have hcompat := metric_mul_christoffel_add (de := de) hEe j
  -- everything as `E (·) Eᵀ`
  have hA : E * de j + (de j)ᵀ * Eᵀ = E * metricDeriv e de j * Eᵀ := by
    simp only [metricDeriv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hEe',
      transpose_coframe_mul hEe, Matrix.mul_one]
  have hB : eᵀ * Γ * Eᵀ + E * Γᵀ * e =
      E * (metric e * Γ + Γᵀ * metric e) * Eᵀ := by
    simp only [metric, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hEe',
      transpose_coframe_mul hEe, Matrix.mul_one]
  calc frameConnection E e dE de j + (frameConnection E e dE de j)ᵀ
      = (eᵀ * Γ * Eᵀ + E * Γᵀ * e) - (E * de j + (de j)ᵀ * Eᵀ) := by
        simp only [frameConnection, Matrix.transpose_add, Matrix.transpose_mul,
          Matrix.transpose_transpose, Γ]
        rw [hdEt, hdE]
        simp only [Matrix.mul_assoc]
        abel
    _ = 0 := by rw [hA, hB, hcompat, sub_self]

/-- `ω_j E = -(∂_j E + E Γ_jᵀ)`. -/
theorem frameConnection_mul_frame (hEe : E * e = 1) (hd : ∀ l, dE l * e + E * de l = 0)
    (j : Fin d) : frameConnection E e dE de j * E = -(dE j + E * (christoffel E e de j)ᵀ) := by
  have hanti := frameConnection_antisymm hEe hd j
  have hω : frameConnection E e dE de j = -(frameConnection E e dE de j)ᵀ :=
    eq_neg_of_add_eq_zero_left hanti
  rw [hω]
  simp only [frameConnection, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.neg_mul, Matrix.add_mul, Matrix.mul_assoc,
    coframe_mul_frame hEe, Matrix.mul_one]

/-- **Trace of the Christoffel symbols**: `Σ_j Γ^j_{jl} = tr(E ∂_l e)`. -/
theorem sum_christoffel_trace (hEe : E * e = 1) (l : Fin d) :
    ∑ j, christoffel E e de j j l = Matrix.trace (E * de l) := by
  have hg : ∀ j n, ginv E j n = ginv E n j := fun j n => by
    have := congrFun (congrFun (ginv_transpose (E := E)) n) j
    simpa [Matrix.transpose_apply] using this
  have hswap : ∑ j, ∑ n, ginv E j n * metricDeriv e de n j l =
      ∑ j, ∑ n, ginv E j n * metricDeriv e de j n l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => ?_
    rw [hg]
  have htr : ∑ j, ∑ n, ginv E j n * metricDeriv e de l n j =
      Matrix.trace (ginv E * metricDeriv e de l) := by
    simp [Matrix.trace, Matrix.mul_apply]
  have htr2 : Matrix.trace (ginv E * metricDeriv e de l) = 2 * Matrix.trace (E * de l) := by
    have h1 : Matrix.trace (Eᵀ * E * (de l * eᵀ)) = Matrix.trace (E * de l) := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        transpose_coframe_mul hEe, Matrix.one_mul]
    have h2 : Matrix.trace (Eᵀ * E * (e * (de l)ᵀ)) = Matrix.trace (E * de l) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEe, Matrix.one_mul, ← Matrix.transpose_mul,
        Matrix.trace_transpose, Matrix.trace_mul_comm]
    rw [ginv, metricDeriv, Matrix.mul_add, Matrix.trace_add, h1, h2]
    ring
  have hexp : ∑ j, christoffel E e de j j l = (1 / 2 : ℝ) *
      (∑ j, ∑ n, ginv E j n * metricDeriv e de j n l +
        ∑ j, ∑ n, ginv E j n * metricDeriv e de l n j -
        ∑ j, ∑ n, ginv E j n * metricDeriv e de n j l) := by
    simp only [christoffel, christoffelLower, Matrix.mul_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hexp, hswap, htr, htr2]
  ring

end algebra

/-! ### Clifford algebra -/

section clifford

variable {γ : Fin d → Matrix (Fin N) (Fin N) ℂ}

/-- `[γ_a γ_b, γ_c] = 2 δ_{bc} γ_a - 2 δ_{ac} γ_b`. -/
theorem commutator_pair (hγ : IsClifford γ) (a b c : Fin d) :
    γ a * γ b * γ c - γ c * (γ a * γ b) =
      (if b = c then (2 : ℂ) else 0) • γ a - (if a = c then (2 : ℂ) else 0) • γ b := by
  have h1 : γ b * γ c = (if b = c then (2 : ℂ) else 0) • 1 - γ c * γ b :=
    eq_sub_of_add_eq (hγ b c)
  have h2 : γ c * γ a = (if a = c then (2 : ℂ) else 0) • 1 - γ a * γ c := by
    have := hγ a c
    rw [add_comm] at this
    exact eq_sub_of_add_eq this
  calc γ a * γ b * γ c - γ c * (γ a * γ b) = γ a * (γ b * γ c) - (γ c * γ a) * γ b := by
        simp only [Matrix.mul_assoc]
    _ = γ a * ((if b = c then (2 : ℂ) else 0) • 1 - γ c * γ b) -
          ((if a = c then (2 : ℂ) else 0) • 1 - γ a * γ c) * γ b := by rw [h1, h2]
    _ = _ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
        abel

variable (E e : Matrix (Fin d) (Fin d) ℝ) (dE de : Fin d → Matrix (Fin d) (Fin d) ℝ)

/-- `cliffordMap` is additive. -/
theorem cliffordMap_add (M M' : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) :
    cliffordMap γ (M + M') k = cliffordMap γ M k + cliffordMap γ M' k := by
  simp [cliffordMap, add_smul, Finset.sum_add_distrib]

theorem cliffordMap_neg (M : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) :
    cliffordMap γ (-M) k = -cliffordMap γ M k := by
  simp [cliffordMap, neg_smul, Finset.sum_neg_distrib]

theorem cliffordMap_zero (k : Fin d) : cliffordMap γ (0 : Matrix (Fin d) (Fin d) ℝ) k = 0 := by
  simp [cliffordMap]

/-- **`eq:supp-clifford-coeff`**: `c^j c^k + c^k c^j = 2 g^{jk} I`. -/
theorem cliffordCoeff_anticomm (hγ : IsClifford γ) (j k : Fin d) :
    cliffordCoeff E γ j * cliffordCoeff E γ k + cliffordCoeff E γ k * cliffordCoeff E γ j =
      ((2 * ginv E j k : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have hprod : ∀ p q : Fin d, cliffordCoeff E γ p * cliffordCoeff E γ q =
      ∑ a, ∑ b, (((E a p : ℝ) : ℂ) * ((E b q : ℝ) : ℂ)) • (γ a * γ b) := by
    intro p q
    simp only [cliffordCoeff, cliffordMap, Finset.sum_mul_sum, smul_mul_smul_comm]
  rw [hprod j k, hprod k j,
    Finset.sum_comm (f := fun a b => (((E a k : ℝ) : ℂ) * ((E b j : ℝ) : ℂ)) • (γ a * γ b)),
    ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  have : ∀ a b : Fin d, (((E a j : ℝ) : ℂ) * ((E b k : ℝ) : ℂ)) • (γ a * γ b) +
      (((E b k : ℝ) : ℂ) * ((E a j : ℝ) : ℂ)) • (γ b * γ a) =
      (((E a j : ℝ) : ℂ) * ((E b k : ℝ) : ℂ)) • ((if a = b then (2 : ℂ) else 0) • 1) := by
    intro a b
    rw [← hγ a b, smul_add, mul_comm ((E b k : ℝ) : ℂ)]
  simp_rw [this, smul_smul, ← Finset.sum_smul]
  congr 1
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ginv,
    Matrix.mul_apply, Matrix.transpose_apply]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- `[Ω_j, γ_c] = Σ_a ω_{jac} γ_a` (uses the antisymmetry of `ω_j`). -/
theorem spinorConnection_commutator (hγ : IsClifford γ) (hEe : E * e = 1)
    (hd : ∀ l, dE l * e + E * de l = 0) (j c : Fin d) :
    spinorConnection E e dE de γ j * γ c - γ c * spinorConnection E e dE de γ j =
      ∑ a, ((frameConnection E e dE de j a c : ℝ) : ℂ) • γ a := by
  set ω := frameConnection E e dE de j with hωdef
  have hanti : ∀ a b, ω a b = -ω b a := by
    intro a b
    have := congrFun (congrFun (frameConnection_antisymm hEe hd j) a) b
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply] at this
    rw [← hωdef] at this
    linarith
  have hexp : spinorConnection E e dE de γ j * γ c - γ c * spinorConnection E e dE de γ j =
      (1 / 4 : ℂ) • ∑ a, ∑ b, ((ω a b : ℝ) : ℂ) • (γ a * γ b * γ c - γ c * (γ a * γ b)) := by
    simp only [spinorConnection, ← hωdef, Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul,
      Finset.mul_sum, smul_sub, Finset.sum_sub_distrib]
  rw [hexp]
  simp_rw [commutator_pair hγ, smul_sub, smul_smul, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_comm (f := fun a b => if a = c then (((ω a b : ℝ) : ℂ) * 2) • γ b else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hanti c a, ← sub_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- **Metric compatibility of Clifford multiplication** (first display of the proof of
`lem:supp-density-symmetric`): `∂_j c^k + [Ω_j, c^k] + Γ^k_{jl} c^l = 0`, for the Levi-Civita
spin connection built from the frame. -/
theorem metric_compatibility (hγ : IsClifford γ) (hEe : E * e = 1)
    (hd : ∀ l, dE l * e + E * de l = 0) (j k : Fin d) :
    cliffordMap γ (dE j) k +
      (spinorConnection E e dE de γ j * cliffordCoeff E γ k -
        cliffordCoeff E γ k * spinorConnection E e dE de γ j) +
      ∑ l, ((christoffel E e de j k l : ℝ) : ℂ) • cliffordCoeff E γ l = 0 := by
  have hcomm : spinorConnection E e dE de γ j * cliffordCoeff E γ k -
      cliffordCoeff E γ k * spinorConnection E e dE de γ j =
      cliffordMap γ (frameConnection E e dE de j * E) k := by
    simp only [cliffordCoeff, cliffordMap, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul, ← Finset.sum_sub_distrib, ← smul_sub]
    simp_rw [spinorConnection_commutator E e dE de hγ hEe hd j, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_smul, Matrix.mul_apply]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hΓ : ∑ l, ((christoffel E e de j k l : ℝ) : ℂ) • cliffordCoeff E γ l =
      cliffordMap γ (E * (christoffel E e de j)ᵀ) k := by
    simp only [cliffordCoeff, cliffordMap, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_smul, Matrix.mul_apply]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.transpose_apply]
    ring
  rw [hcomm, hΓ, ← cliffordMap_add, ← cliffordMap_add, frameConnection_mul_frame hEe hd j]
  rw [show dE j + -(dE j + E * (christoffel E e de j)ᵀ) + E * (christoffel E e de j)ᵀ = 0 by abel]
  exact cliffordMap_zero k

/-- **The contracted identity** of the proof of `lem:supp-density-symmetric`:
`Σ_j (∂_j c^j + [Ω_j, c^j]) = -Σ_l tr(E ∂_l e) c^l`, where `tr(E ∂_l e) = Γ^j_{jl}`
(`sum_christoffel_trace`) is `∂_l log ρ` (`hasDerivAt_det_coframe`). -/
theorem contracted_identity (hγ : IsClifford γ) (hEe : E * e = 1)
    (hd : ∀ l, dE l * e + E * de l = 0) :
    ∑ j, (cliffordMap γ (dE j) j +
      (spinorConnection E e dE de γ j * cliffordCoeff E γ j -
        cliffordCoeff E γ j * spinorConnection E e dE de γ j)) =
      -∑ l, ((Matrix.trace (E * de l) : ℝ) : ℂ) • cliffordCoeff E γ l := by
  have h : ∀ j, cliffordMap γ (dE j) j +
      (spinorConnection E e dE de γ j * cliffordCoeff E γ j -
        cliffordCoeff E γ j * spinorConnection E e dE de γ j) =
      -∑ l, ((christoffel E e de j j l : ℝ) : ℂ) • cliffordCoeff E γ l := fun j =>
    eq_neg_of_add_eq_zero_left (metric_compatibility E e dE de hγ hEe hd j j)
  simp_rw [h, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul, ← sum_christoffel_trace (de := de) hEe l]
  push_cast
  rfl

end clifford

/-! ### The pointwise density-symmetric identity -/

section pointwise

variable {γ : Fin d → Matrix (Fin N) (Fin N) ℂ}
variable (E e : Matrix (Fin d) (Fin d) ℝ) (dE de : Fin d → Matrix (Fin d) (Fin d) ℝ)

/-- The pointwise algebra of `eq:supp-density-symmetric`: with `σ = ρ^{1/2}(x)`, `∂_j(σ⁻¹) = s_j`
where `σ s_j = -½ ∂_j log ρ = -½ tr(E ∂_j e)`, the conjugated Dirac operator at `x` equals the
density-symmetric operator at `x`. -/
theorem densitySymmetric_pointwise (hγ : IsClifford γ) (hEe : E * e = 1)
    (hd : ∀ l, dE l * e + E * de l = 0) (σ : ℂ) (hσ : σ ≠ 0) (s : Fin d → ℂ)
    (hs : ∀ j, σ * s j = -(1 / 2 : ℂ) * ((Matrix.trace (E * de j) : ℝ) : ℂ))
    (ψx : Fin N → ℂ) (dψ : Fin d → Fin N → ℂ) :
    σ • ((-Complex.I) • ∑ j, cliffordCoeff E γ j *ᵥ
        ((σ⁻¹ • dψ j + s j • ψx) + spinorConnection E e dE de γ j *ᵥ (σ⁻¹ • ψx))) =
      (-(Complex.I / 2)) • ∑ j, (cliffordCoeff E γ j *ᵥ (dψ j + spinorConnection E e dE de γ j *ᵥ ψx)
        + ((cliffordMap γ (dE j) j *ᵥ ψx + cliffordCoeff E γ j *ᵥ dψ j) +
          spinorConnection E e dE de γ j *ᵥ (cliffordCoeff E γ j *ᵥ ψx))) := by
  have key := congrArg (fun M => M *ᵥ ψx) (contracted_identity E e dE de hγ hEe hd)
  simp only [Matrix.sum_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.neg_mulVec,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec] at key
  set c := cliffordCoeff E γ
  set Ω := spinorConnection E e dE de γ
  set τ : Fin d → ℂ := fun j => ((Matrix.trace (E * de j) : ℝ) : ℂ) with hτ
  have hτj : ∀ j, ((Matrix.trace (E * de j) : ℝ) : ℂ) = τ j := fun j => rfl
  simp only [hτj] at key hs
  -- key : Σ (dc ψ + (Ω (c ψ) - c (Ω ψ))) = -Σ τ • c ψ
  have hL : ∀ j, σ • ((-Complex.I) • (c j *ᵥ ((σ⁻¹ • dψ j + s j • ψx) + Ω j *ᵥ (σ⁻¹ • ψx)))) =
      (-Complex.I) • (c j *ᵥ dψ j) + (Complex.I / 2) • (τ j • (c j *ᵥ ψx)) +
        (-Complex.I) • (c j *ᵥ (Ω j *ᵥ ψx)) := by
    intro j
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp only [smul_add, smul_smul]
    have e1 : σ * (-Complex.I * σ⁻¹) = -Complex.I := by field_simp
    have e2 : σ * (-Complex.I * s j) = Complex.I / 2 * τ j := by
      rw [mul_left_comm, hs j]; ring
    rw [e1, e2]
  rw [Finset.smul_sum, Finset.smul_sum]
  simp_rw [hL]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, smul_add, Matrix.mulVec_add]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at key
  rw [eq_sub_of_add_eq key]
  module

end pointwise

/-! ### Fields on a chart -/

section analytic

variable (E e : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (γ : Fin d → Matrix (Fin N) (Fin N) ℂ)

/-- The entrywise partial derivative `∂_l M(y)`. -/
noncomputable def partialMat (M : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (l : Fin d)
    (y : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => lineDeriv ℝ (fun z => M z a b) y (dir l)

/-- The Clifford coefficient fields `c^k(y) = E_a{}^k(y) γ_a`. -/
noncomputable def cliffordField : Coefficients d N := fun k y => cliffordCoeff (E y) γ k

/-- The Levi-Civita spinor connection field `Ω_j(y)` of the frame `E` (coframe `e`). -/
noncomputable def spinConnectionField : Coefficients d N := fun j y =>
  spinorConnection (E y) (e y) (fun l => partialMat E l y) (fun l => partialMat e l y) γ j

/-- The Riemannian density `ρ = det e`. -/
noncomputable def density (y : Fin d → ℝ) : ℝ := (e y).det

/-- `ρ^{1/2}`. -/
noncomputable def halfDensity (y : Fin d → ℝ) : ℝ := Real.sqrt (density e y)

/-- **The geometric Dirac operator `eq:supp-geometric-dirac`**,
`D_g ψ = -i Σ_j c^j (∂_j + Ω_j) ψ`, with the Levi-Civita spin connection of the frame. -/
noncomputable def geometricDirac (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (y : Fin d → ℝ) : Fin N → ℂ :=
  (-Complex.I) • ∑ j, cliffordField E γ j y *ᵥ covDeriv (spinConnectionField E e γ) j ψ y

/-- `det g = (det e)²`: `ρ = det e = √(det g)` for an oriented coframe. -/
theorem det_metric (y : Fin d → ℝ) : (metric (e y)).det = (density e y) ^ 2 := by
  rw [metric, Matrix.det_mul, Matrix.det_transpose, density, sq]

theorem density_eq_sqrt_det_metric (y : Fin d → ℝ) (hy : 0 ≤ (e y).det) :
    density e y = Real.sqrt (metric (e y)).det := by
  rw [det_metric, Real.sqrt_sq (by simpa [density] using hy)]

variable {E e}

theorem hasDerivAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin d → ℝ) → F} {x : Fin d → ℝ} (hf : DifferentiableAt ℝ f x) (v : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (lineDeriv ℝ f x v) 0 :=
  hf.lineDifferentiableAt.hasLineDerivAt

theorem eventually_line_mem {Q : Set (Fin d → ℝ)} (hQ : IsOpen Q) {x : Fin d → ℝ} (hx : x ∈ Q)
    (v : Fin d → ℝ) : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ Q := by
  have hc : Continuous (fun t : ℝ => x + t • v) := by fun_prop
  have h0 : x + (0 : ℝ) • v = x := by simp
  have := hc.continuousAt (x := 0)
  rw [ContinuousAt, h0] at this
  exact this (hQ.mem_nhds hx)

/-- **The differentiated frame relation** `∂_l E e + E ∂_l e = 0` at `x`, from `E e = 1` on the
open chart. -/
theorem partialMat_frame_coframe {Q : Set (Fin d → ℝ)} (hQ : IsOpen Q) {x : Fin d → ℝ}
    (hx : x ∈ Q) (hEe : ∀ y ∈ Q, E y * e y = 1)
    (hE : ∀ a b, DifferentiableAt ℝ (fun y => E y a b) x)
    (he : ∀ a b, DifferentiableAt ℝ (fun y => e y a b) x) (l : Fin d) :
    partialMat E l x * e x + E x * partialMat e l x = 0 := by
  ext a c
  have hφ : HasDerivAt (fun t : ℝ => ∑ b, E (x + t • dir l) a b * e (x + t • dir l) b c)
      (∑ b, (partialMat E l x a b * e x b c + E x a b * partialMat e l x b c)) 0 := by
    apply HasDerivAt.fun_sum
    intro b _
    have h1 := hasDerivAt_line (hE a b) (dir l)
    have h2 := hasDerivAt_line (he b c) (dir l)
    have := h1.mul h2
    simp only [zero_smul, add_zero] at this
    convert this using 1
    all_goals rfl
  have hconst : HasDerivAt (fun t : ℝ => ∑ b, E (x + t • dir l) a b * e (x + t • dir l) b c)
      0 0 := by
    apply (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin d) (Fin d) ℝ) a c)).congr_of_eventuallyEq
    filter_upwards [eventually_line_mem hQ hx (dir l)] with t ht
    rw [← Matrix.mul_apply, hEe _ ht]
  have := hφ.unique hconst
  simpa [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib] using this

/-- **Jacobi's formula on the chart**: `∂_l (det e) = det e · tr(E ∂_l e)`, i.e.
`∂_l log ρ = tr(E ∂_l e) = Γ^j_{jl}` (`sum_christoffel_trace`). -/
theorem hasDerivAt_det_coframe {Q : Set (Fin d → ℝ)} (_hQ : IsOpen Q) {x : Fin d → ℝ}
    (hx : x ∈ Q) (hEe : ∀ y ∈ Q, E y * e y = 1)
    (he : ∀ a b, DifferentiableAt ℝ (fun y => e y a b) x) (l : Fin d) :
    HasDerivAt (fun t : ℝ => density e (x + t • dir l))
      ((e x).det * Matrix.trace (E x * partialMat e l x)) 0 := by
  have hU : ∀ i j, HasDerivAt (fun s : ℝ => e (x + s • dir l) i j) (partialMat e l x i j) 0 :=
    fun i j => hasDerivAt_line (he i j) (dir l)
  have h := RenewalGeometry.hasDerivAt_det hU
  simp only [zero_smul, add_zero] at h
  have hadj : Matrix.adjugate (e x) = (e x).det • E x := by
    have hx' := hEe x hx
    calc Matrix.adjugate (e x) = Matrix.adjugate (e x) * (e x * E x) := by
          rw [coframe_mul_frame hx', Matrix.mul_one]
      _ = (e x).det • E x := by
          rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at h
  exact h

/-- The derivative of `ρ^{-1/2}` along `e_l`: `σ ∂_l(σ⁻¹) = -½ tr(E ∂_l e)`. -/
theorem hasDerivAt_inv_halfDensity {Q : Set (Fin d → ℝ)} (hQ : IsOpen Q) {x : Fin d → ℝ}
    (hx : x ∈ Q) (hEe : ∀ y ∈ Q, E y * e y = 1)
    (he : ∀ a b, DifferentiableAt ℝ (fun y => e y a b) x) (hdet : 0 < (e x).det) (l : Fin d) :
    HasDerivAt (fun t : ℝ => (halfDensity e (x + t • dir l))⁻¹)
      (-(1 / 2) * Matrix.trace (E x * partialMat e l x) * (halfDensity e x)⁻¹) 0 := by
  have hρ := hasDerivAt_det_coframe hQ hx hEe he l
  have hρx : density e (x + (0 : ℝ) • dir l) = (e x).det := by simp [density]
  have hρ0 : density e (x + (0 : ℝ) • dir l) ≠ 0 := by rw [hρx]; exact hdet.ne'
  have hsq := hρ.sqrt hρ0
  have hσ0 : Real.sqrt (density e (x + (0 : ℝ) • dir l)) ≠ 0 := by
    rw [hρx]; exact (Real.sqrt_pos.mpr hdet).ne'
  have hinv : HasDerivAt (fun t : ℝ => (Real.sqrt (density e (x + t • dir l)))⁻¹) _ 0 :=
    hsq.inv hσ0
  unfold halfDensity
  refine hinv.congr_deriv ?_
  rw [hρx]
  have hs : Real.sqrt (e x).det ≠ 0 := (Real.sqrt_pos.mpr hdet).ne'
  have hss : Real.sqrt (e x).det ^ 2 = (e x).det := Real.sq_sqrt hdet.le
  simp only [density]
  field_simp
  rw [hss]
  ring

/-- **`lem:supp-density-symmetric`, `eq:supp-density-symmetric`.**  On an open chart `Q`, for a
frame `E` with coframe `e` (`E e = 1` on `Q`), entrywise differentiable at `x ∈ Q` and oriented
(`det e(x) > 0`), Clifford matrices `γ_a`, the Levi-Civita spin connection `Ω_j` and the density
`ρ = det e = √(det g)`, every spinor field `ψ` differentiable at `x` satisfies
`ρ^{1/2} D_g (ρ^{-1/2} ψ) = -(i/2) Σ_j (c^j ∇_j ψ + ∇_j (c^j ψ))` at `x`, with
`D_g = -i Σ_j c^j(∂_j + Ω_j)` (`geometricDirac`); the right side is the continuum operator
`densitySymmetricDirac` of `lem:supp-general-core`. -/
theorem densitySymmetric_identity {Q : Set (Fin d → ℝ)} (hQ : IsOpen Q) {x : Fin d → ℝ}
    (hx : x ∈ Q) (hEe : ∀ y ∈ Q, E y * e y = 1)
    (hE : ∀ a b, DifferentiableAt ℝ (fun y => E y a b) x)
    (he : ∀ a b, DifferentiableAt ℝ (fun y => e y a b) x) (hdet : 0 < (e x).det)
    (hγ : IsClifford γ) (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (hψ : DifferentiableAt ℝ ψ x) :
    ((halfDensity e x : ℝ) : ℂ) •
        geometricDirac E e γ (fun y => (((halfDensity e y)⁻¹ : ℝ) : ℂ) • ψ y) x =
      densitySymmetricDirac (cliffordField E γ) (spinConnectionField E e γ) ψ x := by
  set σ : ℝ := halfDensity e x with hσdef
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hdet
  have hd := partialMat_frame_coframe hQ hx hEe hE he
  -- line derivative of `σ⁻¹ ψ`
  have hF1 : ∀ j, lineDeriv ℝ (fun y => (((halfDensity e y)⁻¹ : ℝ) : ℂ) • ψ y) x (dir j) =
      ((σ⁻¹ : ℝ) : ℂ) • lineDeriv ℝ ψ x (dir j) +
        ((-(1 / 2) * Matrix.trace (E x * partialMat e j x) * σ⁻¹ : ℝ) : ℂ) • ψ x := by
    intro j
    have hc := (hasDerivAt_inv_halfDensity hQ hx hEe he hdet j).ofReal_comp
    have hf := hasDerivAt_line hψ (dir j)
    have := hc.smul hf
    simp only [zero_smul, add_zero] at this
    exact HasLineDerivAt.lineDeriv this
  -- line derivative of `c^j ψ`
  have hF2 : ∀ j, lineDeriv ℝ (fun z => cliffordField E γ j z *ᵥ ψ z) x (dir j) =
      cliffordMap γ (partialMat E j x) j *ᵥ ψ x + cliffordField E γ j x *ᵥ lineDeriv ℝ ψ x (dir j)
      := by
    intro j
    have hexp : (fun z => cliffordField E γ j z *ᵥ ψ z) =
        fun z => ∑ a, ((E z a j : ℝ) : ℂ) • (γ a *ᵥ ψ z) := by
      funext z
      simp only [cliffordField, cliffordCoeff, cliffordMap, Matrix.sum_mulVec, Matrix.smul_mulVec]
    rw [hexp]
    have hder : HasDerivAt (fun t : ℝ => ∑ a, ((E (x + t • dir j) a j : ℝ) : ℂ) •
        (γ a *ᵥ ψ (x + t • dir j)))
        (∑ a, (((E x a j : ℝ) : ℂ) • (γ a *ᵥ lineDeriv ℝ ψ x (dir j)) +
          ((partialMat E j x a j : ℝ) : ℂ) • (γ a *ᵥ ψ x))) 0 := by
      apply HasDerivAt.fun_sum
      intro a _
      have hc := (hasDerivAt_line (hE a j) (dir j)).ofReal_comp
      set L : (Fin N → ℂ) →L[ℝ] (Fin N → ℂ) :=
        LinearMap.toContinuousLinearMap ((Matrix.mulVecLin (γ a)).restrictScalars ℝ)
      have hf : HasDerivAt (fun t : ℝ => γ a *ᵥ ψ (x + t • dir j))
          (γ a *ᵥ lineDeriv ℝ ψ x (dir j)) 0 :=
        L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line hψ (dir j))
      have := hc.smul hf
      simp only [zero_smul, add_zero] at this
      exact this
    have hl : HasLineDerivAt ℝ (fun z => ∑ a, ((E z a j : ℝ) : ℂ) • (γ a *ᵥ ψ z))
        (∑ a, (((E x a j : ℝ) : ℂ) • (γ a *ᵥ lineDeriv ℝ ψ x (dir j)) +
          ((partialMat E j x a j : ℝ) : ℂ) • (γ a *ᵥ ψ x))) x (dir j) := hder
    rw [hl.lineDeriv]
    simp only [cliffordField, cliffordCoeff, cliffordMap, Matrix.sum_mulVec, Matrix.smul_mulVec,
      Finset.sum_add_distrib, partialMat]
    abel
  unfold geometricDirac densitySymmetricDirac covDeriv
  simp_rw [hF1, hF2]
  have hσc : ((σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσpos.ne'
  have hpt := densitySymmetric_pointwise (γ := γ) (E x) (e x) (fun l => partialMat E l x)
    (fun l => partialMat e l x) hγ (hEe x hx) hd ((σ : ℝ) : ℂ)
    hσc
    (fun j => ((-(1 / 2) * Matrix.trace (E x * partialMat e j x) * σ⁻¹ : ℝ) : ℂ))
    (fun j => by
      push_cast
      field_simp)
    (ψ x) (fun j => lineDeriv ℝ ψ x (dir j))
  convert hpt using 3
  · simp only [cliffordField, spinConnectionField, Complex.ofReal_inv, ← hσdef]
  · simp only [cliffordField, spinConnectionField]

end analytic

/-! ### Non-vacuity: a conformal metric in two dimensions -/

section nonvacuity

/-- The two-dimensional Pauli Clifford generators `γ_1 = σ₁`, `γ_2 = σ₂`. -/
def pauli : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0]]

theorem pauli_isClifford : IsClifford pauli := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauli] <;> norm_num)

/-- The conformal coframe `e(y) = e^{y_0²} I` (metric `g = e^{2 y_0²} δ`, Gaussian curvature
`-2 e^{-2 y_0²} ≠ 0`). -/
noncomputable def confCoframe (y : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Real.exp (y 0 ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Its frame `E(y) = e^{-y_0²} I`. -/
noncomputable def confFrame (y : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Real.exp (-(y 0 ^ 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

theorem confFrame_mul_confCoframe (y : Fin 2 → ℝ) : confFrame y * confCoframe y = 1 := by
  rw [confFrame, confCoframe, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

/-- **Non-vacuity of `densitySymmetric_identity`**: the hypotheses hold for the non-constant
conformal coframe `e = e^{y_0²} I` on `ℝ²` with the Pauli generators, at every point, for every
spinor field differentiable at the point. -/
theorem densitySymmetric_nonvacuous (x : Fin 2 → ℝ) (ψ : (Fin 2 → ℝ) → (Fin 2 → ℂ))
    (hψ : DifferentiableAt ℝ ψ x) :
    ((halfDensity confCoframe x : ℝ) : ℂ) • geometricDirac confFrame confCoframe pauli
        (fun y => (((halfDensity confCoframe y)⁻¹ : ℝ) : ℂ) • ψ y) x =
      densitySymmetricDirac (cliffordField confFrame pauli)
        (spinConnectionField confFrame confCoframe pauli) ψ x := by
  refine densitySymmetric_identity pauli isOpen_univ (Set.mem_univ x)
    (fun y _ => confFrame_mul_confCoframe y) (fun a b => ?_) (fun a b => ?_) ?_ pauli_isClifford
    ψ hψ
  · simp only [confFrame, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  · simp only [confCoframe, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  · rw [confCoframe, Matrix.det_smul, Matrix.det_one, mul_one]
    positivity

end nonvacuity

end RenewalGeometry.DensitySymmetricSpinDirac
