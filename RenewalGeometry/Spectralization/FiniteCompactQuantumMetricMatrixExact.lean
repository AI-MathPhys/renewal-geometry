/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.FiniteCompactQuantumMetricExact

/-!
# Finite compact quantum metric-space structure: the matrix instantiation

Paper `predictive_spectral_geometry`, label `prop:finite-CQMS`.

`FiniteCompactQuantumMetricExact` proves the finite-dimensional Lip-norm theory
for an abstract package `LipData V` (a continuous seminorm `L` on a
finite-dimensional real normed space `V`, a unit `u` in its kernel, and a
normalized functional `τ`).  This file instantiates that package with the
concrete spectral data of the proposition:

* the algebra is a `*`-subalgebra `S` of the matrices `Matrix H H ℂ` on a
  finite Hilbert space `H` (every finite-dimensional C*-algebra is one; the
  representation is the inclusion `S.subtype`, which is faithful, so the paper's
  `‖a‖` is the Euclidean operator norm of the matrix);
* the real order-unit space `A_sa` is the self-adjoint part `selfAdjointPart S`,
  a real submodule of `Matrix H H ℂ` carrying the operator norm;
* the seminorm is `lipSA D S a = ‖[D, a]‖` (equal to `lipD D S.subtype`), the
  unit is `1`, and `τ` is the normalized trace.

The kernel hypothesis `Ker ∂ = ℂ 1` of the paper is transported to the
abstract `LipData.KernelConstants` predicate on the self-adjoint part
(`kernelConstants`), and the abstract theorems are restated with the concrete
seminorm: the Poincaré–Lip inequality, finiteness and bi-Lipschitz comparison
of the Monge–Kantorovich distance `mk_{L_D}` with the dual norm
(`finite_cqms_matrix`), the topological clause (`finite_cqms_matrix_tendsto`),
the Leibniz and star identities (`finite_cqms_matrix_leibniz_star`), and the
converse: a non-scalar self-adjoint element of the kernel of `∂`
(`finite_cqms_matrix_converse`).
-/

open Matrix Filter Topology
open scoped Matrix.Norms.L2Operator InnerProductSpace ComplexOrder

namespace RenewalGeometry
namespace FiniteCompactQuantumMetric

variable {H : Type*} [Fintype H] [DecidableEq H]

/-! ## The self-adjoint part of a matrix `*`-subalgebra -/

/-- `prop:finite-CQMS`: the self-adjoint part `A_sa` of a `*`-subalgebra `S` of
matrices, as a real submodule of `Matrix H H ℂ` (it inherits the Euclidean
operator norm). -/
def selfAdjointPart (S : StarSubalgebra ℂ (Matrix H H ℂ)) : Submodule ℝ (Matrix H H ℂ) where
  carrier := {a | a ∈ S ∧ star a = a}
  add_mem' := fun {a b} ha hb => ⟨S.add_mem ha.1 hb.1, by rw [star_add, ha.2, hb.2]⟩
  zero_mem' := ⟨S.zero_mem, star_zero _⟩
  smul_mem' := fun c a ha =>
    ⟨by rw [← Complex.coe_smul]; exact S.smul_mem ha.1 _, by rw [star_smul, star_trivial, ha.2]⟩

/-- `prop:finite-CQMS`: membership in the self-adjoint part. -/
theorem mem_selfAdjointPart {S : StarSubalgebra ℂ (Matrix H H ℂ)} {a : Matrix H H ℂ} :
    a ∈ selfAdjointPart S ↔ a ∈ S ∧ star a = a := Iff.rfl

/-- `prop:finite-CQMS`: the unit `1 ∈ A_sa`. -/
def saOne (S : StarSubalgebra ℂ (Matrix H H ℂ)) : selfAdjointPart S :=
  ⟨1, S.one_mem, star_one _⟩

/-- `prop:finite-CQMS`: the unit of `A_sa` is the identity matrix. -/
@[simp]
theorem coe_saOne (S : StarSubalgebra ℂ (Matrix H H ℂ)) :
    ((saOne S : selfAdjointPart S) : Matrix H H ℂ) = 1 := rfl

/-! ## The spectral seminorm on the self-adjoint part -/

/-- `prop:finite-CQMS`: the spectral seminorm `L_D(a) = ‖[D, a]‖` on the
self-adjoint part (Euclidean operator norm). -/
noncomputable def lipSA (D : Matrix H H ℂ) (S : StarSubalgebra ℂ (Matrix H H ℂ))
    (v : selfAdjointPart S) : ℝ :=
  ‖D * (v : Matrix H H ℂ) - (v : Matrix H H ℂ) * D‖

/-- `prop:finite-CQMS`: `lipSA` is the restriction of `lipD` for the inclusion
representation `S.subtype`. -/
theorem lipSA_eq_lipD (D : Matrix H H ℂ) (S : StarSubalgebra ℂ (Matrix H H ℂ))
    (v : selfAdjointPart S) :
    lipSA D S v = lipD D S.subtype ⟨(v : Matrix H H ℂ), v.2.1⟩ := rfl

/-- `prop:finite-CQMS`: the normalized trace `τ(a) = Re tr(a) / dim H` on the
self-adjoint part, as a real linear functional. -/
noncomputable def normalizedTrace (S : StarSubalgebra ℂ (Matrix H H ℂ)) :
    selfAdjointPart S →ₗ[ℝ] ℝ where
  toFun v := (Matrix.trace (v : Matrix H H ℂ)).re / Fintype.card H
  map_add' v w := by
    simp only [Submodule.coe_add, Matrix.trace_add, Complex.add_re, add_div]
  map_smul' c v := by
    simp only [Submodule.coe_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
      RingHom.id_apply, mul_div_assoc]

/-- `prop:finite-CQMS`: the normalized trace, unfolded. -/
theorem normalizedTrace_apply (S : StarSubalgebra ℂ (Matrix H H ℂ)) (v : selfAdjointPart S) :
    normalizedTrace S v = (Matrix.trace (v : Matrix H H ℂ)).re / Fintype.card H := rfl

/-- `prop:finite-CQMS`: the normalized trace of the unit is `1`. -/
theorem normalizedTrace_saOne [Nonempty H] (S : StarSubalgebra ℂ (Matrix H H ℂ)) :
    normalizedTrace S (saOne S) = 1 := by
  have h : (Fintype.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [normalizedTrace_apply, coe_saOne, Matrix.trace_one, Complex.natCast_re, div_self h]

/-! ## The Lip-norm package -/

/-- `prop:finite-CQMS`: the concrete Lip-norm package on `A_sa`: seminorm
`L_D`, unit `1`, normalized trace `τ`. -/
noncomputable def lipData [Nonempty H] (D : Matrix H H ℂ) (S : StarSubalgebra ℂ (Matrix H H ℂ)) :
    LipData (selfAdjointPart S) where
  L := lipSA D S
  continuous :=
    ((continuous_const.mul continuous_subtype_val).sub
      (continuous_subtype_val.mul continuous_const)).norm
  nonneg := fun _ => norm_nonneg _
  homog := fun c v => by
    show ‖D * (c • (v : Matrix H H ℂ)) - (c • (v : Matrix H H ℂ)) * D‖ = |c| * lipSA D S v
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, norm_smul, Real.norm_eq_abs, lipSA]
  subadd := fun v w => by
    show ‖D * ((v : Matrix H H ℂ) + w) - ((v : Matrix H H ℂ) + w) * D‖ ≤ lipSA D S v + lipSA D S w
    rw [Matrix.mul_add, Matrix.add_mul, show D * (v : Matrix H H ℂ) + D * w - (v * D + w * D)
      = (D * v - v * D) + (D * w - w * D) by abel]
    exact norm_add_le _ _
  u := saOne S
  L_u := by
    show ‖D * (1 : Matrix H H ℂ) - (1 : Matrix H H ℂ) * D‖ = 0
    rw [Matrix.mul_one, Matrix.one_mul, sub_self, norm_zero]
  τ := normalizedTrace S
  τ_u := normalizedTrace_saOne S

/-- `prop:finite-CQMS`: the seminorm of the package is `lipSA`. -/
@[simp]
theorem lipData_L [Nonempty H] (D : Matrix H H ℂ) (S : StarSubalgebra ℂ (Matrix H H ℂ)) :
    (lipData D S).L = lipSA D S := rfl

/-- `prop:finite-CQMS`: the unit of the package is `1`. -/
@[simp]
theorem lipData_u [Nonempty H] (D : Matrix H H ℂ) (S : StarSubalgebra ℂ (Matrix H H ℂ)) :
    (lipData D S).u = saOne S := rfl

/-- `prop:finite-CQMS`: the functional of the package is the normalized trace. -/
@[simp]
theorem lipData_τ [Nonempty H] (D : Matrix H H ℂ) (S : StarSubalgebra ℂ (Matrix H H ℂ)) :
    (lipData D S).τ = normalizedTrace S := rfl

/-! ## Kernel transport -/

/-- `prop:finite-CQMS`: transport of the hypothesis `Ker ∂ = ℂ 1` to the
self-adjoint part: a self-adjoint `a ∈ S` with `[D, a] = 0` is a real multiple
of the unit. -/
theorem kernelConstants [Nonempty H] (D : Matrix H H ℂ) (S : StarSubalgebra ℂ (Matrix H H ℂ))
    (hker : ∀ a ∈ S, D * a - a * D = 0 → ∃ z : ℂ, a = z • (1 : Matrix H H ℂ)) :
    (lipData D S).KernelConstants := by
  intro v hv
  have hcomm : D * (v : Matrix H H ℂ) - (v : Matrix H H ℂ) * D = 0 := norm_eq_zero.mp hv
  obtain ⟨z, hz⟩ := hker _ v.2.1 hcomm
  have hstar : star z = z := by
    have h := v.2.2
    rw [hz, star_smul, star_one] at h
    have := congrFun (congrFun h (Classical.arbitrary H)) (Classical.arbitrary H)
    simpa using this
  have hz' : (z.re : ℂ) = z := Complex.conj_eq_iff_re.mp hstar
  refine ⟨z.re, Subtype.ext ?_⟩
  show (v : Matrix H H ℂ) = z.re • (1 : Matrix H H ℂ)
  rw [hz, ← Complex.coe_smul, hz']

/-! ## Main theorem -/

/-- **Proposition `prop:finite-CQMS`** (matrix instantiation).  For a
`*`-subalgebra `S` of matrices and a Dirac matrix `D` with `Ker ∂ = ℂ 1`, the
spectral seminorm `L_D(a) = ‖[D, a]‖` on the self-adjoint part satisfies the
Poincaré–Lip inequality `‖a - τ(a) 1‖ ≤ C L_D(a)`, is dominated by the norm,
and for all states `φ, ψ` the Monge–Kantorovich distance
`mk_{L_D}(φ, ψ) = sup {|φ(a) - ψ(a)| : L_D(a) ≤ 1}` is a finite supremum bounded
by `C ‖φ - ψ‖ ≤ 2C`, dominates `|φ(a) - ψ(a)| / L_D(a)`, and is bi-Lipschitz
equivalent to the dual norm distance. -/
theorem finite_cqms_matrix [Nonempty H] (D : Matrix H H ℂ) (S : StarSubalgebra ℂ (Matrix H H ℂ))
    (hker : ∀ a ∈ S, D * a - a * D = 0 → ∃ z : ℂ, a = z • (1 : Matrix H H ℂ)) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      (∀ v : selfAdjointPart S, ‖v - normalizedTrace S v • saOne S‖ ≤ C * lipSA D S v) ∧
      (∀ v : selfAdjointPart S, lipSA D S v ≤ K * ‖v‖) ∧
      ∀ φ ψ : selfAdjointPart S →L[ℝ] ℝ, (lipData D S).IsState φ → (lipData D S).IsState ψ →
        BddAbove ((lipData D S).mkValues φ ψ) ∧
        0 ≤ (lipData D S).mkDist φ ψ ∧
        (lipData D S).mkDist φ ψ ≤ C * ‖φ - ψ‖ ∧
        (lipData D S).mkDist φ ψ ≤ 2 * C ∧
        (∀ v, |φ v - ψ v| ≤ lipSA D S v * (lipData D S).mkDist φ ψ) ∧
        ‖φ - ψ‖ ≤ K * (lipData D S).mkDist φ ψ :=
  finite_compact_quantum_metric (lipData D S) (kernelConstants D S hker)

/-- `prop:finite-CQMS`: the **Leibniz inequality** and the **star identity** for
`L_D` on the whole `*`-subalgebra `S` (inclusion representation `S.subtype`,
Hermitian `D`). -/
theorem finite_cqms_matrix_leibniz_star (D : Matrix H H ℂ) (hD : Dᴴ = D)
    (S : StarSubalgebra ℂ (Matrix H H ℂ)) :
    (∀ a b : S, lipD D S.subtype (a * b) ≤
      ‖(a : Matrix H H ℂ)‖ * lipD D S.subtype b + ‖(b : Matrix H H ℂ)‖ * lipD D S.subtype a) ∧
    ∀ a : S, lipD D S.subtype (star a) = lipD D S.subtype a :=
  ⟨fun a b => lipD_mul_le D S.subtype a b, fun a => lipD_star D hD S.subtype a⟩

/-- `prop:finite-CQMS`: **`mk_{L_D}` induces the (weak-`*` = norm) topology on
the state space**: `mk_{L_D}`-convergence of states is exactly norm convergence
in the dual of `A_sa`. -/
theorem finite_cqms_matrix_tendsto [Nonempty H] (D : Matrix H H ℂ)
    (S : StarSubalgebra ℂ (Matrix H H ℂ))
    (hker : ∀ a ∈ S, D * a - a * D = 0 → ∃ z : ℂ, a = z • (1 : Matrix H H ℂ))
    {C K : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v : selfAdjointPart S, ‖v - normalizedTrace S v • saOne S‖ ≤ C * lipSA D S v)
    (hK0 : 0 ≤ K) (hK : ∀ v : selfAdjointPart S, lipSA D S v ≤ K * ‖v‖)
    {ι : Type*} {l : Filter ι} {φ : ι → (selfAdjointPart S →L[ℝ] ℝ)}
    {ψ : selfAdjointPart S →L[ℝ] ℝ}
    (hφ : ∀ i, (lipData D S).IsState (φ i)) (hψ : (lipData D S).IsState ψ) :
    Tendsto (fun i => (lipData D S).mkDist (φ i) ψ) l (𝓝 0) ↔ Tendsto φ l (𝓝 ψ) :=
  (lipData D S).tendsto_mkDist_iff (kernelConstants D S hker) hC0 hC hK0 hK hφ hψ

/-! ## Converse -/

/-- `prop:finite-CQMS` (converse, kernel element): if `Ker ∂ ≠ ℂ 1` is witnessed
by a non-scalar self-adjoint `a ∈ S` commuting with `D`, then `a` is a
non-scalar element of `A_sa` with `L_D(a) = 0`. -/
theorem finite_cqms_matrix_converse (D : Matrix H H ℂ) (S : StarSubalgebra ℂ (Matrix H H ℂ))
    (h : ∃ a ∈ S, star a = a ∧ D * a - a * D = 0 ∧ ∀ z : ℂ, a ≠ z • (1 : Matrix H H ℂ)) :
    ∃ v : selfAdjointPart S, lipSA D S v = 0 ∧ ∀ c : ℝ, v ≠ c • saOne S := by
  obtain ⟨a, haS, hstar, hcomm, hne⟩ := h
  refine ⟨⟨a, haS, hstar⟩, ?_, fun c hc => hne (c : ℂ) ?_⟩
  · show ‖D * a - a * D‖ = 0
    rw [hcomm, norm_zero]
  · have := congrArg Subtype.val hc
    rw [Complex.coe_smul]
    exact this

/-! ## Vector states and the separating clause of the converse -/

/-- `prop:finite-CQMS`: the vector state `a ↦ Re ⟪x, a x⟫` of `x ∈ H` on the
self-adjoint part, as a continuous real linear functional. -/
noncomputable def vectorState (S : StarSubalgebra ℂ (Matrix H H ℂ)) (x : EuclideanSpace ℂ H) :
    selfAdjointPart S →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (⟪x, toEuclideanCLM (n := H) (𝕜 := ℂ) (v : Matrix H H ℂ) x⟫_ℂ).re
      map_add' := fun v w => by
        simp only [Submodule.coe_add, map_add, _root_.add_apply, inner_add_right,
          Complex.add_re]
      map_smul' := fun c v => by
        simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
        rw [← Complex.coe_smul, map_smul, _root_.smul_apply, inner_smul_right,
          Complex.re_ofReal_mul] }

/-- `prop:finite-CQMS`: the vector state, unfolded. -/
theorem vectorState_apply (S : StarSubalgebra ℂ (Matrix H H ℂ)) (x : EuclideanSpace ℂ H)
    (v : selfAdjointPart S) :
    vectorState S x v = (⟪x, toEuclideanCLM (n := H) (𝕜 := ℂ) (v : Matrix H H ℂ) x⟫_ℂ).re := rfl

/-- `prop:finite-CQMS`: a unit vector defines a state (normalized at `1`,
contractive for the operator norm). -/
theorem isState_vectorState [Nonempty H] (D : Matrix H H ℂ) (S : StarSubalgebra ℂ (Matrix H H ℂ))
    {x : EuclideanSpace ℂ H} (hx : ‖x‖ = 1) : (lipData D S).IsState (vectorState S x) := by
  refine ⟨?_, ?_⟩
  · show (⟪x, toEuclideanCLM (n := H) (𝕜 := ℂ) (1 : Matrix H H ℂ) x⟫_ℂ).re = 1
    rw [map_one, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hx]
    simp
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul, vectorState_apply, Real.norm_eq_abs]
    calc |(⟪x, toEuclideanCLM (n := H) (𝕜 := ℂ) (v : Matrix H H ℂ) x⟫_ℂ).re|
        ≤ ‖⟪x, toEuclideanCLM (n := H) (𝕜 := ℂ) (v : Matrix H H ℂ) x⟫_ℂ‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ‖x‖ * ‖toEuclideanCLM (n := H) (𝕜 := ℂ) (v : Matrix H H ℂ) x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖toEuclideanCLM (n := H) (𝕜 := ℂ) (v : Matrix H H ℂ)‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖v‖ := by rw [hx, one_mul, mul_one, l2_opNorm_toEuclideanCLM, Submodule.coe_norm]

/-- `prop:finite-CQMS`: a non-scalar self-adjoint matrix is separated by two
vector states (polarization: if `Re ⟪x, a x⟫` were constant on unit vectors,
the symmetric operator `a - λ 1` would have vanishing quadratic form). -/
theorem exists_vectorState_ne [Nonempty H] (S : StarSubalgebra ℂ (Matrix H H ℂ))
    {a : Matrix H H ℂ} (haS : a ∈ S) (ha : star a = a)
    (hne : ∀ z : ℂ, a ≠ z • (1 : Matrix H H ℂ)) :
    ∃ x y : EuclideanSpace ℂ H, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      vectorState S x ⟨a, haS, ha⟩ ≠ vectorState S y ⟨a, haS, ha⟩ := by
  by_contra hcon
  push Not at hcon
  set T := toEuclideanCLM (n := H) (𝕜 := ℂ) a with hT
  let x₀ : EuclideanSpace ℂ H := PiLp.single 2 (Classical.arbitrary H) 1
  have hx₀ : ‖x₀‖ = 1 := by rw [PiLp.norm_single, norm_one]
  set lam : ℝ := (⟪x₀, T x₀⟫_ℂ).re with hlam
  have hunit : ∀ x : EuclideanSpace ℂ H, ‖x‖ = 1 → (⟪x, T x⟫_ℂ).re = lam :=
    fun x hx => hcon x x₀ hx hx₀
  have hall : ∀ x : EuclideanSpace ℂ H, (⟪x, T x⟫_ℂ).re = lam * ‖x‖ ^ 2 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have h1 : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
        rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have key := hunit _ h1
      rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, Complex.re_ofReal_mul,
        Complex.re_ofReal_mul] at key
      rw [← key]
      field_simp
  set b : Matrix H H ℂ := a - (lam : ℂ) • (1 : Matrix H H ℂ) with hb
  have hsa : IsSelfAdjoint b := by
    rw [IsSelfAdjoint, hb, star_sub, ha, star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
  have hsym : (toEuclideanCLM (n := H) (𝕜 := ℂ) b :
      EuclideanSpace ℂ H →ₗ[ℂ] EuclideanSpace ℂ H).IsSymmetric :=
    (hsa.map (toEuclideanCLM (n := H) (𝕜 := ℂ))).isSymmetric
  have hzero : ∀ x : EuclideanSpace ℂ H,
      ⟪(toEuclideanCLM (n := H) (𝕜 := ℂ) b : EuclideanSpace ℂ H →ₗ[ℂ] EuclideanSpace ℂ H) x, x⟫_ℂ
        = 0 := by
    intro x
    have hre : (⟪x, toEuclideanCLM (n := H) (𝕜 := ℂ) b x⟫_ℂ).re = 0 := by
      rw [hb, map_sub, map_smul, map_one, _root_.sub_apply,
        _root_.smul_apply, one_apply_eq_self, inner_sub_right,
        inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.sub_re, Complex.re_ofReal_mul, hall]
      simp [sq]
    have hconj := hsym.conj_inner_sym x x
    rw [ContinuousLinearMap.coe_coe] at hconj ⊢
    have hreal := (Complex.conj_eq_iff_re.mp hconj).symm
    rw [hreal, ← inner_conj_symm, Complex.conj_re, hre, Complex.ofReal_zero]
  have hT0 : (toEuclideanCLM (n := H) (𝕜 := ℂ) b :
      EuclideanSpace ℂ H →ₗ[ℂ] EuclideanSpace ℂ H) = 0 := (inner_map_self_eq_zero _).mp hzero
  have hT0' : toEuclideanCLM (n := H) (𝕜 := ℂ) b = 0 :=
    ContinuousLinearMap.ext fun x => by simpa using LinearMap.congr_fun hT0 x
  have hb0 : b = 0 := (toEuclideanCLM (n := H) (𝕜 := ℂ)).injective (hT0'.trans (map_zero _).symm)
  exact hne (lam : ℂ) (sub_eq_zero.mp hb0)

/-- `prop:finite-CQMS` (converse, full clause): if `Ker ∂ ≠ ℂ 1` is witnessed by
a non-scalar self-adjoint `a ∈ S` commuting with `D`, then there are two
(vector) states `φ, ψ` for which the supremum defining `mk_{L_D}(φ, ψ)` is
unbounded: the distance is infinite. -/
theorem finite_cqms_matrix_converse_not_bddAbove [Nonempty H] (D : Matrix H H ℂ)
    (S : StarSubalgebra ℂ (Matrix H H ℂ))
    (h : ∃ a ∈ S, star a = a ∧ D * a - a * D = 0 ∧ ∀ z : ℂ, a ≠ z • (1 : Matrix H H ℂ)) :
    ∃ φ ψ : selfAdjointPart S →L[ℝ] ℝ, (lipData D S).IsState φ ∧ (lipData D S).IsState ψ ∧
      ¬ BddAbove ((lipData D S).mkValues φ ψ) := by
  obtain ⟨a, haS, hstar, hcomm, hne⟩ := h
  obtain ⟨x, y, hx, hy, hsep⟩ := exists_vectorState_ne S haS hstar hne
  refine ⟨vectorState S x, vectorState S y, isState_vectorState D S hx,
    isState_vectorState D S hy, ?_⟩
  refine (lipData D S).not_bddAbove_of_kernel (v := ⟨a, haS, hstar⟩) ?_ hsep
  show ‖D * a - a * D‖ = 0
  rw [hcomm, norm_zero]

/-! ## Weak-`*` versus norm convergence in finite dimension -/

/-- `prop:finite-CQMS`: on the dual of a finite-dimensional real normed space,
pointwise (weak-`*`) convergence of functionals is the same as norm
convergence. -/
theorem tendsto_iff_forall_tendsto_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} {l : Filter ι} {φ : ι → (V →L[ℝ] ℝ)} {ψ : V →L[ℝ] ℝ} :
    Tendsto φ l (𝓝 ψ) ↔ ∀ v, Tendsto (fun i => φ i v) l (𝓝 (ψ v)) := by
  constructor
  · intro h v
    have h' := tendsto_iff_norm_sub_tendsto_zero.mp h
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) (by simpa using h'.mul_const ‖v‖)
    rw [← _root_.sub_apply]
    exact (φ i - ψ).le_opNorm v
  · intro h
    let b := Module.finBasis ℝ V
    let Φ : (V →L[ℝ] ℝ) →ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
      { toFun := fun f i => f (b i)
        map_add' := fun f g => by ext i; simp
        map_smul' := fun c f => by ext i; simp }
    have hΦ : LinearMap.ker Φ = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro f hf
      have hf' : ∀ i, f (b i) = 0 := fun i => congrFun hf i
      exact ContinuousLinearMap.ext fun v =>
        LinearMap.congr_fun (b.ext (f₁ := (f : V →ₗ[ℝ] ℝ)) (f₂ := 0)
          fun i => by simpa using hf' i) v
    have hemb := LinearMap.isClosedEmbedding_of_injective hΦ
    rw [hemb.tendsto_nhds_iff, tendsto_pi_nhds]
    intro i
    exact h (b i)

/-! ## Positive normalized functionals are states -/

/-- `prop:finite-CQMS`: for a self-adjoint `v`, the matrices `‖v‖ 1 ± v` are positive
semidefinite (the operator norm dominates the quadratic form). -/
theorem posSemidef_norm_smul_one_add_smul (S : StarSubalgebra ℂ (Matrix H H ℂ))
    (v : selfAdjointPart S) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ((‖v‖ : ℂ) • (1 : Matrix H H ℂ) + (ε : ℂ) • (v : Matrix H H ℂ)).PosSemidef := by
  have hv : star (v : Matrix H H ℂ) = v := v.2.2
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · show ((‖v‖ : ℂ) • (1 : Matrix H H ℂ) + (ε : ℂ) • (v : Matrix H H ℂ))ᴴ = _
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_one,
      ← star_eq_conjTranspose, hv, Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
  · set X : EuclideanSpace ℂ H := WithLp.toLp 2 x
    set q : ℂ := star x ⬝ᵥ ((v : Matrix H H ℂ) *ᵥ x) with hq
    have hexp : star x ⬝ᵥ (((‖v‖ : ℂ) • (1 : Matrix H H ℂ) + (ε : ℂ) • (v : Matrix H H ℂ)) *ᵥ x)
        = (‖v‖ : ℂ) * (star x ⬝ᵥ x) + (ε : ℂ) * q := by
      rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
        dotProduct_smul, smul_eq_mul, smul_eq_mul]
    -- `star x ⬝ᵥ x = ‖X‖²`
    have hxx : star x ⬝ᵥ x = ((‖X‖ ^ 2 : ℝ) : ℂ) := by
      have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) X
      rw [EuclideanSpace.inner_eq_star_dotProduct] at this
      rw [dotProduct_comm]
      exact this.trans (by push_cast; rfl)
    -- `q = ⟪X, v X⟫` is real and bounded by `‖v‖ ‖X‖²`
    have hqinner : q = ⟪X, toEuclideanCLM (n := H) (𝕜 := ℂ) (v : Matrix H H ℂ) X⟫_ℂ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, hq, dotProduct_comm]
      rfl
    have hqim : q.im = 0 := by
      have hconj : star q = q := by
        rw [hq, ← star_dotProduct_star, star_star, star_mulVec, ← star_eq_conjTranspose, hv,
          ← dotProduct_mulVec]
      exact Complex.conj_eq_iff_im.mp hconj
    have hqre : |q.re| ≤ ‖v‖ * ‖X‖ ^ 2 := by
      rw [hqinner]
      calc |(⟪X, toEuclideanCLM (n := H) (𝕜 := ℂ) (v : Matrix H H ℂ) X⟫_ℂ).re|
          ≤ ‖⟪X, toEuclideanCLM (n := H) (𝕜 := ℂ) (v : Matrix H H ℂ) X⟫_ℂ‖ :=
            Complex.abs_re_le_norm _
        _ ≤ ‖X‖ * ‖toEuclideanCLM (n := H) (𝕜 := ℂ) (v : Matrix H H ℂ) X‖ :=
            norm_inner_le_norm _ _
        _ ≤ ‖X‖ * (‖toEuclideanCLM (n := H) (𝕜 := ℂ) (v : Matrix H H ℂ)‖ * ‖X‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ = ‖v‖ * ‖X‖ ^ 2 := by
            rw [l2_opNorm_toEuclideanCLM, Submodule.coe_norm]
            ring
    rw [hexp, hxx, Complex.nonneg_iff]
    constructor
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, hqim, mul_zero]
      have h := abs_le.mp hqre
      rcases hε with rfl | rfl <;> linarith [h.1, h.2]
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        mul_zero, hqim, add_zero]

/-- `prop:finite-CQMS`: **positive normalized functionals are states**: a functional on `A_sa`
with `φ(1) = 1` and `φ(v) ≥ 0` for every positive semidefinite `v ∈ A_sa` is contractive, hence
a state in the sense of `LipData.IsState`.  Thus the paper's state space `S(A)` is contained in
the state space to which `finite_cqms_matrix` and `finite_cqms_matrix_tendsto` apply. -/
theorem isState_of_nonneg [Nonempty H] (D : Matrix H H ℂ) (S : StarSubalgebra ℂ (Matrix H H ℂ))
    (φ : selfAdjointPart S →L[ℝ] ℝ) (hφ1 : φ (saOne S) = 1)
    (hpos : ∀ v : selfAdjointPart S, (v : Matrix H H ℂ).PosSemidef → 0 ≤ φ v) :
    (lipData D S).IsState φ := by
  refine ⟨hφ1, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, Real.norm_eq_abs, abs_le]
  have hw : ∀ ε : ℝ, ε = 1 ∨ ε = -1 → 0 ≤ ‖v‖ + ε * φ v := by
    intro ε hε
    have hmem := hpos (‖v‖ • saOne S + ε • v) (by
      show ((‖v‖ • (saOne S : Matrix H H ℂ) + ε • (v : Matrix H H ℂ))).PosSemidef
      rw [coe_saOne, ← Complex.coe_smul, ← Complex.coe_smul]
      exact posSemidef_norm_smul_one_add_smul S v hε)
    rwa [map_add, map_smul, map_smul, hφ1, smul_eq_mul, mul_one, smul_eq_mul] at hmem
  constructor
  · have := hw 1 (Or.inl rfl)
    linarith
  · have := hw (-1) (Or.inr rfl)
    linarith

end FiniteCompactQuantumMetric
end RenewalGeometry
