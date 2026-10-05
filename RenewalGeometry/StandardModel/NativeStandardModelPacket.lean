/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.FiniteInterfaceGeneral
import RenewalGeometry.StandardModel.RenewalLatticeCarrier
import RenewalGeometry.GaugeTheory.NativeActionGaugeInvariance

/-!
# The Standard-Model representation packet of the native local action
  (`prop:renewal-interface`, items (I2)–(I4); `tab:SM-representations`, `lem:SM-descent`,
  `eq:native-densities`; Einstein–Standard-Model action-closure manuscript)

The native local action `NativeDensity.localAction` (`eq:native-local-action`) is defined for any
representation packet `NativeDensity.Data 𝔄 𝓗 𝓢` and is gauge invariant for any covariant packet
`NativeGauge.CovData`.  This file builds **the Standard-Model packet** `smCovData θ` on the minimal
branch of `tab:SM-representations`, for every coefficient bank `θ`:

* **spinor fibre**: Dirac spinors in the Weyl basis, index `SpinI = Fin 2 ⊕ Fin 2` (left ⊕ right
  Weyl components), gamma matrices `gam a = i Γ^a` (`Γ⁰ = [[0,1],[1,0]]`, `Γ^k = [[0,σ_k],[-σ_k,0]]`)
  satisfying the Clifford relations `γ^aγ^b + γ^bγ^a = 2η^{ab}` for `η = diag(-1,1,1,1)`
  (`gam_clifford`), chirality `gam5 = diag(-1, 1)` (`gam5_sq`, `gam5_anticomm`), and the Lorentz
  spin representation `σ(ω) = ¼ (ηω)_{ab} γ^aγ^b` (`sigmaL`);
* **fermion carrier**: `𝓢 = ℂ^{spin} ⊗ ℂ³_gen ⊗ ℂ^{table rows}` (`SF`, Euclidean), on which the
  internal gauge algebra acts by `1 ⊗ 1 ⊗ X` and the spin/Clifford operators by `A ⊗ 1 ⊗ 1`;
* **gauge algebra**: `𝔄 = End(ℂ²_Higgs) × End(ℂ^{table rows})` (`Alg`, a C*-algebra), the ambient
  algebra of the Higgs and fermion representations; `G_SM` is embedded by
  `ι(y) = (U₂(y), tableRep(y))` (`iota`), whose image `smG` is the gauge group of the packet;
  `ρ_H`, `ρ_S` are the projections onto the two representation blocks;
* **Yang–Mills metric** (`ymForm`): the `Ad_{G_SM}`-invariant form
  `2g₃⁻² ⟨D°, D'°⟩ + 2g₂⁻² ⟨L°, L'°⟩ + g₁⁻² Re(Ē E')` built from the `d_R` block `D` (colour),
  the `L_L` block `L` (weak) and the `e_R` entry `E` (hypercharge) of the fermion block, `°` the
  traceless part, `⟨A, B⟩ = Re tr(A^*B)`; on the represented Lie algebra of `S(U(3)×U(2))` it is the
  sum of the three invariant metrics with coefficients `g_j^{-2}` (`eq:SM-action`);
* **Higgs form** `Re⟨·,·⟩` (`innerSL ℝ`), **Yukawa map** `H ↦ 1_spin ⊗ 𝓜_𝐘(H)` with the covariant
  blocks `yukawaMin` of `lem:SM-descent` for the bank's `Y_u, Y_d, Y_e` (`yukMat`).

`smCovData θ : NativeGauge.CovData Alg EH SF` proves every covariance field: unitary conjugation
preserves norms (`norm_conj`), `Ad`-invariance of `ymForm` (`ipA_conj`), unitarity of `ρ_H` and
`ρ_S` (`hermH_inv`, `ρS_isom`), commutation of the internal group with the spin representation and
the Clifford action (`σ_comm`, `γ_comm`), and covariance of the Yukawa blocks (`yukawa_cov`).
Disclosed rendering: the gauge potentials range over the ambient algebra `Alg` (the group is not a
vector space); only the gauge group `smG` is the image of `S(U(3)×U(2))`.
-/

open Matrix
open scoped Kronecker

noncomputable section

namespace RenewalGeometry
namespace NativeSMPacket

open FiniteInterfaceTable FiniteInterfaceGeneral SMDescentYukawa
open NativeScaling (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Dirac matrices in the Weyl basis -/

/-- The spinor index: left and right Weyl components. -/
abbrev SpinI : Type := Fin 2 ⊕ Fin 2

/-- The Pauli matrices. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

theorem pauli_anticomm (k l : Fin 3) :
    pauli k * pauli l + pauli l * pauli k = (2 * if k = l then (1 : ℂ) else 0) • 1 := by
  fin_cases k <;> fin_cases l <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq]

/-- The Weyl-basis matrices `Γ⁰ = [[0,1],[1,0]]`, `Γ^k = [[0,σ_k],[-σ_k,0]]`. -/
def bigGam : Fin 4 → Matrix SpinI SpinI ℂ :=
  Fin.cons (fromBlocks 0 1 1 0) fun k => fromBlocks 0 (pauli k) (-pauli k) 0

/-- **The frame gamma matrices** `γ^a = i Γ^a`. -/
def gam (a : Fin 4) : Matrix SpinI SpinI ℂ := Complex.I • bigGam a

/-- The spinor chirality `γ₅ = diag(-1, 1)` (left, right). -/
def gam5 : Matrix SpinI SpinI ℂ := fromBlocks (-1) 0 0 1

theorem etaC_zero_zero : etaC 0 0 = -1 := by simp [etaC, minkowskiEta]

theorem etaC_zero_succ (l : Fin 3) : etaC 0 l.succ = 0 := by
  simp [etaC, minkowskiEta, Matrix.diagonal_apply, (Fin.succ_ne_zero l).symm]

theorem etaC_succ_zero (l : Fin 3) : etaC l.succ 0 = 0 := by
  simp [etaC, minkowskiEta, Matrix.diagonal_apply, Fin.succ_ne_zero l]

theorem etaC_succ_succ (k l : Fin 3) : etaC k.succ l.succ = if k = l then 1 else 0 := by
  simp only [etaC, minkowskiEta, Matrix.diagonal_apply, Fin.succ_inj]
  split_ifs with h
  · subst h; fin_cases k <;> simp
  · simp

theorem bigGam_anticomm (a c : Fin 4) :
    bigGam a * bigGam c + bigGam c * bigGam a = (-(2 * etaC a c)) • 1 := by
  refine Fin.cases ?_ (fun k => ?_) a <;> refine Fin.cases ?_ (fun l => ?_) c
  · simp only [bigGam, Fin.cons_zero, fromBlocks_multiply, etaC_zero_zero, ← fromBlocks_one]
    simp [fromBlocks_add, fromBlocks_smul]
    norm_num [two_smul, one_add_one_eq_two]
  · simp only [bigGam, Fin.cons_zero, Fin.cons_succ, fromBlocks_multiply, etaC_zero_succ,
      ← fromBlocks_one]
    simp [fromBlocks_add, fromBlocks_smul]
  · simp only [bigGam, Fin.cons_zero, Fin.cons_succ, fromBlocks_multiply, etaC_succ_zero,
      ← fromBlocks_one]
    simp [fromBlocks_add, fromBlocks_smul]
  · rw [show (1 : Matrix SpinI SpinI ℂ) = fromBlocks 1 0 0 1 from fromBlocks_one.symm,
      fromBlocks_smul]
    have h := pauli_anticomm k l
    simp only [bigGam, Fin.cons_succ, fromBlocks_multiply, fromBlocks_add, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_zero, smul_zero]
    rw [← neg_add, h, etaC_succ_succ, neg_smul]

/-- **The Clifford relations** `γ^aγ^b + γ^bγ^a = 2η^{ab}`, `η = diag(-1,1,1,1)`. -/
theorem gam_clifford (a c : Fin 4) : gam a * gam c + gam c * gam a = (2 * etaC a c) • 1 := by
  simp only [gam, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← smul_add, bigGam_anticomm]
  rw [Complex.I_mul_I]
  congr 1
  ring

theorem gam5_sq : gam5 * gam5 = 1 := by
  simp [gam5, fromBlocks_multiply, ← fromBlocks_one]

theorem gam5_anticomm (a : Fin 4) : gam5 * gam a = -(gam a * gam5) := by
  simp only [gam, Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]
  congr 1
  refine Fin.cases ?_ (fun k => ?_) a <;>
    simp [gam5, bigGam, fromBlocks_multiply, fromBlocks_neg]

/-- **The Lorentz spin representation** `σ(ω) = ¼ (ηω)_{ab} γ^aγ^b` (real-linear in `ω`). -/
def sigmaL : Mat →ₗ[ℝ] Matrix SpinI SpinI ℂ where
  toFun ω := ∑ a, ∑ c, (((1 / 4 : ℝ) * (minkowskiEta * ω) a c : ℝ) : ℂ) • (gam a * gam c)
  map_add' ω ω' := by
    simp only [Matrix.mul_add, Matrix.add_apply, mul_add, Complex.ofReal_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' r ω := by
    simp only [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [show (1 / 4 : ℝ) * (r * (minkowskiEta * ω) a c) = r * ((1 / 4) * (minkowskiEta * ω) a c)
      by ring, Complex.ofReal_mul, mul_smul, Complex.coe_smul]

/-! ### Carriers -/


/-- The table rows of the minimal branch (as indexed by the interface). -/
abbrev RowM : Type := TableRow .minimal

/-- The table rows of the minimal branch (block-unfolded form used by the lattice carrier). -/
abbrev Row : Type := RenewalRealization.Row

/-- The fermion fibre index `spin × generation × table row`. -/
abbrev FibI : Type := FermionIdx SpinI .minimal

/-- The Higgs space `ℂ²`. -/
abbrev EH : Type := EuclideanSpace ℂ (Fin 2)

/-- The table-row space `ℂ^{15}`. -/
abbrev ER : Type := EuclideanSpace ℂ Row

/-- **The fermion fibre** `𝓢 = ℂ^{spin} ⊗ ℂ³_gen ⊗ ℂ^{table rows}`. -/
abbrev SF : Type := EuclideanSpace ℂ FibI

/-- **The gauge algebra** `End(ℂ²_Higgs) × End(ℂ^{table rows})`. -/
abbrev Alg : Type := (EH →L[ℂ] EH) × (ER →L[ℂ] ER)

/-- Matrices as operators on Euclidean space. -/
local notation "toE" => Matrix.toEuclideanCLM (𝕜 := ℂ)

/-- Restriction of scalars `ℂ → ℝ` for operators, as an `ℝ`-algebra homomorphism. -/
def restrictR (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    (V →L[ℂ] V) →ₐ[ℝ] (V →L[ℝ] V) where
  toFun T := T.restrictScalars ℝ
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' r := by ext v; simp [Algebra.algebraMap_eq_smul_one]

theorem restrictR_apply (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : V →L[ℂ] V) (v : V) : restrictR V T v = T v := rfl

/-- Matrices on the fermion fibre as real operators on `𝓢`. -/
def RF : Matrix FibI FibI ℂ →ₐ[ℝ] (SF →L[ℝ] SF) :=
  (restrictR SF).comp
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := FibI)).toAlgEquiv.toAlgHom.restrictScalars ℝ)

theorem RF_apply (M : Matrix FibI FibI ℂ) (v : SF) : RF M v = toE M v := by
  show restrictR SF (toE M) v = _
  rfl

theorem continuous_RF : Continuous RF := LinearMap.continuous_of_finiteDimensional RF.toLinearMap

/-- The identification of the two spellings of the minimal table rows. -/
def rowCast : Matrix Row Row ℂ →ₐ[ℂ] Matrix RowM RowM ℂ := AlgHom.id ℂ _

/-- The identification of the generation × table-row matrices. -/
def internalCast : Matrix (Fin 3 × Row) (Fin 3 × Row) ℂ →ₐ[ℂ]
    Matrix (InternalIdx .minimal) (InternalIdx .minimal) ℂ := AlgHom.id ℂ _

theorem internalOp_add (A B : Matrix (InternalIdx .minimal) (InternalIdx .minimal) ℂ) :
    internalOp SpinI (A + B) = internalOp SpinI A + internalOp SpinI B := by
  simp only [internalOp, kronecker_add]

theorem internalOp_smul (r : ℝ) (A : Matrix (InternalIdx .minimal) (InternalIdx .minimal) ℂ) :
    internalOp SpinI (r • A) = r • internalOp SpinI A := by
  simp only [internalOp, kronecker_smul]

/-- The internal lift `M ↦ 1_spin ⊗ 1_gen ⊗ M` of table-row matrices. -/
def kronAlg : Matrix RowM RowM ℂ →ₐ[ℂ] Matrix FibI FibI ℂ where
  toFun M := internalOp SpinI ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ M)
  map_one' := by rw [one_kronecker_one, internalOp_one]
  map_mul' M N := by rw [internalOp_mul, ← mul_kronecker_mul, Matrix.one_mul]
  map_zero' := by simp only [internalOp]; rw [kronecker_zero, kronecker_zero]
  map_add' M N := by simp only [internalOp]; rw [kronecker_add, kronecker_add]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, internalOp]
    rw [kronecker_smul, one_kronecker_one, kronecker_smul, one_kronecker_one]

/-- The internal lift on the block-unfolded rows. -/
def liftRow : Matrix Row Row ℂ →ₐ[ℂ] Matrix FibI FibI ℂ := kronAlg.comp rowCast

theorem liftRow_tableRepM (y : SMGaugeGroup) :
    liftRow (RenewalRealization.tableRepM y) = fibreRep SpinI .minimal y := rfl

/-! ### The gauge group `G_SM ↪ Alg` -/

/-- `y ↦ (U₂(y), tableRep(y))`. -/
def iotaA : SMGaugeGroup →* Alg where
  toFun y := (toE (smU2 y), toE (RenewalRealization.tableRepM y))
  map_one' := Prod.ext (by simp) (by simp)
  map_mul' y y' := Prod.ext (by simp) (by simp)

theorem iotaA_apply (y : SMGaugeGroup) :
    iotaA y = (toE (smU2 y), toE (RenewalRealization.tableRepM y)) := rfl

/-- **The embedding of `G_SM` in the units of the gauge algebra.** -/
def iota : SMGaugeGroup →* Algˣ := iotaA.toHomUnits

/-- **The gauge group of the packet**: the image of `S(U(3)×U(2))`. -/
def smG : Subgroup Algˣ := iota.range

theorem coe_iota (y : SMGaugeGroup) : ((iota y : Algˣ) : Alg) = iotaA y := rfl

theorem coe_iota_inv (y : SMGaugeGroup) : (((iota y)⁻¹ : Algˣ) : Alg) = iotaA y⁻¹ := by
  rw [← map_inv]; rfl

/-! ### Unitarity of the representations -/

theorem extRep_star (A3 : Matrix (Fin 3) (Fin 3) ℂ) (A2 : Matrix (Fin 2) (Fin 2) ℂ) :
    star (RenewalRealization.extRep A3 A2) =
      RenewalRealization.extRep (star A3) (star A2) := by
  simp only [RenewalRealization.extRep, star_eq_conjTranspose, fromBlocks_conjTranspose,
    conjTranspose_zero, conjTranspose_smul, conjTranspose_kronecker, conjTranspose_one,
    det_conjTranspose, star_star]

theorem star_tableRepM (y : SMGaugeGroup) :
    star (RenewalRealization.tableRepM y) = RenewalRealization.tableRepM y⁻¹ := by
  rw [← RenewalRealization.extRep_smGauge, extRep_star, RenewalRealization.extRep_star_smGauge]

theorem star_tableRepM_mul (y : SMGaugeGroup) :
    star (RenewalRealization.tableRepM y) * RenewalRealization.tableRepM y = 1 := by
  rw [star_tableRepM, ← map_mul, inv_mul_cancel, map_one]

theorem tableRepM_mul_star (y : SMGaugeGroup) :
    RenewalRealization.tableRepM y * star (RenewalRealization.tableRepM y) = 1 := by
  rw [star_tableRepM, ← map_mul, mul_inv_cancel, map_one]

theorem kronAlg_star (M : Matrix RowM RowM ℂ) : star (kronAlg M) = kronAlg (star M) := by
  show star (internalOp SpinI ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ M)) =
    internalOp SpinI ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ star M)
  simp only [internalOp, star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one]

theorem star_fibreRep (y : SMGaugeGroup) :
    star (fibreRep SpinI .minimal y) = fibreRep SpinI .minimal y⁻¹ := by
  rw [show fibreRep SpinI .minimal y = kronAlg (tableRep .minimal y) from rfl, kronAlg_star,
    show star (tableRep .minimal y) = tableRep .minimal y⁻¹ from star_tableRepM y]
  rfl

theorem star_fibreRep_mul (y : SMGaugeGroup) :
    star (fibreRep SpinI .minimal y) * fibreRep SpinI .minimal y = 1 := by
  rw [star_fibreRep, ← map_mul, inv_mul_cancel, map_one]

theorem star_smU2_mul (y : SMGaugeGroup) : star (smU2 y) * smU2 y = 1 :=
  (Unitary.mem_iff.mp (smU2_mem y)).1

theorem smU2_mul_star (y : SMGaugeGroup) : smU2 y * star (smU2 y) = 1 :=
  (Unitary.mem_iff.mp (smU2_mem y)).2

theorem star_smU3_mul (y : SMGaugeGroup) : star (smU3 y) * smU3 y = 1 :=
  (Unitary.mem_iff.mp (smU3_mem y)).1

theorem smU3_mul_star (y : SMGaugeGroup) : smU3 y * star (smU3 y) = 1 :=
  (Unitary.mem_iff.mp (smU3_mem y)).2

theorem iotaA_mem_unitary (y : SMGaugeGroup) : iotaA y ∈ unitary Alg := by
  have h1 : star (toE (smU2 y)) * toE (smU2 y) = 1 := by
    rw [← map_star, ← map_mul, star_smU2_mul, map_one]
  have h2 : toE (smU2 y) * star (toE (smU2 y)) = 1 := by
    rw [← map_star, ← map_mul, smU2_mul_star, map_one]
  have h3 : star (toE (RenewalRealization.tableRepM y)) *
      toE (RenewalRealization.tableRepM y) = 1 := by
    rw [← map_star, ← map_mul, star_tableRepM_mul, map_one]
  have h4 : toE (RenewalRealization.tableRepM y) *
      star (toE (RenewalRealization.tableRepM y)) = 1 := by
    rw [← map_star, ← map_mul, tableRepM_mul_star, map_one]
  rw [Unitary.mem_iff]
  exact ⟨Prod.ext h1 h3, Prod.ext h2 h4⟩

theorem iota_mem_unitaryUnits (y : SMGaugeGroup) : iota y ∈ NativeGauge.unitaryUnits Alg :=
  ⟨⟨iotaA y, iotaA_mem_unitary y⟩, Units.ext rfl⟩

/-- Unitary matrices preserve the complex inner product. -/
theorem inner_toE_unitary {n : Type} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : star U * U = 1) (u v : EuclideanSpace ℂ n) :
    inner ℂ (toE U u) (toE U v) = inner ℂ u v := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply]
  have : ContinuousLinearMap.adjoint (toE U) * toE U = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← map_mul, hU, map_one]
  rw [this, ContinuousLinearMap.one_apply]

theorem norm_toE_unitary {n : Type} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : star U * U = 1) (v : EuclideanSpace ℂ n) : ‖toE U v‖ = ‖v‖ := by
  have h1 := @norm_sq_eq_re_inner ℂ _ _ _ _ (toE U v)
  have h2 := @norm_sq_eq_re_inner ℂ _ _ _ _ v
  rw [inner_toE_unitary hU, ← h2] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1


/-! ### The Yang–Mills metric with coefficients `g_j^{-2}` -/

local notation "TM" => RenewalRealization.tableRepM

/-- The `d_R` row indices. -/
def dRi (k : Fin 3) : Row := Sum.inr (Sum.inl (Sum.inr k))

/-- The `L_L` row indices. -/
def lRi (k : Fin 2) : Row := Sum.inl (Sum.inr k)

/-- The `e_R` row index. -/
def eRi (u : Unit) : Row := Sum.inr (Sum.inr u)

/-- The `d_R` row embedding `ℂ³ → ℂ^{rows}`. -/
def Pd : Matrix Row (Fin 3) ℂ := fun r k => if r = dRi k then 1 else 0

/-- The `L_L` row embedding `ℂ² → ℂ^{rows}`. -/
def Pl : Matrix Row (Fin 2) ℂ := fun r k => if r = lRi k then 1 else 0

/-- The `e_R` row embedding `ℂ → ℂ^{rows}`. -/
def Pe : Matrix Row Unit ℂ := fun r k => if r = eRi k then 1 else 0

theorem TM_Pd (y : SMGaugeGroup) : TM y * Pd = Pd * smU3 y := by
  ext r k
  simp only [Matrix.mul_apply, Pd, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [RenewalRealization.tableRepM_apply]
  rcases r with ((q | l) | ((u | d) | e)) <;> simp [dRi, fromBlocks]

theorem Pdt_TM (y : SMGaugeGroup) : Pdᵀ * TM y = smU3 y * Pdᵀ := by
  ext k r
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Pd, mul_ite, mul_one, mul_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [RenewalRealization.tableRepM_apply]
  rcases r with ((q | l) | ((u | d) | e)) <;> simp [dRi, fromBlocks]

theorem TM_Pl (y : SMGaugeGroup) :
    TM y * Pl = Pl * ((smU2 y).det ^ (-1 : ℤ) • smU2 y) := by
  ext r k
  simp only [Matrix.mul_apply, Pl, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [RenewalRealization.tableRepM_apply]
  rcases r with ((q | l) | ((u | d) | e)) <;> simp [lRi, fromBlocks]

theorem Plt_TM (y : SMGaugeGroup) :
    Plᵀ * TM y = ((smU2 y).det ^ (-1 : ℤ) • smU2 y) * Plᵀ := by
  ext k r
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Pl, mul_ite, mul_one, mul_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [RenewalRealization.tableRepM_apply]
  rcases r with ((q | l) | ((u | d) | e)) <;> simp [lRi, fromBlocks]

theorem TM_Pe (y : SMGaugeGroup) :
    TM y * Pe = Pe * ((smU2 y).det ^ (-1 : ℤ) • (1 : Matrix Unit Unit ℂ)) := by
  ext r k
  simp only [Matrix.mul_apply, Pe, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [RenewalRealization.tableRepM_apply]
  rcases r with ((q | l) | ((u | d) | e)) <;> simp [eRi, fromBlocks]

theorem Pet_TM (y : SMGaugeGroup) :
    Peᵀ * TM y = ((smU2 y).det ^ (-1 : ℤ) • (1 : Matrix Unit Unit ℂ)) * Peᵀ := by
  ext k r
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Pe, mul_ite, mul_one, mul_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [RenewalRealization.tableRepM_apply]
  rcases r with ((q | l) | ((u | d) | e)) <;> simp [eRi, fromBlocks]

/-- The colour (`d_R`) block. -/
def dBlk (M : Matrix Row Row ℂ) : Matrix (Fin 3) (Fin 3) ℂ := Pdᵀ * M * Pd

/-- The weak (`L_L`) block. -/
def lBlk (M : Matrix Row Row ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Plᵀ * M * Pl

/-- The hypercharge (`e_R`) entry. -/
def eBlk (M : Matrix Row Row ℂ) : Matrix Unit Unit ℂ := Peᵀ * M * Pe

theorem det_smU2_inv (y : SMGaugeGroup) : (smU2 y⁻¹).det = star (smU2 y).det := by
  rw [RenewalRealization.smU2_inv, star_eq_conjTranspose, det_conjTranspose]

theorem chi_mul_chi_inv (y : SMGaugeGroup) :
    (smU2 y).det ^ (-1 : ℤ) * (smU2 y⁻¹).det ^ (-1 : ℤ) = 1 := by
  rw [det_smU2_inv, _root_.zpow_neg_one, _root_.zpow_neg_one, ← mul_inv, mul_comm]
  have h := smChi_star y
  simp only [smChi_apply] at h
  rw [h, inv_one]

theorem dBlk_conj (y : SMGaugeGroup) (M : Matrix Row Row ℂ) :
    dBlk (TM y * M * TM y⁻¹) = smU3 y * dBlk M * star (smU3 y) := by
  calc Pdᵀ * (TM y * M * TM y⁻¹) * Pd = (Pdᵀ * TM y) * M * (TM y⁻¹ * Pd) := by
        simp only [Matrix.mul_assoc]
    _ = (smU3 y * Pdᵀ) * M * (Pd * smU3 y⁻¹) := by rw [Pdt_TM, TM_Pd]
    _ = smU3 y * dBlk M * star (smU3 y) := by
        rw [RenewalRealization.smU3_inv, dBlk]; simp only [Matrix.mul_assoc]

theorem lBlk_conj (y : SMGaugeGroup) (M : Matrix Row Row ℂ) :
    lBlk (TM y * M * TM y⁻¹) = smU2 y * lBlk M * star (smU2 y) := by
  calc Plᵀ * (TM y * M * TM y⁻¹) * Pl = (Plᵀ * TM y) * M * (TM y⁻¹ * Pl) := by
        simp only [Matrix.mul_assoc]
    _ = ((smU2 y).det ^ (-1 : ℤ) • smU2 y * Plᵀ) * M *
        (Pl * ((smU2 y⁻¹).det ^ (-1 : ℤ) • smU2 y⁻¹)) := by rw [Plt_TM, TM_Pl]
    _ = ((smU2 y⁻¹).det ^ (-1 : ℤ) * (smU2 y).det ^ (-1 : ℤ)) •
        (smU2 y * lBlk M * smU2 y⁻¹) := by
        simp only [lBlk, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    _ = smU2 y * lBlk M * star (smU2 y) := by
        rw [mul_comm, chi_mul_chi_inv, one_smul, RenewalRealization.smU2_inv]

theorem eBlk_conj (y : SMGaugeGroup) (M : Matrix Row Row ℂ) :
    eBlk (TM y * M * TM y⁻¹) = eBlk M := by
  calc Peᵀ * (TM y * M * TM y⁻¹) * Pe = (Peᵀ * TM y) * M * (TM y⁻¹ * Pe) := by
        simp only [Matrix.mul_assoc]
    _ = ((smU2 y).det ^ (-1 : ℤ) • (1 : Matrix Unit Unit ℂ) * Peᵀ) * M *
        (Pe * ((smU2 y⁻¹).det ^ (-1 : ℤ) • (1 : Matrix Unit Unit ℂ))) := by rw [Pet_TM, TM_Pe]
    _ = ((smU2 y⁻¹).det ^ (-1 : ℤ) * (smU2 y).det ^ (-1 : ℤ)) • eBlk M := by
        simp only [eBlk, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
          Matrix.one_mul, Matrix.mul_one]
    _ = eBlk M := by rw [mul_comm, chi_mul_chi_inv, one_smul]

/-- The traceless part `A - (tr A / n) 1`. -/
def tl {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Matrix n n ℂ :=
  A - (A.trace / Fintype.card n) • 1

/-- The real trace form `Re tr(A^* B)`. -/
def frob {n : Type} [Fintype n] (A B : Matrix n n ℂ) : ℝ := (Aᴴ * B).trace.re

section Invariance

variable {n : Type} [Fintype n] [DecidableEq n]

theorem tl_conj {U : Matrix n n ℂ} (h1 : star U * U = 1) (h2 : U * star U = 1)
    (A : Matrix n n ℂ) : tl (U * A * star U) = U * tl A * star U := by
  have ht : (U * A * star U).trace = A.trace := by
    rw [Matrix.trace_mul_cycle, h1, Matrix.one_mul]
  simp only [tl, ht, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, h2]

theorem frob_conj {U : Matrix n n ℂ} (h1 : star U * U = 1) (A B : Matrix n n ℂ) :
    frob (U * A * star U) (U * B * star U) = frob A B := by
  have h1' : Uᴴ * U = 1 := h1
  have e : (U * A * star U)ᴴ * (U * B * star U) = U * (Aᴴ * B) * star U := by
    simp only [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, h1', Matrix.one_mul]
  rw [frob, e, Matrix.trace_mul_cycle, h1, Matrix.one_mul, frob]

theorem frob_add_left (A A' B : Matrix n n ℂ) : frob (A + A') B = frob A B + frob A' B := by
  simp only [frob, conjTranspose_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re]

theorem frob_add_right (A B B' : Matrix n n ℂ) : frob A (B + B') = frob A B + frob A B' := by
  simp only [frob, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

theorem frob_smul_left (r : ℝ) (A B : Matrix n n ℂ) : frob (r • A) B = r * frob A B := by
  simp only [frob, conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul]

theorem frob_smul_right (r : ℝ) (A B : Matrix n n ℂ) : frob A (r • B) = r * frob A B := by
  simp only [frob, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem tl_add (A B : Matrix n n ℂ) : tl (A + B) = tl A + tl B := by
  simp only [tl, Matrix.trace_add, add_div, add_smul]
  abel

theorem tl_smul (r : ℝ) (A : Matrix n n ℂ) : tl (r • A) = r • tl A := by
  simp only [tl, Matrix.trace_smul, smul_sub, smul_div_assoc, smul_assoc]

end Invariance

theorem dBlk_add (M N : Matrix Row Row ℂ) : dBlk (M + N) = dBlk M + dBlk N := by
  simp only [dBlk, Matrix.mul_add, Matrix.add_mul]

theorem lBlk_add (M N : Matrix Row Row ℂ) : lBlk (M + N) = lBlk M + lBlk N := by
  simp only [lBlk, Matrix.mul_add, Matrix.add_mul]

theorem eBlk_add (M N : Matrix Row Row ℂ) : eBlk (M + N) = eBlk M + eBlk N := by
  simp only [eBlk, Matrix.mul_add, Matrix.add_mul]

theorem dBlk_smul (r : ℝ) (M : Matrix Row Row ℂ) : dBlk (r • M) = r • dBlk M := by
  simp only [dBlk, Matrix.mul_smul, Matrix.smul_mul]

theorem lBlk_smul (r : ℝ) (M : Matrix Row Row ℂ) : lBlk (r • M) = r • lBlk M := by
  simp only [lBlk, Matrix.mul_smul, Matrix.smul_mul]

theorem eBlk_smul (r : ℝ) (M : Matrix Row Row ℂ) : eBlk (r • M) = r • eBlk M := by
  simp only [eBlk, Matrix.mul_smul, Matrix.smul_mul]

/-- **The Yang–Mills metric** on the fermion block:
`2g₃⁻² ⟨D°, D'°⟩ + 2g₂⁻² ⟨L°, L'°⟩ + g₁⁻² ⟨E, E'⟩`. -/
def ymForm (θ : CoefficientBank (Fin 3)) (M N : Matrix Row Row ℂ) : ℝ :=
  2 / θ.g3 ^ 2 * frob (tl (dBlk M)) (tl (dBlk N)) +
    2 / θ.g2 ^ 2 * frob (tl (lBlk M)) (tl (lBlk N)) +
    1 / θ.g1 ^ 2 * frob (eBlk M) (eBlk N)

/-- `Ad_{G_SM}`-invariance of the Yang–Mills metric. -/
theorem ymForm_conj (θ : CoefficientBank (Fin 3)) (y : SMGaugeGroup) (M N : Matrix Row Row ℂ) :
    ymForm θ (TM y * M * TM y⁻¹) (TM y * N * TM y⁻¹) = ymForm θ M N := by
  simp only [ymForm, dBlk_conj, lBlk_conj, eBlk_conj, tl_conj (star_smU3_mul y) (smU3_mul_star y),
    tl_conj (star_smU2_mul y) (smU2_mul_star y), frob_conj (star_smU3_mul y),
    frob_conj (star_smU2_mul y)]

/-- The Yang–Mills metric as a real bilinear form. -/
def ymBil (θ : CoefficientBank (Fin 3)) : Matrix Row Row ℂ →ₗ[ℝ] Matrix Row Row ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (ymForm θ)
    (fun M M' N => by
      simp only [ymForm, dBlk_add, lBlk_add, eBlk_add, tl_add, frob_add_left]; ring)
    (fun r M N => by
      simp only [ymForm, dBlk_smul, lBlk_smul, eBlk_smul, tl_smul, frob_smul_left, smul_eq_mul]
      ring)
    (fun M N N' => by
      simp only [ymForm, dBlk_add, lBlk_add, eBlk_add, tl_add, frob_add_right]; ring)
    (fun r M N => by
      simp only [ymForm, dBlk_smul, lBlk_smul, eBlk_smul, tl_smul, frob_smul_right, smul_eq_mul]
      ring)

/-- A real bilinear form on a finite-dimensional space as a continuous bilinear map. -/
def bilinCLM {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ B)

theorem bilinCLM_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v : V) : bilinCLM B u v = B u v := rfl

/-- The fermion block of the gauge algebra, as matrices. -/
def inL : Alg →ₗ[ℝ] Matrix Row Row ℂ :=
  ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Row)).symm.toAlgEquiv.toLinearEquiv.toLinearMap.restrictScalars
    ℝ) ∘ₗ LinearMap.snd ℝ _ _

theorem inL_apply (X : Alg) : inL X = (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Row)).symm X.2 := rfl

theorem inL_conj (y : SMGaugeGroup) (X : Alg) :
    inL (iotaA y * X * iotaA y⁻¹) = TM y * inL X * TM y⁻¹ := by
  simp only [inL_apply, iotaA_apply, Prod.snd_mul, map_mul, StarAlgEquiv.symm_apply_apply]

/-- **The Yang–Mills metric on the gauge algebra.** -/
def ipA (θ : CoefficientBank (Fin 3)) : Alg →L[ℝ] Alg →L[ℝ] ℝ :=
  bilinCLM ((ymBil θ).compl₁₂ inL inL)

theorem ipA_apply (θ : CoefficientBank (Fin 3)) (X Y : Alg) :
    ipA θ X Y = ymForm θ (inL X) (inL Y) := rfl

/-! ### The representations `ρ_H`, `ρ_S`, the spin representation, gammas and Yukawa map -/

/-- `ρ_H`: projection onto the Higgs block. -/
def rhoHA : Alg →ₐ[ℝ] (EH →L[ℝ] EH) :=
  (restrictR EH).comp (AlgHom.fst ℝ (EH →L[ℂ] EH) (ER →L[ℂ] ER))

/-- `ρ_S`: the fermion block acting as `1_spin ⊗ 1_gen ⊗ X`. -/
def rhoSA : Alg →ₐ[ℝ] (SF →L[ℝ] SF) :=
  RF.comp ((liftRow.restrictScalars ℝ).comp
    (((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Row)).symm.toAlgEquiv.toAlgHom.restrictScalars ℝ).comp
      (AlgHom.snd ℝ (EH →L[ℂ] EH) (ER →L[ℂ] ER))))

theorem rhoHA_iota (y : SMGaugeGroup) (v : EH) : rhoHA (iotaA y) v = toE (smU2 y) v := rfl

theorem rhoSA_iota (y : SMGaugeGroup) : rhoSA (iotaA y) = RF (fibreRep SpinI .minimal y) := by
  show RF (liftRow ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Row)).symm
    (toE (RenewalRealization.tableRepM y)))) = _
  rw [StarAlgEquiv.symm_apply_apply]
  rfl

/-- `A ↦ A ⊗ 1_gen ⊗ 1_row` as a real-linear map. -/
def spinOpL : Matrix SpinI SpinI ℂ →ₗ[ℝ] Matrix FibI FibI ℂ where
  toFun A := spinOp .minimal A
  map_add' A B := by simp only [spinOp, add_kronecker]
  map_smul' r A := by simp only [spinOp, smul_kronecker, RingHom.id_apply]

/-- The spin representation `σ(ω) ⊗ 1` on `𝓢`. -/
def sigmaA : Mat →L[ℝ] (SF →L[ℝ] SF) :=
  LinearMap.toContinuousLinearMap (RF.toLinearMap ∘ₗ spinOpL ∘ₗ sigmaL)

theorem sigmaA_apply (ω : Mat) : sigmaA ω = RF (spinOp .minimal (sigmaL ω)) := rfl

/-- The gamma matrices `γ^a ⊗ 1` on `𝓢`. -/
def gamA (a : Fin 4) : SF →L[ℝ] SF := RF (spinOp .minimal (gam a))

/-! #### Real linearity of the Yukawa blocks -/

theorem higgsConj_add (H H' : Fin 2 → ℂ) : higgsConj (H + H') = higgsConj H + higgsConj H' := by
  funext k; fin_cases k <;> simp [higgsConj, star_add] <;> ring

theorem higgsConj_smul (r : ℝ) (H : Fin 2 → ℂ) : higgsConj (r • H) = r • higgsConj H := by
  funext k; fin_cases k <;> simp [higgsConj, star_smul]

theorem fromCols_add' {m n₁ n₂ : Type*} (A A' : Matrix m n₁ ℂ) (B B' : Matrix m n₂ ℂ) :
    fromCols (A + A') (B + B') = fromCols A B + fromCols A' B' := by
  ext i (j | j) <;> simp

theorem fromCols_smul' {m n₁ n₂ : Type*} (r : ℝ) (A : Matrix m n₁ ℂ) (B : Matrix m n₂ ℂ) :
    fromCols (r • A) (r • B) = r • fromCols A B := by
  ext i (j | j) <;> simp

theorem tQu_add (H H' : Fin 2 → ℂ) : tQu (H + H') = tQu H + tQu H' := by
  ext p b; simp only [tQu, higgsConj_add, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp

theorem tQd_add (H H' : Fin 2 → ℂ) : tQd (H + H') = tQd H + tQd H' := by
  ext p b; simp only [tQd, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp

theorem tLe_add (H H' : Fin 2 → ℂ) : tLe (H + H') = tLe H + tLe H' := by
  ext p b; simp [tLe]

theorem tQu_smul (r : ℝ) (H : Fin 2 → ℂ) : tQu (r • H) = r • tQu H := by
  ext p b; simp only [tQu, higgsConj_smul, Matrix.smul_apply, Pi.smul_apply]; split_ifs <;> simp

theorem tQd_smul (r : ℝ) (H : Fin 2 → ℂ) : tQd (r • H) = r • tQd H := by
  ext p b; simp only [tQd, Matrix.smul_apply, Pi.smul_apply]; split_ifs <;> simp

theorem tLe_smul (r : ℝ) (H : Fin 2 → ℂ) : tLe (r • H) = r • tLe H := by
  ext p b; simp [tLe]

theorem leftBlock_add (Y : YukawaBank) (H H' : Fin 2 → ℂ) :
    leftBlock Y (H + H') = leftBlock Y H + leftBlock Y H' := by
  simp only [leftBlock, tQu_add, tQd_add, tLe_add, add_kronecker, fromCols_add', fromBlocks_add,
    add_zero]

theorem leftBlock_smul (Y : YukawaBank) (r : ℝ) (H : Fin 2 → ℂ) :
    leftBlock Y (r • H) = r • leftBlock Y H := by
  simp only [leftBlock, tQu_smul, tQd_smul, tLe_smul, smul_kronecker, fromCols_smul',
    fromBlocks_smul, smul_zero]

theorem yukawaMin_add (Y : YukawaBank) (H H' : Fin 2 → ℂ) :
    yukawaMin Y (H + H') = yukawaMin Y H + yukawaMin Y H' := by
  simp only [yukawaMin, hermBlock, leftBlock_add, conjTranspose_add, fromBlocks_add, add_zero]

theorem yukawaMin_smul (Y : YukawaBank) (r : ℝ) (H : Fin 2 → ℂ) :
    yukawaMin Y (r • H) = r • yukawaMin Y H := by
  simp only [yukawaMin, hermBlock, leftBlock_smul, conjTranspose_smul, star_trivial,
    fromBlocks_smul, smul_zero]

theorem yM_add (θ : CoefficientBank (Fin 3)) (H H' : Fin 2 → ℂ) :
    RenewalRealization.yM θ (H + H') = RenewalRealization.yM θ H + RenewalRealization.yM θ H' := by
  simp only [RenewalRealization.yM, yukawaMin_add, submatrix_add, Pi.add_apply]

theorem yM_smul (θ : CoefficientBank (Fin 3)) (r : ℝ) (H : Fin 2 → ℂ) :
    RenewalRealization.yM θ (r • H) = r • RenewalRealization.yM θ H := by
  simp only [RenewalRealization.yM, yukawaMin_smul, submatrix_smul, Pi.smul_apply]

/-- **The Yukawa map** `H ↦ 1_spin ⊗ 𝓜_𝐘(H)` (`lem:SM-descent`, minimal branch), real-linear. -/
def yukL (θ : CoefficientBank (Fin 3)) : EH →ₗ[ℝ] Matrix FibI FibI ℂ where
  toFun H := internalOp SpinI (internalCast (RenewalRealization.yM θ (WithLp.ofLp H)))
  map_add' H H' := by
    simp only [WithLp.ofLp_add, yM_add, map_add, internalOp_add]
  map_smul' r H := by
    simp only [WithLp.ofLp_smul, yM_smul, RingHom.id_apply]
    rw [show internalCast (r • RenewalRealization.yM θ (WithLp.ofLp H)) =
      r • internalCast (RenewalRealization.yM θ (WithLp.ofLp H)) from rfl, internalOp_smul]

/-- The Yukawa map as continuous real-linear operators on `𝓢`. -/
def yukA (θ : CoefficientBank (Fin 3)) : EH →L[ℝ] (SF →L[ℝ] SF) :=
  LinearMap.toContinuousLinearMap (RF.toLinearMap ∘ₗ yukL θ)

theorem yukA_apply (θ : CoefficientBank (Fin 3)) (H : EH) :
    yukA θ H = RF (internalOp SpinI (internalCast (RenewalRealization.yM θ (WithLp.ofLp H)))) :=
  rfl

/-- The descent representation on generation × rows is `1_gen ⊗ tableRep`. -/
theorem rhoMin_submatrix (y : SMGaugeGroup) :
    (rhoMin y).submatrix RenewalRealization.genEquiv RenewalRealization.genEquiv =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ TM y := by
  ext ⟨g, r⟩ ⟨g', r'⟩
  simp only [submatrix_apply, RenewalRealization.rhoMin_genEquiv, kronecker_apply]
  ring

/-- **Covariance of the Yukawa blocks**: `𝓜(U₂ H) = ρ(y) 𝓜(H) ρ(y)⁻¹`. -/
theorem yM_covariant (θ : CoefficientBank (Fin 3)) (y : SMGaugeGroup) (H : Fin 2 → ℂ) :
    RenewalRealization.yM θ (smU2 y *ᵥ H) =
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ TM y) * RenewalRealization.yM θ H *
        ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ TM y⁻¹) := by
  have hc := yukawaMin_covariant (RenewalRealization.ybank θ) y H
  have hs : (rhoMin y * yukawaMin (RenewalRealization.ybank θ) H).submatrix
      RenewalRealization.genEquiv RenewalRealization.genEquiv =
      (yukawaMin (RenewalRealization.ybank θ) (repH y *ᵥ H) * rhoMin y).submatrix
      RenewalRealization.genEquiv RenewalRealization.genEquiv := by rw [hc]
  rw [← submatrix_mul_equiv _ _ _ RenewalRealization.genEquiv,
    ← submatrix_mul_equiv _ _ _ RenewalRealization.genEquiv, rhoMin_submatrix] at hs
  have hR : ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ TM y) * ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ TM y⁻¹)
      = 1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul, ← map_mul, mul_inv_cancel, map_one, one_kronecker_one]
  change _ = ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ TM y) * RenewalRealization.yM θ H *
        ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ TM y⁻¹)
  rw [show RenewalRealization.yM θ H = (yukawaMin (RenewalRealization.ybank θ) H).submatrix
    RenewalRealization.genEquiv RenewalRealization.genEquiv from rfl, hs,
    show RenewalRealization.yM θ (smU2 y *ᵥ H) = (yukawaMin (RenewalRealization.ybank θ)
      (smU2 y *ᵥ H)).submatrix RenewalRealization.genEquiv RenewalRealization.genEquiv from rfl,
    Matrix.mul_assoc, hR, Matrix.mul_one]
  rfl

/-! ### The covariant packet -/

/-- **The Standard-Model native packet** for the coefficient bank `θ`. -/
def smData (θ : CoefficientBank (Fin 3)) : NativeDensity.Data Alg EH SF where
  κ := θ.kappa
  Λ := θ.Lambda
  lamH := θ.lambdaH
  vH := θ.vH
  ipA := ipA θ
  hermH := innerSL ℝ
  ρH := rhoHA
  ρH_cont := LinearMap.continuous_of_finiteDimensional rhoHA.toLinearMap
  ρS := rhoSA
  ρS_cont := LinearMap.continuous_of_finiteDimensional rhoSA.toLinearMap
  σ := sigmaA
  γ := gamA
  yukawa := yukA θ

theorem mem_smG {g : Algˣ} (hg : g ∈ smG) : ∃ y, g = iota y := by
  obtain ⟨y, rfl⟩ := hg
  exact ⟨y, rfl⟩

/-- **The covariant Standard-Model native packet** (`NativeGauge.CovData`): every standing
covariance assumption of the representation packet holds for `G = S(U(3)×U(2))`. -/
def smCovData (θ : CoefficientBank (Fin 3)) : NativeGauge.CovData Alg EH SF where
  toData := smData θ
  G := smG
  norm_conj g hg X := by
    obtain ⟨y, rfl⟩ := mem_smG hg
    exact NativeGauge.norm_conj_unitaryUnits (iota_mem_unitaryUnits y) X
  ipA_conj g hg X Y := by
    obtain ⟨y, rfl⟩ := mem_smG hg
    show ipA θ _ _ = ipA θ X Y
    rw [ipA_apply, ipA_apply, coe_iota, coe_iota_inv, inL_conj, inL_conj, ymForm_conj]
  hermH_inv g hg u v := by
    obtain ⟨y, rfl⟩ := mem_smG hg
    show innerSL ℝ (rhoHA (iota y) u) (rhoHA (iota y) v) = innerSL ℝ u v
    rw [innerSL_apply_apply, innerSL_apply_apply, coe_iota, rhoHA_iota, rhoHA_iota]
    exact congrArg Complex.re (inner_toE_unitary (star_smU2_mul y) u v)
  σ_comm g hg m := by
    obtain ⟨y, rfl⟩ := mem_smG hg
    show Commute (rhoSA (iota y)) (sigmaA m)
    rw [coe_iota, rhoSA_iota, sigmaA_apply, fibreRep_apply]
    exact (show Commute (internalOp SpinI (internalRep .minimal y)) (spinOp .minimal (sigmaL m))
      from (spinOp_mul_internalOp _ _).symm).map RF
  γ_comm g hg a := by
    obtain ⟨y, rfl⟩ := mem_smG hg
    show Commute (rhoSA (iota y)) (gamA a)
    rw [coe_iota, rhoSA_iota, gamA, fibreRep_apply]
    exact (show Commute (internalOp SpinI (internalRep .minimal y)) (spinOp .minimal (gam a))
      from (spinOp_mul_internalOp _ _).symm).map RF
  yukawa_cov g hg H := by
    obtain ⟨y, rfl⟩ := mem_smG hg
    show yukA θ (rhoHA (iota y) H) = rhoSA (iota y) * yukA θ H * rhoSA ((iota y)⁻¹ : Algˣ)
    rw [coe_iota, coe_iota_inv, rhoSA_iota, rhoSA_iota, yukA_apply, yukA_apply, ← map_mul,
      ← map_mul]
    congr 1
    have hH : WithLp.ofLp (rhoHA (iotaA y) H) = smU2 y *ᵥ WithLp.ofLp H := by
      rw [rhoHA_iota, Matrix.ofLp_toEuclideanCLM]
    rw [hH, yM_covariant, fibreRep_apply, fibreRep_apply, internalOp_mul, internalOp_mul,
      map_mul, map_mul]
    rfl
  ρS_isom g hg v := by
    obtain ⟨y, rfl⟩ := mem_smG hg
    show ‖rhoSA (iota y) v‖ = ‖v‖
    rw [coe_iota, rhoSA_iota, RF_apply, norm_toE_unitary (star_fibreRep_mul y)]

end NativeSMPacket
end RenewalGeometry
