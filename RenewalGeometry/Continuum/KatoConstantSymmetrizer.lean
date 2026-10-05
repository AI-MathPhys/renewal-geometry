/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoGalerkinCFL
import RenewalGeometry.Continuum.KatoPhysicalIdentification

/-!
# Kato's theory for systems symmetric in a fixed positive component norm

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` of the
Einstein–Standard-Model action-closure manuscript: the system `eq:generated-symmetric-system`
`U_t + A^i(U)∂_iU = F(U)` is the actual-jet system of `prop:actual-jet-writer`, whose principal
matrices "are symmetric in the fixed positive component norm after realification", i.e.
`M A^i(v)` is symmetric for a fixed positive-definite `M` (the block inner product), while
`A^i(v)` itself need not be symmetric.  The constant change of variables `V = S U`, `S = √M`
(`exists_sqrt_factor`), conjugates the system to `V_t + S A^i(S⁻¹V) S⁻¹ ∂_iV = S F(S⁻¹V)` with
Euclidean-symmetric principal part (`trA_symm`) and commutes with the Fourier truncation.

* `trA`, `trF`, `trA_symm`, `contDiff_trA`, `contDiff_trF` — the conjugated system;
* `genP_tr`, `twoSided_of_tr` — classical solutions transfer back;
  **`kato_two_sided_symmetrizer`** — Kato's local existence on `(-T, T) × 𝕋^d` for `M`-symmetric
  systems;
* `actGS`, `GN_tr` (`G'_N(S a) = S G_N(a)`), `P0_act` — the Galerkin schemes transfer;
  **`galerkin_symmetrizer`** (`eq:generated-Galerkin`) and **`midpoint_cfl_symmetrizer`**
  (`eq:generated-midpoint`, `eq:generated-CFL`, `eq:generated-uniform`) for `M`-symmetric
  systems, with cutoff-uniform `H^q` bounds.
* Non-vacuity: a non-symmetric `A^1 = [[0, 2], [1, 0]]` symmetric for `M = diag(1, 2)`.

Disclosed rendering: `Σ = 𝕋^d`; coefficients smooth on all of `ℝ^n`; the `H^q` norms are the
Euclidean ones (equivalent to the `M`-weighted norms with constants depending only on `M`).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.KatoSymm

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin Matrix

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### The conjugated system -/

/-- The principal matrix `A^i(v)` as a matrix. -/
def amat (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (i : Fin d) (v : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => A i a b v

/-- The conjugated principal matrices `S A^i(S⁻¹ v) S⁻¹` of the variable `V = S U`. -/
def trA (S Si : Matrix (Fin n) (Fin n) ℝ) (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) :
    Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ :=
  fun i a b v => (S * amat A i (Si *ᵥ v) * Si) a b

/-- The conjugated lower-order term `S F(S⁻¹ v)`. -/
def trF (S Si : Matrix (Fin n) (Fin n) ℝ) (F : Fin n → (Fin n → ℝ) → ℝ) :
    Fin n → (Fin n → ℝ) → ℝ :=
  fun a v => (S *ᵥ fun c => F c (Si *ᵥ v)) a

theorem contDiff_mulVec (B : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ∞ fun v : Fin n → ℝ => B *ᵥ v :=
  (Matrix.mulVecLin B).toContinuousLinearMap.contDiff

theorem contDiff_trA {S Si : Matrix (Fin n) (Fin n) ℝ}
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) :
    ∀ i a b, ContDiff ℝ ∞ (trA S Si A i a b) := by
  intro i a b
  have e : trA S Si A i a b = fun v => ∑ e, (∑ c, S a c * A i c e (Si *ᵥ v)) * Si e b := by
    funext v; simp [trA, amat, Matrix.mul_apply]
  rw [e]
  exact ContDiff.sum fun e _ => (ContDiff.sum fun c _ =>
    contDiff_const.mul ((hA i c e).comp (contDiff_mulVec Si))).mul contDiff_const

theorem contDiff_trF {S Si : Matrix (Fin n) (Fin n) ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) : ∀ a, ContDiff ℝ ∞ (trF S Si F a) := by
  intro a
  have e : trF S Si F a = fun v => ∑ c, S a c * F c (Si *ᵥ v) := by
    funext v; simp [trF, Matrix.mulVec, dotProduct]
  rw [e]
  exact ContDiff.sum fun c _ => contDiff_const.mul ((hF c).comp (contDiff_mulVec Si))

/-- **Symmetry of the conjugated system**: if every `A^i(v)` is symmetric for the fixed inner
product `⟨ξ, η⟩_M = ξᵀMη` (`M A^i(v)` symmetric) and `M = SᵀS` with `S⁻¹ = Si`, then the
conjugated matrices `S A^i S⁻¹` are symmetric. -/
theorem trA_symm {S Si M : Matrix (Fin n) (Fin n) ℝ} (hSSi : S * Si = 1) (hM : Sᵀ * S = M)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    (hMA : ∀ i v, (M * amat A i v)ᵀ = M * amat A i v) :
    ∀ i a b v, trA S Si A i a b v = trA S Si A i b a v := by
  intro i a b v
  set B := amat A i (Si *ᵥ v)
  have hSit : Siᵀ * Sᵀ = 1 := by rw [← Matrix.transpose_mul, hSSi, Matrix.transpose_one]
  have key : S * B * Si = (S * B * Si)ᵀ := by
    have h1 : S * B * Si = Siᵀ * (M * B) * Si := by
      rw [← hM, ← Matrix.mul_assoc Siᵀ, ← Matrix.mul_assoc Siᵀ, hSit, Matrix.one_mul,
        Matrix.mul_assoc S]
    have h2 : (M * B)ᵀ = M * B := hMA i _
    rw [h1, Matrix.transpose_mul, Matrix.transpose_mul, h2, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  have := congrFun (congrFun key a) b
  simp only [Matrix.transpose_apply] at this
  exact this

/-- A positive-definite `M` factors as `M = SᵀS` with `S` invertible (`S = √M`). -/
theorem exists_sqrt_factor {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) :
    ∃ S Si : Matrix (Fin n) (Fin n) ℝ, Sᵀ * S = M ∧ S * Si = 1 ∧ Si * S = 1 := by
  classical
  open scoped MatrixOrder in
  have h0 : 0 ≤ M := hM.posSemidef.nonneg
  open scoped MatrixOrder in
  have hS : (CFC.sqrt M)ᵀ * CFC.sqrt M = M := by
    have hs : IsSelfAdjoint (CFC.sqrt M) := (CFC.sqrt_nonneg M).isSelfAdjoint
    have : (CFC.sqrt M)ᵀ = CFC.sqrt M := by
      have := hs.star_eq
      rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
    rw [this, CFC.sqrt_mul_sqrt_self M h0]
  open scoped MatrixOrder in
  have hdet : IsUnit (CFC.sqrt M).det := by
    have h1 : (CFC.sqrt M * CFC.sqrt M).det = M.det := by rw [CFC.sqrt_mul_sqrt_self M h0]
    rw [det_mul] at h1
    have h2 := hM.det_pos
    rw [isUnit_iff_ne_zero]
    intro h; rw [h, zero_mul] at h1; linarith
  open scoped MatrixOrder in
  exact ⟨CFC.sqrt M, (CFC.sqrt M)⁻¹, hS, Matrix.mul_nonsing_inv _ hdet,
    Matrix.nonsing_inv_mul _ hdet⟩

/-! ### Transfer of classical solutions -/

/-- The constant linear change of variables `U ↦ B U` on fields. -/
def act (B : Matrix (Fin n) (Fin n) ℝ) (U : Fin n → ST d → ℝ) : Fin n → ST d → ℝ :=
  fun b x => (B *ᵥ fun c => U c x) b

/-- The same change of variables on the spatial derivatives. -/
def actP (B : Matrix (Fin n) (Fin n) ℝ) (P : Fin n → Fin d → ST d → ℝ) :
    Fin n → Fin d → ST d → ℝ :=
  fun b i x => (B *ᵥ fun c => P c i x) b

theorem act_apply (B : Matrix (Fin n) (Fin n) ℝ) (U : Fin n → ST d → ℝ) (b : Fin n) (x : ST d) :
    act B U b x = ∑ c, B b c * U c x := by
  simp [act, Matrix.mulVec, dotProduct]

theorem actP_apply (B : Matrix (Fin n) (Fin n) ℝ) (P : Fin n → Fin d → ST d → ℝ) (b : Fin n)
    (i : Fin d) (x : ST d) : actP B P b i x = ∑ c, B b c * P c i x := by
  simp [actP, Matrix.mulVec, dotProduct]

theorem act_act {B C : Matrix (Fin n) (Fin n) ℝ} (U : Fin n → ST d → ℝ) :
    act B (act C U) = act (B * C) U := by
  funext b x
  simp only [act]
  have : (fun c => (C *ᵥ fun c => U c x) c) = C *ᵥ fun c => U c x := rfl
  rw [this, Matrix.mulVec_mulVec]

theorem act_one (U : Fin n → ST d → ℝ) : act 1 U = U := by
  funext b x; simp [act]

theorem genP_vec (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ) (x : ST d) :
    (fun b => genP A F U P b x) = (fun b => F b (fun c => U c x)) -
      ∑ i, amat A i (fun c => U c x) *ᵥ (fun c => P c i x) := by
  funext b
  simp [genP, amat, Matrix.mulVec, dotProduct, Finset.sum_apply]

/-- **The generator transforms covariantly**: `S⁻¹ G'(V, P') = G(S⁻¹V, S⁻¹P')`. -/
theorem genP_tr {S Si : Matrix (Fin n) (Fin n) ℝ} (hSiS : Si * S = 1)
    (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    (V : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ) (x : ST d) :
    (fun b => genP A F (act Si V) (actP Si P) b x) =
      Si *ᵥ fun c => genP (trA S Si A) (trF S Si F) V P c x := by
  rw [genP_vec, genP_vec]
  have hu : (fun c => act Si V c x) = Si *ᵥ fun c => V c x := rfl
  have hp : ∀ i, (fun c => actP Si P c i x) = Si *ᵥ fun c => P c i x := fun i => rfl
  have hF : (fun b => trF S Si F b (fun c => V c x)) =
      S *ᵥ fun c => F c (Si *ᵥ fun c => V c x) := rfl
  have hA : ∀ i, amat (trA S Si A) i (fun c => V c x) =
      S * amat A i (Si *ᵥ fun c => V c x) * Si := fun i => by
    ext a b; simp [amat, trA]
  simp only [hu, hp, hF, hA, Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hSiS, Matrix.one_mul, Matrix.one_mulVec]

/-- **Transfer of two-sided solutions**: a two-sided solution `(V, P')` of the conjugated system
with data `S U₀` gives the two-sided solution `(S⁻¹V, S⁻¹P')` of the original system with data
`U₀`. -/
theorem twoSided_of_tr {S Si : Matrix (Fin n) (Fin n) ℝ} (hSiS : Si * S = 1)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    {U₀ : Fin n → ST d → ℝ} {T : ℝ} {V : Fin n → ST d → ℝ} {P : Fin n → Fin d → ST d → ℝ}
    (h : TwoSidedSol (trA S Si A) (trF S Si F) (act S U₀) T V P) :
    TwoSidedSol A F U₀ T (act Si V) (actP Si P) := by
  refine ⟨fun b => ?_, fun b i => ?_, fun b k x => ?_, fun b i k x => ?_, fun b y => ?_,
    fun b i x => ?_, fun b t ht y => ?_⟩
  · rw [show act Si V b = fun x => ∑ c, Si b c * V c x from funext fun x => act_apply Si V b x]
    exact continuous_finsetSum _ fun c _ => continuous_const.mul (h.contU c)
  · rw [show actP Si P b i = fun x => ∑ c, Si b c * P c i x from
      funext fun x => actP_apply Si P b i x]
    exact continuous_finsetSum _ fun c _ => continuous_const.mul (h.contP c i)
  · simp only [act_apply, h.perU _ k x]
  · simp only [actP_apply, h.perP _ i k x]
  · have e : (fun c => V c (Fin.cons 0 y)) = fun c => act S U₀ c (Fin.cons 0 y) :=
      funext fun c => h.init c y
    have : act Si V b (Fin.cons 0 y) = act Si (act S U₀) b (Fin.cons 0 y) := by
      simp only [act, e]
    rw [this, act_act, hSiS, act_one]
  · simp only [act_apply, actP_apply]
    exact HasDerivAt.fun_sum fun c _ => (h.space c i x).const_mul _
  · have hd : HasDerivAt (fun s => act Si V b (Fin.cons s y))
        (∑ c, Si b c * genP (trA S Si A) (trF S Si F) V P c (Fin.cons t y)) t := by
      simp only [act_apply]
      exact HasDerivAt.fun_sum fun c _ => (h.time c t ht y).const_mul _
    have e := congrFun (genP_tr hSiS A F V P (Fin.cons t y)) b
    rw [e]
    simpa [Matrix.mulVec, dotProduct] using hd

/-- The `H^q` energy of `B U` is controlled by that of `U`:
`‖BU‖²_{H^q} ≤ n (Σ B²) ‖U‖²_{H^q}`. -/
theorem energyQ_act_le (B : Matrix (Fin n) (Fin n) ℝ) {U : Fin n → ST d → ℝ}
    (hU : ∀ b, ContDiff ℝ ∞ (U b)) (q : ℕ) (t : ℝ) :
    energyQ q (act B U) t ≤ (n * ∑ a, ∑ c, B a c ^ 2) * energyQ q U t := by
  have hE0 := energyQ_nonneg q U t
  have hb : ∀ a, Q q (act B U a) t ≤ n * ((∑ c, B a c ^ 2) * energyQ q U t) := by
    intro a
    have e : act B U a = fun x => ∑ c, B a c * U c x := funext fun x => act_apply B U a x
    rw [e]
    refine (Q_sum_le q Finset.univ (fun c => contDiff_const.mul (hU c)) t).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ∑ c, Q q (fun x => B a c * U c x) t = ∑ c, B a c ^ 2 * Q q (U c) t :=
          Finset.sum_congr rfl fun c _ => Q_const_mul q (hU c) _ t
      _ ≤ ∑ c, B a c ^ 2 * energyQ q U t := Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (KatoGalerkin.Q_le_energyQ q U t c) (sq_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  calc energyQ q (act B U) t = ∑ a, Q q (act B U a) t := rfl
    _ ≤ ∑ a, n * ((∑ c, B a c ^ 2) * energyQ q U t) := Finset.sum_le_sum fun a _ => hb a
    _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul]; ring

theorem contDiff_act (B : Matrix (Fin n) (Fin n) ℝ) {U : Fin n → ST d → ℝ}
    (hU : ∀ b, ContDiff ℝ ∞ (U b)) : ∀ b, ContDiff ℝ ∞ (act B U b) := fun b => by
  have e : act B U b = fun x => ∑ c, B b c * U c x := funext fun x => act_apply B U b x
  rw [e]; exact ContDiff.sum fun c _ => contDiff_const.mul (hU c)

theorem isSPeriodic_act (B : Matrix (Fin n) (Fin n) ℝ) {U : Fin n → ST d → ℝ}
    (hU : ∀ b, IsSPeriodic (U b)) : ∀ b, IsSPeriodic (act B U b) := fun b k x => by
  simp only [act_apply, hU _ k x]

/-- **Kato's local existence for systems symmetric in a fixed positive component norm**
(`thm:generated-dynamics`, `prop:actual-jet-writer`: "the matrices `𝒜^j` are symmetric in the
fixed positive component norm").  Let `M` be a positive-definite matrix and let every `A^i(v)`
be `M`-symmetric (`M A^i(v)` symmetric), `A^i`, `F` smooth, `m > d/2`, `q ≥ 2m`, `q ≥ m + 2`.
For every data radius `R₀` there is `T > 0` such that every smooth periodic datum with
`‖U₀‖_{H^q} ≤ R₀` has a classical solution of `∂_tU + Σ_i A^i(U)∂_iU = F(U)` on
`(-T, T) × 𝕋^d`.  (Reduction by the constant change of variables `V = √M U` to the Euclidean
symmetric case `kato_two_sided`.) -/
theorem kato_two_sided_symmetrizer {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    (hq2 : m + 2 ≤ q) {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (hMA : ∀ i v, (M * amat A i v)ᵀ = M * amat A i v) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) →
      (∀ b, IsSPeriodic (U₀ b)) → energyQ q U₀ 0 ≤ R₀ ^ 2 →
      ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ), TwoSidedSol A F U₀ T U P := by
  obtain ⟨S, Si, hSM, hSSi, hSiS⟩ := exists_sqrt_factor hM
  set cS := (n : ℝ) * ∑ a, ∑ c, S a c ^ 2 with hcS
  have hcS0 : 0 ≤ cS := by positivity
  obtain ⟨T, hT, hex⟩ := kato_two_sided (A := trA S Si A) (F := trF S Si F) hm hq hq2
    (contDiff_trA hA) (trA_symm hSSi hSM hMA) (contDiff_trF hF)
    (R₀ := Real.sqrt cS * R₀) (by positivity)
  refine ⟨T, hT, fun U₀ hU hUp hE => ?_⟩
  have hE' : energyQ q (act S U₀) 0 ≤ (Real.sqrt cS * R₀) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hcS0]
    exact (energyQ_act_le S hU q 0).trans (mul_le_mul_of_nonneg_left hE hcS0)
  obtain ⟨V, P, hV⟩ := hex (act S U₀) (contDiff_act S hU) (isSPeriodic_act S hUp) hE'
  exact ⟨_, _, twoSided_of_tr hSiS hV⟩

/-! ### Transfer of the spectral Galerkin and midpoint schemes -/

/-- The constant change of variables on the Galerkin space (componentwise in the modes; it
commutes with the Fourier truncation `P_N`). -/
def actGS (B : Matrix (Fin n) (Fin n) ℝ) {N : ℕ} (a : GS d n N) : GS d n N :=
  WithLp.toLp 2 fun p => ∑ c, B p.1 c * a (c, p.2)

theorem actGS_apply (B : Matrix (Fin n) (Fin n) ℝ) {N : ℕ} (a : GS d n N)
    (p : Fin n × KatoGalerkin.box (d := d) N) : actGS B a p = ∑ c, B p.1 c * a (c, p.2) := rfl

theorem actGS_add (B : Matrix (Fin n) (Fin n) ℝ) {N : ℕ} (a a' : GS d n N) :
    actGS B (a + a') = actGS B a + actGS B a' := by
  refine PiLp.ext fun p => ?_
  rw [PiLp.add_apply, actGS_apply, actGS_apply, actGS_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PiLp.add_apply, mul_add]

theorem actGS_smul (B : Matrix (Fin n) (Fin n) ℝ) {N : ℕ} (r : ℝ) (a : GS d n N) :
    actGS B (r • a) = r • actGS B a := by
  refine PiLp.ext fun p => ?_
  rw [PiLp.smul_apply, actGS_apply, actGS_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PiLp.smul_apply, smul_eq_mul]; ring

theorem actGS_mid (B : Matrix (Fin n) (Fin n) ℝ) {N : ℕ} (a a' : GS d n N) :
    actGS B (SpectralGalerkin.mid a a') = SpectralGalerkin.mid (actGS B a) (actGS B a') := by
  simp only [SpectralGalerkin.mid, actGS_smul, actGS_add]

theorem actGS_actGS (B C : Matrix (Fin n) (Fin n) ℝ) {N : ℕ} (a : GS d n N) :
    actGS B (actGS C a) = actGS (B * C) a := by
  refine PiLp.ext fun p => ?_
  simp only [actGS_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => by ring

theorem actGS_one {N : ℕ} (a : GS d n N) : actGS 1 a = a := by
  refine PiLp.ext fun p => ?_
  rw [actGS_apply]
  simp [Matrix.one_apply]

/-- `‖B a‖ ≤ √(Σ B²) ‖a‖` on the Galerkin space. -/
theorem norm_actGS_le (B : Matrix (Fin n) (Fin n) ℝ) {N : ℕ} (a : GS d n N) :
    ‖actGS B a‖ ≤ Real.sqrt (∑ b, ∑ c, B b c ^ 2) * ‖a‖ := by
  have hsq : ‖actGS B a‖ ^ 2 ≤ (∑ b, ∑ c, B b c ^ 2) * ‖a‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    calc ∑ b, ∑ k : KatoGalerkin.box (d := d) N, (actGS B a) (b, k) ^ 2
        ≤ ∑ b, ∑ k : KatoGalerkin.box (d := d) N, (∑ c, B b c ^ 2) * ∑ c, a (c, k) ^ 2 :=
          Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun k _ => by
            rw [actGS_apply]
            exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ b, ∑ c, B b c ^ 2) * ∑ c, ∑ k : KatoGalerkin.box (d := d) N, a (c, k) ^ 2 := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.mul_sum, Finset.sum_comm]
  have h0 : 0 ≤ Real.sqrt (∑ b, ∑ c, B b c ^ 2) * ‖a‖ := by positivity
  refine abs_le_of_sq_le_sq' ?_ h0 |>.2
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact hsq

theorem cf_actGS (q : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) {N : ℕ} (a : GS d n N) (b : Fin n)
    (k : Fin d → ℤ) : cf q (actGS B a) b k = ∑ c, B b c * cf q a c k := by
  unfold cf
  split_ifs with hk
  · rw [actGS_apply, Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => by ring
  · simp

theorem fld_actGS (q : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) {N : ℕ} (a : GS d n N) :
    fld q (actGS B a) = act B (fld q a) := by
  funext b x
  rw [act_apply, fld, tfs]
  simp only [cf_actGS, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [fld, tfs, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The spatial derivatives of a field, as `P`-data. -/
def pdOf (u : Fin n → ST d → ℝ) : Fin n → Fin d → ST d → ℝ := fun b i x => pd (u b) i.succ x

theorem genG_eq_genP (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    (u : Fin n → ST d → ℝ) (b : Fin n) (x : ST d) : genG A F u b x = genP A F u (pdOf u) b x :=
  rfl

theorem pdOf_act (B : Matrix (Fin n) (Fin n) ℝ) {u : Fin n → ST d → ℝ}
    (hu : ∀ b, ContDiff ℝ ∞ (u b)) : pdOf (act B u) = actP B (pdOf u) := by
  funext b i x
  rw [actP_apply]
  simp only [pdOf]
  have e : act B u b = fun x => ∑ c, B b c * u c x := funext fun x => act_apply B u b x
  rw [e]
  unfold SobolevOpen.pd
  rw [fderiv_fun_sum (fun c _ => ((hu c).differentiable (by simp) x).const_mul _)]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [fderiv_const_mul ((hu c).differentiable (by simp) x)]
  rfl

theorem actP_actP (B C : Matrix (Fin n) (Fin n) ℝ) (P : Fin n → Fin d → ST d → ℝ) :
    actP B (actP C P) = actP (B * C) P := by
  funext b i x
  simp only [actP]
  have : (fun c => (C *ᵥ fun c => P c i x) c) = C *ᵥ fun c => P c i x := rfl
  rw [this, Matrix.mulVec_mulVec]

theorem actP_one (P : Fin n → Fin d → ST d → ℝ) : actP 1 P = P := by
  funext b i x; simp [actP]

/-- **The generator of the conjugated system**: `G'(S U) = S G(U)`. -/
theorem genG_tr {S Si : Matrix (Fin n) (Fin n) ℝ} (hSSi : S * Si = 1) (hSiS : Si * S = 1)
    (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (x : ST d) :
    (fun b => genG (trA S Si A) (trF S Si F) (act S u) b x) =
      S *ᵥ fun c => genG A F u c x := by
  have h := genP_tr hSiS A F (act S u) (actP S (pdOf u)) x
  rw [act_act, hSiS, act_one, actP_actP, hSiS, actP_one] at h
  simp only [genG_eq_genP, pdOf_act S hu]
  rw [show (fun b => genP A F u (pdOf u) b x) = _ from h, Matrix.mulVec_mulVec, hSSi,
    Matrix.one_mulVec]

theorem coef_lincomb (B : Matrix (Fin n) (Fin n) ℝ) (b : Fin n) {g : Fin n → ST d → ℝ}
    (hg : ∀ c, Continuous (g c)) (t : ℝ) (k : Fin d → ℤ) :
    coef (fun x => ∑ c, B b c * g c x) t k = ∑ c, B b c * coef (g c) t k := by
  unfold coef
  have e : (fun x => casS k x * ∑ c, B b c * g c x) =
      fun x => ∑ c, B b c * (casS k x * g c x) := by
    funext x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  rw [e, sint_sum Finset.univ (f := fun c x => B b c * (casS k x * g c x))
    (fun c => continuous_const.mul ((contDiff_casS k).continuous.mul (hg c)))]
  exact Finset.sum_congr rfl fun c _ => sint_const_mul _ _ _

/-- **The projected generator commutes with the change of variables**:
`G'_N(S a) = S G_N(a)`. -/
theorem GN_tr {S Si : Matrix (Fin n) (Fin n) ℝ} (hSSi : S * Si = 1) (hSiS : Si * S = 1)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) (q : ℕ) {N : ℕ}
    (a : GS d n N) : GN (trA S Si A) (trF S Si F) q (actGS S a) = actGS S (GN A F q a) := by
  refine PiLp.ext fun p => ?_
  rw [GN_apply, actGS_apply, fld_actGS]
  have e : genG (trA S Si A) (trF S Si F) (act S (fld q a)) p.1 =
      fun x => ∑ c, S p.1 c * genG A F (fld q a) c x := by
    funext x
    have := congrFun (genG_tr hSSi hSiS A F (fun b => contDiff_fld q a b) x) p.1
    simpa [Matrix.mulVec, dotProduct] using this
  rw [e, coef_lincomb S p.1 (fun c => (contDiff_genG hA hF (fun b => contDiff_fld q a b) c).continuous),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [GN_apply]; ring

theorem P0_act (q N : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) {U₀ : Fin n → ST d → ℝ}
    (hU : ∀ b, Continuous (U₀ b)) : P0 q N (act B U₀) = actGS B (P0 (d := d) q N U₀) := by
  refine PiLp.ext fun p => ?_
  rw [actGS_apply]
  simp only [P0]
  show Real.sqrt (wq q p.2.1) * coef (act B U₀ p.1) 0 p.2.1 =
    ∑ c, B p.1 c * (Real.sqrt (wq q p.2.1) * coef (U₀ c) 0 p.2.1)
  rw [show act B U₀ p.1 = fun x => ∑ c, B p.1 c * U₀ c x from funext fun x => act_apply B U₀ p.1 x,
    coef_lincomb B p.1 hU, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **The CFL midpoint scheme for systems symmetric in a fixed positive component norm**
(`eq:generated-midpoint`, `eq:generated-CFL`, `eq:generated-uniform` for the block inner product
of `prop:actual-jet-writer`): with `M` positive definite and every `A^i(v)` `M`-symmetric, for every
data radius `R₀` there are `T > 0`, `R`, `c_* > 0`, `τ_* > 0` such that for every cutoff `N`, every
step `τ(N + 1) ≤ c_*`, `τ ≤ τ_*` and every finite initial state `‖U_{0,N}‖_{H^q} ≤ R₀`, the
implicit midpoint recursion `U^{j+1} = U^j + τ G_N((U^j + U^{j+1})/2)` exists on `[0, T]` with
`‖U^j‖_{H^q} ≤ R` (conjugation by `√M`, `midpoint_uniform_cfl`). -/
theorem midpoint_cfl_symmetrizer {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (hMA : ∀ i v, (M * amat A i v)ᵀ = M * amat A i v) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0, ∃ τstar > 0, ∀ (N : ℕ) (τ : ℝ), 0 < τ →
      τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τstar → ∀ a₀ : GS d n N, ‖a₀‖ ≤ R₀ →
      ∃ U : ℕ → GS d n N, U 0 = a₀ ∧ ∀ j : ℕ, (j : ℝ) * τ ≤ T →
        ‖U j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
          U (j + 1) = U j + τ • GN A F q (SpectralGalerkin.mid (U j) (U (j + 1)))) := by
  obtain ⟨S, Si, hSM, hSSi, hSiS⟩ := exists_sqrt_factor hM
  set cS := Real.sqrt (∑ b, ∑ c, S b c ^ 2) with hcS
  set cSi := Real.sqrt (∑ b, ∑ c, Si b c ^ 2) with hcSi
  obtain ⟨T, hT, R, hR, cstar, hc, τstar, hτs, CM, _, h⟩ := KatoCFL.midpoint_uniform_cfl
    (A := trA S Si A) (F := trF S Si F) hm hq (contDiff_trA hA) (trA_symm hSSi hSM hMA)
    (contDiff_trF hF) (R₀ := cS * R₀) (by positivity)
  refine ⟨T, hT, cSi * R, by positivity, cstar, hc, τstar, hτs,
    fun N τ hτ hcfl hτ' a₀ ha₀ => ?_⟩
  obtain ⟨V, hV0, hV⟩ := h N τ hτ hcfl hτ' (actGS S a₀)
    ((norm_actGS_le S a₀).trans (mul_le_mul_of_nonneg_left ha₀ (Real.sqrt_nonneg _)))
  have hVS : ∀ j, actGS S (actGS Si (V j)) = V j := fun j => by
    rw [actGS_actGS, hSSi, actGS_one]
  refine ⟨fun j => actGS Si (V j), ?_, fun j hj => ⟨?_, fun hj1 => ?_⟩⟩
  · simp only [hV0, actGS_actGS, hSiS, actGS_one]
  · exact (norm_actGS_le Si _).trans (mul_le_mul_of_nonneg_left (hV j hj).1 (Real.sqrt_nonneg _))
  · have hrec := ((hV j hj).2 hj1).1
    have hm' : SpectralGalerkin.mid (V j) (V (j + 1)) =
        actGS S (SpectralGalerkin.mid (actGS Si (V j)) (actGS Si (V (j + 1)))) := by
      rw [actGS_mid, hVS, hVS]
    show actGS Si (V (j + 1)) = actGS Si (V j) +
      τ • GN A F q (SpectralGalerkin.mid (actGS Si (V j)) (actGS Si (V (j + 1))))
    conv_lhs => rw [hrec]
    rw [actGS_add, actGS_smul, hm', GN_tr hSSi hSiS hA hF, actGS_actGS, hSiS, actGS_one]

/-- **The spectral Galerkin evolution for systems symmetric in a fixed positive component norm**
(`eq:generated-Galerkin`): for every data radius `R₀` there are `T > 0` and `R` such that for every
cutoff `N` and every smooth periodic datum with `‖U₀‖_{H^q} ≤ R₀` the Galerkin ODE
`ȧ = G_N(a)`, `a(0) = P_N U₀`, has a solution on `[0, T]` with `‖a(t)‖_{H^q} ≤ R`. -/
theorem galerkin_symmetrizer {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (hMA : ∀ i v, (M * amat A i v)ᵀ = M * amat A i v) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∃ R ≥ 0, ∀ (N : ℕ) (U₀ : Fin n → ST d → ℝ), (∀ b, ContDiff ℝ ∞ (U₀ b)) →
      (∀ b, IsSPeriodic (U₀ b)) → energyQ q U₀ 0 ≤ R₀ ^ 2 →
      ∃ γ : ℝ → GS d n N, γ 0 = P0 q N U₀ ∧ ∀ t ∈ Set.Icc 0 T,
        HasDerivWithinAt γ (GN A F q (γ t)) (Set.Icc 0 T) t ∧ ‖γ t‖ ≤ R := by
  obtain ⟨S, Si, hSM, hSSi, hSiS⟩ := exists_sqrt_factor hM
  set cS := (n : ℝ) * ∑ a, ∑ c, S a c ^ 2 with hcS
  have hcS0 : 0 ≤ cS := by positivity
  set cSi := Real.sqrt (∑ b, ∑ c, Si b c ^ 2) with hcSi
  obtain ⟨T, hT, K, -, h⟩ := galerkin_uniform (A := trA S Si A) (F := trF S Si F) hm hq
    (contDiff_trA hA) (trA_symm hSSi hSM hMA) (contDiff_trF hF) (R₀ := Real.sqrt cS * R₀)
    (by positivity)
  refine ⟨T, hT, cSi * (2 * (Real.sqrt cS * R₀) + 1), by positivity,
    fun N U₀ hU hUp hE => ?_⟩
  have hE' : energyQ q (act S U₀) 0 ≤ (Real.sqrt cS * R₀) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hcS0]
    exact (energyQ_act_le S hU q 0).trans (mul_le_mul_of_nonneg_left hE hcS0)
  obtain ⟨γ', hγ0, hγ⟩ := h N (act S U₀) (contDiff_act S hU) (isSPeriodic_act S hUp) hE'
  set L : GS d n N →L[ℝ] GS d n N := LinearMap.toContinuousLinearMap
    { toFun := actGS Si, map_add' := actGS_add Si, map_smul' := actGS_smul Si } with hL
  have hLa : ∀ a, L a = actGS Si a := fun a => rfl
  refine ⟨fun t => actGS Si (γ' t), ?_, fun t ht => ⟨?_, ?_⟩⟩
  · simp only [hγ0, P0_act q N S (fun b => (hU b).continuous), actGS_actGS, hSiS, actGS_one]
  · have hd := L.hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht).1
    have e : L (GN (trA S Si A) (trF S Si F) q (γ' t)) = GN A F q (actGS Si (γ' t)) := by
      rw [hLa]
      conv_lhs => rw [← actGS_one (γ' t), ← hSSi, ← actGS_actGS S Si (γ' t)]
      rw [GN_tr hSSi hSiS hA hF, actGS_actGS, hSiS, actGS_one]
    rw [e] at hd
    exact hd
  · exact (norm_actGS_le Si _).trans (mul_le_mul_of_nonneg_left (hγ t ht).2.1
      (Real.sqrt_nonneg _))

/-! ### Non-vacuity -/

/-- A non-symmetric principal matrix `A^1 = [[0, 2], [1, 0]]` (`A^2 = A^3 = 0`) that is symmetric
for the fixed inner product `M = diag(1, 2)`. -/
def exampleAM : Fin 3 → Fin 2 → Fin 2 → (Fin 2 → ℝ) → ℝ :=
  fun i a b _ => if i = 0 then (if a = 0 ∧ b = 1 then 2 else if a = 1 ∧ b = 0 then 1 else 0)
    else 0

/-- **Non-vacuity of `kato_two_sided_symmetrizer` beyond the Euclidean case**: the system
`∂_tU + A^1∂_1U = -U` on `𝕋³` with the non-symmetric `A^1 = [[0, 2], [1, 0]]`, symmetric for
`M = diag(1, 2)`, has a two-sided classical solution for the zero datum. -/
example : ∃ T > 0, ∃ (U : Fin 2 → ST 3 → ℝ) (P : Fin 2 → Fin 3 → ST 3 → ℝ),
    TwoSidedSol exampleAM (fun a v => -v a) (fun _ _ => 0) T U P := by
  have hM : (Matrix.diagonal ![(1 : ℝ), 2]).PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i; fin_cases i <;> norm_num
  have hMA : ∀ i v, (Matrix.diagonal ![(1 : ℝ), 2] * amat exampleAM i v)ᵀ =
      Matrix.diagonal ![(1 : ℝ), 2] * amat exampleAM i v := by
    intro i v
    ext a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp [amat, exampleAM, Matrix.diagonal_mul, Matrix.transpose_apply] <;> norm_num
  obtain ⟨T, hT, h⟩ := kato_two_sided_symmetrizer (d := 3) (n := 2) (m := 2) (q := 4)
    (by norm_num) le_rfl le_rfl (A := exampleAM) (F := fun a v => -v a)
    (fun _ _ _ => by unfold exampleAM; exact contDiff_const)
    (fun a => (contDiff_apply ℝ ℝ a).neg) hM hMA zero_le_one
  obtain ⟨U, P, hU⟩ := h (fun _ _ => 0) (fun _ => contDiff_const) (fun _ _ _ => rfl)
    (by rw [energyQ_zero]; norm_num)
  exact ⟨T, hT, U, P, hU⟩

end RenewalGeometry.KatoSymm
