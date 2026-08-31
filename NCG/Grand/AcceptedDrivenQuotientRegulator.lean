/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteRewardLumpabilityAndTiltedSelfEnergy
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Exact descent of driven dynamics and regulator transfer

This module proves `cor:accepted-driven-quotient-regulator` without assuming
the driven intertwinings.  They are derived from tilted closure and transport
of the Perron diagonal gauges.  The regulator statement is expressed for an
arbitrary filter, so it applies in particular to locally uniform cutoff/tilt
convergence on a fixed finite carrier.
-/

open Matrix
open scoped BigOperators Topology Matrix.Norms.Operator

namespace NCG.AcceptedDrivenQuotientRegulator

/-- Perron diagonal gauge. -/
def perronGauge {n : ℕ} (r : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal r

/-- Pointwise inverse Perron gauge. -/
noncomputable def inversePerronGauge {n : ℕ}
    (r : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => (r i)⁻¹

/-- Matrix of a deterministic decoder `sigma`: each fine state belongs to
exactly one coarse fibre. -/
def deterministicDecoder {m n : ℕ} (sigma : Fin n → Fin m) :
    Matrix (Fin n) (Fin m) ℝ :=
  fun i a => if sigma i = a then 1 else 0

/-- A coarse retraction is fibre-respecting when it has no matrix entry
between a coarse state and a fine state outside that decoder fibre. -/
def RetractionRespectsFibers {m n : ℕ} (sigma : Fin n → Fin m)
    (R : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ a i, R a i ≠ 0 → sigma i = a

@[simp] theorem deterministicDecoder_mulVec {m n : ℕ}
    (sigma : Fin n → Fin m) (x : Fin m → ℝ) (i : Fin n) :
    (deterministicDecoder sigma).mulVec x i = x (sigma i) := by
  classical
  simp [deterministicDecoder, Matrix.mulVec, dotProduct]

/-- Deterministic decoding transports both a Perron diagonal gauge and its
pointwise inverse; no separate gauge intertwining assumptions are needed. -/
theorem deterministicDecoder_perron_gauges_transport {m n : ℕ}
    (sigma : Fin n → Fin m) (rbar : Fin m → ℝ) :
    let r := (deterministicDecoder sigma).mulVec rbar
    perronGauge r * deterministicDecoder sigma =
        deterministicDecoder sigma * perronGauge rbar
      ∧ inversePerronGauge r * deterministicDecoder sigma =
        deterministicDecoder sigma * inversePerronGauge rbar := by
  classical
  dsimp only
  constructor <;> ext i a <;> by_cases hia : sigma i = a
  · subst a
    simp [perronGauge, inversePerronGauge, deterministicDecoder]
  · simp [perronGauge, inversePerronGauge, deterministicDecoder, hia]
  · subst a
    simp [perronGauge, inversePerronGauge, deterministicDecoder]
  · simp [perronGauge, inversePerronGauge, deterministicDecoder, hia]

/-- A fibre-respecting retraction transports the same diagonal Perron gauges
in the reverse direction. -/
theorem fibreRetraction_perron_gauges_transport {m n : ℕ}
    (sigma : Fin n → Fin m) (R : Matrix (Fin m) (Fin n) ℝ)
    (rbar : Fin m → ℝ) (hR : RetractionRespectsFibers sigma R) :
    let r := (deterministicDecoder sigma).mulVec rbar
    R * perronGauge r = perronGauge rbar * R
      ∧ R * inversePerronGauge r = inversePerronGauge rbar * R := by
  classical
  dsimp only
  constructor <;> ext a i <;> by_cases hai : R a i = 0
  · simp [perronGauge, inversePerronGauge, hai]
  · have hfiber := hR a i hai
    subst a
    simp [perronGauge, inversePerronGauge, mul_comm]
  · simp [perronGauge, inversePerronGauge, hai]
  · have hfiber := hR a i hai
    subst a
    simp [perronGauge, inversePerronGauge, mul_comm]

/-- Continuous-time Perron--Doob driven generator. -/
noncomputable def drivenGenerator {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (ψ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  inversePerronGauge r * B * perronGauge r - ψ • 1

/-- Exact tilted closure plus deterministic decoder transport of the Perron
gauges implies both driven intertwinings.  No driven intertwining is assumed. -/
theorem driven_generator_exact_descent
    {m n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (Bbar : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin n → ℝ) (rbar : Fin m → ℝ) (ψ : ℝ)
    (hBC : B * C = C * Bbar) (hRB : R * B = Bbar * R)
    (hDC : perronGauge r * C = C * perronGauge rbar)
    (hIC : inversePerronGauge r * C = C * inversePerronGauge rbar)
    (hRD : R * perronGauge r = perronGauge rbar * R)
    (hRI : R * inversePerronGauge r = inversePerronGauge rbar * R) :
    drivenGenerator B r ψ * C = C * drivenGenerator Bbar rbar ψ
      ∧ R * drivenGenerator B r ψ = drivenGenerator Bbar rbar ψ * R := by
  constructor
  · calc
      drivenGenerator B r ψ * C =
          inversePerronGauge r * B * (perronGauge r * C) - ψ • C := by
            simp only [drivenGenerator, Matrix.sub_mul, Matrix.smul_mul,
              Matrix.one_mul, Matrix.mul_assoc]
      _ = inversePerronGauge r * B * (C * perronGauge rbar) - ψ • C := by
            rw [hDC]
      _ = inversePerronGauge r * (B * C) * perronGauge rbar - ψ • C := by
            simp only [Matrix.mul_assoc]
      _ = inversePerronGauge r * (C * Bbar) * perronGauge rbar - ψ • C := by
            rw [hBC]
      _ = (inversePerronGauge r * C) * Bbar * perronGauge rbar - ψ • C := by
            simp only [Matrix.mul_assoc]
      _ = (C * inversePerronGauge rbar) * Bbar * perronGauge rbar - ψ • C := by
            rw [hIC]
      _ = C * drivenGenerator Bbar rbar ψ := by
            simp only [drivenGenerator, Matrix.mul_sub, Matrix.mul_smul,
              Matrix.mul_one, Matrix.mul_assoc]
  · calc
      R * drivenGenerator B r ψ =
          (R * inversePerronGauge r) * B * perronGauge r - ψ • R := by
            simp only [drivenGenerator, Matrix.mul_sub, Matrix.mul_smul,
              Matrix.mul_one, Matrix.mul_assoc]
      _ = (inversePerronGauge rbar * R) * B * perronGauge r - ψ • R := by
            rw [hRI]
      _ = inversePerronGauge rbar * (R * B) * perronGauge r - ψ • R := by
            simp only [Matrix.mul_assoc]
      _ = inversePerronGauge rbar * (Bbar * R) * perronGauge r - ψ • R := by
            rw [hRB]
      _ = inversePerronGauge rbar * Bbar * (R * perronGauge r) - ψ • R := by
            simp only [Matrix.mul_assoc]
      _ = inversePerronGauge rbar * Bbar * (perronGauge rbar * R) - ψ • R := by
            rw [hRD]
      _ = drivenGenerator Bbar rbar ψ * R := by
            simp only [drivenGenerator, Matrix.sub_mul, Matrix.smul_mul,
              Matrix.one_mul, Matrix.mul_assoc]

/-- Exact tilted closure through a deterministic decoder and a
fibre-respecting retraction automatically descends the driven generator. -/
theorem deterministic_driven_generator_exact_descent
    {m n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (Bbar : Matrix (Fin m) (Fin m) ℝ)
    (sigma : Fin n → Fin m)
    (R : Matrix (Fin m) (Fin n) ℝ)
    (rbar : Fin m → ℝ) (psi : ℝ)
    (hRfib : RetractionRespectsFibers sigma R)
    (hBC : B * deterministicDecoder sigma =
      deterministicDecoder sigma * Bbar)
    (hRB : R * B = Bbar * R) :
    let r := (deterministicDecoder sigma).mulVec rbar
    drivenGenerator B r psi * deterministicDecoder sigma =
        deterministicDecoder sigma * drivenGenerator Bbar rbar psi
      ∧ R * drivenGenerator B r psi =
        drivenGenerator Bbar rbar psi * R := by
  dsimp only
  obtain ⟨hDC, hIC⟩ :=
    deterministicDecoder_perron_gauges_transport sigma rbar
  obtain ⟨hRD, hRI⟩ :=
    fibreRetraction_perron_gauges_transport sigma R rbar hRfib
  exact driven_generator_exact_descent B Bbar (deterministicDecoder sigma) R
    _ rbar psi hBC hRB hDC hIC hRD hRI

/-- The usual deterministic decoder identities transport the Perron vectors
themselves: the fine right vector is `C rbar`, and the fine left vector is
`ellbar R`. -/
theorem perron_vectors_transport
    {m n : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin n → ℝ) (rbar : Fin m → ℝ)
    (ell : Fin n → ℝ) (ellbar : Fin m → ℝ)
    (hr : r = C.mulVec rbar)
    (hell : ell = fun i => ∑ j, ellbar j * R j i) :
    r = C.mulVec rbar ∧ ell = fun i => ∑ j, ellbar j * R j i :=
  ⟨hr, hell⟩

/-- Exact tilted intertwinings transport normalized Perron vectors whenever
the normalized left and right eigendirections are unique.  Thus the vector
identities used by driven descent are consequences of tilted closure and the
Perron separation hypothesis, rather than extra driven-process assumptions. -/
theorem perron_vectors_transport_of_unique_normalization
    {m n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (Bbar : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ)
    (psi : ℝ) (r : Fin n → ℝ) (rbar : Fin m → ℝ)
    (ell : Fin n → ℝ) (ellbar : Fin m → ℝ)
    (hBC : B * C = C * Bbar) (hRB : R * B = Bbar * R)
    (hrbar : Bbar.mulVec rbar = psi • rbar)
    (hellbar : ellbar ᵥ* Bbar = psi • ellbar)
    (hCrnorm : ∑ i, C.mulVec rbar i = 1)
    (hellRnorm : ∑ i, (ellbar ᵥ* R) i = 1)
    (hrUnique : ∀ x, B.mulVec x = psi • x → (∑ i, x i = 1) → x = r)
    (hellUnique : ∀ x, x ᵥ* B = psi • x → (∑ i, x i = 1) → x = ell) :
    r = C.mulVec rbar ∧ ell = ellbar ᵥ* R := by
  have hrightEig : B.mulVec (C.mulVec rbar) = psi • C.mulVec rbar := by
    rw [Matrix.mulVec_mulVec, hBC, ← Matrix.mulVec_mulVec, hrbar,
      Matrix.mulVec_smul]
  have hleftEig : (ellbar ᵥ* R) ᵥ* B = psi • (ellbar ᵥ* R) := by
    rw [Matrix.vecMul_vecMul, hRB, ← Matrix.vecMul_vecMul, hellbar,
      Matrix.smul_vecMul]
  exact ⟨(hrUnique _ hrightEig hCrnorm).symm,
    (hellUnique _ hleftEig hellRnorm).symm⟩

/-- The normalized normal matrix for a right Perron eigenvector.  Its
invertibility is an exact finite-dimensional form of simplicity/separation of
the Perron eigendirection. -/
def perronNormalMatrix {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (psi : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  let M := B - psi • 1
  Mᵀ * M + Matrix.vecMulVec (fun _ => 1) (fun _ => 1)

/-- A normalized right Perron vector solves the nonsingular Perron normal
equation. -/
theorem perronNormalMatrix_mulVec
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (psi : ℝ)
    (r : Fin n → ℝ) (heig : B.mulVec r = psi • r)
    (hnorm : ∑ i, r i = 1) :
    (perronNormalMatrix B psi).mulVec r = fun _ => 1 := by
  let M : Matrix (Fin n) (Fin n) ℝ := B - psi • 1
  have hMr : M.mulVec r = 0 := by
    simp only [M, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      heig, sub_self]
  simp only [perronNormalMatrix, M, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    hMr, Matrix.mulVec_zero, Matrix.vecMulVec_mulVec, zero_add]
  ext i
  simp [dotProduct, hnorm]

/-- Under the separation certificate, the normalized Perron vector is an
explicit inverse-normal-matrix expression. -/
theorem rightPerron_eq_normalMatrix_inv_mulVec
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (psi : ℝ)
    (r : Fin n → ℝ) (heig : B.mulVec r = psi • r)
    (hnorm : ∑ i, r i = 1)
    (hsep : IsUnit (perronNormalMatrix B psi).det) :
    r = (perronNormalMatrix B psi)⁻¹ *ᵥ (fun _ => 1) := by
  have hnormal := perronNormalMatrix_mulVec B psi r heig hnorm
  calc
    r = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ r := by simp
    _ = ((perronNormalMatrix B psi)⁻¹ * perronNormalMatrix B psi) *ᵥ r := by
      rw [Matrix.nonsing_inv_mul _ hsep]
    _ = (perronNormalMatrix B psi)⁻¹ *ᵥ
        (perronNormalMatrix B psi *ᵥ r) := by
      rw [Matrix.mulVec_mulVec]
    _ = (perronNormalMatrix B psi)⁻¹ *ᵥ (fun _ => 1) := by rw [hnormal]

/-- Continuity of the Perron normal matrix under simultaneous convergence of
the tilted matrix and exponent. -/
theorem perronNormalMatrix_tendsto
    {alpha : Type*} {l : Filter alpha} {n : ℕ}
    (Bq : alpha → Matrix (Fin n) (Fin n) ℝ) (psiq : alpha → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (psi : ℝ)
    (hB : Filter.Tendsto Bq l (𝓝 B))
    (hpsi : Filter.Tendsto psiq l (𝓝 psi)) :
    Filter.Tendsto (fun q => perronNormalMatrix (Bq q) (psiq q)) l
      (𝓝 (perronNormalMatrix B psi)) := by
  let Mq : alpha → Matrix (Fin n) (Fin n) ℝ :=
    fun q => Bq q - psiq q • 1
  let M : Matrix (Fin n) (Fin n) ℝ := B - psi • 1
  let C : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.vecMulVec (fun _ => 1) (fun _ => 1)
  have hM : Filter.Tendsto Mq l (𝓝 M) := by
    exact hB.sub (hpsi.smul_const (1 : Matrix (Fin n) (Fin n) ℝ))
  have hMt : Filter.Tendsto (fun q => (Mq q)ᵀ) l (𝓝 Mᵀ) :=
    continuous_id.matrix_transpose.continuousAt.tendsto.comp hM
  change Filter.Tendsto (fun q => (Mq q)ᵀ * Mq q + C) l
    (𝓝 (Mᵀ * M + C))
  exact (hMt.mul hM).add tendsto_const_nhds

/-- A fixed-dimensional family of normalized right Perron vectors converges
from convergence of the tilted matrices/exponents and a uniform separation
certificate.  Thus Perron-vector convergence is a theorem, not a regulator
input. -/
theorem rightPerronVector_tendsto
    {alpha : Type*} {l : Filter alpha} {n : ℕ}
    (Bq : alpha → Matrix (Fin n) (Fin n) ℝ)
    (psiq : alpha → ℝ) (rq : alpha → Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (psi : ℝ) (r : Fin n → ℝ)
    (hB : Filter.Tendsto Bq l (𝓝 B))
    (hpsi : Filter.Tendsto psiq l (𝓝 psi))
    (heigq : ∀ q, (Bq q).mulVec (rq q) = psiq q • rq q)
    (hnormq : ∀ q, ∑ i, rq q i = 1)
    (heig : B.mulVec r = psi • r) (hnorm : ∑ i, r i = 1)
    (hsepq : ∀ q, IsUnit (perronNormalMatrix (Bq q) (psiq q)).det)
    (hsep : IsUnit (perronNormalMatrix B psi).det) :
    Filter.Tendsto rq l (𝓝 r) := by
  let Kq := fun q => perronNormalMatrix (Bq q) (psiq q)
  let K := perronNormalMatrix B psi
  have hK : Filter.Tendsto Kq l (𝓝 K) :=
    perronNormalMatrix_tendsto Bq psiq B psi hB hpsi
  have hdet : Filter.Tendsto (fun q => (Kq q).det) l (𝓝 K.det) := by
    exact continuous_id.matrix_det.continuousAt.tendsto.comp hK
  have hadj : Filter.Tendsto (fun q => (Kq q).adjugate) l (𝓝 K.adjugate) := by
    exact continuous_id.matrix_adjugate.continuousAt.tendsto.comp hK
  have hinv : Filter.Tendsto (fun q => (Kq q)⁻¹) l (𝓝 K⁻¹) := by
    have hringInv : Filter.Tendsto
        (fun q => Ring.inverse (Kq q).det) l (𝓝 (Ring.inverse K.det)) := by
      simpa only [Ring.inverse_eq_inv] using hdet.inv₀ hsep.ne_zero
    simpa only [Matrix.inv_def] using hringInv.smul hadj
  have happ : Filter.Tendsto
      (fun q => (Kq q)⁻¹ *ᵥ (fun _ => 1)) l
      (𝓝 (K⁻¹ *ᵥ (fun _ => 1))) := by
    have hc : Continuous
        (fun A : Matrix (Fin n) (Fin n) ℝ => A *ᵥ (fun _ => 1)) :=
      continuous_id.matrix_mulVec continuous_const
    exact hc.continuousAt.tendsto.comp hinv
  have hreprq : ∀ q, rq q = (Kq q)⁻¹ *ᵥ (fun _ => 1) := by
    intro q
    exact rightPerron_eq_normalMatrix_inv_mulVec
      (Bq q) (psiq q) (rq q) (heigq q) (hnormq q) (hsepq q)
  have hrepr : r = K⁻¹ *ᵥ (fun _ => 1) :=
    rightPerron_eq_normalMatrix_inv_mulVec B psi r heig hnorm hsep
  simpa only [← hrepr] using happ.congr'
    (Filter.Eventually.of_forall fun q => (hreprq q).symm)

/-- Left Perron vectors obey the same finite-dimensional perturbation theorem,
by applying the right-vector normal equation to the transposed matrices. -/
theorem leftPerronVector_tendsto
    {alpha : Type*} {l : Filter alpha} {n : ℕ}
    (Bq : alpha → Matrix (Fin n) (Fin n) ℝ)
    (psiq : alpha → ℝ) (ellq : alpha → Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (psi : ℝ) (ell : Fin n → ℝ)
    (hB : Filter.Tendsto Bq l (𝓝 B))
    (hpsi : Filter.Tendsto psiq l (𝓝 psi))
    (heigq : ∀ q, ellq q ᵥ* Bq q = psiq q • ellq q)
    (hnormq : ∀ q, ∑ i, ellq q i = 1)
    (heig : ell ᵥ* B = psi • ell) (hnorm : ∑ i, ell i = 1)
    (hsepq : ∀ q,
      IsUnit (perronNormalMatrix (Bq q)ᵀ (psiq q)).det)
    (hsep : IsUnit (perronNormalMatrix Bᵀ psi).det) :
    Filter.Tendsto ellq l (𝓝 ell) := by
  have hBt : Filter.Tendsto (fun q => (Bq q)ᵀ) l (𝓝 Bᵀ) :=
    continuous_id.matrix_transpose.continuousAt.tendsto.comp hB
  apply rightPerronVector_tendsto (fun q => (Bq q)ᵀ) psiq ellq
    Bᵀ psi ell hBt hpsi
  · intro q
    simpa only [Matrix.mulVec_transpose] using heigq q
  · exact hnormq
  · simpa only [Matrix.mulVec_transpose] using heig
  · exact hnorm
  · exact hsepq
  · exact hsep

/-- Regulator transfer for driven generators.  The hypotheses are convergence
of the coarse tilted operator, Perron gauge and inverse gauge, and Perron
exponent; the conclusion is convergence of the Doob generator itself. -/
theorem drivenGenerator_tendsto
    {α : Type*} {l : Filter α} {n : ℕ}
    (Bq : α → Matrix (Fin n) (Fin n) ℝ)
    (Dq Iq : α → Matrix (Fin n) (Fin n) ℝ)
    (ψq : α → ℝ)
    (B D I : Matrix (Fin n) (Fin n) ℝ) (ψ : ℝ)
    (hB : Filter.Tendsto Bq l (𝓝 B))
    (hD : Filter.Tendsto Dq l (𝓝 D))
    (hI : Filter.Tendsto Iq l (𝓝 I))
    (hψ : Filter.Tendsto ψq l (𝓝 ψ)) :
    Filter.Tendsto
      (fun q => Iq q * Bq q * Dq q - ψq q •
        (1 : Matrix (Fin n) (Fin n) ℝ)) l
      (𝓝 (I * B * D - ψ • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  exact ((hI.mul hB).mul hD).sub (hψ.smul_const 1)

/-- Perron diagonal gauges depend continuously on the Perron vector. -/
theorem perronGauge_tendsto
    {alpha : Type*} {l : Filter alpha} {n : ℕ}
    (rq : alpha → Fin n → ℝ) (r : Fin n → ℝ)
    (hr : Filter.Tendsto rq l (𝓝 r)) :
    Filter.Tendsto (fun q => perronGauge (rq q)) l
      (𝓝 (perronGauge r)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  by_cases hij : i = j
  · subst j
    simpa [perronGauge] using (tendsto_pi_nhds.mp hr i)
  · simpa [perronGauge, hij] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : alpha => (0 : ℝ)) l (𝓝 0))

/-- The inverse Perron gauges are continuous at a vector with no zero
coordinate.  A uniform positive Perron floor is a stronger manuscript
hypothesis supplying this condition. -/
theorem inversePerronGauge_tendsto
    {alpha : Type*} {l : Filter alpha} {n : ℕ}
    (rq : alpha → Fin n → ℝ) (r : Fin n → ℝ)
    (hr : Filter.Tendsto rq l (𝓝 r)) (hr0 : ∀ i, r i ≠ 0) :
    Filter.Tendsto (fun q => inversePerronGauge (rq q)) l
      (𝓝 (inversePerronGauge r)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  by_cases hij : i = j
  · subst j
    simpa [inversePerronGauge] using
      ((tendsto_pi_nhds.mp hr i).inv₀ (hr0 i))
  · simpa [inversePerronGauge, hij] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : alpha => (0 : ℝ)) l (𝓝 0))

/-- Locally convergent tilted matrices, Perron vectors and Perron exponents
automatically give convergence of the Doob generators.  In particular the
manuscript's locally uniform finite-dimensional convergence follows by using
the locally-uniform function-space filter. -/
theorem drivenGenerator_tendsto_of_perron
    {alpha : Type*} {l : Filter alpha} {n : ℕ}
    (Bq : alpha → Matrix (Fin n) (Fin n) ℝ)
    (rq : alpha → Fin n → ℝ) (psiq : alpha → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (psi : ℝ)
    (hB : Filter.Tendsto Bq l (𝓝 B))
    (hr : Filter.Tendsto rq l (𝓝 r))
    (hpsi : Filter.Tendsto psiq l (𝓝 psi))
    (hr0 : ∀ i, r i ≠ 0) :
    Filter.Tendsto (fun q => drivenGenerator (Bq q) (rq q) (psiq q)) l
      (𝓝 (drivenGenerator B r psi)) := by
  simpa [drivenGenerator] using drivenGenerator_tendsto
    Bq (fun q => perronGauge (rq q))
    (fun q => inversePerronGauge (rq q)) psiq
    B (perronGauge r) (inversePerronGauge r) psi hB
    (perronGauge_tendsto rq r hr)
    (inversePerronGauge_tendsto rq r hr hr0) hpsi

/-- Finite-time semigroups converge in every Banach-algebra realization of
the finite generator (for example its bounded-operator realization). -/
theorem drivenSemigroup_tendsto
    {α 𝔸 : Type*} {l : Filter α}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (Lq : α → 𝔸) (L : 𝔸) (hL : Filter.Tendsto Lq l (𝓝 L)) :
    Filter.Tendsto (fun q => NormedSpace.exp (Lq q)) l
      (𝓝 (NormedSpace.exp L)) :=
  hL.exp

/-- Normalized Perron product, the stationary law of the driven chain. -/
noncomputable def stationaryLaw {n : ℕ}
    (ell r : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ell i * r i / ∑ j, ell j * r j

/-- Convergence of left/right Perron vectors with a nonzero limiting
normalization gives convergence of every stationary-law coordinate. -/
theorem stationaryLaw_tendsto_apply
    {α : Type*} {l : Filter α} {n : ℕ}
    (ellq rq : α → Fin n → ℝ) (ell r : Fin n → ℝ)
    (hell : Filter.Tendsto ellq l (𝓝 ell))
    (hr : Filter.Tendsto rq l (𝓝 r))
    (hZ : (∑ j, ell j * r j) ≠ 0) (i : Fin n) :
    Filter.Tendsto (fun q => stationaryLaw (ellq q) (rq q) i) l
      (𝓝 (stationaryLaw ell r i)) := by
  have hnum : Filter.Tendsto (fun q => ellq q i * rq q i) l
      (𝓝 (ell i * r i)) :=
    ((tendsto_pi_nhds.mp hell) i).mul ((tendsto_pi_nhds.mp hr) i)
  have hden : Filter.Tendsto (fun q => ∑ j, ellq q j * rq q j) l
      (𝓝 (∑ j, ell j * r j)) := by
    apply tendsto_finset_sum
    intro j _
    exact ((tendsto_pi_nhds.mp hell) j).mul ((tendsto_pi_nhds.mp hr) j)
  exact hnum.div hden hZ

/-- Complete fixed-dimensional regulator transfer.  Matrix and Perron-exponent
convergence plus finite normal-matrix separation derive both Perron-vector
limits; the driven generator, every stationary-law coordinate, and the
finite-time semigroup then converge.  Since the filter is arbitrary, choosing
the locally-uniform function-space filter gives precisely the manuscript's
locally-uniform-in-tilt conclusion. -/
theorem fixedDimensional_driven_regulator_transfer
    {alpha : Type*} {l : Filter alpha} {n : ℕ}
    (Bq : alpha → Matrix (Fin n) (Fin n) ℝ)
    (psiq : alpha → ℝ)
    (rq ellq : alpha → Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (psi : ℝ)
    (r ell : Fin n → ℝ)
    (hB : Filter.Tendsto Bq l (𝓝 B))
    (hpsi : Filter.Tendsto psiq l (𝓝 psi))
    (hrEigq : ∀ q, (Bq q).mulVec (rq q) = psiq q • rq q)
    (hrNormq : ∀ q, ∑ i, rq q i = 1)
    (hrEig : B.mulVec r = psi • r) (hrNorm : ∑ i, r i = 1)
    (hellEigq : ∀ q, ellq q ᵥ* Bq q = psiq q • ellq q)
    (hellNormq : ∀ q, ∑ i, ellq q i = 1)
    (hellEig : ell ᵥ* B = psi • ell) (hellNorm : ∑ i, ell i = 1)
    (hrSepq : ∀ q, IsUnit (perronNormalMatrix (Bq q) (psiq q)).det)
    (hrSep : IsUnit (perronNormalMatrix B psi).det)
    (hellSepq : ∀ q,
      IsUnit (perronNormalMatrix (Bq q)ᵀ (psiq q)).det)
    (hellSep : IsUnit (perronNormalMatrix Bᵀ psi).det)
    (hr0 : ∀ i, r i ≠ 0)
    (hZ : (∑ j, ell j * r j) ≠ 0) :
    Filter.Tendsto
        (fun q => drivenGenerator (Bq q) (rq q) (psiq q)) l
        (𝓝 (drivenGenerator B r psi))
      ∧ (∀ i, Filter.Tendsto
          (fun q => stationaryLaw (ellq q) (rq q) i) l
          (𝓝 (stationaryLaw ell r i)))
      ∧ Filter.Tendsto
          (fun q => NormedSpace.exp
            (drivenGenerator (Bq q) (rq q) (psiq q))) l
          (𝓝 (NormedSpace.exp (drivenGenerator B r psi))) := by
  have hr := rightPerronVector_tendsto Bq psiq rq B psi r hB hpsi
    hrEigq hrNormq hrEig hrNorm hrSepq hrSep
  have hell := leftPerronVector_tendsto Bq psiq ellq B psi ell hB hpsi
    hellEigq hellNormq hellEig hellNorm hellSepq hellSep
  have hL := drivenGenerator_tendsto_of_perron Bq rq psiq B r psi
    hB hr hpsi hr0
  have hsemigroup : Filter.Tendsto
      (fun q => NormedSpace.exp
        (drivenGenerator (Bq q) (rq q) (psiq q))) l
      (𝓝 (NormedSpace.exp (drivenGenerator B r psi))) :=
    drivenSemigroup_tendsto
      (α := alpha) (𝔸 := Matrix (Fin n) (Fin n) ℝ) (l := l)
      (fun q => drivenGenerator (Bq q) (rq q) (psiq q))
      (drivenGenerator B r psi) hL
  refine ⟨hL, ?_, hsemigroup⟩
  intro i
  exact stationaryLaw_tendsto_apply ellq rq ell r hell hr hZ i

end NCG.AcceptedDrivenQuotientRegulator
