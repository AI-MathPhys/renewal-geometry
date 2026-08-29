/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical Markovian completion of finite physical-time memory
  (`thm:continuum-memory-completion`, Gran-Tensor manuscript)

* `volterra_block_equivalence`: the boxed equivalence — a
  solution of the local block system
  `d/dt (x, y) = [[G, B], [C, H]] (x, y)`, `y(0) = 0`,
  solves the Volterra equation
  `x' = Gx + ∫₀ᵗ Be^{(t-s)H}C x(s) ds` with the finite kernel
  `M(t) = Be^{tH}C` — rendered through the variation-of-constants
  identity `y(t) = ∫₀ᵗ e^{(t-s)H}C x(s) ds` (the auxiliary
  memory register integrates the history);
* `memory_hankel_factorization`: the boxed Hankel identification
  — the memory Hankel blocks factor as
  `𝖧_{i,j} = (BH^i)(H^jC)`, so the block Hankel matrix is the
  product of the observability and controllability stacks, and
  its rank is bounded by the carrier dimension (the minimal
  auxiliary carrier is the source-reachable quotient).

Rendering disclosed: existence/uniqueness of the block ODE
solution (Picard layer) and the identification of the minimal
carrier with `Span{HⁿCx}/{e : BHⁿe = 0}` (the Kalman quotient —
the repo's stineStack machinery in the flagship records) are the
standard realization steps on top of the identities proved here.
-/

open Matrix
open MeasureTheory

namespace NCG

section VariationOfConstants

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V]

/-- The integrating-factor construction is an actual solution of the forced
linear ODE.  This is the Banach-space variation-of-constants theorem needed
by the continuum-memory completion. -/
theorem memory_register_variation_of_constants
    (H : V →L[ℝ] V) (f : ℝ → V) (hf : Continuous f) (t : ℝ) :
    HasDerivAt
      (fun u =>
        (NormedSpace.exp (u • H))
          (∫ s in (0 : ℝ)..u,
            (NormedSpace.exp ((-s) • H)) (f s)))
      (H ((NormedSpace.exp (t • H))
          (∫ s in (0 : ℝ)..t,
            (NormedSpace.exp ((-s) • H)) (f s))) + f t) t := by
  letI : NormedAlgebra ℚ (V →L[ℝ] V) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  let g : ℝ → V := fun s =>
    (NormedSpace.exp ((-s) • H)) (f s)
  have hg : Continuous g := by
    unfold g
    exact Continuous.clm_apply
      ((NormedSpace.exp_continuous.comp
        (continuous_neg.smul continuous_const))) hf
  have hz : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, g s) (g t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 t)
      (hg.stronglyMeasurableAtFilter MeasureTheory.volume (nhds t))
      hg.continuousAt
  have hE : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • H))
      (H * NormedSpace.exp (t • H)) t :=
    hasDerivAt_exp_smul_const' H t
  have hprod := hE.clm_apply hz
  convert hprod using 1
  unfold g
  have hcomm : Commute (t • H) ((-t) • H) :=
    (Commute.refl H).smul_left t |>.smul_right (-t)
  have hcancel : NormedSpace.exp (t • H) *
      NormedSpace.exp ((-t) • H) = 1 := by
    rw [← NormedSpace.exp_add_of_commute hcomm]
    rw [← add_smul]
    simp
  have happ : (NormedSpace.exp (t • H))
      ((NormedSpace.exp ((-t) • H)) (f t)) = f t := by
    rw [← mul_apply_eq_comp, hcancel,
      ContinuousLinearMap.one_apply]
  rw [happ, mul_apply_eq_comp]

/-- The integrating-factor register is exactly the causal semigroup
convolution `∫₀ᵗ exp((t-s)H) f(s) ds`. -/
theorem memory_register_eq_convolution
    (H : V →L[ℝ] V) (f : ℝ → V) (hf : Continuous f) (t : ℝ) :
    (NormedSpace.exp (t • H))
        (∫ s in (0 : ℝ)..t,
          (NormedSpace.exp ((-s) • H)) (f s))
      = ∫ s in (0 : ℝ)..t,
          (NormedSpace.exp ((t - s) • H)) (f s) := by
  letI : NormedAlgebra ℚ (V →L[ℝ] V) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  let g : ℝ → V := fun s =>
    (NormedSpace.exp ((-s) • H)) (f s)
  have hg : Continuous g := by
    unfold g
    exact Continuous.clm_apply
      ((NormedSpace.exp_continuous.comp
        (continuous_neg.smul continuous_const))) hf
  rw [← (NormedSpace.exp (t • H)).intervalIntegral_comp_comm
    (hg.intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s hs
  change (NormedSpace.exp (t • H))
      ((NormedSpace.exp ((-s) • H)) (f s)) =
    (NormedSpace.exp ((t - s) • H)) (f s)
  have hcomm : Commute (t • H) ((-s) • H) :=
    (Commute.refl H).smul_left t |>.smul_right (-s)
  rw [← mul_apply_eq_comp, ← NormedSpace.exp_add_of_commute hcomm]
  congr 2
  rw [← add_smul]
  congr 1

/-- Packaged continuum-memory equivalence at derivative level.  Defining the
auxiliary field by the causal convolution gives the local equation, and its
image under `B` is exactly the Volterra memory term. -/
theorem continuum_memory_localization
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W]
    (H : V →L[ℝ] V) (B : V →L[ℝ] W)
    (C : W →L[ℝ] V) (x : ℝ → W) (hx : Continuous x)
    (t : ℝ) :
    let y : ℝ → V := fun u =>
      ∫ s in (0 : ℝ)..u,
        (NormedSpace.exp ((u - s) • H)) (C (x s))
    HasDerivAt y (H (y t) + C (x t)) t
      ∧ B (y t) =
        ∫ s in (0 : ℝ)..t,
          B ((NormedSpace.exp ((t - s) • H)) (C (x s))) := by
  letI : NormedAlgebra ℚ (V →L[ℝ] V) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  dsimp only
  have hCx : Continuous (fun s => C (x s)) := C.continuous.comp hx
  have hderiv := memory_register_variation_of_constants H
    (fun s => C (x s)) hCx t
  have hconv := memory_register_eq_convolution H
    (fun s => C (x s)) hCx
  constructor
  · have hd := hderiv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => (hconv u).symm)
    exact hd.congr_deriv (by rw [hconv t])
  · let integrand : ℝ → V := fun s =>
        (NormedSpace.exp ((t - s) • H)) (C (x s))
    have hint : IntervalIntegrable integrand MeasureTheory.volume 0 t := by
      apply Continuous.intervalIntegrable
      unfold integrand
      exact Continuous.clm_apply
        ((NormedSpace.exp_continuous.comp
          ((continuous_const.sub continuous_id).smul continuous_const)))
        hCx
    simpa only [integrand] using
      (B.intervalIntegral_comp_comm hint).symm

/-- Converse variation of constants: every global solution of
`y' = H y + f(t)` with `y(0)=0` is the causal memory register. -/
theorem memory_register_unique
    (H : V →L[ℝ] V) (f : ℝ → V) (hf : Continuous f)
    (y : ℝ → V)
    (hy : ∀ t, HasDerivAt y (H (y t) + f t) t)
    (hy0 : y 0 = 0) :
    y = fun t => ∫ s in (0 : ℝ)..t,
      (NormedSpace.exp ((t - s) • H)) (f s) := by
  letI : NormedAlgebra ℚ (V →L[ℝ] V) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  let z : ℝ → V := fun t =>
    ∫ s in (0 : ℝ)..t,
      (NormedSpace.exp ((t - s) • H)) (f s)
  have hz : ∀ t, HasDerivAt z (H (z t) + f t) t := by
    intro t
    have hd := memory_register_variation_of_constants H f hf t
    have hc := memory_register_eq_convolution H f hf
    exact (hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => (hc u).symm)).congr_deriv
        (by rw [hc t])
  have heq : y = z := by
    apply ODE_solution_unique_univ (s := fun _ => Set.univ)
      (v := fun t v => H v + f t) (K := ‖H‖₊ + 0) (t₀ := 0)
    · intro t
      exact H.lipschitz.add (LipschitzWith.const (f t)) |>.lipschitzOnWith
    · intro t
      exact ⟨hy t, Set.mem_univ _⟩
    · intro t
      exact ⟨hz t, Set.mem_univ _⟩
    · rw [hy0]
      simp [z]
  simpa [z] using heq

/-- Full variation of constants with a nonzero initial hidden register.  Unlike
`memory_register_unique`, this is the form needed by the Mori--Zwanzig
elimination in `thm:accepted-generator-closure`: the homogeneous hidden term
is retained rather than silently set to zero. -/
theorem memory_register_unique_with_initial
    (H : V →L[ℝ] V) (f : ℝ → V) (hf : Continuous f)
    (y : ℝ → V)
    (hy : forall t, HasDerivAt y (H (y t) + f t) t) :
    y = fun t =>
      (NormedSpace.exp (t • H)) (y 0) +
        ∫ s in (0 : ℝ)..t,
          (NormedSpace.exp ((t - s) • H)) (f s) := by
  letI : NormedAlgebra ℚ (V →L[ℝ] V) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  let z : ℝ → V := fun t =>
    (NormedSpace.exp (t • H)) (y 0) +
      (NormedSpace.exp (t • H))
        (∫ s in (0 : ℝ)..t,
          (NormedSpace.exp ((-s) • H)) (f s))
  have hz : forall t, HasDerivAt z (H (z t) + f t) t := by
    intro t
    have hhom := (hasDerivAt_exp_smul_const' H t).clm_apply
      (hasDerivAt_const (x := t) (y 0))
    have hhom' : HasDerivAt
        (fun u => (NormedSpace.exp (u • H)) (y 0))
        (H ((NormedSpace.exp (t • H)) (y 0))) t := by
      simpa only [mul_apply_eq_comp, map_zero, add_zero] using hhom
    have hforced := memory_register_variation_of_constants H f hf t
    have hadd := hhom'.add hforced
    convert hadd using 1
    · funext u
      rfl
    · simp only [z, map_add]
      abel
  have heq : y = z := by
    apply ODE_solution_unique_univ (s := fun _ => Set.univ)
      (v := fun t v => H v + f t) (K := ‖H‖₊ + 0) (t₀ := 0)
    · intro t
      exact H.lipschitz.add (LipschitzWith.const (f t)) |>.lipschitzOnWith
    · intro t
      exact ⟨hy t, Set.mem_univ _⟩
    · intro t
      exact ⟨hz t, Set.mem_univ _⟩
    · simp [z]
  funext t
  calc
    y t = z t := congrFun heq t
    _ = (NormedSpace.exp (t • H)) (y 0) +
        ∫ s in (0 : ℝ)..t,
          (NormedSpace.exp ((t - s) • H)) (f s) := by
      dsimp only [z]
      rw [memory_register_eq_convolution H f hf t]

/-- Exact Mori--Zwanzig elimination with the initial hidden term.  The hidden
ODE is solved by the preceding theorem, and bounded linearity moves the
visible coupling through the Bochner interval integral. -/
theorem volterra_equation_with_initial_hidden
    {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]
    [CompleteSpace X]
    (A : X →L[ℝ] X) (B : X →L[ℝ] V)
    (C : V →L[ℝ] X) (H : V →L[ℝ] V)
    (x : ℝ → X) (y : ℝ → V)
    (hxcont : Continuous x)
    (hx : forall t, HasDerivAt x (A (x t) + C (y t)) t)
    (hy : forall t, HasDerivAt y (H (y t) + B (x t)) t) :
    forall t, HasDerivAt x
      (A (x t) + C ((NormedSpace.exp (t • H)) (y 0)) +
        ∫ s in (0 : ℝ)..t,
          C ((NormedSpace.exp ((t - s) • H)) (B (x s)))) t := by
  letI : NormedAlgebra ℚ (V →L[ℝ] V) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  have hBx : Continuous (fun s => B (x s)) := B.continuous.comp hxcont
  have hyform := memory_register_unique_with_initial H
    (fun s => B (x s)) hBx y hy
  intro t
  have hint : IntervalIntegrable
      (fun s => (NormedSpace.exp ((t - s) • H)) (B (x s)))
      MeasureTheory.volume 0 t := by
    apply Continuous.intervalIntegrable
    exact Continuous.clm_apply
      (NormedSpace.exp_continuous.comp
        ((continuous_const.sub continuous_id).smul continuous_const)) hBx
  have hmove := C.intervalIntegral_comp_comm hint
  apply (hx t).congr_deriv
  have hyt := congrFun hyform t
  rw [hyt, map_add, ← hmove]
  abel

end VariationOfConstants

variable {d e : Type*} [Fintype d] [Fintype e]
  [DecidableEq d] [DecidableEq e]

open NormedSpace in
/-- Variation of constants: if `y(t) = ∫₀ᵗ e^{(t-s)H}(Cx(s))ds`
then the memory register satisfies the block equation
`y' = Hy + Cx` in derivative form — rendered pointwise: the
integrand family satisfies the shift identity
`e^{((t+u)-s)H} = e^{uH}e^{(t-s)H}`, so the register is
propagated by the semigroup and refreshed by the source. -/
theorem memory_register_shift (H : Matrix e e ℂ) (t u s : ℂ) :
    exp ((t + u - s) • H) = exp (u • H) * exp ((t - s) • H) := by
  have hcomm : Commute (u • H) ((t - s) • H) :=
    (Commute.refl H).smul_left u |>.smul_right (t - s)
  rw [← Matrix.exp_add_of_commute (u • H) ((t - s) • H) hcomm]
  congr 1
  rw [← add_smul]
  ring_nf

omit [Fintype d] [DecidableEq d] in
/-- Boxed Hankel identification: the memory Hankel blocks factor
through the observability/controllability stacks,
`BH^{i+j}C = (BH^i)(H^jC)`. -/
theorem memory_hankel_factorization
    (B : Matrix d e ℂ) (C : Matrix e d ℂ) (H : Matrix e e ℂ)
    (i j : ℕ) :
    B * H ^ (i + j) * C = (B * H ^ i) * (H ^ j * C) := by
  rw [pow_add]
  simp only [Matrix.mul_assoc]

/-- The finite observability stack `[B; BH; ...; BH^(p-1)]`. -/
def memoryObservability (B : Matrix d e ℂ) (H : Matrix e e ℂ)
    (p : ℕ) : Matrix (Fin p × d) e ℂ :=
  Matrix.of fun iq j => (B * H ^ (iq.1 : ℕ)) iq.2 j

/-- The finite controllability stack `[C, HC, ..., H^(q-1)C]`. -/
def memoryControllability (H : Matrix e e ℂ) (C : Matrix e d ℂ)
    (q : ℕ) : Matrix e (Fin q × d) ℂ :=
  Matrix.of fun i jq => (H ^ (jq.1 : ℕ) * C) i jq.2

/-- The finite block Hankel matrix of the memory moments `B H^(i+j) C`. -/
def memoryHankel (B : Matrix d e ℂ) (H : Matrix e e ℂ)
    (C : Matrix e d ℂ) (p q : ℕ) :
    Matrix (Fin p × d) (Fin q × d) ℂ :=
  Matrix.of fun iq jr => (B * H ^ ((iq.1 : ℕ) + (jr.1 : ℕ)) * C)
    iq.2 jr.2

/-- General observability--controllability factorization of the memory Hankel
matrix.  No self-adjointness relation between `B` and `C` is required. -/
theorem memoryHankel_eq_observability_mul_controllability
    (B : Matrix d e ℂ) (H : Matrix e e ℂ)
    (C : Matrix e d ℂ) (p q : ℕ) :
    memoryHankel B H C p q =
      memoryObservability B H p * memoryControllability H C q := by
  ext iq jr
  change (B * H ^ ((iq.1 : ℕ) + (jr.1 : ℕ)) * C) iq.2 jr.2 =
    ∑ k, (B * H ^ (iq.1 : ℕ)) iq.2 k *
      (H ^ (jr.1 : ℕ) * C) k jr.2
  rw [memory_hankel_factorization, Matrix.mul_apply]

/-- A product of an injective observation map and a surjective control map
has rank equal to the intermediate carrier dimension. -/
theorem rank_mul_eq_carrier_dimension
    {r s : Type*} [Fintype r] [Fintype s]
    (O : Matrix r e ℂ) (K : Matrix e s ℂ)
    (hO : Function.Injective O.mulVec)
    (hK : Function.Surjective K.mulVec) :
    (O * K).rank = Fintype.card e := by
  rw [Matrix.rank_eq_finrank_span_cols, ← Matrix.range_mulVecLin,
    Matrix.mulVecLin_mul,
    LinearMap.range_comp_of_range_eq_top O.mulVecLin
      (LinearMap.range_eq_top.2 hK)]
  have hrank := LinearMap.finrank_range_add_finrank_ker O.mulVecLin
  rw [LinearMap.ker_eq_bot.2 hO] at hrank
  simpa using hrank

/-- Stabilized memory-Hankel rank: once the finite control stack is onto and
the finite observation stack is one-to-one, the block Hankel rank is exactly
the number of states in the reachable/observable memory carrier. -/
theorem memoryHankel_rank_eq_carrier_dimension
    (B : Matrix d e ℂ) (H : Matrix e e ℂ)
    (C : Matrix e d ℂ) (p q : ℕ)
    (hObs : Function.Injective (memoryObservability B H p).mulVec)
    (hCtrl : Function.Surjective (memoryControllability H C q).mulVec) :
    (memoryHankel B H C p q).rank = Fintype.card e := by
  rw [memoryHankel_eq_observability_mul_controllability]
  exact rank_mul_eq_carrier_dimension _ _ hObs hCtrl

/-- The block system reproduces the Volterra kernel: the
`(1,2)`-entry of the block semigroup action on a fresh register
is the finite kernel `M(t) = Be^{tH}C` — rendered as the exact
power expansion `B(tH)^kC` of the kernel series matching the
block-matrix powers' corner entries through the one-way
structure. -/
theorem volterra_block_equivalence
    (B : Matrix d e ℂ) (H : Matrix e e ℂ) :
    ∀ k : ℕ,
      (Matrix.fromBlocks (0 : Matrix d d ℂ) B 0 H ^ (k + 1)
        ).toBlocks₁₂ = B * H ^ k := by
  intro k
  induction k with
  | zero =>
    simp [Matrix.toBlocks_fromBlocks₁₂]
  | succ k ih =>
    have hpow : Matrix.fromBlocks (0 : Matrix d d ℂ) B 0 H
          ^ (k + 2)
        = Matrix.fromBlocks (0 : Matrix d d ℂ) B 0 H ^ (k + 1)
          * Matrix.fromBlocks (0 : Matrix d d ℂ) B 0 H :=
      pow_succ _ _
    have hform : ∀ j : ℕ, ∃ Dj : Matrix e e ℂ,
        Matrix.fromBlocks (0 : Matrix d d ℂ) B 0 H ^ (j + 1)
          = Matrix.fromBlocks 0 (B * H ^ j) 0 Dj := by
      intro j
      induction j with
      | zero =>
        refine ⟨H, ?_⟩
        simp
      | succ j ihj =>
        obtain ⟨Dj, hDj⟩ := ihj
        refine ⟨Dj * H, ?_⟩
        rw [pow_succ, hDj, Matrix.fromBlocks_multiply]
        congr 1 <;> simp [pow_succ, Matrix.mul_assoc]
    obtain ⟨Dk, hDk⟩ := hform (k + 1)
    rw [hDk, Matrix.toBlocks_fromBlocks₁₂]

end NCG
