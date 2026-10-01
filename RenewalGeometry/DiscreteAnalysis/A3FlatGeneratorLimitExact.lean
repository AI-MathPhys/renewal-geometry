/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.TorusPiecewiseConstantEmbedding
import RenewalGeometry.OperatorLimits.DenseSourceStrongConvergence
import RenewalGeometry.Gravity.HomogeneousADMPacketDerivedExact
import RenewalGeometry.DiscreteAnalysis.A3PeriodicGraphSamplingExact

/-!
# Fourier symbol and flat generator limit of the periodic `A₃` graph (`lem:supp-flat-symbol`)

The periodic `A₃` graph `V_h = Λ_{A₃}/dΛ_{A₃}` (`eq:supp-periodic-vertices`, `h = 1/d`) is encoded
in root-basis coordinates as `(ℤ/d)³` (`A3PeriodicGraphSampling.Vertex`), the twelve roots by
their integer coordinates `rootCoordinates` (tied to the Euclidean roots by
`A3PeriodicSmoothEnergy.root_eq_integerCombination`).  A dual-lattice vector `k ∈ Λ*` is encoded
by its root-basis pairings `κ_i = ⟨k, b_i⟩ ∈ ℤ`; `kvec κ` is the Euclidean vector itself
(`rootPairing_kvec`: `⟨r_a, kvec κ⟩ = Σ_i ρ_{a,i} κ_i`).

* `gen`: the generator `(L_h f)(x) = Σ_α (1/(8h²))[f(x + α) - f(x)]` at the flat rates
  (`eq:supp-root-generator`, `eq:supp-flat-rates`); `gen_modeFn`: every dual-lattice mode
  `e_k(x) = e^{2πih⟨k,x⟩}` is an eigenvector, `-L_h e_k = λ_h(k) e_k`, with
  `λ_h(k) = (4h²)⁻¹ Σ_{a=1}^6 [1 - cos(2πh⟨r_a,k⟩)]` (`HomogeneousADMPacket.flatSymbol`,
  `eq:supp-flat-symbol`).
* `tendsto_flatSymbol`: `λ_h(k) → 2π²‖k‖²` for every fixed `k` (`eq:supp-flat-symbol-limit`).
* Stage operators on `ℓ²(V_h)` (`Stage`): the resolvent `resE N z = (z - L_h)⁻¹`
  (`resE_spec`, `‖resE‖ ≤ 1/z`) and the heat semigroup `semE N t = e^{tL_h}` (`semE_eq_exp`,
  `NormedSpace.exp`).
* Continuum: `L²(𝕋³_{A₃})` in root-basis coordinates is `L²(UnitAddTorus (Fin 3))` (normalised
  Haar measure), the mode `e_k` is Mathlib's `mFourier κ`, and `½Δ` is the Fourier multiplier
  `-2π²‖k‖²` (`contSymbol`); its resolvent `contRes z` and heat semigroup `contSem t` are the
  multipliers `(z + 2π²‖k‖²)⁻¹`, `e^{-2π²t‖k‖²}` (`contOp`, built from `mFourierBasis`).
* `flat_resolvent_strong`, `flat_semigroup_strong` (`eq:supp-flat-generator-limit`): along the
  natural piecewise-constant embeddings (`TorusPiecewiseConstant.pcEmbedding`, cells
  `Π_i (x_i/d, (x_i+1)/d]` in root-basis coordinates, vertex mass `h³`), the resolvents converge
  in the strong varying-Hilbert sense (`VaryingHilbert.System.StrongOperatorConverges`: every
  strongly convergent input family is mapped to a strongly convergent output family) for every
  `z > 0`, and the semigroups for every `t ≥ 0`.  The proof is the manuscript's: a uniformly
  bounded family which acts on the grid samples of the Fourier modes by convergent eigenvalues
  converges strongly (`strongOperatorConverges_of_modes`, via density of trigonometric
  polynomials and `strongOperatorConverges_of_dense_sources_of_uniform_opNorm`).
-/

open Finset ComplexConjugate MeasureTheory UnitAddTorus Filter Topology
open scoped BigOperators Real

namespace RenewalGeometry.A3FlatGenerator

open PeriodicGridSobolev LatticeTorusPlancherel TorusPiecewiseConstant
open A3PeriodicGraphSampling A3PeriodicSmoothEnergy

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-- Integer vector reduced modulo `N`. -/
def castVec (N : ℕ) (κ : Fin 3 → ℤ) : Grid N := fun i => (κ i : ZMod N)

/-- The root step is the translation by the reduced root coordinates. -/
theorem rootStep_eq (x : Grid N) (r : Fin 12) :
    rootStep N x r = x + castVec N (rootCoordinates r) := rfl

/-- Translation by `a` as a linear map. -/
noncomputable def translate (a : Grid N) : Module.End ℂ (Grid N → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x : Grid N => x + a)

theorem isMult_translate (a : Grid N) : IsMult (translate a) (fun κ => latticeChar κ a) := by
  intro u k
  unfold dft translate
  simp only [LinearMap.funLeft_apply, Function.comp_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine (Fintype.sum_equiv (Equiv.addRight a) _
    (fun y => ((N : ℂ) ^ 3)⁻¹ * (conj (latticeChar k (y - a)) * u y)) (fun x => by simp)).trans ?_
  refine sum_congr rfl fun y _ => ?_
  rw [latticeChar_sub_right, map_mul, Complex.conj_conj]
  ring

/-- The `A₃` root generator at the flat rates `k_{α,h} = 1/(8h²)`, `h = 1/N`:
`(L_h f)(x) = Σ_α (1/(8h²)) [f(x + α) - f(x)]` (`eq:supp-root-generator`,
`eq:supp-flat-rates`) on `V_h = Λ/NΛ` in root-basis coordinates. -/
noncomputable def gen (N : ℕ) [NeZero N] : Module.End ℂ (Grid N → ℂ) :=
  ∑ r : Fin 12, (((N : ℂ) ^ 2 / 8) • (translate (castVec N (rootCoordinates r)) - 1))

theorem gen_apply (f : Grid N → ℂ) (x : Grid N) :
    gen N f x = ∑ r : Fin 12, ((N : ℂ) ^ 2 / 8) * (f (rootStep N x r) - f x) := by
  simp [gen, translate, rootStep_eq, LinearMap.sum_apply, Finset.sum_apply]

/-- The real symbol `λ_N(κ) = (N²/8) Σ_α (1 - Re e(κ·α))`. -/
noncomputable def lam (N : ℕ) [NeZero N] (κ : Grid N) : ℝ :=
  ((N : ℝ) ^ 2 / 8) * ∑ r : Fin 12, (1 - (latticeChar κ (castVec N (rootCoordinates r))).re)

theorem lam_nonneg (κ : Grid N) : 0 ≤ lam N κ := by
  unfold lam
  refine mul_nonneg (by positivity) (sum_nonneg fun r _ => ?_)
  have h1 : ‖latticeChar κ (castVec N (rootCoordinates r))‖ = 1 := by
    unfold latticeChar
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  have := Complex.re_le_norm (latticeChar κ (castVec N (rootCoordinates r)))
  linarith

/-- The opposite root. -/
def oppRoot : Fin 12 → Fin 12 := ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8]

theorem oppRoot_involutive : Function.Involutive oppRoot := by
  intro r; fin_cases r <;> rfl

theorem rootCoordinates_oppRoot (r : Fin 12) :
    rootCoordinates (oppRoot r) = -rootCoordinates r := by
  fin_cases r <;> decide

theorem castVec_neg (κ : Fin 3 → ℤ) : castVec N (-κ) = -castVec N κ := by
  funext i; simp [castVec]

/-- The imaginary parts cancel in opposite root pairs. -/
theorem sum_im_latticeChar_roots (κ : Grid N) :
    ∑ r : Fin 12, (latticeChar κ (castVec N (rootCoordinates r))).im = 0 := by
  have h := Fintype.sum_equiv (oppRoot_involutive.toPerm _)
    (fun r => (latticeChar κ (castVec N (rootCoordinates r))).im)
    (fun r => (latticeChar κ (castVec N (rootCoordinates (oppRoot r)))).im) (fun r => by
      simp [Function.Involutive.coe_toPerm, oppRoot_involutive r])
  have hneg : ∀ r, (latticeChar κ (castVec N (rootCoordinates (oppRoot r)))).im =
      -(latticeChar κ (castVec N (rootCoordinates r))).im := by
    intro r
    rw [rootCoordinates_oppRoot, castVec_neg, latticeChar_neg_right, Complex.conj_im]
  simp only [hneg, sum_neg_distrib] at h
  linarith

/-- The generator symbol is real: `Σ_α (1/(8h²))(e(κ·α) - 1) = -λ_N(κ)`. -/
theorem genSym_eq (κ : Grid N) :
    ∑ r : Fin 12, ((N : ℂ) ^ 2 / 8) * (latticeChar κ (castVec N (rootCoordinates r)) - 1) =
      -(lam N κ : ℂ) := by
  have hsum : ∑ r : Fin 12, latticeChar κ (castVec N (rootCoordinates r)) =
      ((∑ r : Fin 12, (latticeChar κ (castVec N (rootCoordinates r))).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.re_sum]
    · rw [Complex.im_sum, sum_im_latticeChar_roots, Complex.ofReal_im]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum, lam]
  push_cast
  rw [Finset.sum_sub_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The generator is the Fourier multiplier `-λ_N`. -/
theorem isMult_gen : IsMult (gen N) (fun κ => -(lam N κ : ℂ)) := by
  intro u k
  have hsum : ∀ s : Finset (Fin 12), dft ((∑ r ∈ s, (((N : ℂ) ^ 2 / 8) •
      (translate (castVec N (rootCoordinates r)) - 1)) : Module.End ℂ (Grid N → ℂ)) u) k =
      (∑ r ∈ s, ((N : ℂ) ^ 2 / 8) * (latticeChar k (castVec N (rootCoordinates r)) - 1)) *
        dft u k := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [dft]
    | insert a s ha ih =>
      rw [sum_insert ha, LinearMap.add_apply, dft_add, ih, sum_insert ha,
        (((isMult_translate _).sub IsMult.one).smul _) u k]
      ring
  rw [gen, hsum, genSym_eq]

/-! ### Dual-lattice modes and the explicit symbol -/

/-- The dual vector `k ∈ Λ*` with root-basis pairings `⟨k, b_i⟩ = κ_i`. -/
noncomputable def kvec (κ : Fin 3 → ℤ) : Fin 3 → ℝ :=
  ![((κ 0 : ℝ) + κ 1 - κ 2) / 2, ((κ 0 : ℝ) - κ 1 + κ 2) / 2, (-(κ 0 : ℝ) + κ 1 + κ 2) / 2]

/-- The dual-lattice mode `e_k(x) = e^{2πih⟨k,x⟩}` on `V_h` (root-basis coordinates `x`). -/
noncomputable def modeFn (N : ℕ) [NeZero N] (κ : Fin 3 → ℤ) : Grid N → ℂ :=
  fun x => latticeChar (castVec N κ) x

theorem latticeChar_castVec (κ ρ : Fin 3 → ℤ) :
    latticeChar (castVec N κ) (castVec N ρ) =
      Complex.exp (Complex.I * ((2 * π * (∑ i, (κ i : ℝ) * ρ i) / N : ℝ) : ℂ)) := by
  unfold latticeChar castVec
  have h : ∀ i, ZMod.stdAddChar ((κ i : ZMod N) * (ρ i : ZMod N)) =
      Complex.exp (Complex.I * ((2 * π * ((κ i : ℝ) * ρ i) / N : ℝ) : ℂ)) := by
    intro i
    rw [show (κ i : ZMod N) * (ρ i : ZMod N) = ((κ i * ρ i : ℤ) : ZMod N) by push_cast; ring,
      ZMod.stdAddChar_coe]
    congr 1; push_cast; ring
  simp only [h]
  rw [← Complex.exp_sum, ← Finset.mul_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]

/-- `lam` at a reduced integer frequency, as a cosine sum over the twelve roots. -/
theorem lam_castVec_eq_cos (κ : Fin 3 → ℤ) :
    lam N (castVec N κ) = ((N : ℝ) ^ 2 / 8) *
      ∑ r : Fin 12, (1 - Real.cos (2 * π * (∑ i, (κ i : ℝ) * rootCoordinates r i) / N)) := by
  unfold lam
  congr 1
  refine sum_congr rfl fun r _ => ?_
  rw [latticeChar_castVec, Complex.exp_re]
  simp [Complex.cos_ofReal_re, Complex.exp_ofReal_mul_I_re]

/-- The six oriented roots `a3Roots 0, 1, 4, 5, 8, 9` of `HomogeneousADMPacket.orientedRoot`. -/
def idx6 : Fin 6 → Fin 12 := ![0, 1, 4, 5, 8, 9]

theorem rootPairing_kvec (κ : Fin 3 → ℤ) (a : Fin 6) :
    HomogeneousADMPacket.rootPairing (kvec κ) a =
      ∑ i, (rootCoordinates (idx6 a) i : ℝ) * κ i := by
  fin_cases a <;>
    simp [HomogeneousADMPacket.rootPairing, HomogeneousADMPacket.orientedRoot, a3Roots, kvec,
      rootCoordinates, idx6, Fin.sum_univ_three] <;> ring

theorem cos_neg_add (a b : ℝ) : Real.cos (-a + b) = Real.cos (a - b) := by
  rw [← Real.cos_neg]; ring_nf

/-- `lem:supp-flat-symbol`, eigenvalue (`eq:supp-flat-symbol`): `λ_N(κ)` is the manuscript's
`λ_h(k) = (4h²)⁻¹ Σ_{a=1}^6 [1 - cos(2πh⟨r_a, k⟩)]` at `h = 1/N`, `k = kvec κ`. -/
theorem lam_castVec (κ : Fin 3 → ℤ) :
    lam N (castVec N κ) = HomogeneousADMPacket.flatSymbol (1 / N) (kvec κ) := by
  rw [lam_castVec_eq_cos]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  set t : Fin 3 → ℝ := fun i => 2 * π * κ i / N with ht
  have hl : ∀ r : Fin 12, 2 * π * (∑ i, (κ i : ℝ) * rootCoordinates r i) / N =
      ∑ i, (rootCoordinates r i : ℝ) * t i := by
    intro r
    rw [Finset.mul_sum, Finset.sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [ht]; ring
  have hr : ∀ a : Fin 6, 2 * π * (1 / N) * HomogeneousADMPacket.rootPairing (kvec κ) a =
      ∑ i, (rootCoordinates (idx6 a) i : ℝ) * t i := by
    intro a
    rw [rootPairing_kvec, Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [ht]; field_simp
  simp only [HomogeneousADMPacket.flatSymbol, hl, hr]
  simp [Fin.sum_univ_succ, Fin.sum_univ_three, rootCoordinates, idx6, cos_neg_add]
  field_simp
  ring

/-- `lem:supp-flat-symbol`, eigenvector clause: `-L_h e_k = λ_h(k) e_k` for every dual-lattice
mode. -/
theorem gen_modeFn (κ : Fin 3 → ℤ) :
    gen N (modeFn N κ) = (-(HomogeneousADMPacket.flatSymbol (1 / N) (kvec κ) : ℂ)) •
      modeFn N κ := by
  funext x
  rw [gen_apply, Pi.smul_apply, smul_eq_mul, ← lam_castVec, ← genSym_eq, Finset.sum_mul]
  refine sum_congr rfl fun r _ => ?_
  simp only [modeFn, rootStep_eq, latticeChar_add_right]
  ring


/-! ### Multiplier operators on the grid -/

theorem dft_synth (c : Grid N → ℂ) (κ₀ : Grid N) :
    dft (fun x => ∑ κ, latticeChar κ x * c κ) κ₀ = c κ₀ := by
  have hn : ((N : ℂ) ^ 3) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  unfold dft
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hrow : ∀ κ : Grid N, ∑ x : Grid N, ((N : ℂ) ^ 3)⁻¹ * (conj (latticeChar κ₀ x) *
      (latticeChar κ x * c κ)) = ((N : ℂ) ^ 3)⁻¹ * (∑ x : Grid N, latticeChar x (κ - κ₀)) * c κ := by
    intro κ
    rw [Finset.mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun x _ => ?_
    rw [latticeChar_sub_right, latticeChar_comm x κ, latticeChar_comm x κ₀]
    ring
  simp only [hrow]
  have hsum : ∀ κ : Grid N, ∑ x : Grid N, latticeChar x (κ - κ₀) =
      if κ = κ₀ then (N : ℂ) ^ 3 else 0 := by
    intro κ
    have := sum_latticeChar (d := 3) (n := N) (κ - κ₀)
    simp_rw [latticeChar_comm _ (κ - κ₀)] at this ⊢
    rw [this]
    simp [sub_eq_zero]
  simp only [hsum]
  rw [Finset.sum_eq_single κ₀]
  · simp [hn]
  · intro b _ hb; simp [hb]
  · simp

/-- The Fourier multiplier operator with symbol `m`. -/
noncomputable def multOp (m : Grid N → ℂ) : Module.End ℂ (Grid N → ℂ) where
  toFun u := fun x => ∑ κ, latticeChar κ x * (m κ * dft u κ)
  map_add' u v := by
    funext x; simp [dft_add, mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    funext x; simp [dft_smul, Finset.mul_sum]; refine sum_congr rfl fun κ _ => by ring

theorem isMult_multOp (m : Grid N → ℂ) : IsMult (multOp m) m := by
  intro u k
  exact dft_synth (fun κ => m κ * dft u κ) k

theorem dft_modeFn (κ : Fin 3 → ℤ) (κ' : Grid N) :
    dft (modeFn N κ) κ' = if κ' = castVec N κ then 1 else 0 := by
  have h : modeFn N κ = fun x => ∑ κ'', latticeChar κ'' x *
      (if κ'' = castVec N κ then (1 : ℂ) else 0) := by
    funext x
    simp [modeFn]
  rw [h, dft_synth]

/-- A Fourier multiplier acts on a mode by its symbol. -/
theorem IsMult.apply_modeFn {T : Module.End ℂ (Grid N → ℂ)} {m : Grid N → ℂ} (h : IsMult T m)
    (κ : Fin 3 → ℤ) : T (modeFn N κ) = m (castVec N κ) • modeFn N κ := by
  apply eq_of_dft_eq
  intro κ'
  rw [h, dft_smul, dft_modeFn, smul_eq_mul]
  split_ifs with hk
  · rw [hk]
  · simp

/-! ### Transport to `ℓ²(V_h)` -/

/-- The stage Hilbert space `ℓ²(V_h)` (`L²(V_h, h³)` up to the unitary factor `N^{3/2}`). -/
abbrev Stage (N : ℕ) := EuclideanSpace ℂ (Grid N)

/-- An endomorphism of grid functions as a bounded operator on `ℓ²(V_h)`. -/
noncomputable def liftE (T : Module.End ℂ (Grid N → ℂ)) : Stage N →L[ℂ] Stage N :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℂ (Grid N → ℂ)).symm.toLinearMap ∘ₗ T ∘ₗ
      (WithLp.linearEquiv 2 ℂ (Grid N → ℂ)).toLinearMap)

theorem liftE_apply (T : Module.End ℂ (Grid N → ℂ)) (f : Stage N) :
    liftE T f = WithLp.toLp 2 (T f.ofLp) := rfl

theorem liftE_mul (T T' : Module.End ℂ (Grid N → ℂ)) : liftE (T * T') = liftE T * liftE T' := by
  ext f : 1
  rfl

theorem liftE_one : liftE (1 : Module.End ℂ (Grid N → ℂ)) = 1 := by
  ext f : 1
  rfl

theorem stage_norm_sq (f : Stage N) : ‖f‖ ^ 2 = (N : ℝ) ^ 3 * gridNormSq f.ofLp := by
  rw [EuclideanSpace.norm_sq_eq, gridNormSq]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp

/-- Multipliers bounded by `C` give operators of norm at most `C`. -/
theorem norm_liftE_multOp_le (m : Grid N → ℂ) (C : ℝ) (hC : 0 ≤ C) (hm : ∀ κ, ‖m κ‖ ≤ C) :
    ‖liftE (multOp m)‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun f => ?_
  have hsq : ‖liftE (multOp m) f‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
    rw [stage_norm_sq, mul_pow, stage_norm_sq, liftE_apply]
    rw [gridNormSq_mult (isMult_multOp m), gridNormSq_eq_sum_dft, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine sum_le_sum fun κ _ => ?_
    have := hm κ
    have h2 : ‖m κ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    have h0 : 0 ≤ (N : ℝ) ^ 3 := by positivity
    calc (N : ℝ) ^ 3 * (‖m κ‖ ^ 2 * ‖dft f.ofLp κ‖ ^ 2)
        ≤ (N : ℝ) ^ 3 * (C ^ 2 * ‖dft f.ofLp κ‖ ^ 2) := by gcongr
      _ = C ^ 2 * ((N : ℝ) ^ 3 * ‖dft f.ofLp κ‖ ^ 2) := by ring
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num) |>.mp hsq

/-! ### Stage resolvent and semigroup -/

/-- The stage generator `L_h` on `ℓ²(V_h)`. -/
noncomputable def genE (N : ℕ) [NeZero N] : Stage N →L[ℂ] Stage N := liftE (gen N)

/-- The stage resolvent `(z - L_h)⁻¹` (`z > 0`), a Fourier multiplier. -/
noncomputable def resE (N : ℕ) [NeZero N] (z : ℝ) : Stage N →L[ℂ] Stage N :=
  liftE (multOp fun κ => (((z + lam N κ : ℝ) : ℂ))⁻¹)

theorem resE_spec (z : ℝ) (hz : 0 < z) :
    ((z : ℂ) • (1 : Stage N →L[ℂ] Stage N) - genE N) * resE N z = 1 ∧
      resE N z * ((z : ℂ) • (1 : Stage N →L[ℂ] Stage N) - genE N) = 1 := by
  have hne : ∀ κ : Grid N, ((z + lam N κ : ℝ) : ℂ) ≠ 0 := fun κ => by
    have := lam_nonneg κ; exact_mod_cast (by linarith : z + lam N κ ≠ 0)
  have hA : IsMult ((z : ℂ) • (1 : Module.End ℂ (Grid N → ℂ)) - gen N)
      (fun κ => ((z + lam N κ : ℝ) : ℂ)) := by
    have := (IsMult.one.smul (z : ℂ)).sub (isMult_gen (N := N))
    intro u k; rw [this u k]; push_cast; ring
  have e1 : ((z : ℂ) • (1 : Module.End ℂ (Grid N → ℂ)) - gen N) *
      multOp (fun κ => (((z + lam N κ : ℝ) : ℂ))⁻¹) = 1 := by
    apply LinearMap.ext; intro u
    exact (hA.mul (isMult_multOp _)).apply_eq' IsMult.one (fun k => mul_inv_cancel₀ (hne k)) u
  have e2 : multOp (fun κ => (((z + lam N κ : ℝ) : ℂ))⁻¹) *
      ((z : ℂ) • (1 : Module.End ℂ (Grid N → ℂ)) - gen N) = 1 := by
    apply LinearMap.ext; intro u
    exact ((isMult_multOp _).mul hA).apply_eq' IsMult.one (fun k => inv_mul_cancel₀ (hne k)) u
  have hlift : ((z : ℂ) • (1 : Stage N →L[ℂ] Stage N) - genE N) =
      liftE ((z : ℂ) • (1 : Module.End ℂ (Grid N → ℂ)) - gen N) := by
    ext f : 1; rfl
  rw [hlift, resE, ← liftE_mul, ← liftE_mul, e1, e2, liftE_one]
  exact ⟨rfl, rfl⟩

theorem norm_resE_le (z : ℝ) (hz : 0 < z) : ‖resE N z‖ ≤ z⁻¹ := by
  refine norm_liftE_multOp_le _ _ (by positivity) fun κ => ?_
  have h := lam_nonneg κ
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  exact inv_anti₀ hz (by linarith)

/-- The stage heat semigroup multiplier `e^{-t λ_N}`. -/
noncomputable def semE (N : ℕ) [NeZero N] (t : ℝ) : Stage N →L[ℂ] Stage N :=
  liftE (multOp fun κ => ((Real.exp (-t * lam N κ) : ℝ) : ℂ))

theorem norm_semE_le (t : ℝ) (ht : 0 ≤ t) : ‖semE N t‖ ≤ 1 := by
  refine norm_liftE_multOp_le _ _ zero_le_one fun κ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have := lam_nonneg κ
  nlinarith


/-! ### The stage semigroup is `e^{t L_h}` -/

/-- The grid character mode `x ↦ e(κ·x)` for a grid frequency `κ`. -/
noncomputable def modeG (κ : Grid N) : Stage N := WithLp.toLp 2 fun x => latticeChar κ x

theorem dft_modeG (κ κ' : Grid N) :
    dft (modeG κ).ofLp κ' = if κ' = κ then 1 else 0 := by
  have h : (modeG κ).ofLp = fun x => ∑ κ'', latticeChar κ'' x *
      (if κ'' = κ then (1 : ℂ) else 0) := by
    funext x
    simp [modeG]
  rw [h, dft_synth]

theorem liftE_modeG {T : Module.End ℂ (Grid N → ℂ)} {m : Grid N → ℂ} (h : IsMult T m)
    (κ : Grid N) : liftE T (modeG κ) = m κ • modeG κ := by
  rw [liftE_apply]
  have : T (modeG κ).ofLp = m κ • (modeG κ).ofLp := by
    apply eq_of_dft_eq
    intro κ'
    rw [h, dft_smul, dft_modeG, smul_eq_mul]
    split_ifs with hk
    · rw [hk]
    · simp
  rw [this]
  rfl

theorem stage_expand (f : Stage N) : f = ∑ κ, dft f.ofLp κ • modeG κ := by
  ext x
  simp only [modeG, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [← dft_inversion f.ofLp x]
  refine sum_congr rfl fun κ _ => mul_comm _ _

/-- The exponential of an operator on an eigenvector. -/
theorem exp_apply_of_eigen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (v : E) (μ : ℂ) (h : A v = μ • v) :
    NormedSpace.exp A v = Complex.exp μ • v := by
  have hpow : ∀ n : ℕ, (A ^ n) v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, h, smul_smul, pow_succ]
  rw [NormedSpace.exp_eq_tsum ℂ]
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have happ := (ContinuousLinearMap.apply ℂ E v).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at happ
  rw [happ]
  simp only [ContinuousLinearMap.smul_apply, hpow, smul_smul]
  have hμ := NormedSpace.expSeries_summable' (𝕂 := ℂ) μ
  simp only [smul_eq_mul] at hμ
  rw [hμ.tsum_smul_const, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ]
  simp [smul_eq_mul]

/-- `lem:supp-flat-symbol`, semigroup identification: the stage multiplier `e^{-tλ_N}` is the
heat semigroup `e^{t L_h}` of the root generator. -/
theorem semE_eq_exp (t : ℝ) : semE N t = NormedSpace.exp ((t : ℂ) • genE N) := by
  ext f : 1
  conv_lhs => rw [stage_expand f]
  conv_rhs => rw [stage_expand f]
  rw [map_sum, map_sum]
  refine sum_congr rfl fun κ _ => ?_
  rw [map_smul, map_smul]
  congr 1
  rw [semE, liftE_modeG (isMult_multOp _),
    exp_apply_of_eigen _ _ (-(t : ℂ) * (lam N κ : ℂ))]
  · congr 1
    push_cast
    rfl
  · rw [ContinuousLinearMap.smul_apply, genE, liftE_modeG isMult_gen, smul_smul]
    congr 1
    ring

/-! ### The continuum Fourier multipliers on `L²(𝕋³)` -/

/-- A bounded multiplier on `ℓ²(ℤ³)`. -/
noncomputable def mulL2 (m : (Fin 3 → ℤ) → ℂ) (C : ℝ) (hm : ∀ κ, ‖m κ‖ ≤ C) :
    lp (fun _ : Fin 3 → ℤ => ℂ) 2 →L[ℂ] lp (fun _ : Fin 3 → ℤ => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨fun κ => m κ * a κ, Memℓp.mono' ((lp.memℓp a).const_smul (C : ℂ))
        (fun κ => by
          rw [norm_mul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right ((hm κ).trans (le_abs_self C)) (norm_nonneg _))⟩
      map_add' := fun a b => by
        ext κ
        change m κ * (a + b) κ = m κ * a κ + m κ * b κ
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c a => by
        ext κ
        change m κ * (c • a) κ = c * (m κ * a κ)
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    |C| (fun a => by
      have h := lp.norm_mono (p := 2) (by norm_num)
        (x := (⟨fun κ => m κ * a κ, Memℓp.mono' ((lp.memℓp a).const_smul (C : ℂ))
          (fun κ => by
            rw [norm_mul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right ((hm κ).trans (le_abs_self C))
              (norm_nonneg _))⟩ : lp (fun _ : Fin 3 → ℤ => ℂ) 2))
        (y := (C : ℂ) • a) (fun κ => by
          simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, norm_mul, Complex.norm_real,
            Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right ((hm κ).trans (le_abs_self C)) (norm_nonneg _))
      refine h.trans (le_of_eq ?_)
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs])

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

/-- The Fourier multiplier on `L²(𝕋³)` with symbol `m`. -/
noncomputable def contOp (m : (Fin 3 → ℤ) → ℂ) (C : ℝ) (hm : ∀ κ, ‖m κ‖ ≤ C) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) :=
  (mFourierBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((mulL2 m C hm).comp mFourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem contOp_mode (m : (Fin 3 → ℤ) → ℂ) (C : ℝ) (hm : ∀ κ, ‖m κ‖ ≤ C) (κ : Fin 3 → ℤ) :
    contOp m C hm (mFourierLp 2 κ) = m κ • mFourierLp 2 κ := by
  have h1 : mFourierBasis.repr (mFourierLp 2 κ) = lp.single 2 κ (1 : ℂ) := by
    rw [← coe_mFourierBasis, HilbertBasis.repr_self]
  have h2 : mulL2 m C hm (lp.single 2 κ (1 : ℂ)) = m κ • lp.single 2 κ (1 : ℂ) := by
    ext κ'
    simp only [mulL2, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
      lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
    split_ifs with h
    · subst h; simp
    · simp
  simp only [contOp, ContinuousLinearMap.comp_apply]
  erw [h1]
  rw [h2]
  erw [map_smul, HilbertBasis.repr_symm_single, coe_mFourierBasis]

theorem norm_mulL2_le (m : (Fin 3 → ℤ) → ℂ) (C : ℝ) (hm : ∀ κ, ‖m κ‖ ≤ C) :
    ‖mulL2 m C hm‖ ≤ |C| :=
  LinearMap.mkContinuous_norm_le _ (abs_nonneg C) _

theorem norm_contOp_le (m : (Fin 3 → ℤ) → ℂ) (C : ℝ) (hC : 0 ≤ C) (hm : ∀ κ, ‖m κ‖ ≤ C) :
    ‖contOp m C hm‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun f => ?_
  simp only [contOp, ContinuousLinearMap.comp_apply]
  erw [LinearIsometryEquiv.norm_map]
  refine ((mulL2 m C hm).le_opNorm _).trans ?_
  erw [LinearIsometryEquiv.norm_map]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact (norm_mulL2_le m C hm).trans (le_of_eq (abs_of_nonneg hC))


/-! ### Pointwise symbol limit -/

/-- `lem:supp-flat-symbol`, `eq:supp-flat-symbol-limit`: `λ_h(k) → 2π²‖k‖²` for every fixed
`k` (here along `h = 1/(n+1)`). -/
theorem tendsto_flatSymbol (k : Fin 3 → ℝ) :
    Tendsto (fun n : ℕ => HomogeneousADMPacket.flatSymbol (1 / ((n + 1 : ℕ) : ℝ)) k) atTop
      (𝓝 (2 * π ^ 2 * ∑ i, k i ^ 2)) := by
  set h : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ) with hdef
  have hh : Tendsto h atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine this.congr fun n => ?_
    simp [hdef]
  have hne : ∀ n, h n ≠ 0 := fun n => by simp [hdef]; positivity
  have hsmall : ∀ᶠ n in atTop, ∀ a, |2 * Real.pi * h n * HomogeneousADMPacket.rootPairing k a| ≤ 1 := by
    rw [Filter.eventually_all]
    intro a
    have ht : Tendsto (fun n => 2 * Real.pi * h n * HomogeneousADMPacket.rootPairing k a) atTop
        (𝓝 0) := by
      have := (hh.const_mul (2 * Real.pi)).mul_const (HomogeneousADMPacket.rootPairing k a)
      simpa using this
    filter_upwards [Metric.tendsto_nhds.mp ht 1 one_pos] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact hn.le
  set K : ℝ := 5 / 96 * (2 * Real.pi) ^ 4 * (∑ a, HomogeneousADMPacket.rootPairing k a ^ 4) / 4
  have hbound : ∀ᶠ n in atTop, ‖HomogeneousADMPacket.flatSymbol (h n) k -
      2 * π ^ 2 * ∑ i, k i ^ 2‖ ≤ K * h n ^ 2 := by
    filter_upwards [hsmall] with n hn
    rw [Real.norm_eq_abs]
    refine (HomogeneousADMPacket.flat_symbol_expansion (h n) (hne n) k hn).trans (le_of_eq ?_)
    simp only [K]; ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
  have := (hh.pow 2).const_mul K
  simpa using this

/-! ### Grid samples of Fourier modes are stage eigenvectors -/

theorem mFourier_samplePt (κ : Fin 3 → ℤ) (x : Grid N) :
    mFourier κ (samplePt x) = latticeChar (castVec N κ) x := by
  simp only [mFourier, ContinuousMap.coe_mk, latticeChar, samplePt, castVec]
  refine prod_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  have e : (κ i : ZMod N) * x i = (((κ i * ((x i).val : ℤ) : ℤ) : ZMod N)) := by
    push_cast
    simp
  rw [e, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

theorem modeSample_eq (κ : Fin 3 → ℤ) :
    modeSample N κ = ((Real.sqrt N ^ 3 : ℝ) : ℂ)⁻¹ • WithLp.toLp 2 (modeFn N κ) := by
  ext x
  simp [modeSample, modeFn, mFourier_samplePt]

theorem liftE_modeSample {T : Module.End ℂ (Grid N → ℂ)} {m : Grid N → ℂ} (h : IsMult T m)
    (κ : Fin 3 → ℤ) : liftE T (modeSample N κ) = m (castVec N κ) • modeSample N κ := by
  rw [modeSample_eq, map_smul, liftE_apply, smul_comm]
  congr 1
  rw [WithLp.ofLp_toLp, IsMult.apply_modeFn h κ]
  rfl

/-! ### The varying Hilbert system and the mode criterion -/

/-- The varying Hilbert system of natural piecewise-constant embeddings, stage `n` having mesh
`h = 1/(n+1)`. -/
noncomputable def pcSystem :
    VaryingHilbert.System (K := ℂ) (H := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))))
      (Hn := fun n => Stage (n + 1)) where
  embedding n := pcEmbedding (n + 1)

/-- The adjoint `J_h^*` (cell averaging). -/
noncomputable def adj (n : ℕ) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) →L[ℂ] Stage (n + 1) :=
  ContinuousLinearMap.adjoint (pcEmbedding (n + 1)).toContinuousLinearMap

theorem adj_embedding (n : ℕ) (s : Stage (n + 1)) : adj n (pcEmbedding (n + 1) s) = s := by
  apply ext_inner_right ℂ
  intro y
  rw [adj, ContinuousLinearMap.adjoint_inner_left]
  exact (pcEmbedding (n + 1)).inner_map_map s y

theorem norm_adj_le (n : ℕ) : ‖adj n‖ ≤ 1 := by
  rw [adj, LinearIsometryEquiv.norm_map]
  exact (pcEmbedding (n + 1)).norm_toContinuousLinearMap_le

theorem tendsto_mode (T : ∀ n, Stage (n + 1) →L[ℂ] Stage (n + 1)) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ n, ‖T n‖ ≤ C) (μ : ℕ → ℂ) (μc : ℂ) (hμ : Tendsto μ atTop (𝓝 μc))
    (κ : Fin 3 → ℤ) (hTm : ∀ n, T n (modeSample (n + 1) κ) = μ n • modeSample (n + 1) κ) :
    Tendsto (fun n => pcEmbedding (n + 1) (T n (adj n (mFourierLp 2 κ)))) atTop
      (𝓝 (μc • mFourierLp 2 κ)) := by
  set e := mFourierLp 2 κ
  set a : ℕ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) :=
    fun n => pcEmbedding (n + 1) (modeSample (n + 1) κ) with ha_def
  have ha : Tendsto a atTop (𝓝 e) := tendsto_pcEmbedding_mode κ
  have hsplit : ∀ n, pcEmbedding (n + 1) (T n (adj n e)) =
      pcEmbedding (n + 1) (T n (adj n (e - a n))) + μ n • a n := by
    intro n
    rw [map_sub, map_sub, map_sub, ha_def]
    simp only
    rw [adj_embedding, hTm, map_smul]
    abel
  have h1 : Tendsto (fun n => pcEmbedding (n + 1) (T n (adj n (e - a n)))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ n, ‖pcEmbedding (n + 1) (T n (adj n (e - a n)))‖ ≤ C * ‖e - a n‖ := by
      intro n
      rw [LinearIsometry.norm_map]
      calc ‖T n (adj n (e - a n))‖ ≤ ‖T n‖ * ‖adj n (e - a n)‖ := (T n).le_opNorm _
        _ ≤ C * (1 * ‖e - a n‖) := by
          gcongr
          · exact hT n
          · exact ((adj n).le_opNorm _).trans (by gcongr; exact norm_adj_le n)
        _ = C * ‖e - a n‖ := by ring
    refine squeeze_zero (fun _ => norm_nonneg _) hb ?_
    have : Tendsto (fun n => ‖e - a n‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.mp ha)
      refine this.congr fun n => ?_
      rw [norm_sub_rev]
    simpa using this.const_mul C
  have h2 : Tendsto (fun n => μ n • a n) atTop (𝓝 (μc • e)) := hμ.smul ha
  have := h1.add h2
  rw [zero_add] at this
  exact this.congr fun n => (hsplit n).symm

theorem dense_span_mFourierLp :
    Dense (Submodule.span ℂ (Set.range (mFourierLp (d := Fin 3) 2)) :
      Set (Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))))) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
    span_mFourierLp_closure_eq_top (by norm_num)]
  rfl

theorem tendsto_of_mem_span
    (A : ℕ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))))
    (B : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))))
    (h : ∀ κ, Tendsto (fun n => A n (mFourierLp 2 κ)) atTop (𝓝 (B (mFourierLp 2 κ)))) :
    ∀ d ∈ Submodule.span ℂ (Set.range (mFourierLp (d := Fin 3) 2)),
      Tendsto (fun n => A n d) atTop (𝓝 (B d)) := by
  intro d hd
  induction hd using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨κ, rfl⟩ := hx
    exact h κ
  | zero => simpa using tendsto_const_nhds
  | add x y _ _ hx hy => simpa [map_add] using hx.add hy
  | smul c x _ hx => simpa [map_smul] using hx.const_smul c

/-- Mode criterion for strong operator convergence along the piecewise-constant embeddings: a
uniformly bounded family of stage operators acting on the grid samples of the Fourier modes by
convergent eigenvalues converges strongly to the continuum Fourier multiplier. -/
theorem strongOperatorConverges_of_modes (T : ∀ n, Stage (n + 1) →L[ℂ] Stage (n + 1))
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ n, ‖T n‖ ≤ C)
    (Tc : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))))
    (μ : ℕ → (Fin 3 → ℤ) → ℂ) (μc : (Fin 3 → ℤ) → ℂ)
    (hμ : ∀ κ, Tendsto (fun n => μ n κ) atTop (𝓝 (μc κ)))
    (hTm : ∀ n κ, T n (modeSample (n + 1) κ) = μ n κ • modeSample (n + 1) κ)
    (hTc : ∀ κ, Tc (mFourierLp 2 κ) = μc κ • mFourierLp 2 κ) :
    pcSystem.StrongOperatorConverges pcSystem T Tc := by
  refine VaryingHilbert.System.strongOperatorConverges_of_dense_sources_of_uniform_opNorm
    pcSystem pcSystem T Tc _ dense_span_mFourierLp (fun d n => adj n d) ?_ C hC hT ?_
  · intro d hd
    have := tendsto_of_mem_span
      (fun n => (pcEmbedding (n + 1)).toLinearMap ∘ₗ (adj n).toLinearMap) LinearMap.id
      (fun κ => by
        have := tendsto_mode (fun _ => ContinuousLinearMap.id ℂ _) 1 zero_le_one
          (fun _ => ContinuousLinearMap.norm_id_le) (fun _ => 1) 1
          tendsto_const_nhds κ (fun n => by simp)
        simpa using this) d hd
    exact this
  · intro d hd
    have := tendsto_of_mem_span
      (fun n => (pcEmbedding (n + 1)).toLinearMap ∘ₗ (T n).toLinearMap ∘ₗ (adj n).toLinearMap)
      Tc.toLinearMap
      (fun κ => by
        have := tendsto_mode T C hC hT (fun n => μ n κ) (μc κ) (hμ κ) κ (fun n => hTm n κ)
        simpa [hTc κ] using this) d hd
    exact this

/-! ### `lem:supp-flat-symbol`: strong resolvent and semigroup convergence -/

/-- The continuum symbol `μ(k) = 2π²‖k‖²` of `-½Δ` at the dual vector `k = kvec κ`. -/
noncomputable def contSymbol (κ : Fin 3 → ℤ) : ℝ := 2 * π ^ 2 * ∑ i, kvec κ i ^ 2

theorem contSymbol_nonneg (κ : Fin 3 → ℤ) : 0 ≤ contSymbol κ := by
  unfold contSymbol; positivity

/-- The resolvent `(z - ½Δ)⁻¹` of the torus Laplacian, as the Fourier multiplier
`(z + 2π²‖k‖²)⁻¹`. -/
noncomputable def contRes (z : ℝ) (hz : 0 < z) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) :=
  contOp (fun κ => (((z + contSymbol κ : ℝ)) : ℂ)⁻¹) z⁻¹ (fun κ => by
    have := contSymbol_nonneg κ
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact inv_anti₀ hz (by linarith))

/-- The heat semigroup `e^{t½Δ}` of the torus, as the Fourier multiplier `e^{-2π²t‖k‖²}`. -/
noncomputable def contSem (t : ℝ) (ht : 0 ≤ t) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) :=
  contOp (fun κ => ((Real.exp (-t * contSymbol κ) : ℝ) : ℂ)) 1 (fun κ => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have := contSymbol_nonneg κ
    nlinarith)

theorem lam_castVec_tendsto (κ : Fin 3 → ℤ) :
    Tendsto (fun n : ℕ => lam (n + 1) (castVec (n + 1) κ)) atTop (𝓝 (contSymbol κ)) := by
  have := tendsto_flatSymbol (kvec κ)
  refine this.congr fun n => ?_
  rw [lam_castVec]

/-- `lem:supp-flat-symbol`, `eq:supp-flat-generator-limit` (strong resolvent sense): for every
`z > 0`, `(z - L_h)⁻¹ → (z - ½Δ)⁻¹` strongly along the natural piecewise-constant embeddings. -/
theorem flat_resolvent_strong (z : ℝ) (hz : 0 < z) :
    pcSystem.StrongOperatorConverges pcSystem (fun n => resE (n + 1) z) (contRes z hz) := by
  refine strongOperatorConverges_of_modes _ z⁻¹ (by positivity) (fun n => norm_resE_le z hz)
    (contRes z hz) (fun n κ => (((z + lam (n + 1) (castVec (n + 1) κ) : ℝ)) : ℂ)⁻¹)
    (fun κ => (((z + contSymbol κ : ℝ)) : ℂ)⁻¹) (fun κ => ?_) (fun n κ => ?_) (fun κ => ?_)
  · have h1 := ((lam_castVec_tendsto κ).const_add z)
    have h2 : Tendsto (fun n : ℕ => (((z + lam (n + 1) (castVec (n + 1) κ) : ℝ)) : ℂ)) atTop
        (𝓝 (((z + contSymbol κ : ℝ)) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp h1
    have hne : (((z + contSymbol κ : ℝ)) : ℂ) ≠ 0 := by
      have := contSymbol_nonneg κ; exact_mod_cast (by linarith : z + contSymbol κ ≠ 0)
    exact h2.inv₀ hne
  · exact liftE_modeSample (isMult_multOp _) κ
  · exact contOp_mode _ _ _ κ

/-- `lem:supp-flat-symbol`, semigroup clause: for every `t ≥ 0`, `e^{tL_h} → e^{t½Δ}` strongly
along the natural piecewise-constant embeddings. -/
theorem flat_semigroup_strong (t : ℝ) (ht : 0 ≤ t) :
    pcSystem.StrongOperatorConverges pcSystem (fun n => NormedSpace.exp ((t : ℂ) • genE (n + 1)))
      (contSem t ht) := by
  simp_rw [← semE_eq_exp]
  refine strongOperatorConverges_of_modes _ 1 zero_le_one (fun n => norm_semE_le t ht)
    (contSem t ht) (fun n κ => ((Real.exp (-t * lam (n + 1) (castVec (n + 1) κ)) : ℝ) : ℂ))
    (fun κ => ((Real.exp (-t * contSymbol κ) : ℝ) : ℂ)) (fun κ => ?_) (fun n κ => ?_)
    (fun κ => ?_)
  · have h1 := ((lam_castVec_tendsto κ).const_mul (-t))
    have h2 := (Real.continuous_exp.tendsto _).comp h1
    exact (Complex.continuous_ofReal.tendsto _).comp h2
  · exact liftE_modeSample (isMult_multOp _) κ
  · exact contOp_mode _ _ _ κ

end RenewalGeometry.A3FlatGenerator
