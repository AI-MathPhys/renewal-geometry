/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PrototypeWardClosure
import NCG.Grand.EntropicHodgeContinuumExact
import NCG.Grand.GTMoscoEquivalenceExact
import NCG.Grand.VaryingHilbertStrongBoundedness

/-!
# Prototype action to physical-time Ward closure

Exact assembly for `cor:prototype-Ward-closure`.  The finite Ward telescoping
estimate is combined with the dimension-free implicit-Euler estimate and the
Grand-Tensor Mosco theorem.  The final perturbation lemma says that a family
which is uniformly close in operator norm to the cutoff heat semigroups has
the same compact-time strong limit on the varying Hilbert spaces.
-/

open Asymptotics Filter Set Topology Matrix NCG.VaryingHilbert
  NCG.VaryingHilbert.System
open scoped ComplexOrder Norms.L2Operator ENNReal

noncomputable section

namespace NCG
namespace PrototypeWardPhysicalTime

universe u v x

variable {iota : ℕ → Type u}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type x} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
variable {Fn : ℕ → Type x}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ ℂ (Fn n)]

/-- A uniform operator-norm perturbation of a varying-space semigroup has the
same compact-time strong limit.  This is the analytic form of shorting the
Ward residual after the finite telescoping estimate. -/
theorem strongUniform_of_operatorNorm_close
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (iota n)))
    {S₁ S₂ : ∀ n, ℝ → EuclideanSpace ℂ (iota n) →L[ℂ]
      EuclideanSpace ℂ (iota n)}
    {S : ℝ → H →L[ℂ] H} {s : Set ℝ}
    (hS₂ : J.StrongOperatorConvergesUniformlyOn S₂ S s)
    (hclose : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ s,
      ‖S₁ n t - S₂ n t‖ < ε) :
    J.StrongOperatorConvergesUniformlyOn S₁ S s := by
  intro z zlim hz
  rw [Metric.tendstoUniformlyOn_iff]
  have hS₂z := hS₂ z zlim hz
  rw [Metric.tendstoUniformlyOn_iff] at hS₂z
  obtain ⟨C, hC, hzC⟩ := hz.exists_pos_uniform_norm_bound J
  intro ε hε
  have hnear := hclose (ε / (2 * C)) (by positivity)
  have hheat := hS₂z (ε / 2) (by positivity)
  filter_upwards [hnear, hheat] with n hn hSn
  intro t ht
  have happ : dist (J.embedding n (S₂ n t (z n)))
      (J.embedding n (S₁ n t (z n))) < ε / 2 := by
    rw [dist_eq_norm, ← map_sub, (J.embedding n).norm_map]
    calc
      ‖S₂ n t (z n) - S₁ n t (z n)‖
          = ‖(S₂ n t - S₁ n t) (z n)‖ := by rfl
      _ ≤ ‖S₂ n t - S₁ n t‖ * ‖z n‖ :=
        (S₂ n t - S₁ n t).le_opNorm (z n)
      _ = ‖S₁ n t - S₂ n t‖ * ‖z n‖ := by rw [norm_sub_rev]
      _ ≤ ‖S₁ n t - S₂ n t‖ * C :=
        mul_le_mul_of_nonneg_left (hzC n) (norm_nonneg _)
      _ < (ε / (2 * C)) * C :=
        mul_lt_mul_of_pos_right (hn t ht) hC
      _ = ε / 2 := by field_simp
  calc
    dist (S t zlim) (J.embedding n (S₁ n t (z n)))
        ≤ dist (S t zlim) (J.embedding n (S₂ n t (z n)))
          + dist (J.embedding n (S₂ n t (z n)))
            (J.embedding n (S₁ n t (z n))) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hSn t ht) happ
    _ = ε := by ring

section FiniteEstimate

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The noise-shorted Ward Gram has the square of the one-step residual as an
operator-norm upper bound. -/
theorem wardGram_norm_le_sq (K W : Matrix E E ℂ) :
    ‖star (K - W) * (K - W)‖ ≤ ‖K - W‖ ^ 2 := by
  calc
    ‖star (K - W) * (K - W)‖
        ≤ ‖star (K - W)‖ * ‖K - W‖ := Matrix.l2_opNorm_mul _ _
    _ = ‖K - W‖ ^ 2 := by rw [norm_star]; ring

/-- Exact finite-cutoff physical-time Ward estimate.  The first term is the
telescoped actual-step residual and the last two terms are the dimension-free
implicit-Euler and time-rounding errors. -/
theorem actual_power_sub_heat_le
    (K A : Matrix E E ℂ) (hK : ‖K‖ ≤ 1) (hA : A.PosSemidef)
    {B tau t : ℝ} (htau : 0 < tau) (htaut : tau ≤ t)
    (hB0 : 0 ≤ B) (hB : ∀ i, hA.1.eigenvalues i ≤ B)
    (hW : ‖((1 : Matrix E E ℂ) + ((tau : ℂ) • A))⁻¹‖ ≤ 1) :
    ‖Matrix.toEuclideanCLM (n := E) (𝕜 := ℂ) (K ^ ⌊t / tau⌋₊) -
        NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := E) (𝕜 := ℂ) A)‖
      ≤ (⌊t / tau⌋₊ : ℕ) *
          ‖K - ((1 : Matrix E E ℂ) + ((tau : ℂ) • A))⁻¹‖
        + (Real.sqrt (⌊t / tau⌋₊ : ℝ))⁻¹ + tau * B := by
  let W : Matrix E E ℂ :=
    ((1 : Matrix E E ℂ) + ((tau : ℂ) • A))⁻¹
  have hW' : ‖W‖ ≤ 1 := by simpa [W] using hW
  have hfinite := (prototype_ward_closure K W hK hW').1 ⌊t / tau⌋₊
  have hfiniteCLM :
      ‖Matrix.toEuclideanCLM (n := E) (𝕜 := ℂ)
          (K ^ ⌊t / tau⌋₊ - W ^ ⌊t / tau⌋₊)‖
        ≤ (⌊t / tau⌋₊ : ℕ) * ‖K - W‖ := by
    change ‖K ^ ⌊t / tau⌋₊ - W ^ ⌊t / tau⌋₊‖
      ≤ (⌊t / tau⌋₊ : ℕ) * ‖K - W‖
    exact hfinite
  have hEuler := EntropicHodgeContinuum.minimizing_movement_floor
    hA htau htaut hB0 hB
  calc
    ‖Matrix.toEuclideanCLM (n := E) (𝕜 := ℂ) (K ^ ⌊t / tau⌋₊) -
        NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := E) (𝕜 := ℂ) A)‖
      ≤ ‖Matrix.toEuclideanCLM (n := E) (𝕜 := ℂ)
          (K ^ ⌊t / tau⌋₊ - W ^ ⌊t / tau⌋₊)‖
        + ‖Matrix.toEuclideanCLM (n := E) (𝕜 := ℂ) (W ^ ⌊t / tau⌋₊) -
          NormedSpace.exp ((-(t : ℂ)) •
            Matrix.toEuclideanCLM (n := E) (𝕜 := ℂ) A)‖ := by
          rw [map_sub]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (⌊t / tau⌋₊ : ℕ) * ‖K - W‖
        + ((Real.sqrt (⌊t / tau⌋₊ : ℝ))⁻¹ + tau * B) :=
      add_le_add hfiniteCLM (by simpa [W] using hEuler)
    _ = (⌊t / tau⌋₊ : ℕ) *
          ‖K - ((1 : Matrix E E ℂ) + ((tau : ℂ) • A))⁻¹‖
        + (Real.sqrt (⌊t / tau⌋₊ : ℝ))⁻¹ + tau * B := by
      simp only [W]
      ring

end FiniteEstimate

/-- The literal actual predictable-step powers at physical time `t`. -/
def actualStepPowers
    (K : ∀ n, Matrix (iota n) (iota n) ℂ) (tau : ℕ → ℝ) :
    ∀ n, ℝ → EuclideanSpace ℂ (iota n) →L[ℂ]
      EuclideanSpace ℂ (iota n) :=
  fun n t ↦ Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ)
    (K n ^ ⌊t / tau n⌋₊)

/-- The manuscript's one-step hypothesis `‖K_X-W_X‖ = o(τ_X)` implies
uniform closeness of the actual floor powers to the cutoff heat semigroups on
every compact time window separated from zero.  This consumes the exact
three-term estimate `actual_power_sub_heat_le`. -/
theorem wardEuler_uniform_closeness
    (K G : ∀ n, Matrix (iota n) (iota n) ℂ)
    (tau : ℕ → ℝ) (B a T : ℝ)
    (hK : ∀ n, ‖K n‖ ≤ 1) (hG : ∀ n, (G n).PosSemidef)
    (htau : ∀ n, 0 < tau n)
    (htau0 : Tendsto tau atTop (𝓝 0))
    (hB0 : 0 ≤ B) (hB : ∀ n i, (hG n).1.eigenvalues i ≤ B)
    (ha : 0 < a) (hT : 0 < T) (s : Set ℝ)
    (hsLower : ∀ t ∈ s, a ≤ t) (hsUpper : ∀ t ∈ s, t ≤ T)
    (hW : ∀ n,
      ‖((1 : Matrix (iota n) (iota n) ℂ) +
        ((tau n : ℂ) • G n))⁻¹‖ ≤ 1)
    (hresidual : (fun n ↦
      ‖K n - ((1 : Matrix (iota n) (iota n) ℂ) +
        ((tau n : ℂ) • G n))⁻¹‖) =o[atTop] tau) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ s,
      ‖actualStepPowers K tau n t -
        NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n))‖ < ε := by
  intro ε hε
  let c : ℝ := ε / (3 * T)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmallResidual := (isLittleO_iff.mp hresidual) hc
  have hrate := NCG.ImplicitEuler.errorRate_tendsto_zero.eventually
    (eventually_lt_nhds (show 0 < ε / 3 by positivity))
  obtain ⟨M, hM⟩ := (eventually_atTop.1 hrate)
  have hMrate : NCG.ImplicitEuler.errorRate M < ε / 3 := hM M le_rfl
  have htauFloor := htau0.eventually
    (eventually_lt_nhds (show 0 < a / (M + 1 : ℕ) by positivity))
  have htauB := htau0.eventually
    (eventually_lt_nhds (show 0 < ε / (3 * (B + 1)) by positivity))
  filter_upwards [hsmallResidual, htauFloor, htauB] with n hnResidual hnFloor hnB
  intro t ht
  let k : ℕ := ⌊t / tau n⌋₊
  let e : ℝ := ‖K n - ((1 : Matrix (iota n) (iota n) ℂ) +
    ((tau n : ℂ) • G n))⁻¹‖
  have htpos : 0 < t := lt_of_lt_of_le ha (hsLower t ht)
  have htau_le_t : tau n ≤ t := by
    have hdenom : (0 : ℝ) < (M + 1 : ℕ) := by positivity
    have hsmall : tau n * (M + 1 : ℕ) < a := by
      exact (lt_div_iff₀ hdenom).mp hnFloor
    have hone : (1 : ℝ) ≤ (M + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
    have htauSmall : tau n < a :=
      lt_of_le_of_lt (by
        simpa using mul_le_mul_of_nonneg_left hone (htau n).le) hsmall
    exact le_trans htauSmall.le (hsLower t ht)
  have hmain := actual_power_sub_heat_le (K n) (G n) (hK n) (hG n)
    (htau n) htau_le_t hB0 (hB n) (hW n)
  have heNonneg : 0 ≤ e := norm_nonneg _
  have heSmall : e ≤ c * tau n := by
    simpa [e, Real.norm_eq_abs, abs_of_pos (htau n)] using hnResidual
  have hkUpper : (k : ℝ) ≤ t / tau n := by
    dsimp [k]
    exact_mod_cast Nat.floor_le (div_nonneg htpos.le (htau n).le)
  have htermOne : (k : ℝ) * e ≤ ε / 3 := by
    calc
      (k : ℝ) * e ≤ (t / tau n) * e :=
        mul_le_mul_of_nonneg_right hkUpper heNonneg
      _ ≤ (t / tau n) * (c * tau n) :=
        mul_le_mul_of_nonneg_left heSmall
          (div_nonneg htpos.le (htau n).le)
      _ = t * c := by field_simp [ne_of_gt (htau n)]
      _ ≤ T * c := mul_le_mul_of_nonneg_right (hsUpper t ht) hc.le
      _ = ε / 3 := by dsimp [c]; field_simp [ne_of_gt hT]
  have hkLower : M + 1 ≤ k := by
    apply Nat.le_floor
    have hdenom : (0 : ℝ) < (M + 1 : ℕ) := by positivity
    have hsmall : tau n * (M + 1 : ℕ) < a :=
      (lt_div_iff₀ hdenom).mp hnFloor
    rw [le_div_iff₀ (htau n)]
    exact le_trans (by simpa [mul_comm] using hsmall.le) (hsLower t ht)
  have hsqrtPos : 0 < Real.sqrt (M + 1 : ℕ) := Real.sqrt_pos.2 (by positivity)
  have hsqrtLe : Real.sqrt (M + 1 : ℕ) ≤ Real.sqrt (k : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hkLower
  have htermTwo : (Real.sqrt (k : ℝ))⁻¹ < ε / 3 := by
    have hinv : (Real.sqrt (k : ℝ))⁻¹ ≤
        (Real.sqrt (M + 1 : ℕ))⁻¹ :=
      (inv_le_inv₀ (hsqrtPos.trans_le hsqrtLe) hsqrtPos).2 hsqrtLe
    exact hinv.trans_lt (by simpa [NCG.ImplicitEuler.errorRate] using hMrate)
  have htauBbound : tau n * B < ε / 3 := by
    have hBlt : tau n * B < (ε / (3 * (B + 1))) * (B + 1) := by
      have hB1 : 0 < B + 1 := by linarith
      have := mul_lt_mul_of_pos_right hnB hB1
      nlinarith [htau n, hB0]
    calc
      tau n * B < (ε / (3 * (B + 1))) * (B + 1) := hBlt
      _ = ε / 3 := by field_simp [show B + 1 ≠ 0 by linarith]
  apply hmain.trans_lt
  change (k : ℝ) * e + (Real.sqrt (k : ℝ))⁻¹ + tau n * B < ε
  linarith

/-- **Prototype action to physical-time Ward closure**
(`cor:prototype-Ward-closure`).  Mosco convergence supplies compact-time
convergence of the reconstructed cutoff heat semigroups.  Any actual
predictable-step powers whose finite Ward/Euler bound tends uniformly to zero
therefore converge to the same physical-time semigroup.  The concrete bound
which discharges `hWardEuler` is `actual_power_sub_heat_le` above. -/
theorem prototype_ward_physical_time_closure
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (iota n)))
    (G : ∀ n, Matrix (iota n) (iota n) ℂ) (hG : ∀ n, (G n).PosSemidef)
    (Dn : ∀ n, Submodule ℂ (EuclideanSpace ℂ (iota n)))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F) (hD : Dense (D : Set H))
    (R : ℝ → H →L[ℂ] H)
    (hstageEquation : ∀ lam, 0 < lam → ∀ n
      (f : EuclideanSpace ℂ (iota n)),
      OperatorGraphResolventEquation (Dn n) (An n) lam f
        (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator (G n) lam f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (hclosed : (operatorLinearPMap D A).IsClosed)
    (hdense : J.IsAsymptoticallyDense)
    (hrealInner : ∀ x y : H, inner ℝ x y = RCLike.re (inner ℂ x y))
    (Kpower : ∀ n, ℝ → EuclideanSpace ℂ (iota n) →L[ℂ]
      EuclideanSpace ℂ (iota n))
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (b : ℝ) (hb : 0 < b) (s : Set ℝ) (hs : IsCompact s)
    (hsNonneg : ∀ t ∈ s, 0 ≤ t)
    (hWardEuler : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ s,
      ‖Kpower n t - NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n))‖ < ε) :
    J.StrongOperatorConvergesUniformlyOn Kpower
      (fun t ↦ operatorGraphResolventHeatNonnegative (R b) b t) s := by
  have hequiv := GTMosco.gt_mosco_equivalence J G hG Dn An D A hD R
    hstageEquation hlimitEquation hclosed hdense hrealInner
  have hheat := hequiv.2.1 (hequiv.1.1 hmosco)
  have hcanonical := hheat id tendsto_id b hb s hs hsNonneg
  exact strongUniform_of_operatorNorm_close J hcanonical hWardEuler

/-- A uniform quadratic coercive floor passes to the Mosco limit.  The proof
uses the recovery half of Mosco convergence; strong convergence preserves the
norm and the recovery limsup then forces the same lower floor at the limit. -/
theorem MoscoConverges.coerciveFloor
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (iota n)))
    {q : (n : ℕ) → EuclideanSpace ℂ (iota n) → ℝ≥0∞}
    {qlim : H → ℝ≥0∞} (hq : J.MoscoConverges q qlim)
    (c : ℝ) (hc : 0 ≤ c)
    (hfloor : ∀ n z, ENNReal.ofReal (c * ‖z‖ ^ 2) ≤ q n z) :
    ∀ z : H, ENNReal.ofReal (c * ‖z‖ ^ 2) ≤ qlim z := by
  intro z
  obtain ⟨zn, hzn, henergy⟩ := hq.recovery z
  have hnorm : Tendsto (fun n ↦ ‖zn n‖) atTop (𝓝 ‖z‖) := by
    simpa only [LinearIsometry.norm_map] using hzn.norm
  have hreal : Tendsto (fun n ↦ c * ‖zn n‖ ^ 2) atTop
      (𝓝 (c * ‖z‖ ^ 2)) := tendsto_const_nhds.mul (hnorm.pow 2)
  have henn : Tendsto (fun n ↦ ENNReal.ofReal (c * ‖zn n‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (c * ‖z‖ ^ 2))) := ENNReal.tendsto_ofReal hreal
  calc
    ENNReal.ofReal (c * ‖z‖ ^ 2) =
        limsup (fun n ↦ ENNReal.ofReal (c * ‖zn n‖ ^ 2)) atTop :=
      henn.limsup_eq.symm
    _ ≤ limsup (fun n ↦ q n (zn n)) atTop :=
      limsup_le_limsup (Eventually.of_forall fun n ↦ hfloor n (zn n))
    _ ≤ qlim z := henergy

/-- Full manuscript-facing closure from the literal hypotheses.  It combines
the one-step `o(tau)` Ward estimate, floor-time Euler approximation, the exact
Grand-Tensor Mosco theorem, and passage of every uniform coercive floor. -/
theorem prototype_ward_closure_from_littleO
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (iota n)))
    (G : ∀ n, Matrix (iota n) (iota n) ℂ) (hG : ∀ n, (G n).PosSemidef)
    (K : ∀ n, Matrix (iota n) (iota n) ℂ)
    (tau : ℕ → ℝ) (B a T : ℝ)
    (hK : ∀ n, ‖K n‖ ≤ 1) (htau : ∀ n, 0 < tau n)
    (htau0 : Tendsto tau atTop (𝓝 0))
    (hB0 : 0 ≤ B) (hB : ∀ n i, (hG n).1.eigenvalues i ≤ B)
    (ha : 0 < a) (hT : 0 < T)
    (hW : ∀ n, ‖((1 : Matrix (iota n) (iota n) ℂ) +
      ((tau n : ℂ) • G n))⁻¹‖ ≤ 1)
    (hresidual : (fun n ↦ ‖K n -
      ((1 : Matrix (iota n) (iota n) ℂ) +
        ((tau n : ℂ) • G n))⁻¹‖) =o[atTop] tau)
    (Dn : ∀ n, Submodule ℂ (EuclideanSpace ℂ (iota n)))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F) (hD : Dense (D : Set H))
    (R : ℝ → H →L[ℂ] H)
    (hstageEquation : ∀ lam, 0 < lam → ∀ n
      (f : EuclideanSpace ℂ (iota n)),
      OperatorGraphResolventEquation (Dn n) (An n) lam f
        (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator (G n) lam f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (hclosed : (operatorLinearPMap D A).IsClosed)
    (hdense : J.IsAsymptoticallyDense)
    (hrealInner : ∀ x y : H, inner ℝ x y = RCLike.re (inner ℂ x y))
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (b : ℝ) (hb : 0 < b) (s : Set ℝ) (hs : IsCompact s)
    (hsLower : ∀ t ∈ s, a ≤ t) (hsUpper : ∀ t ∈ s, t ≤ T) :
    J.StrongOperatorConvergesUniformlyOn (actualStepPowers K tau)
        (fun t ↦ operatorGraphResolventHeatNonnegative (R b) b t) s ∧
      ∀ c : ℝ, 0 ≤ c →
        (∀ n z, ENNReal.ofReal (c * ‖z‖ ^ 2) ≤
          ennrealOperatorGraphEnergy (Dn n) (An n) z) →
        ∀ z : H, ENNReal.ofReal (c * ‖z‖ ^ 2) ≤
          ennrealOperatorGraphEnergy D A z := by
  have hsNonneg : ∀ t ∈ s, 0 ≤ t := fun t ht ↦
    (ha.trans_le (hsLower t ht)).le
  have hclose := wardEuler_uniform_closeness K G tau B a T hK hG htau
    htau0 hB0 hB ha hT s hsLower hsUpper hW hresidual
  constructor
  · exact prototype_ward_physical_time_closure J G hG Dn An D A hD R
      hstageEquation hlimitEquation hclosed hdense hrealInner
      (actualStepPowers K tau) hmosco b hb s hs hsNonneg hclose
  · intro c hc hfloor
    exact MoscoConverges.coerciveFloor J (hmosco id tendsto_id) c hc hfloor

end PrototypeWardPhysicalTime
end NCG
