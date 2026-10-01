/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CubicalInterfaceLifting
import RenewalGeometry.Continuum.DistributionalCurvatureCompactness
import RenewalGeometry.Continuum.CubicalJumpFormula

/-!
# Constructive connection-and-interface curvature criterion
  (`thm:supp-interface-curvature`, `eq:main-lifted-curvature`, `eq:supp-connection-jumps`,
  `eq:supp-connection-interface-budget`; emergent-spacetime manuscript, supplement)

A piecewise connection `ω_h` on the uniform cubical mesh of side `h` in `ℝ^{n+1}` has a broken
(cellwise) exterior derivative `d_b ω_h` and face jumps `J_f = n_f^♭ ∧ [ω_h]_f`, related to the
full distributional derivative by `eq:supp-connection-jumps`,
`d_dist ω_h = d_b ω_h + Σ_f J_f δ_f` (`HasBrokenDerivativeJumps`).  The lifted curvature
(`eq:main-lifted-curvature`) is `R_h^lift = d_b ω_h + ω_h ∧ ω_h + 𝓛_h J` (`liftedCurvature`), with
the volume lifting `𝓛_h` of `CubicalInterfaceLifting.lean`.

* `eLpNorm_wedge_le`: `‖ω ∧ ω‖_{L²} ≤ 2 ‖ω‖_{L⁴}²` (Hölder);
* `eLpNorm_liftedCurvature_le`: `‖R^lift‖_{L²(K)} ≤ ‖d_b ω‖₂ + 2‖ω_a‖₄‖ω_b‖₄ + C 𝒥_h`;
* `norm_integral_liftedCurvature_sub_curvaturePairing_le`: the discrepancy of `R^lift` from the
  full distributional curvature `d_dist ω + ω ∧ ω` is exactly the lifting error, hence at most
  `C_U h 𝒥_h Lip(Φ)` on each test;
* `interface_curvature_criterion`: **`thm:supp-interface-curvature`**;
* `interface_curvature_exists_cluster`: existence of weak `L²` cluster points
  (finite-dimensional coefficient algebra), via `curvature_weak_compactness`;
* `connection_jump_formula`: the jump formula `eq:supp-connection-jumps` is a theorem for cellwise
  `C¹` connections (`CubicalJumpFormula.lean`), with `J_f = n_f^♭ ∧ [ω]_f` (`connectionJump`);
* `interface_curvature_criterion_cellwise`: **`thm:supp-interface-curvature`** for cellwise `C¹`
  connections, with no jump-formula hypothesis;
* `heavisideConnection`: a discontinuous cellwise connection (non-vacuity of the packet).
-/

open MeasureTheory Filter Topology ENNReal Set TopologicalSpace
open scoped NNReal Distributions

noncomputable section

namespace RenewalGeometry.InterfaceCurvature

open InterfaceLifting DistributionalCurvature

set_option linter.unusedSectionVars false

variable {n : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- `eq:supp-connection-jumps`: the full distributional exterior derivative of the piecewise
connection `ω` is its broken derivative `d_b ω` plus the face measures `Σ_f J_f δ_f`, tested
against every `ψ ∈ 𝓓(Ω)`: `⟨(d_dist ω)_{ab}, ψ⟩ = ∫ ψ (d_b ω)_{ab} + Σ_f ∫_f ψ (J_f)_{ab}`. -/
def HasBrokenDerivativeJumps (Ω : Opens (Fin (n + 1) → ℝ)) (h : ℝ) (F : Finset (Face n))
    (ω : Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (db : Fin (n + 1) → Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (J : Fin (n + 1) → Fin (n + 1) → Face n → (Fin n → ℝ) → A) : Prop :=
  ∀ ψ : 𝓓(Ω, ℝ), ∀ a b,
    -(∫ x, pderiv a ψ x • ω b x) + (∫ x, pderiv b ψ x • ω a x) =
      (∫ x, ψ x • db a b x) + faceMeasurePairing h F (J a b) ψ

/-- The lifted curvature `R_h^lift = d_b ω + ω ∧ ω + 𝓛_h J` (`eq:main-lifted-curvature`),
componentwise: `(ω ∧ ω)_{ab} = ω_a ω_b - ω_b ω_a`. -/
def liftedCurvature (h : ℝ) (η : ℝ → ℝ) (F : Finset (Face n))
    (ω : Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (db : Fin (n + 1) → Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (J : Fin (n + 1) → Fin (n + 1) → Face n → (Fin n → ℝ) → A) (a b : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) : A :=
  db a b x + (ω a x * ω b x - ω b x * ω a x) + interfaceLift h η F (J a b) x

instance holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 := by
  refine ⟨?_⟩
  have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
  rw [h4, ENNReal.mul_inv (by simp) (by simp), ← two_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-- Hölder for the matrix exterior product: `‖ω_a ω_b - ω_b ω_a‖_{L²} ≤ 2 ‖ω_a‖_{L⁴} ‖ω_b‖_{L⁴}`. -/
theorem eLpNorm_wedge_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {u v : X → A}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) :
    eLpNorm (fun x => u x * v x - v x * u x) 2 μ ≤ 2 * eLpNorm u 4 μ * eLpNorm v 4 μ := by
  have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 4) (q := 4) (r := 2) hu hv
    (fun s t => s * t - t * s) 2 (Eventually.of_forall fun x => by
      have h1 : ‖u x * v x - v x * u x‖ ≤ 2 * ‖u x‖ * ‖v x‖ := by
        calc ‖u x * v x - v x * u x‖ ≤ ‖u x * v x‖ + ‖v x * u x‖ := norm_sub_le _ _
          _ ≤ ‖u x‖ * ‖v x‖ + ‖v x‖ * ‖u x‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ = 2 * ‖u x‖ * ‖v x‖ := by ring
      rw [← NNReal.coe_le_coe]
      push_cast
      exact h1)
  simpa using this

theorem aestronglyMeasurable_interfaceLift {η : ℝ → ℝ} (hη : IsLiftingProfile η) (h : ℝ)
    (F : Finset (Face n)) (J : Face n → (Fin n → ℝ) → A)
    (hJ : ∀ f ∈ F, AEStronglyMeasurable (J f) (volume.restrict (faceBox h f))) :
    AEStronglyMeasurable (interfaceLift h η F J) volume := by
  have : interfaceLift h η F J = ∑ f ∈ F, faceLift h η f (J f) := by
    funext x; simp [interfaceLift]
  rw [this]
  exact Finset.aestronglyMeasurable_sum _ fun f hf => aestronglyMeasurable_faceLift hη h f (hJ f hf)

/-- **`L²` bound of the lifted curvature** (`eq:main-lifted-curvature`, second line):
`‖R^lift_{ab}‖_{L²(K)} ≤ ‖(d_b ω)_{ab}‖_{L²(K)} + 2 ‖ω_a‖_{L⁴(K)} ‖ω_b‖_{L⁴(K)} + C 𝒥_h`,
`C = ((n+1) ‖η‖₂²)^{1/2}`. -/
theorem eLpNorm_liftedCurvature_le {η : ℝ → ℝ} (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h)
    (K : Set (Fin (n + 1) → ℝ)) (F : Finset (Face n)) (ω : Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (db : Fin (n + 1) → Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (J : Fin (n + 1) → Fin (n + 1) → Face n → (Fin n → ℝ) → A)
    (hω : ∀ a, AEStronglyMeasurable (ω a) (volume.restrict K))
    (hdb : ∀ a b, AEStronglyMeasurable (db a b) (volume.restrict K))
    (hJ : ∀ a b, ∀ f ∈ F, MemLp (J a b f) 2 (volume.restrict (faceBox h f))) (a b : Fin (n + 1)) :
    eLpNorm (liftedCurvature h η F ω db J a b) 2 (volume.restrict K) ≤
      eLpNorm (db a b) 2 (volume.restrict K) +
        2 * eLpNorm (ω a) 4 (volume.restrict K) * eLpNorm (ω b) 4 (volume.restrict K) +
        ENNReal.ofReal (Real.sqrt ((n + 1) * ∫ s, η s ^ 2) *
          Real.sqrt (interfaceBudgetSq h F (J a b))) := by
  have hw : AEStronglyMeasurable (fun x => ω a x * ω b x - ω b x * ω a x) (volume.restrict K) :=
    ((hω a).mul (hω b)).sub ((hω b).mul (hω a))
  have hL : AEStronglyMeasurable (interfaceLift h η F (J a b)) volume :=
    aestronglyMeasurable_interfaceLift hη h F (J a b) fun f hf => (hJ a b f hf).1
  have h1 := eLpNorm_add_le ((hdb a b).add hw) hL.restrict (p := 2) (by norm_num)
  have h2 := eLpNorm_add_le (hdb a b) hw (p := 2) (by norm_num)
  have h3 := eLpNorm_wedge_le (hω a) (hω b)
  have h4 : eLpNorm (interfaceLift h η F (J a b)) 2 (volume.restrict K) ≤
      eLpNorm (interfaceLift h η F (J a b)) 2 volume :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have h5 := eLpNorm_interfaceLift_le hη hh F (J a b) (hJ a b)
  calc eLpNorm (liftedCurvature h η F ω db J a b) 2 (volume.restrict K)
      = eLpNorm ((db a b + fun x => ω a x * ω b x - ω b x * ω a x) +
          interfaceLift h η F (J a b)) 2 (volume.restrict K) := rfl
    _ ≤ _ := h1
    _ ≤ _ := add_le_add h2 (h4.trans h5)
    _ ≤ _ := by gcongr

/-- A test function on `int K` times a function integrable on `K` is integrable. -/
theorem integrable_test_smul {K : Set (Fin (n + 1) → ℝ)} (hK : IsCompact K)
    (ψ : 𝓓(interiorOpens K, ℝ)) {G : (Fin (n + 1) → ℝ) → A} (hG : IntegrableOn G K) :
    Integrable fun x => ψ x • G x := by
  obtain ⟨M, hM⟩ := exists_bound_of_eq_zero_off ψ.continuous ψ.hasCompactSupport
    fun x hx => test_eq_zero_off ψ hx
  have h1 : IntegrableOn (fun x => ψ x • G x) K := by
    refine hG.smul_of_top_right (φ := fun x => ψ x) ?_
    exact memLp_top_of_bound ψ.continuous.aestronglyMeasurable M (Eventually.of_forall hM)
  refine h1.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  have : x ∉ tsupport ψ := fun h => hx (interior_subset (ψ.tsupport_subset h))
  rw [test_eq_zero_off ψ this, zero_smul]

/-- **Distributional error of the lifted curvature** (`eq:main-lifted-curvature`, last
sentence): under the jump formula `eq:supp-connection-jumps`, the discrepancy
`⟨R^lift - (d_dist ω + ω ∧ ω), Φ⟩` equals the lifting error `⟨𝓛_h J - Σ J_f δ_f, Φ⟩` and is
therefore at most `C_U h 𝒥_h Lip(Φ)`. -/
theorem norm_integral_liftedCurvature_sub_curvaturePairing_le {η : ℝ → ℝ}
    (hη : IsLiftingProfile η) {h : ℝ} (hh : 0 < h) {K : Set (Fin (n + 1) → ℝ)}
    (hK : IsCompact K) (F : Finset (Face n)) (ω : Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (db : Fin (n + 1) → Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (J : Fin (n + 1) → Fin (n + 1) → Face n → (Fin n → ℝ) → A)
    (hjump : HasBrokenDerivativeJumps (interiorOpens K) h F ω db J)
    (hω : ∀ a, MemLp (ω a) 4 (volume.restrict K))
    (hdb : ∀ a b, MemLp (db a b) 2 (volume.restrict K))
    (hJ : ∀ a b, ∀ f ∈ F, MemLp (J a b f) 2 (volume.restrict (faceBox h f)))
    {U : Set (Fin (n + 1) → ℝ)} (hU : ∀ f ∈ F, cell h f.2 ⊆ U) (hUf : volume U ≠ ∞)
    (ψ : 𝓓(interiorOpens K, ℝ)) {L : ℝ≥0} (hL : LipschitzWith L ψ) (a b : Fin (n + 1)) :
    ‖(∫ x, ψ x • liftedCurvature h η F ω db J a b x) - curvaturePairing ω ψ a b‖ ≤
      (1 / 4 * Real.sqrt ((n + 1) * (volume U).toReal)) * h *
        Real.sqrt (interfaceBudgetSq h F (J a b)) * L := by
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hdb1 : IntegrableOn (db a b) K := (hdb a b).integrable (by norm_num)
  have hm : ∀ c e, IntegrableOn (fun x => ω c x * ω e x) K := fun c e =>
    ((hω e).mul' (hω c) (r := 2)).integrable (by norm_num)
  have hLm : MemLp (interfaceLift h η F (J a b)) 2 volume :=
    ⟨aestronglyMeasurable_interfaceLift hη h F (J a b) fun f hf => (hJ a b f hf).1,
      (eLpNorm_interfaceLift_le hη hh F (J a b) (hJ a b)).trans_lt ENNReal.ofReal_lt_top⟩
  have hL1 : IntegrableOn (interfaceLift h η F (J a b)) K :=
    (hLm.restrict K).integrable (by norm_num)
  have i1 := integrable_test_smul hK ψ hdb1
  have i2 := integrable_test_smul hK ψ (hm a b)
  have i3 := integrable_test_smul hK ψ (hm b a)
  have i4 := integrable_test_smul hK ψ hL1
  have hsplit : ∫ x, ψ x • liftedCurvature h η F ω db J a b x =
      (∫ x, ψ x • db a b x) + ((∫ x, ψ x • (ω a x * ω b x)) - ∫ x, ψ x • (ω b x * ω a x)) +
        ∫ x, ψ x • interfaceLift h η F (J a b) x := by
    have j2 : Integrable (fun x => ψ x • (ω a x * ω b x) - ψ x • (ω b x * ω a x)) := i2.sub i3
    have j1 : Integrable (fun x => ψ x • db a b x +
        (ψ x • (ω a x * ω b x) - ψ x • (ω b x * ω a x))) := i1.add j2
    simp only [liftedCurvature, smul_add, smul_sub]
    rw [integral_add j1 i4, integral_add i1 j2, integral_sub i2 i3]
  have hcp : curvaturePairing ω ψ a b = (∫ x, ψ x • db a b x) +
      faceMeasurePairing h F (J a b) ψ +
        ((∫ x, ψ x • (ω a x * ω b x)) - ∫ x, ψ x • (ω b x * ω a x)) := by
    rw [curvaturePairing, ← hjump ψ a b]; abel
  have hdiff : (∫ x, ψ x • liftedCurvature h η F ω db J a b x) - curvaturePairing ω ψ a b =
      (∫ x, ψ x • interfaceLift h η F (J a b) x) - faceMeasurePairing h F (J a b) ψ := by
    rw [hsplit, hcp]; abel
  obtain ⟨M, hM⟩ := exists_bound_of_eq_zero_off ψ.continuous ψ.hasCompactSupport
    fun x hx => test_eq_zero_off ψ hx
  rw [hdiff]
  exact (interface_lifting_bounds hη hh F (J a b) (hJ a b) hU hUf).2 ψ M
    (fun x => by simpa [Real.norm_eq_abs] using hM x) L hL

theorem integral_test_smul_eq_setIntegral {K : Set (Fin (n + 1) → ℝ)}
    (ψ : 𝓓(interiorOpens K, ℝ)) (G : (Fin (n + 1) → ℝ) → A) :
    ∫ x, ψ x • G x = ∫ x in K, ψ x • G x := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  have : x ∉ tsupport ψ := fun h => hx (interior_subset (ψ.tsupport_subset h))
  rw [test_eq_zero_off ψ this, zero_smul]

/-- Every test function is Lipschitz (`‖∇Φ‖_∞ < ∞`). -/
theorem exists_lipschitzWith_test {Ω : Opens (Fin (n + 1) → ℝ)} (ψ : 𝓓(Ω, ℝ)) :
    ∃ L, LipschitzWith L ψ :=
  ContDiff.lipschitzWith_of_hasCompactSupport ψ.hasCompactSupport ψ.contDiff (by simp)

/-- **Constructive connection-and-interface curvature criterion
(`thm:supp-interface-curvature`).**  Let `K ⊆ ℝ^{n+1}` be compact, `η` a lifting profile, and,
for each mesh width `h_m > 0`, let `ω_m` be a piecewise connection on the cubical mesh of side
`h_m` (coefficients in a complete normed algebra `A`, e.g. a matrix Lie algebra) with broken
derivative `(d_b ω_m)_{ab}` and face jumps `(J_m)_{ab,f} ∈ L²(f)` over a finite face family `F_m`
whose cells lie in a fixed `U` of finite volume, satisfying the jump formula
`eq:supp-connection-jumps` on `int K`.  Assume the budget `eq:supp-connection-interface-budget`
`‖d_b ω_m‖_{L²(K)} + ‖ω_m‖_{L⁴(K)}² + 𝒥_{h_m} ≤ C_K` (componentwise).  Then:
1. `R^lift_m` is uniformly bounded in `L²(K)`, by `C_K (3 + ((n+1)‖η‖₂²)^{1/2})`;
2. its discrepancy from the full distributional curvature `d_dist ω_m + ω_m ∧ ω_m` is at most
   `C_U h_m C_K Lip(Φ)` on every test `Φ ∈ 𝓓(int K)`, `C_U = ¼((n+1) vol U)^{1/2}`;
3. if moreover `h_m → 0` and `ω_m → ω` strongly in `L²_loc(int K)`, every weak `L²(K)` cluster
   point `R` of `R^lift_m` (limit of a subsequence tested against `L²(K)`) satisfies
   `R = dω + ω ∧ ω` in distributions on `int K`. -/
theorem interface_curvature_criterion {η : ℝ → ℝ} (hη : IsLiftingProfile η)
    {K : Set (Fin (n + 1) → ℝ)} (hK : IsCompact K) (h : ℕ → ℝ) (hh : ∀ m, 0 < h m)
    (F : ℕ → Finset (Face n)) (ω : ℕ → Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (db : ℕ → Fin (n + 1) → Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (J : ℕ → Fin (n + 1) → Fin (n + 1) → Face n → (Fin n → ℝ) → A)
    (hjump : ∀ m, HasBrokenDerivativeJumps (interiorOpens K) (h m) (F m) (ω m) (db m) (J m))
    (hωm : ∀ m a, AEStronglyMeasurable (ω m a) (volume.restrict K))
    (hdbm : ∀ m a b, AEStronglyMeasurable (db m a b) (volume.restrict K))
    (hJ : ∀ m a b, ∀ f ∈ F m, MemLp (J m a b f) 2 (volume.restrict (faceBox (h m) f)))
    {U : Set (Fin (n + 1) → ℝ)} (hU : ∀ m, ∀ f ∈ F m, cell (h m) f.2 ⊆ U)
    (hUf : volume U ≠ ∞) {C : ℝ} (hC0 : 0 ≤ C)
    (hbudget : ∀ m a b, eLpNorm (db m a b) 2 (volume.restrict K) +
      eLpNorm (ω m a) 4 (volume.restrict K) ^ 2 +
        ENNReal.ofReal (Real.sqrt (interfaceBudgetSq (h m) (F m) (J m a b))) ≤ ENNReal.ofReal C) :
    (∀ m a b, eLpNorm (liftedCurvature (h m) η (F m) (ω m) (db m) (J m) a b) 2
        (volume.restrict K) ≤ ENNReal.ofReal (C * (3 + Real.sqrt ((n + 1) * ∫ s, η s ^ 2)))) ∧
      (∀ m (ψ : 𝓓(interiorOpens K, ℝ)) (L : ℝ≥0), LipschitzWith L ψ → ∀ a b,
        ‖(∫ x, ψ x • liftedCurvature (h m) η (F m) (ω m) (db m) (J m) a b x) -
            curvaturePairing (ω m) ψ a b‖ ≤
          (1 / 4 * Real.sqrt ((n + 1) * (volume U).toReal)) * h m * C * L) ∧
      (Tendsto h atTop (𝓝 0) → ∀ ω' : Fin (n + 1) → (Fin (n + 1) → ℝ) → A,
        StrongL2LocTendsto (interiorOpens K) ω ω' →
        ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ Rlim : Fin (n + 1) → Fin (n + 1) → (Fin (n + 1) → ℝ) → A,
        (∀ a b (g : (Fin (n + 1) → ℝ) → ℝ), MemLp g 2 (volume.restrict K) →
          Tendsto (fun m => ∫ x in K, g x •
            liftedCurvature (h (φ m)) η (F (φ m)) (ω (φ m)) (db (φ m)) (J (φ m)) a b x) atTop
            (𝓝 (∫ x in K, g x • Rlim a b x))) →
        IsDistributionalCurvature (interiorOpens K) ω' Rlim) := by
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  -- individual budget bounds
  have bdb : ∀ m a b, eLpNorm (db m a b) 2 (volume.restrict K) ≤ ENNReal.ofReal C := fun m a b =>
    le_trans (le_trans le_self_add le_self_add) (hbudget m a b)
  have bω2 : ∀ m a b, eLpNorm (ω m a) 4 (volume.restrict K) ^ 2 ≤ ENNReal.ofReal C :=
    fun m a b => le_trans (le_trans le_add_self le_self_add) (hbudget m a b)
  have bω : ∀ m a, eLpNorm (ω m a) 4 (volume.restrict K) ≤ ENNReal.ofReal (Real.sqrt C) := by
    intro m a
    have h1 := bω2 m a a
    have h2 : ENNReal.ofReal C = ENNReal.ofReal (Real.sqrt C) ^ 2 := by
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hC0]
    rw [h2] at h1
    exact (ENNReal.pow_le_pow_left_iff (by norm_num)).1 h1
  have bJ : ∀ m a b, Real.sqrt (interfaceBudgetSq (h m) (F m) (J m a b)) ≤ C := by
    intro m a b
    have h1 : ENNReal.ofReal (Real.sqrt (interfaceBudgetSq (h m) (F m) (J m a b))) ≤
        ENNReal.ofReal C := le_trans le_add_self (hbudget m a b)
    exact (ENNReal.ofReal_le_ofReal_iff hC0).1 h1
  have hωmem : ∀ m a, MemLp (ω m a) 4 (volume.restrict K) := fun m a =>
    ⟨hωm m a, (bω m a).trans_lt ENNReal.ofReal_lt_top⟩
  have hdbmem : ∀ m a b, MemLp (db m a b) 2 (volume.restrict K) := fun m a b =>
    ⟨hdbm m a b, (bdb m a b).trans_lt ENNReal.ofReal_lt_top⟩
  -- clause 2
  have hdist : ∀ m (ψ : 𝓓(interiorOpens K, ℝ)) (L : ℝ≥0), LipschitzWith L ψ → ∀ a b,
      ‖(∫ x, ψ x • liftedCurvature (h m) η (F m) (ω m) (db m) (J m) a b x) -
          curvaturePairing (ω m) ψ a b‖ ≤
        (1 / 4 * Real.sqrt ((n + 1) * (volume U).toReal)) * h m * C * L := by
    intro m ψ L hL a b
    refine (norm_integral_liftedCurvature_sub_curvaturePairing_le hη (hh m) hK (F m) (ω m) (db m)
      (J m) (hjump m) (hωmem m) (hdbmem m) (hJ m) (hU m) hUf ψ hL a b).trans ?_
    have := bJ m a b
    have hc : 0 ≤ 1 / 4 * Real.sqrt ((n + 1) * (volume U).toReal) * h m :=
      mul_nonneg (by positivity) (hh m).le
    gcongr
  refine ⟨fun m a b => ?_, hdist, fun hh0 ω' hω' φ hφ Rlim hweak => ?_⟩
  · -- clause 1
    refine (eLpNorm_liftedCurvature_le hη (hh m) K (F m) (ω m) (db m) (J m) (hωm m) (hdbm m)
      (hJ m) a b).trans ?_
    have e1 := bdb m a b
    have e2 : 2 * eLpNorm (ω m a) 4 (volume.restrict K) * eLpNorm (ω m b) 4 (volume.restrict K) ≤
        ENNReal.ofReal (2 * C) := by
      calc 2 * eLpNorm (ω m a) 4 (volume.restrict K) * eLpNorm (ω m b) 4 (volume.restrict K)
          ≤ 2 * ENNReal.ofReal (Real.sqrt C) * ENNReal.ofReal (Real.sqrt C) := by
            gcongr
            · exact bω m a
            · exact bω m b
        _ = ENNReal.ofReal (2 * C) := by
            rw [mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
              Real.mul_self_sqrt hC0, ENNReal.ofReal_mul (by norm_num)]
            simp
    have e3 : ENNReal.ofReal (Real.sqrt ((n + 1) * ∫ s, η s ^ 2) *
        Real.sqrt (interfaceBudgetSq (h m) (F m) (J m a b))) ≤
        ENNReal.ofReal (Real.sqrt ((n + 1) * ∫ s, η s ^ 2) * C) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (bJ m a b) (Real.sqrt_nonneg _))
    calc _ ≤ ENNReal.ofReal C + ENNReal.ofReal (2 * C) +
          ENNReal.ofReal (Real.sqrt ((n + 1) * ∫ s, η s ^ 2) * C) := by gcongr
      _ = ENNReal.ofReal (C * (3 + Real.sqrt ((n + 1) * ∫ s, η s ^ 2))) := by
          rw [← ENNReal.ofReal_add hC0 (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  · -- clause 3
    refine isDistributionalCurvature_of_tendsto (hω'.comp hφ)
      (fun m => liftedCurvature (h (φ m)) η (F (φ m)) (ω (φ m)) (db (φ m)) (J (φ m))) Rlim
      (fun ψ a b => ?_) (fun ψ a b => ?_)
    · have := hweak a b ψ (test_memLp ψ 2)
      rw [integral_test_smul_eq_setIntegral ψ]
      exact this.congr fun m => (integral_test_smul_eq_setIntegral ψ _).symm
    · obtain ⟨L, hL⟩ := exists_lipschitzWith_test ψ
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hlim : Tendsto (fun m => (1 / 4 * Real.sqrt ((n + 1) * (volume U).toReal)) *
          h (φ m) * C * L) atTop (𝓝 0) := by
        have := ((hh0.comp hφ.tendsto_atTop).const_mul
          (1 / 4 * Real.sqrt ((n + 1) * (volume U).toReal))).mul_const C |>.mul_const (L : ℝ)
        simpa using this
      exact squeeze_zero (fun _ => norm_nonneg _) (fun m => hdist (φ m) ψ L hL a b) hlim

/-- **Existence of the identified weak cluster point** (`thm:supp-interface-curvature` with
`thm:supp-curvature-compactness`, `p = 2`): for a finite-dimensional coefficient algebra, under
the hypotheses of `interface_curvature_criterion` with `h_m → 0` and `ω_m → ω` strongly in
`L²_loc(int K)`, some subsequence of `R^lift_m` converges weakly in `L²(K)`, and its limit equals
`dω + ω ∧ ω` in distributions on `int K`. -/
theorem interface_curvature_exists_cluster [FiniteDimensional ℝ A] {η : ℝ → ℝ}
    (hη : IsLiftingProfile η) {K : Set (Fin (n + 1) → ℝ)} (hK : IsCompact K) (h : ℕ → ℝ)
    (hh : ∀ m, 0 < h m) (F : ℕ → Finset (Face n)) (ω : ℕ → Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (db : ℕ → Fin (n + 1) → Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (J : ℕ → Fin (n + 1) → Fin (n + 1) → Face n → (Fin n → ℝ) → A)
    (hjump : ∀ m, HasBrokenDerivativeJumps (interiorOpens K) (h m) (F m) (ω m) (db m) (J m))
    (hωm : ∀ m a, AEStronglyMeasurable (ω m a) (volume.restrict K))
    (hdbm : ∀ m a b, AEStronglyMeasurable (db m a b) (volume.restrict K))
    (hJ : ∀ m a b, ∀ f ∈ F m, MemLp (J m a b f) 2 (volume.restrict (faceBox (h m) f)))
    {U : Set (Fin (n + 1) → ℝ)} (hU : ∀ m, ∀ f ∈ F m, cell (h m) f.2 ⊆ U)
    (hUf : volume U ≠ ∞) {C : ℝ} (hC0 : 0 ≤ C)
    (hbudget : ∀ m a b, eLpNorm (db m a b) 2 (volume.restrict K) +
      eLpNorm (ω m a) 4 (volume.restrict K) ^ 2 +
        ENNReal.ofReal (Real.sqrt (interfaceBudgetSq (h m) (F m) (J m a b))) ≤ ENNReal.ofReal C)
    (hh0 : Tendsto h atTop (𝓝 0)) (ω' : Fin (n + 1) → (Fin (n + 1) → ℝ) → A)
    (hω' : StrongL2LocTendsto (interiorOpens K) ω ω') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Rlim : Fin (n + 1) → Fin (n + 1) → (Fin (n + 1) → ℝ) → A,
      (∀ a b, MemLp (Rlim a b) 2 (volume.restrict K)) ∧
      (∀ a b (g : (Fin (n + 1) → ℝ) → ℝ), MemLp g 2 (volume.restrict K) →
        Tendsto (fun m => ∫ x in K, g x •
          liftedCurvature (h (φ m)) η (F (φ m)) (ω (φ m)) (db (φ m)) (J (φ m)) a b x) atTop
          (𝓝 (∫ x in K, g x • Rlim a b x))) ∧
      IsDistributionalCurvature (interiorOpens K) ω' Rlim := by
  obtain ⟨hbd, hdist, -⟩ := interface_curvature_criterion hη hK h hh F ω db J hjump hωm hdbm hJ
    hU hUf hC0 hbudget
  set R : ℕ → Fin (n + 1) → Fin (n + 1) → (Fin (n + 1) → ℝ) → A :=
    fun m => liftedCurvature (h m) η (F m) (ω m) (db m) (J m) with hR
  have hRmeas : ∀ m a b, AEStronglyMeasurable (R m a b) (volume.restrict K) := fun m a b =>
    (((hdbm m a b).add (((hωm m a).mul (hωm m b)).sub ((hωm m b).mul (hωm m a)))).add
      (aestronglyMeasurable_interfaceLift hη (h m) (F m) (J m a b)
        fun f hf => (hJ m a b f hf).1).restrict)
  have hRmem : ∀ m a b, MemLp (R m a b) 2 (volume.restrict K) := fun m a b =>
    ⟨hRmeas m a b, (hbd m a b).trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨φ, hφ, Rlim, hmem, hweak, hid, -⟩ := curvature_weak_compactness (p := 2) (q := 2)
    (by norm_num) (by norm_num) hK R hRmem ENNReal.ofReal_ne_top hbd
  refine ⟨φ, hφ, Rlim, hmem, hweak, hid ω ω' hω' fun ψ a b => ?_⟩
  obtain ⟨L, hL⟩ := exists_lipschitzWith_test ψ
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun m => (1 / 4 * Real.sqrt ((n + 1) * (volume U).toReal)) *
      h m * C * L) atTop (𝓝 0) := by
    have := ((hh0.const_mul (1 / 4 * Real.sqrt ((n + 1) * (volume U).toReal))).mul_const C).mul_const
      (L : ℝ)
    simpa using this
  exact squeeze_zero (fun _ => norm_nonneg _) (fun m => hdist m ψ L hL a b) hlim

/-- Non-vacuity of the hypothesis packet of `interface_curvature_criterion`: the zero
connection on the unit cube of `ℝ⁴` with no faces. -/
example : ∃ (ω : ℕ → Fin 4 → (Fin 4 → ℝ) → ℝ) (db : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℝ)
    (J : ℕ → Fin 4 → Fin 4 → Face 3 → (Fin 3 → ℝ) → ℝ),
    (∀ m : ℕ, HasBrokenDerivativeJumps (interiorOpens (Set.Icc (0 : Fin 4 → ℝ) 1)) (1 / ((m : ℝ) + 1))
      ∅ (ω m) (db m) (J m)) ∧
    ∀ (m : ℕ) a b, eLpNorm (db m a b) 2 (volume.restrict (Set.Icc (0 : Fin 4 → ℝ) 1)) +
      eLpNorm (ω m a) 4 (volume.restrict (Set.Icc (0 : Fin 4 → ℝ) 1)) ^ 2 +
        ENNReal.ofReal (Real.sqrt (interfaceBudgetSq (1 / ((m : ℝ) + 1)) ∅ (J m a b))) ≤
          ENNReal.ofReal 0 := by
  refine ⟨fun _ _ _ => 0, fun _ _ _ _ => 0, fun _ _ _ _ _ => 0, fun m ψ a b => ?_, fun m a b => ?_⟩
  · simp [faceMeasurePairing]
  · simp [interfaceBudgetSq]

/-! ### Cellwise `C¹` connections: the jump formula is a theorem -/

section Cellwise

open CubicalJump

/-- The face jump of a cellwise connection, `J_f = n_f^♭ ∧ [ω]_f` for the face `f ⊥ e_i`:
`(J_f)_{ab} = δ_{a i} [ω_b]_f - δ_{b i} [ω_a]_f`. -/
def connectionJump (h : ℝ) (P : Fin (n + 1) → (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A)
    (a b : Fin (n + 1)) (f : Face n) (y : Fin n → ℝ) : A :=
  (if f.1 = a then faceJump h (P b) f y else 0) - (if f.1 = b then faceJump h (P a) f y else 0)

/-- The broken exterior derivative `(d_b ω)_{ab} = ∂_a^b ω_b - ∂_b^b ω_a` of a cellwise
connection `ω_b = cellwise h (P b)`. -/
def brokenExteriorDeriv (h : ℝ) (P : Fin (n + 1) → (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A)
    (a b : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : A :=
  brokenPDeriv h (P b) a x - brokenPDeriv h (P a) b x

/-- **`eq:supp-connection-jumps` for cellwise `C¹` connections**: if `ω_b = cellwise h (P b)`
with every `P b` cellwise `C¹`, and `F` contains every face meeting `Ω`, then
`d_dist ω = d_b ω + Σ_f J_f δ_f` with `J_f = n_f^♭ ∧ [ω]_f` (`connectionJump`). -/
theorem connection_jump_formula {h : ℝ} (hh : 0 < h)
    {P : Fin (n + 1) → (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A}
    {S : Finset (Fin (n + 1) → ℤ)} (hP : ∀ b, IsCellwiseC1 (P b) S) (Ω : Opens (Fin (n + 1) → ℝ))
    (F : Finset (Face n)) (hF : ∀ f : Face n, ∀ y ∈ faceBox h f, facePoint h f y ∈ Ω → f ∈ F) :
    HasBrokenDerivativeJumps Ω h F (fun b => cellwise h (P b)) (brokenExteriorDeriv h P)
      (connectionJump h P) := by
  classical
  intro ψ a b
  have hψ1 : ContDiff ℝ 1 ψ := ψ.contDiff.of_le (by simp)
  have hFψ : ∀ c (k : Fin (n + 1) → ℤ), ∀ y ∈ faceBox h (c, k), ψ (facePoint h (c, k) y) ≠ 0 →
      (c, k) ∈ F := fun c k y hy hne =>
    hF _ y hy (ψ.tsupport_subset (subset_tsupport _ hne))
  have Ja := partial_jump_formula hh (hP b) a hψ1 ψ.hasCompactSupport F (hFψ a)
  have Jb := partial_jump_formula hh (hP a) b hψ1 ψ.hasCompactSupport F (hFψ b)
  have i1 := integrable_smul_brokenPDeriv hh (hP b) a ψ.continuous ψ.hasCompactSupport
  have i2 := integrable_smul_brokenPDeriv hh (hP a) b ψ.continuous ψ.hasCompactSupport
  have hdb : ∫ x, ψ x • brokenExteriorDeriv h P a b x =
      (∫ x, ψ x • brokenPDeriv h (P b) a x) - ∫ x, ψ x • brokenPDeriv h (P a) b x := by
    simp only [brokenExteriorDeriv, smul_sub]; exact integral_sub i1 i2
  have hface : faceMeasurePairing h F (connectionJump h P a b) ψ =
      (∑ f ∈ F.filter (fun f => f.1 = a),
        ∫ y in faceBox h f, ψ (facePoint h f y) • faceJump h (P b) f y) -
      ∑ f ∈ F.filter (fun f => f.1 = b),
        ∫ y in faceBox h f, ψ (facePoint h f y) • faceJump h (P a) f y := by
    rw [faceMeasurePairing, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    have j1 := integrableOn_smul_faceJump hh (hP b) ψ.continuous f
    have j2 := integrableOn_smul_faceJump hh (hP a) ψ.continuous f
    simp only [connectionJump]
    split_ifs with ha hb
    · simp only [smul_sub]; exact integral_sub j1 j2
    · simp
    · simp only [zero_sub, smul_neg, integral_neg]
    · simp
  rw [hdb, hface]
  have Jb' : ∫ x, DistributionalCurvature.pderiv b ψ x • cellwise h (P a) x =
      -((∫ x, ψ x • brokenPDeriv h (P a) b x) + ∑ f ∈ F.filter (fun f => f.1 = b),
        ∫ y in faceBox h f, ψ (facePoint h f y) • faceJump h (P a) f y) := by
    rw [← Jb, neg_neg]
  rw [Jb', Ja]
  abel

theorem continuous_connectionJump {h : ℝ}
    {P : Fin (n + 1) → (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A}
    {S : Finset (Fin (n + 1) → ℤ)} (hP : ∀ b, IsCellwiseC1 (P b) S) (a b : Fin (n + 1))
    (f : Face n) : Continuous (connectionJump h P a b f) := by
  unfold connectionJump
  split_ifs
  · exact (continuous_faceJump (hP b) f).sub (continuous_faceJump (hP a) f)
  · exact (continuous_faceJump (hP b) f).sub continuous_const
  · exact continuous_const.sub (continuous_faceJump (hP a) f)
  · exact continuous_const.sub continuous_const

/-- **`thm:supp-interface-curvature` for cellwise `C¹` connections.**  Same conclusions as
`interface_curvature_criterion`, for the piecewise connections `ω_m = cellwise h_m (P_m ·)` of the
cubical meshes of side `h_m`, with the broken derivative `d_b ω_m` (`brokenExteriorDeriv`) and the
face jumps `J_f = n_f^♭ ∧ [ω_m]_f` (`connectionJump`); the jump formula
`eq:supp-connection-jumps` and all measurability/integrability side conditions are now proved
(`connection_jump_formula`), so the only hypotheses are the mesh data, a face family `F_m`
covering `int K` with cells in a fixed `U` of finite volume, and the budget
`eq:supp-connection-interface-budget`. -/
theorem interface_curvature_criterion_cellwise {η : ℝ → ℝ} (hη : IsLiftingProfile η)
    {K : Set (Fin (n + 1) → ℝ)} (hK : IsCompact K) (h : ℕ → ℝ) (hh : ∀ m, 0 < h m)
    (P : ℕ → Fin (n + 1) → (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A)
    (S : ℕ → Finset (Fin (n + 1) → ℤ)) (hP : ∀ m b, IsCellwiseC1 (P m b) (S m))
    (F : ℕ → Finset (Face n))
    (hF : ∀ m, ∀ f : Face n, ∀ y ∈ faceBox (h m) f, facePoint (h m) f y ∈ interior K → f ∈ F m)
    {U : Set (Fin (n + 1) → ℝ)} (hU : ∀ m, ∀ f ∈ F m, cell (h m) f.2 ⊆ U)
    (hUf : volume U ≠ ∞) {C : ℝ} (hC0 : 0 ≤ C)
    (hbudget : ∀ m a b, eLpNorm (brokenExteriorDeriv (h m) (P m) a b) 2 (volume.restrict K) +
      eLpNorm (cellwise (h m) (P m a)) 4 (volume.restrict K) ^ 2 +
        ENNReal.ofReal (Real.sqrt (interfaceBudgetSq (h m) (F m) (connectionJump (h m) (P m) a b)))
          ≤ ENNReal.ofReal C) :
    (∀ m a b, eLpNorm (liftedCurvature (h m) η (F m) (fun b => cellwise (h m) (P m b))
        (brokenExteriorDeriv (h m) (P m)) (connectionJump (h m) (P m)) a b) 2
        (volume.restrict K) ≤ ENNReal.ofReal (C * (3 + Real.sqrt ((n + 1) * ∫ s, η s ^ 2)))) ∧
      (∀ m (ψ : 𝓓(interiorOpens K, ℝ)) (L : ℝ≥0), LipschitzWith L ψ → ∀ a b,
        ‖(∫ x, ψ x • liftedCurvature (h m) η (F m) (fun b => cellwise (h m) (P m b))
            (brokenExteriorDeriv (h m) (P m)) (connectionJump (h m) (P m)) a b x) -
            curvaturePairing (fun b => cellwise (h m) (P m b)) ψ a b‖ ≤
          (1 / 4 * Real.sqrt ((n + 1) * (volume U).toReal)) * h m * C * L) ∧
      (Tendsto h atTop (𝓝 0) → ∀ ω' : Fin (n + 1) → (Fin (n + 1) → ℝ) → A,
        StrongL2LocTendsto (interiorOpens K) (fun m b => cellwise (h m) (P m b)) ω' →
        ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ Rlim : Fin (n + 1) → Fin (n + 1) → (Fin (n + 1) → ℝ) → A,
        (∀ a b (g : (Fin (n + 1) → ℝ) → ℝ), MemLp g 2 (volume.restrict K) →
          Tendsto (fun m => ∫ x in K, g x •
            liftedCurvature (h (φ m)) η (F (φ m)) (fun b => cellwise (h (φ m)) (P (φ m) b))
              (brokenExteriorDeriv (h (φ m)) (P (φ m))) (connectionJump (h (φ m)) (P (φ m))) a b x)
            atTop (𝓝 (∫ x in K, g x • Rlim a b x))) →
        IsDistributionalCurvature (interiorOpens K) ω' Rlim) :=
  interface_curvature_criterion hη hK h hh F (fun m b => cellwise (h m) (P m b))
    (fun m => brokenExteriorDeriv (h m) (P m)) (fun m => connectionJump (h m) (P m))
    (fun m => connection_jump_formula (hh m) (hP m) (interiorOpens K) (F m)
      fun f y hy hmem => hF m f y hy hmem)
    (fun m a => aestronglyMeasurable_cellwise (hh m) (hP m a) _)
    (fun m a b => (aestronglyMeasurable_brokenPDeriv (hh m) (hP m b) a _).sub
      (aestronglyMeasurable_brokenPDeriv (hh m) (hP m a) b _))
    (fun m a b f _ => memLp_faceBox_of_continuous (hh m) (continuous_connectionJump (hP m) a b f)
      f 2)
    hU hUf hC0 hbudget

end Cellwise

/-! ### Non-vacuity: a discontinuous cellwise connection -/

section NonVacuity

open CubicalJump

/-- The unit-cell indicator in the `dx¹` component: a discontinuous cellwise connection. -/
noncomputable def heavisideConnection : Fin 2 → (Fin 2 → ℤ) → (Fin 2 → ℝ) → ℝ :=
  fun b k => if b = 1 ∧ k = 0 then fun _ => 1 else 0

example : HasBrokenDerivativeJumps (n := 1)
    (interiorOpens (Set.Icc ![-1 / 4, 1 / 4] ![1 / 4, 3 / 4])) 1
    {((0 : Fin 2), (0 : Fin 2 → ℤ))} (fun b => cellwise 1 (heavisideConnection b))
    (brokenExteriorDeriv 1 heavisideConnection) (connectionJump 1 heavisideConnection) := by
  refine connection_jump_formula one_pos (S := {0}) (fun b => ⟨fun k => ?_, fun k hk => ?_⟩) _ _ ?_
  · unfold heavisideConnection; split_ifs
    · exact contDiff_const
    · exact contDiff_const
  · have : k ≠ 0 := by simpa using hk
    simp [heavisideConnection, this]
  · rintro ⟨i, k⟩ y hy hmem
    have hI : facePoint 1 (i, k) y ∈ Set.Icc ![-1 / 4, 1 / 4] ![1 / 4, 3 / 4] :=
      interior_subset hmem
    rw [Set.mem_Icc, Pi.le_def, Pi.le_def] at hI
    obtain ⟨hlo, hhi⟩ := hI
    have hb := hy 0 (mem_univ _)
    fin_cases i
    · have h0lo := hlo 0
      have h0hi := hhi 0
      have h1lo := hlo 1
      have h1hi := hhi 1
      simp [facePoint, faceLevel] at h0lo h0hi h1lo h1hi hb
      have e0 : k 0 = 0 := by
        have a1 : (-1 : ℝ) < k 0 := by linarith
        have a2 : (k 0 : ℝ) < 1 := by linarith
        have b1 : (-1 : ℤ) < k 0 := by exact_mod_cast a1
        have b2 : k 0 < 1 := by exact_mod_cast a2
        omega
      have e1 : k 1 = 0 := by
        have a1 : (k 1 : ℝ) < 1 := by linarith
        have a2 : (-1 : ℝ) < k 1 := by linarith
        have b1 : k 1 < 1 := by exact_mod_cast a1
        have b2 : (-1 : ℤ) < k 1 := by exact_mod_cast a2
        omega
      have : k = 0 := by
        funext m; fin_cases m
        · exact e0
        · exact e1
      simp [this]
    · exfalso
      have h1lo := hlo 1
      have h1hi := hhi 1
      simp [facePoint, faceLevel] at h1lo h1hi
      have a1 : (0 : ℝ) < k 1 := by linarith
      have a2 : (k 1 : ℝ) < 1 := by linarith
      have b1 : (0 : ℤ) < k 1 := by exact_mod_cast a1
      have b2 : k 1 < 1 := by exact_mod_cast a2
      omega

/-- The jump of `heavisideConnection` across the face `x⁰ = 0` is `1`. -/
example (y : Fin 1 → ℝ) : connectionJump 1 heavisideConnection 0 1 ((0 : Fin 2), 0) y = 1 := by
  have : (0 : Fin 2 → ℤ) - Pi.single 0 1 ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  simp [connectionJump, faceJump, heavisideConnection]

end NonVacuity

end RenewalGeometry.InterfaceCurvature
