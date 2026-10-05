/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSpinorCompactness
import RenewalGeometry.Analysis.WeakJetPairing

/-!
# Weak `H¹` compactness of covariant grid graphs in an arbitrary finite-dimensional fibre

Generic infrastructure (no renewal notions) for the first step of
`prop:native-spinor-variation` of the Einstein–SM action-closure manuscript ("the graph identity
in `lem:native-critical-grid` gives ordinary discrete `H¹` bounds"), in a form that applies to the
literal record encodings of spinors **and** dual spinors.

Setting: unit-torus rendering of the periodic box (grid `(ℤ/N)⁴`, mesh `h = 1/N`, raw
reconstruction `R_h^0 = pc`), a finite-dimensional real normed fibre `X` (any norm), a connection
with values in a normed space `E` acting through a bounded linear map `ρ : E → End X`, and links
`e^{h ρ(A_μ)}` that are **isometries of the fibre norm** (unitary internal links).  The covariant
graph is `𝒟^U_μ Ψ = (e^{hρ(A_μ)} T_μ Ψ - Ψ)/h` (`covGraph`, `eq:native-internal-graph`).

* `eLpNorm_pc_four_le_covGraph`: covariant (Kato) grid Sobolev `eq:native-grid-Sobolev-b` in an
  arbitrary normed fibre (the Kato inequality only uses that the links preserve the norm).
* `weak_compactness_of_L4`: the conclusions of `NativeSpinor.native_spinor_weak_compactness` for
  a Euclidean fibre, from a uniform `L⁴` bound instead of unitarity, together with the ordinary
  discrete `H¹` bound `sup_k ‖D⁺_μ Ψ_k‖_{2,h} < ∞` (the graph identity
  `D⁺Ψ = 𝒟^UΨ - B^ρ TΨ` with `R^0 B^ρ → ρ(A)` in `L⁴` and Hölder).
* `covariant_graph_weak_compactness` (**main theorem**): for any finite-dimensional normed fibre
  `X` with a linear frame `Θ : X ≃ ℝ^r`, norm-preserving links, strong `L⁴` connection convergence
  and a bounded covariant graph, the reconstructions are bounded in `L⁴`, the ordinary first
  differences are bounded in `L²`, and after extraction `R^0 Ψ_k → Ψ₀` strongly in `L²` (`Ψ₀ ∈ L⁴`)
  while the first differences converge **weakly** in `L²` (against every real `L²` scalar and every
  functional of the fibre) to `u₀`, where `u₀_μ` is the weak derivative `∂_μ Ψ₀`: every frame
  component of `Ψ₀` lies in `H¹` with weak derivative the corresponding component of `u₀_μ`.
* `real_weak_of_complex_weak`, `ae_eq_re_of_complex_weak`: complex inner-product weak limits of
  real sequences are real, and give real dual-pairing weak limits.
* `tendsto_integral_of_weak_functional`: weak convergence against all scalar `L²` functions and all
  fibre functionals gives the weak-convergence hypothesis of
  `WeakJetPairing.weak_jet_variation` for every `L²` dual-valued coefficient (any finite-dimensional
  fibre).
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.CovariantGraph

open TorusTrigReconstruction NativeCriticalGrid TorusPiecewiseConstantTranslation
  NativeYMIdentification NativeGridLp TorusSobolev NativeHiggs

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

local notation "𝕋" => UnitAddTorus (Fin 4)

local instance fact_one_le_four_cg : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_two_cg : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance holder442_cg : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two
local instance holder221_cg : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The covariant graph in an arbitrary normed fibre -/

section Graph

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {N : ℕ}

/-- **The covariant graph** `𝒟^U_μ Ψ = (e^{hρ(A_μ)} T_μ Ψ - Ψ)/h`, `h = 1/N`
(`eq:native-internal-graph`), in an arbitrary normed fibre `X`. -/
def covGraph (N : ℕ) (ρ : E →L[ℝ] (X →L[ℝ] X)) (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → E)
    (Ψ : LatticeTorusPlancherel.Grid 4 N → X) (μ : Fin 4) (x : LatticeTorusPlancherel.Grid 4 N) :
    X :=
  (N : ℝ) • (NormedSpace.exp ((N : ℝ)⁻¹ • ρ (A x μ)) (Ψ (x + Pi.single μ 1)) - Ψ x)

/-- The graph identity `D⁺_μ Ψ = 𝒟^U_μ Ψ - B^ρ_μ T_μ Ψ`. -/
theorem DpV_eq_covGraph_sub (ρ : E →L[ℝ] (X →L[ℝ] X))
    (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → E) (Ψ : LatticeTorusPlancherel.Grid 4 N → X)
    (μ : Fin 4) (x : LatticeTorusPlancherel.Grid 4 N) :
    DpV μ Ψ x = covGraph N ρ A Ψ μ x - linkCoeff N (ρ (A x μ)) (Ψ (x + Pi.single μ 1)) := by
  simp only [DpV, covGraph, linkCoeff, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  rw [← smul_sub]
  congr 1
  abel

/-- **Covariant grid Sobolev in an arbitrary normed fibre** (`eq:native-grid-Sobolev-b`):
`‖R_h^0 Ψ‖_{L⁴} ≤ 3 Σ_μ ‖𝒟^U_μ Ψ‖_{2,h} + 4 ‖Ψ‖_{2,h}` for norm-preserving links. -/
theorem eLpNorm_pc_four_le_covGraph [NeZero N] (ρ : E →L[ℝ] (X →L[ℝ] X))
    (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → E) (Ψ : LatticeTorusPlancherel.Grid 4 N → X)
    (hU : ∀ x μ (v : X), ‖NormedSpace.exp ((N : ℝ)⁻¹ • ρ (A x μ)) v‖ = ‖v‖) :
    eLpNorm (pc Ψ) 4 (volume : Measure 𝕋) ≤
      ENNReal.ofReal (3 * ∑ μ, gridNorm (covGraph N ρ A Ψ μ) + 4 * gridNorm Ψ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [eLpNorm_pc_four_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := GridSobolev.grid_sobolev_L4_covariant (inv_pos.2 hN) (Fintype.card_fin 4)
    (fun x μ (v : X) => NormedSpace.exp ((N : ℝ)⁻¹ • ρ (A x μ)) v) (fun x μ v => hU x μ v) Ψ
  rw [mul_inv_cancel₀ hN.ne', div_one] at h
  have hcov : ∀ μ, GridSobolev.gridCovFwd ((N : ℝ)⁻¹)
      (fun x μ (v : X) => NormedSpace.exp ((N : ℝ)⁻¹ • ρ (A x μ)) v) μ Ψ = covGraph N ρ A Ψ μ := by
    intro μ; funext x
    simp only [GridSobolev.gridCovFwd, covGraph, inv_inv, GridSobolev.gridStep]
  simp only [hcov, gridL2Norm_inv_eq_gridNorm] at h
  exact h

end Graph

/-! ### Euclidean fibre: compactness from a uniform `L⁴` bound -/

section Euclid

variable {r : ℕ} [NeZero r] {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- The Euclidean fibre `ℝ^r`. -/
local notation "V" => EuclideanSpace ℝ (Fin r)

/-- **Weak `H¹` compactness of a covariant graph from a uniform `L⁴` bound** (Euclidean fibre).
The conclusions of `NativeSpinor.native_spinor_weak_compactness`, with the unitarity hypothesis
replaced by its only use (the uniform `L⁴` bound of the reconstructions), and with the ordinary
discrete `H¹` bound added to the conclusions. -/
theorem weak_compactness_of_L4 (hn : Tendsto n atTop atTop) (ρ : E →L[ℝ] (V →L[ℝ] V))
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → E}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → E}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ))
    {Ψ : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → V} {BΨ BK : ℝ} {C4 : ℝ≥0∞} (hC4 : C4 ≠ ∞)
    (hH4 : ∀ k, eLpNorm (pc (Ψ k)) 4 volume ≤ C4)
    (hΨ : ∀ k, gridNorm (Ψ k) ≤ BΨ)
    (hK : ∀ k μ, gridNorm (higgsLink (n k) ρ (A k) (Ψ k) μ) ≤ BK) :
    (∃ BD : ℝ, ∀ k μ, gridNorm (DpV μ (Ψ k)) ≤ BD) ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ψ₀ : UnitAddTorus (Fin 4) → V,
      ∃ f : Fin r → L²(UnitAddTorus (Fin 4)),
      LpTendsto volume 2 (fun k => pc (Ψ (φ k))) Ψ₀ ∧ MemLp Ψ₀ 4 volume ∧
      ∀ j, ((f j : UnitAddTorus (Fin 4) → ℂ) =ᵐ[volume] fun y => ((Ψ₀ y j : ℝ) : ℂ)) ∧
        MemH 1 (f j) ∧
        (∀ μ (g : L²(UnitAddTorus (Fin 4))), Tendsto
          (fun k => inner ℂ g (pcLp (Dp μ (coordGrid j (Ψ (φ k)))))) atTop
          (𝓝 (inner ℂ g (weakDeriv μ (f j))))) ∧
        Tendsto (fun k => ‖trigLp (coordGrid j (Ψ (φ k))) - f j‖) atTop (𝓝 0) ∧
        (∃ C, ∀ k, sobSq 1 (trigLp (coordGrid j (Ψ (φ k)))) ≤ C) ∧
        (∀ μ (g : L²(UnitAddTorus (Fin 4))), Tendsto
          (fun k => inner ℂ g (weakDeriv μ (trigLp (coordGrid j (Ψ (φ k)))))) atTop
          (𝓝 (inner ℂ g (weakDeriv μ (f j))))) := by
  set App : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.id ℝ (V →L[ℝ] V)
  have hApp : ‖App‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe]; exact ContinuousLinearMap.norm_id_le
  have hTH4 : ∀ k μ, eLpNorm (pc (T μ (Ψ k))) 4 volume ≤ C4 := fun k μ => by
    rw [eLpNorm_pc_T]; exact hH4 k
  -- the link coefficients
  have hB : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => linkCoeff (n k) (ρ (A k x μ))))
      (fun y => ρ (A₀ μ y)) := fun μ =>
    ⟨fun k => memLp_pc_gen _ 4, ρ.comp_memLp' (hA μ).memLp_lim,
      tendsto_linkCoeff hn ρ (hA μ).memLp_lim (hA μ).tendsto⟩
  have hBb : ∀ μ, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ k,
      eLpNorm (pc (fun x => linkCoeff (n k) (ρ (A k x μ)))) 4 volume ≤ C :=
    fun μ => exists_bound_of_lpTendsto (hB μ)
  choose CB hCB hCBb using hBb
  -- the product `B T Ψ`
  set P : ∀ k, Fin 4 → LatticeTorusPlancherel.Grid 4 (n k) → V := fun k μ x =>
    linkCoeff (n k) (ρ (A k x μ)) (Ψ k (x + Pi.single μ 1))
  have hPpc : ∀ k μ, pc (P k μ) = fun y => App (pc (fun x => linkCoeff (n k) (ρ (A k x μ))) y)
      (pc (T μ (Ψ k)) y) := fun k μ => rfl
  have hP2 : ∀ k μ, eLpNorm (pc (P k μ)) 2 volume ≤ CB μ * C4 := by
    intro k μ
    rw [hPpc]
    refine (eLpNorm_bilin_le' (p := 4) (q := 4) App (stronglyMeasurable_pc _).aestronglyMeasurable
      (stronglyMeasurable_pc _).aestronglyMeasurable).trans ?_
    calc (‖App‖₊ : ℝ≥0∞) * eLpNorm (pc fun x => linkCoeff (n k) (ρ (A k x μ))) 4 volume *
          eLpNorm (pc (T μ (Ψ k))) 4 volume ≤ 1 * CB μ * C4 := by
          gcongr
          · exact_mod_cast hApp
          · exact hCBb μ k
          · exact hTH4 k μ
      _ = CB μ * C4 := by rw [one_mul]
  -- discrete `H¹` bound from the graph identity
  set BD : ℝ := BK + ∑ μ, (CB μ * C4).toReal
  have hDb : ∀ k μ, gridNorm (DpV μ (Ψ k)) ≤ BD := by
    intro k μ
    have e : DpV μ (Ψ k) = higgsLink (n k) ρ (A k) (Ψ k) μ - P k μ := by
      funext x; exact DpV_eq_higgsLink_sub ρ (A k) (Ψ k) μ x
    rw [e]
    have hsub : gridNorm (higgsLink (n k) ρ (A k) (Ψ k) μ - P k μ) ≤
        gridNorm (higgsLink (n k) ρ (A k) (Ψ k) μ) + gridNorm (P k μ) := by
      have := gridNorm_add_le (higgsLink (n k) ρ (A k) (Ψ k) μ) (-P k μ)
      rwa [← sub_eq_add_neg, show gridNorm (-P k μ) = gridNorm (P k μ) by
        unfold gridNorm; simp [norm_neg]] at this
    have hP : gridNorm (P k μ) ≤ (CB μ * C4).toReal := by
      have := hP2 k μ
      rw [eLpNorm_pc_two_eq] at this
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (hCB μ) hC4) this
      rwa [ENNReal.toReal_ofReal (gridNorm_nonneg _)] at this
    have h2 : (CB μ * C4).toReal ≤ ∑ μ, (CB μ * C4).toReal :=
      Finset.single_le_sum (f := fun μ => (CB μ * C4).toReal) (fun _ _ => ENNReal.toReal_nonneg)
        (Finset.mem_univ μ)
    linarith [hK k μ]
  -- discrete Rellich for the frame components
  set u : Fin r → ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → ℂ := fun j k => coordGrid j (Ψ k)
  set B₀ := max BΨ BD
  have huB : ∀ j k, gridNorm (u j k) ≤ B₀ := fun j k =>
    (gridNorm_coordGrid_le j (Ψ k)).trans ((hΨ k).trans (le_max_left _ _))
  have huD : ∀ j k μ, gridNorm (Dp μ (u j k)) ≤ B₀ := fun j k μ => by
    simp only [u]; rw [Dp_coordGrid]
    exact (gridNorm_coordGrid_le j _).trans ((hDb k μ).trans (le_max_right _ _))
  obtain ⟨φ, hφ, f, hf⟩ := exists_subseq_tendsto_pcLp_family r hn u (B := B₀) huB huD
  have hnφ : Tendsto (fun k => n (φ k)) atTop atTop := hn.comp hφ.tendsto_atTop
  have hfL : ∀ j, LpTendsto volume 2 (fun k => pc (u j (φ k))) (f j : UnitAddTorus (Fin 4) → ℂ) :=
    fun j => lpTendsto_of_norm_pcLp (n := fun k => n (φ k)) (hf j)
  have hreal : ∀ j, (f j : UnitAddTorus (Fin 4) → ℂ) =ᵐ[volume] fun y => (((f j) y).re : ℂ) :=
    fun j => ae_eq_re_of_lpTendsto (hfL j) fun k y => by simp [u, pc, coordGrid]
  -- the limit field
  set Ψ₀ : UnitAddTorus (Fin 4) → V := fun y => ∑ j, ((f j) y).re • EuclideanSpace.single j 1
  have hH₀j : ∀ y j, Ψ₀ y j = ((f j) y).re := by
    intro y j
    simp [Ψ₀, Pi.single_apply]
  have hmemH₀ : ∀ p : ℝ≥0∞, (∀ j, MemLp (f j : UnitAddTorus (Fin 4) → ℂ) p volume) →
      MemLp Ψ₀ p volume := by
    intro p hp
    have : Ψ₀ = ∑ j, fun y => ((f j) y).re • (EuclideanSpace.single j 1 : V) := by
      funext y; simp [Ψ₀, Finset.sum_apply]
    rw [this]
    exact memLp_finsetSum' _ fun j _ =>
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j 1 : V)).comp_memLp'
        (Complex.reCLM.comp_memLp' (hp j))
  -- strong `L²` convergence of the values
  have hH2 : LpTendsto volume 2 (fun k => pc (Ψ (φ k))) Ψ₀ := by
    refine lpTendsto_of_coord (fun k => memLp_pc_gen _ 2) (hmemH₀ 2 fun j => Lp.memLp (f j))
      fun j => ?_
    refine ((hfL j).clm Complex.reCLM).congr (fun k => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · simp [u, pc, coordGrid]
    · simp [hH₀j]
  have hH₀4 : MemLp Ψ₀ 4 volume := hH2.memLp_of_bound (by norm_num) hC4 fun k => hH4 (φ k)
  -- `lem:native-critical-grid`: weak limits of the forward differences
  have hwk := fun j => weak_limit_of_bounded hnφ (u := fun k => u j (φ k)) (B := B₀)
    (fun k => huB j (φ k)) (fun k μ => huD j (φ k) μ) (hf j)
  refine ⟨⟨BD, hDb⟩, φ, hφ, Ψ₀, f, hH2, hH₀4, fun j => ⟨?_, (hwk j).1, (hwk j).2.1,
    (hwk j).2.2.1, ⟨_, fun k => ((hwk j).2.2.2.1 k).trans
      (add_le_add (pow_le_pow_left₀ (gridNorm_nonneg _) (huB j (φ k)) 2) le_rfl)⟩,
    (hwk j).2.2.2.2⟩⟩
  filter_upwards [hreal j] with y hy
  rw [hy, hH₀j]

end Euclid

/-! ### Complex inner-product weak limits of real sequences -/

section RealWeak

/-- The inner product of `L²(𝕋⁴; ℂ)` against the complexification of a real `L²` function. -/
theorem re_inner_ofReal (g : 𝕋 → ℝ) (hg : MemLp g 2 volume) (F : L²(𝕋)) :
    (inner ℂ ((hg.ofReal (K := ℂ)).toLp _) F).re = ∫ z, g z * ((F : 𝕋 → ℂ) z).re := by
  rw [MeasureTheory.L2.inner_def]
  change RCLike.re (∫ a, inner ℂ _ _) = _
  rw [← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [(hg.ofReal (K := ℂ)).coeFn_toLp] with z hz
  rw [hz]
  simp [RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

theorem im_inner_ofReal (g : 𝕋 → ℝ) (hg : MemLp g 2 volume) (F : L²(𝕋)) :
    (inner ℂ ((hg.ofReal (K := ℂ)).toLp _) F).im = ∫ z, g z * ((F : 𝕋 → ℂ) z).im := by
  rw [MeasureTheory.L2.inner_def]
  change RCLike.im (∫ a, inner ℂ _ _) = _
  rw [← integral_im (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [(hg.ofReal (K := ℂ)).coeFn_toLp] with z hz
  rw [hz]
  simp [RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

variable {U : ℕ → L²(𝕋)} {W : L²(𝕋)} {u : ℕ → 𝕋 → ℝ}

/-- **Real dual-pairing weak limits from complex inner-product weak limits**: if `U_k` are the
complexifications of real functions `u_k` and `⟪G, U_k⟫ → ⟪G, W⟫` for every `G ∈ L²`, then
`∫ g u_k → ∫ g Re W` for every real `g ∈ L²`. -/
theorem real_weak_of_complex_weak (hU : ∀ k, (U k : 𝕋 → ℂ) =ᵐ[volume] fun z => ((u k z : ℝ) : ℂ))
    (hw : ∀ G : L²(𝕋), Tendsto (fun k => inner ℂ G (U k)) atTop (𝓝 (inner ℂ G W)))
    (g : 𝕋 → ℝ) (hg : MemLp g 2 volume) :
    Tendsto (fun k => ∫ z, g z * u k z) atTop (𝓝 (∫ z, g z * ((W : 𝕋 → ℂ) z).re)) := by
  have h := (Complex.continuous_re.tendsto _).comp (hw ((hg.ofReal (K := ℂ)).toLp _))
  rw [Function.comp_def, re_inner_ofReal g hg W] at h
  refine h.congr fun k => ?_
  rw [re_inner_ofReal g hg (U k)]
  refine integral_congr_ae ?_
  filter_upwards [hU k] with z hz
  simp [hz]

/-- **Weak limits of real sequences are real**: under the hypotheses of
`real_weak_of_complex_weak`, `W = Re W` almost everywhere. -/
theorem ae_eq_re_of_complex_weak (hU : ∀ k, (U k : 𝕋 → ℂ) =ᵐ[volume] fun z => ((u k z : ℝ) : ℂ))
    (hw : ∀ G : L²(𝕋), Tendsto (fun k => inner ℂ G (U k)) atTop (𝓝 (inner ℂ G W))) :
    (W : 𝕋 → ℂ) =ᵐ[volume] fun z => ((((W : 𝕋 → ℂ) z).re : ℝ) : ℂ) := by
  have hWm : MemLp (fun z => ((W : 𝕋 → ℂ) z).im) 2 volume :=
    Complex.imCLM.comp_memLp' (Lp.memLp W)
  set g : 𝕋 → ℝ := fun z => ((W : 𝕋 → ℂ) z).im
  have h := (Complex.continuous_im.tendsto _).comp (hw ((hWm.ofReal (K := ℂ)).toLp _))
  rw [Function.comp_def, im_inner_ofReal g hWm W] at h
  have h0 : ∀ k, (inner ℂ ((hWm.ofReal (K := ℂ)).toLp _) (U k)).im = 0 := by
    intro k
    rw [im_inner_ofReal g hWm (U k)]
    refine (integral_congr_ae ?_).trans (integral_zero 𝕋 ℝ)
    filter_upwards [hU k] with z hz
    simp [hz]
  simp only [h0] at h
  have hz : ∫ z, g z * g z = 0 := tendsto_nhds_unique h tendsto_const_nhds
  have hint : Integrable (fun z => g z * g z) volume := hWm.integrable_mul hWm
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => mul_self_nonneg (g z)) hint).1 hz
  filter_upwards [hae] with z hz'
  have : g z = 0 := mul_self_eq_zero.1 hz'
  apply Complex.ext <;> simp_all [g]

end RealWeak

/-! ### Weak convergence against all functionals of a finite-dimensional fibre -/

section Functional

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **Weak `L²` convergence in a finite-dimensional fibre, tested by `L²` dual-valued
coefficients**: if `∫ φ ℓ(u_k) → ∫ φ ℓ(u₀)` for every fibre functional `ℓ` and every real
`φ ∈ L²`, then `∫ g(u_k) → ∫ g(u₀)` for every `g ∈ L²(𝕋⁴; Y*)` (the weak-convergence hypothesis
of `WeakJetPairing.weak_jet_variation`). -/
theorem tendsto_integral_of_weak_functional {u : ℕ → 𝕋 → Y} {u₀ : 𝕋 → Y}
    (hu : ∀ k, MemLp (u k) 2 volume) (hu₀ : MemLp u₀ 2 volume)
    (hw : ∀ (ℓ : Y →L[ℝ] ℝ) (φ : 𝕋 → ℝ), MemLp φ 2 volume →
      Tendsto (fun k => ∫ y, φ y * ℓ (u k y)) atTop (𝓝 (∫ y, φ y * ℓ (u₀ y))))
    (g : 𝕋 → Y →L[ℝ] ℝ) (hg : MemLp g 2 volume) :
    Tendsto (fun k => ∫ y, g y (u k y)) atTop (𝓝 (∫ y, g y (u₀ y))) := by
  classical
  set b := Module.finBasis ℝ Y
  set c : Fin (Module.finrank ℝ Y) → Y →L[ℝ] ℝ := fun i =>
    LinearMap.toContinuousLinearMap (b.coord i)
  have hdec : ∀ (w : 𝕋 → Y) (y : 𝕋), g y (w y) = ∑ i, g y (b i) * c i (w y) := by
    intro w y
    conv_lhs => rw [← b.sum_repr (w y)]
    simp only [map_sum, map_smul, smul_eq_mul, c, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hφ : ∀ i, MemLp (fun y => g y (b i)) 2 volume := fun i =>
    hg.of_le_mul (c := ‖b i‖) (LpProductContinuity.aestronglyMeasurable_apply hg.1
      aestronglyMeasurable_const) (Eventually.of_forall fun y => by
        rw [mul_comm]; exact (g y).le_opNorm _)
  have hint : ∀ (w : 𝕋 → Y), MemLp w 2 volume → ∀ i,
      Integrable (fun y => g y (b i) * c i (w y)) volume := fun w hw' i =>
    (hφ i).integrable_mul ((c i).comp_memLp' hw')
  simp_rw [hdec]
  rw [integral_finset_sum _ fun i _ => hint u₀ hu₀ i]
  have : (fun k => ∫ y, ∑ i, g y (b i) * c i (u k y)) =
      fun k => ∑ i, ∫ y, g y (b i) * c i (u k y) := by
    funext k
    rw [integral_finset_sum _ fun i _ => hint (u k) (hu k) i]
  rw [this]
  exact tendsto_finset_sum _ fun i _ => hw (c i) _ (hφ i)

end Functional

/-! ### Arbitrary finite-dimensional fibre with norm-preserving links -/

section General

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {r : ℕ} [NeZero r] {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- The Euclidean fibre `ℝ^r`. -/
local notation "V" => EuclideanSpace ℝ (Fin r)

theorem gridNorm_clm_le {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {N : ℕ} [NeZero N]
    (L : X →L[ℝ] Z) (u : LatticeTorusPlancherel.Grid 4 N → X) :
    gridNorm (fun x => L (u x)) ≤ ‖L‖ * gridNorm u := by
  have h1 : gridNorm (fun x => L (u x)) ≤ gridNorm (fun x => ‖L‖ * ‖u x‖) :=
    gridNorm_mono fun x => by
      rw [Real.norm_of_nonneg (by positivity)]; exact L.le_opNorm _
  rw [gridNorm_const_mul _ (norm_nonneg L)] at h1
  have h2 : gridNorm (fun x => ‖u x‖) = gridNorm u := by
    unfold gridNorm; simp only [norm_norm]
  rwa [h2] at h1

/-- Conjugation of fibre operators by a frame `Θ : X ≃ V`, as a continuous linear map. -/
def conjL (Θ : X ≃L[ℝ] V) : (X →L[ℝ] X) →L[ℝ] (V →L[ℝ] V) :=
  (ContinuousLinearMap.compL ℝ V X V (Θ : X →L[ℝ] V)).comp
    ((ContinuousLinearMap.compL ℝ V X X).flip (Θ.symm : V →L[ℝ] X))

theorem conjL_apply (Θ : X ≃L[ℝ] V) (T : X →L[ℝ] X) (v : V) :
    conjL Θ T v = Θ (T (Θ.symm v)) := rfl

theorem exp_conjL (Θ : X ≃L[ℝ] V) (T : X →L[ℝ] X) :
    NormedSpace.exp (conjL Θ T) = conjL Θ (NormedSpace.exp T) := by
  let +nondep : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ (X →L[ℝ] X)
  let +nondep : NormedAlgebra ℚ (V →L[ℝ] V) := .restrictScalars ℚ ℝ (V →L[ℝ] V)
  have h := NormedSpace.map_exp (Θ.conjContinuousAlgEquiv : (X →L[ℝ] X) →ₐ[ℝ] (V →L[ℝ] V))
    Θ.conjContinuousAlgEquiv.continuous T
  have e : ∀ S : X →L[ℝ] X,
      (Θ.conjContinuousAlgEquiv : (X →L[ℝ] X) →ₐ[ℝ] (V →L[ℝ] V)) S = conjL Θ S := by
    intro S; ext v; rfl
  rw [e, e] at h
  exact h.symm

/-- The frame-conjugated representation `ρ_Θ(A) = Θ ρ(A) Θ⁻¹`. -/
def conjRep (Θ : X ≃L[ℝ] V) (ρ : E →L[ℝ] (X →L[ℝ] X)) : E →L[ℝ] (V →L[ℝ] V) := (conjL Θ).comp ρ

theorem higgsLink_conjRep {N : ℕ} (Θ : X ≃L[ℝ] V) (ρ : E →L[ℝ] (X →L[ℝ] X))
    (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → E) (Ψ : LatticeTorusPlancherel.Grid 4 N → X)
    (μ : Fin 4) (x : LatticeTorusPlancherel.Grid 4 N) :
    higgsLink N (conjRep Θ ρ) A (fun x => Θ (Ψ x)) μ x = Θ (covGraph N ρ A Ψ μ x) := by
  have e : NormedSpace.exp ((N : ℝ)⁻¹ • conjRep Θ ρ (A x μ)) =
      conjL Θ (NormedSpace.exp ((N : ℝ)⁻¹ • ρ (A x μ))) := by
    rw [← exp_conjL]
    congr 1
    simp [conjRep, map_smul]
  rw [higgsLink, covGraph, e, conjL_apply, ContinuousLinearEquiv.symm_apply_apply, map_smul,
    map_sub]

theorem DpV_clm {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {N : ℕ} (L : X →L[ℝ] Z)
    (μ : Fin 4) (u : LatticeTorusPlancherel.Grid 4 N → X) :
    DpV μ (fun x => L (u x)) = fun x => L (DpV μ u x) := by
  funext x; simp [DpV, map_smul, map_sub]

/-- **Weak `H¹` compactness of covariant graphs in an arbitrary finite-dimensional fibre**
(`prop:native-spinor-variation`, first assertion; `lem:native-critical-grid`).  Let `X` be a
finite-dimensional real normed fibre with a linear frame `Θ : X ≃ ℝ^r`, let `R_h^0 A_h → A₀`
strongly in `L⁴`, let the internal links `e^{h ρ(A_h)}` preserve the fibre norm, and let the
covariant graph be bounded: `‖Ψ_h‖_{2,h} ≤ B_Ψ`, `‖𝒟^U_μ Ψ_h‖_{2,h} ≤ B_K`.  Then
* the reconstructions are uniformly bounded in `L⁴` and the ordinary first differences are
  uniformly bounded in `L²` (ordinary discrete `H¹` bound);
* after extraction, `R_h^0 Ψ_h → Ψ₀` strongly in `L²`, `Ψ₀ ∈ L⁴`, and `R_h^0 D⁺_μ Ψ_h ⇀ u₀_μ`
  weakly in `L²`: `∫ φ ℓ(R^0 D⁺_μΨ_h) → ∫ φ ℓ(u₀_μ)` for every fibre functional `ℓ` and real
  `φ ∈ L²`;
* `u₀ = ∂Ψ₀`: every frame component `(ΘΨ₀)^j` has an `L²` representative `f` in `H¹` whose weak
  derivatives are the frame components `(Θ u₀_μ)^j`. -/
theorem covariant_graph_weak_compactness (Θ : X ≃L[ℝ] V) (hn : Tendsto n atTop atTop)
    (ρ : E →L[ℝ] (X →L[ℝ] X)) {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → E}
    {A₀ : Fin 4 → 𝕋 → E} (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ))
    (hU : ∀ k x μ (v : X), ‖NormedSpace.exp ((n k : ℝ)⁻¹ • ρ (A k x μ)) v‖ = ‖v‖)
    {Ψ : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → X} {BΨ BK : ℝ}
    (hΨ : ∀ k, gridNorm (Ψ k) ≤ BΨ) (hK : ∀ k μ, gridNorm (covGraph (n k) ρ (A k) (Ψ k) μ) ≤ BK) :
    (∃ C4 : ℝ≥0∞, C4 ≠ ∞ ∧ ∀ k, eLpNorm (pc (Ψ k)) 4 volume ≤ C4) ∧
    (∃ BD : ℝ, ∀ k μ, gridNorm (DpV μ (Ψ k)) ≤ BD) ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ψ₀ : 𝕋 → X, ∃ u₀ : Fin 4 → 𝕋 → X,
      LpTendsto volume 2 (fun k => pc (Ψ (φ k))) Ψ₀ ∧ MemLp Ψ₀ 4 volume ∧
      (∀ μ, MemLp (u₀ μ) 2 volume) ∧
      (∀ μ (ℓ : X →L[ℝ] ℝ) (g : 𝕋 → ℝ), MemLp g 2 volume →
        Tendsto (fun k => ∫ z, g z * ℓ (pc (DpV μ (Ψ (φ k))) z)) atTop
          (𝓝 (∫ z, g z * ℓ (u₀ μ z)))) ∧
      ∀ j, ∃ f : L²(𝕋), ((f : 𝕋 → ℂ) =ᵐ[volume] fun z => ((Θ (Ψ₀ z) j : ℝ) : ℂ)) ∧
        MemH 1 f ∧ (∀ μ, (weakDeriv μ f : 𝕋 → ℂ) =ᵐ[volume] fun z => ((Θ (u₀ μ z) j : ℝ) : ℂ)) ∧
        Tendsto (fun k => ‖trigLp (coordGrid j (fun x => Θ (Ψ (φ k) x))) - f‖) atTop (𝓝 0) ∧
        (∃ C, ∀ k, sobSq 1 (trigLp (coordGrid j (fun x => Θ (Ψ (φ k) x)))) ≤ C) ∧
        (∀ μ (g : L²(𝕋)), Tendsto
          (fun k => inner ℂ g (weakDeriv μ (trigLp (coordGrid j (fun x => Θ (Ψ (φ k) x))))))
          atTop (𝓝 (inner ℂ g (weakDeriv μ f)))) := by
  -- the `L⁴` bound in the fibre norm (covariant grid Sobolev)
  have hBΨ0 : 0 ≤ BΨ := (gridNorm_nonneg _).trans (hΨ 0)
  have hBK0 : 0 ≤ BK := (gridNorm_nonneg _).trans (hK 0 0)
  set C4 : ℝ≥0∞ := ENNReal.ofReal (3 * (4 * BK) + 4 * BΨ)
  have hC4 : C4 ≠ ∞ := ENNReal.ofReal_ne_top
  have hH4 : ∀ k, eLpNorm (pc (Ψ k)) 4 volume ≤ C4 := by
    intro k
    refine (eLpNorm_pc_four_le_covGraph ρ (A k) (Ψ k) (hU k)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hs : ∑ μ, gridNorm (covGraph (n k) ρ (A k) (Ψ k) μ) ≤ 4 * BK := by
      have := Finset.sum_le_sum (fun μ (_ : μ ∈ (Finset.univ : Finset (Fin 4))) => hK k μ)
      simpa using this
    nlinarith [hΨ k]
  -- transfer to the Euclidean frame
  set Ψ' : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → V := fun k x => Θ (Ψ k x)
  have hH4' : ∀ k, eLpNorm (pc (Ψ' k)) 4 volume ≤ ‖(Θ : X →L[ℝ] V)‖₊ * C4 := by
    intro k
    have : eLpNorm (pc (Ψ' k)) 4 volume ≤ ‖(Θ : X →L[ℝ] V)‖₊ • eLpNorm (pc (Ψ k)) 4 volume :=
      eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z =>
        (Θ : X →L[ℝ] V).le_opNNNorm _) 4
    exact this.trans (by rw [ENNReal.smul_def, smul_eq_mul]; gcongr; exact hH4 k)
  have hΨ' : ∀ k, gridNorm (Ψ' k) ≤ ‖(Θ : X →L[ℝ] V)‖ * BΨ := fun k =>
    (gridNorm_clm_le (Θ : X →L[ℝ] V) (Ψ k)).trans
      (mul_le_mul_of_nonneg_left (hΨ k) (norm_nonneg _))
  have hK' : ∀ k μ, gridNorm (higgsLink (n k) (conjRep Θ ρ) (A k) (Ψ' k) μ) ≤
      ‖(Θ : X →L[ℝ] V)‖ * BK := by
    intro k μ
    have e : higgsLink (n k) (conjRep Θ ρ) (A k) (Ψ' k) μ =
        fun x => (Θ : X →L[ℝ] V) (covGraph (n k) ρ (A k) (Ψ k) μ x) :=
      funext fun x => higgsLink_conjRep Θ ρ (A k) (Ψ k) μ x
    rw [e]
    exact (gridNorm_clm_le _ _).trans (mul_le_mul_of_nonneg_left (hK k μ) (norm_nonneg _))
  obtain ⟨⟨BD, hBD⟩, φ, hφ, Ψ₀', f, hH2, hH₀4, hj⟩ := weak_compactness_of_L4 hn (conjRep Θ ρ) hA
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hC4) hH4' hΨ' hK'
  -- the ordinary discrete `H¹` bound in the fibre
  have hDΨ : ∀ k μ, DpV μ (Ψ k) = fun x => (Θ.symm : V →L[ℝ] X) (DpV μ (Ψ' k) x) := by
    intro k μ
    rw [show Ψ' k = fun x => (Θ : X →L[ℝ] V) (Ψ k x) from rfl, DpV_clm]
    funext x; simp
  have hBD' : ∀ k μ, gridNorm (DpV μ (Ψ k)) ≤ ‖(Θ.symm : V →L[ℝ] X)‖ * BD := by
    intro k μ
    rw [hDΨ]
    exact (gridNorm_clm_le _ _).trans (mul_le_mul_of_nonneg_left (hBD k μ) (norm_nonneg _))
  -- the weak limits of the frame components
  set W : Fin 4 → Fin r → L²(𝕋) := fun μ j => weakDeriv μ (f j)
  set v₀ : Fin 4 → 𝕋 → V := fun μ z => ∑ j, ((W μ j : 𝕋 → ℂ) z).re • EuclideanSpace.single j 1
  have hv₀j : ∀ μ z j, v₀ μ z j = ((W μ j : 𝕋 → ℂ) z).re := by
    intro μ z j; simp [v₀, Pi.single_apply]
  have hv₀m : ∀ μ, MemLp (v₀ μ) 2 volume := by
    intro μ
    have : v₀ μ = ∑ j, fun z => ((W μ j : 𝕋 → ℂ) z).re • (EuclideanSpace.single j 1 : V) := by
      funext z; simp [v₀, Finset.sum_apply]
    rw [this]
    exact memLp_finsetSum' _ fun j _ =>
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j 1 : V)).comp_memLp'
        (Complex.reCLM.comp_memLp' (Lp.memLp (W μ j)))
  set u₀ : Fin 4 → 𝕋 → X := fun μ z => Θ.symm (v₀ μ z)
  -- the complex weak limits, coordinatewise
  have hU : ∀ μ j k, ((pcLp (Dp μ (coordGrid j (Ψ' (φ k))))) : 𝕋 → ℂ) =ᵐ[volume]
      fun z => ((pc (DpV μ (Ψ' (φ k))) z j : ℝ) : ℂ) := by
    intro μ j k
    filter_upwards [(memLp_pc (Dp μ (coordGrid j (Ψ' (φ k))))).coeFn_toLp] with z hz
    rw [pcLp, hz, Dp_coordGrid]
    rfl
  have hwj : ∀ μ j (G : L²(𝕋)), Tendsto (fun k => inner ℂ G (pcLp (Dp μ (coordGrid j (Ψ' (φ k))))))
      atTop (𝓝 (inner ℂ G (W μ j))) := fun μ j G => (hj j).2.2.1 μ G
  have hcoord : ∀ μ j (g : 𝕋 → ℝ), MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z * pc (DpV μ (Ψ' (φ k))) z j) atTop
        (𝓝 (∫ z, g z * v₀ μ z j)) := by
    intro μ j g hg
    have := real_weak_of_complex_weak (hU μ j) (hwj μ j) g hg
    simpa only [hv₀j] using this
  refine ⟨⟨C4, hC4, hH4⟩, ⟨_, hBD'⟩, φ, hφ, fun z => Θ.symm (Ψ₀' z), u₀, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hH2.clm (Θ.symm : V →L[ℝ] X)).congr (fun k => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => rfl)
    simp [Ψ', pc]
  · exact (Θ.symm : V →L[ℝ] X).comp_memLp' hH₀4
  · exact fun μ => (Θ.symm : V →L[ℝ] X).comp_memLp' (hv₀m μ)
  · intro μ ℓ g hg
    set c : Fin r → ℝ := fun j => ℓ (Θ.symm (EuclideanSpace.single j 1))
    have hdec : ∀ w : V, ℓ (Θ.symm w) = ∑ j, c j * w j := by
      intro w
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin r) ℝ).sum_repr w]
      simp only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr,
        EuclideanSpace.basisFun_apply, c]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hpc : ∀ k z, pc (DpV μ (Ψ (φ k))) z = Θ.symm (pc (DpV μ (Ψ' (φ k))) z) := by
      intro k z; rw [hDΨ]; rfl
    have hm : ∀ k j, MemLp (fun z => pc (DpV μ (Ψ' (φ k))) z j) 2 volume := fun k j =>
      (EuclideanSpace.proj j : V →L[ℝ] ℝ).comp_memLp' (memLp_pc_gen (DpV μ (Ψ' (φ k))) 2)
    have hm₀ : ∀ j, MemLp (fun z => v₀ μ z j) 2 volume := fun j =>
      (EuclideanSpace.proj j : V →L[ℝ] ℝ).comp_memLp' (hv₀m μ)
    have hL : ∀ k, ∫ z, g z * ℓ (pc (DpV μ (Ψ (φ k))) z) =
        ∑ j, c j * ∫ z, g z * pc (DpV μ (Ψ' (φ k))) z j := by
      intro k
      simp_rw [hpc, hdec, Finset.mul_sum]
      rw [integral_finset_sum _ fun j _ => ?_]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun z => by ring)
      · exact ((hg.integrable_mul (hm k j)).const_mul (c j)).congr
          (Eventually.of_forall fun z => by simp only [Pi.mul_apply]; ring)
    have hL₀ : ∫ z, g z * ℓ (u₀ μ z) = ∑ j, c j * ∫ z, g z * v₀ μ z j := by
      simp_rw [u₀, hdec, Finset.mul_sum]
      rw [integral_finset_sum _ fun j _ => ?_]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun z => by ring)
      · exact ((hg.integrable_mul (hm₀ j)).const_mul (c j)).congr
          (Eventually.of_forall fun z => by simp only [Pi.mul_apply]; ring)
    simp_rw [hL, hL₀]
    exact tendsto_finset_sum _ fun j _ => (hcoord μ j g hg).const_mul (c j)
  · intro j
    refine ⟨f j, ?_, (hj j).2.1, fun μ => ?_, (hj j).2.2.2.1, (hj j).2.2.2.2.1,
      (hj j).2.2.2.2.2⟩
    · simpa using (hj j).1
    · have h := ae_eq_re_of_complex_weak (hU μ j) (hwj μ j)
      filter_upwards [h] with z hz
      simp only [u₀, ContinuousLinearEquiv.apply_symm_apply, hv₀j]
      exact hz

end General

end

end RenewalGeometry.CovariantGraph
