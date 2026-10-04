/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeHiggsCompactness

/-!
# Weak native spinor graphs (`prop:native-spinor-variation`, first assertion)

Setting as in `Continuum/NativeHiggsCompactness.lean` (unit-torus rendering of the periodic box,
grid `(ℤ/N)⁴`, mesh `h = 1/N`): a spinor (or dual spinor) field is read in one fixed orthonormal
real frame of its fibre, `Ψ_h(x) ∈ V = ℝ^r` (a complex spinor multiplet is its realification); the
connection takes values in a real normed space `E` acting through a bounded linear map
`ρ : E → End(V)` (the compact internal representation, or its contragredient for the dual spinor),
and the internal links `e^{h ρ(A_μ)}` are unitary.  The positive internal-link graph of
`eq:native-spinor-graph` is
`sup_h (‖Ψ_h‖_{2,h} + Σ_μ ‖𝒟^U_{μ,h} Ψ_h‖_{2,h}) < ∞`, `𝒟^U_μ Ψ = (ρ(U_μ) T_μ Ψ - Ψ)/h`
(`NativeHiggs.higgsLink`, `eq:native-internal-graph`).

* `native_spinor_weak_compactness` — **weak `H¹` spinor compactness**: under the graph bound and
  strong `L⁴` connection convergence, after extraction `R_h^0 Ψ_h → Ψ` strongly in `L²` with
  `Ψ ∈ L⁴`, every frame component of `Ψ` lies in `H¹`, the forward differences converge weakly in
  `L²` to `∂Ψ`, the link term `B^ρ_h T Ψ_h → ρ(A) Ψ` strongly in `L²`, the covariant packet
  `𝒟^U_h Ψ_h ⇀ ∂Ψ + ρ(A)Ψ = D_A Ψ` weakly in `L²`, and the trigonometric reconstructions converge
  strongly in `L²` and weakly in `H¹` (bounded `H¹` norms).  No strong convergence of the spinor
  first differences is used or claimed.
* `native_spinor_pair_bilinear` — joint extraction for a spinor and a dual spinor (two unitary
  representations) and strong `L¹` convergence of every bounded bilinear `β(Ψ_h, Ψ̄_h)` (the
  undifferentiated spinor bilinears), which also stay bounded in `L²`.

The proof is the paper's first step: covariant (Kato) grid Sobolev gives the `L⁴` bound, the graph
identity `D⁺Ψ = 𝒟^UΨ - B^ρ TΨ` with `R_h^0 B^ρ_h → ρ(A)` in `L⁴` gives ordinary discrete `H¹`
bounds, discrete Rellich extracts strong `L²` limits of the values, the critical product passes
strongly in `L²` (bounded-coefficient approximation), and `lem:native-critical-grid`
(`NativeCriticalGrid.weak_limit_of_bounded`) gives the weak derivative limits.
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.NativeSpinor

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

local instance fact_one_le_four_sp : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_two_sp : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance holder442_sp : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two
local instance holder221_sp : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The spinor fibre in a fixed orthonormal real frame. -/
local notation "V" => EuclideanSpace ℝ (Fin r)

section Main

variable [NeZero r] {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem coordGrid_add {N : ℕ} (j : Fin r) (a b : LatticeTorusPlancherel.Grid 4 N → V) :
    coordGrid j (a + b) = coordGrid j a + coordGrid j b := by
  funext x
  simp [coordGrid]

/-- **Weak native spinor graphs** (`prop:native-spinor-variation`, first assertion; unit-torus
rendering, spinor in a fixed orthonormal real frame `V = ℝ^r`).  Let `R_h^0 A_h → A` strongly in
`L⁴`, let the internal links `e^{h ρ(A_h)}` be unitary, and let the positive internal-link graph be
bounded: `‖Ψ_h‖_{2,h} ≤ B_Ψ`, `‖𝒟^U_{μ,h} Ψ_h‖_{2,h} ≤ B_K`.  Then after extraction there are
`Ψ` and `L²` representatives `f j` of its frame components with
* `R_h^0 Ψ_h → Ψ` strongly in `L²`, and `Ψ ∈ L⁴`;
* `R_h^0 (B^ρ_h T_μ Ψ_h) → ρ(A_μ) Ψ` strongly in `L²`;
* for every frame component `j`: `f j = Ψ^j` a.e., `f j ∈ H¹`, `R_h^0 D⁺_μ Ψ^j_h ⇀ ∂_μ Ψ^j`
  weakly in `L²`, the covariant packet satisfies `R_h^0 (𝒟^U_μ Ψ_h)^j ⇀ ∂_μ Ψ^j + (ρ(A_μ)Ψ)^j`
  weakly in `L²` (i.e. `𝒟^U_h Ψ_h ⇀ D_A Ψ`), `𝓘_h^trig Ψ^j_h → Ψ^j` strongly in `L²` with bounded
  `H¹` norms, and `∂_μ 𝓘_h^trig Ψ^j_h ⇀ ∂_μ Ψ^j` weakly in `L²`. -/
theorem native_spinor_weak_compactness (hn : Tendsto n atTop atTop) (ρ : E →L[ℝ] (V →L[ℝ] V))
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → E}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → E}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ))
    (hU : ∀ k x μ (v : V), ‖NormedSpace.exp ((n k : ℝ)⁻¹ • ρ (A k x μ)) v‖ = ‖v‖)
    {Ψ : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → V} {BΨ BK : ℝ}
    (hΨ : ∀ k, gridNorm (Ψ k) ≤ BΨ)
    (hK : ∀ k μ, gridNorm (higgsLink (n k) ρ (A k) (Ψ k) μ) ≤ BK) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ψ₀ : UnitAddTorus (Fin 4) → V,
      ∃ f : Fin r → L²(UnitAddTorus (Fin 4)), ∃ G : Fin 4 → Fin r → L²(UnitAddTorus (Fin 4)),
      LpTendsto volume 2 (fun k => pc (Ψ (φ k))) Ψ₀ ∧ MemLp Ψ₀ 4 volume ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (fun x => linkCoeff (n (φ k)) (ρ (A (φ k) x μ))
          (Ψ (φ k) (x + Pi.single μ 1)))) (fun y => ρ (A₀ μ y) (Ψ₀ y))) ∧
      ∀ j, ((f j : UnitAddTorus (Fin 4) → ℂ) =ᵐ[volume] fun y => ((Ψ₀ y j : ℝ) : ℂ)) ∧
        MemH 1 (f j) ∧
        (∀ μ, (G μ j : UnitAddTorus (Fin 4) → ℂ) =ᵐ[volume]
          fun y => (((ρ (A₀ μ y) (Ψ₀ y)) j : ℝ) : ℂ)) ∧
        (∀ μ (g : L²(UnitAddTorus (Fin 4))), Tendsto
          (fun k => inner ℂ g (pcLp (Dp μ (coordGrid j (Ψ (φ k)))))) atTop
          (𝓝 (inner ℂ g (weakDeriv μ (f j))))) ∧
        (∀ μ (g : L²(UnitAddTorus (Fin 4))), Tendsto
          (fun k => inner ℂ g (pcLp (coordGrid j (higgsLink (n (φ k)) ρ (A (φ k)) (Ψ (φ k)) μ))))
          atTop (𝓝 (inner ℂ g (weakDeriv μ (f j) + G μ j)))) ∧
        Tendsto (fun k => ‖trigLp (coordGrid j (Ψ (φ k))) - f j‖) atTop (𝓝 0) ∧
        (∃ C, ∀ k, sobSq 1 (trigLp (coordGrid j (Ψ (φ k)))) ≤ C) ∧
        (∀ μ (g : L²(UnitAddTorus (Fin 4))), Tendsto
          (fun k => inner ℂ g (weakDeriv μ (trigLp (coordGrid j (Ψ (φ k)))))) atTop
          (𝓝 (inner ℂ g (weakDeriv μ (f j))))) := by
  set App : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.id ℝ (V →L[ℝ] V)
  have hApp : ‖App‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe]; exact ContinuousLinearMap.norm_id_le
  have hBΨ0 : 0 ≤ BΨ := (gridNorm_nonneg _).trans (hΨ 0)
  have hBK0 : 0 ≤ BK := (gridNorm_nonneg _).trans (hK 0 0)
  -- the `L⁴` bound (covariant grid Sobolev)
  set C4 : ℝ≥0∞ := ENNReal.ofReal (3 * (4 * BK) + 4 * BΨ)
  have hC4 : C4 ≠ ∞ := ENNReal.ofReal_ne_top
  have hH4 : ∀ k, eLpNorm (pc (Ψ k)) 4 volume ≤ C4 := by
    intro k
    refine (eLpNorm_pc_four_le_graph ρ (A k) (Ψ k) (hU k)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hs : ∑ μ, gridNorm (higgsLink (n k) ρ (A k) (Ψ k) μ) ≤ 4 * BK := by
      have := Finset.sum_le_sum (fun μ (_ : μ ∈ (Finset.univ : Finset (Fin 4))) => hK k μ)
      simpa using this
    nlinarith [hΨ k]
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
    exact memLp_finset_sum' _ fun j _ =>
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
  -- the critical product `B^ρ T Ψ → ρ(A) Ψ`, strongly in `L²`
  have hPconv : ∀ μ, LpTendsto volume 2 (fun k => pc (P (φ k) μ))
      (fun y => ρ (A₀ μ y) (Ψ₀ y)) := by
    intro μ
    have hTH2 : LpTendsto volume 2 (fun k => pc (T μ (Ψ (φ k)))) Ψ₀ :=
      hH2.shift hnφ (by norm_num) μ
    have hQ := lpTendsto_bilin_of_bdd App (hB μ).memLp_lim hTH2 hC4 (fun k => hTH4 (φ k) μ)
      (fun k => memLp_pc_gen _ 4)
    have hBφ := (hB μ).comp_strictMono hφ
    refine ⟨fun k => memLp_pc_gen _ 2, hQ.memLp_lim, ?_⟩
    have hdiff : Tendsto (fun k => eLpNorm (pc (P (φ k) μ) -
        fun y => App (ρ (A₀ μ y)) (pc (T μ (Ψ (φ k))) y)) 2 volume) atTop (𝓝 0) := by
      have hup : Tendsto (fun k => eLpNorm (pc (fun x => linkCoeff (n (φ k)) (ρ (A (φ k) x μ))) -
          fun y => ρ (A₀ μ y)) 4 volume * C4) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.mul_const hBφ.tendsto (Or.inr hC4)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => zero_le)
        fun k => ?_
      have e : pc (P (φ k) μ) - (fun y => App (ρ (A₀ μ y)) (pc (T μ (Ψ (φ k))) y)) =
          fun y => App ((pc (fun x => linkCoeff (n (φ k)) (ρ (A (φ k) x μ))) -
            fun y => ρ (A₀ μ y)) y) (pc (T μ (Ψ (φ k))) y) := by
        funext y; rw [hPpc]; simp only [Pi.sub_apply, map_sub, ContinuousLinearMap.sub_apply]
      rw [e]
      refine (eLpNorm_bilin_le' (p := 4) (q := 4) App
        (((hBφ.memLp k).1.sub hBφ.memLp_lim.1)) (stronglyMeasurable_pc _).aestronglyMeasurable).trans ?_
      calc (‖App‖₊ : ℝ≥0∞) * eLpNorm (pc (fun x => linkCoeff (n (φ k)) (ρ (A (φ k) x μ))) -
            fun y => ρ (A₀ μ y)) 4 volume * eLpNorm (pc (T μ (Ψ (φ k)))) 4 volume
          ≤ 1 * eLpNorm (pc (fun x => linkCoeff (n (φ k)) (ρ (A (φ k) x μ))) -
            fun y => ρ (A₀ μ y)) 4 volume * C4 := by
            gcongr
            · exact_mod_cast hApp
            · exact hTH4 (φ k) μ
        _ = _ := by rw [one_mul]
    have hsum := hdiff.add hQ.tendsto
    rw [zero_add] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun k => zero_le)
      fun k => ?_
    have e : pc (P (φ k) μ) - (fun y => ρ (A₀ μ y) (Ψ₀ y)) =
        (pc (P (φ k) μ) - fun y => App (ρ (A₀ μ y)) (pc (T μ (Ψ (φ k))) y)) +
          ((fun y => App (ρ (A₀ μ y)) (pc (T μ (Ψ (φ k))) y)) - fun y => App (ρ (A₀ μ y)) (Ψ₀ y)) := by
      funext y; simp [App]
    rw [e]
    exact eLpNorm_add_le ((memLp_pc_gen _ 2).1.sub (hQ.memLp k).1)
      ((hQ.memLp k).1.sub hQ.memLp_lim.1) (by norm_num)
  -- frame components of the link term
  set ℓ : Fin r → V →L[ℝ] ℂ := fun j => Complex.ofRealCLM.comp (EuclideanSpace.proj j)
  have hPj : ∀ j μ, LpTendsto volume 2 (fun k => pc (coordGrid j (P (φ k) μ)))
      (fun y => (((ρ (A₀ μ y) (Ψ₀ y)) j : ℝ) : ℂ)) := by
    intro j μ
    refine ((hPconv μ).clm (ℓ j)).congr (fun k => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · simp only [pc, coordGrid, ℓ, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
      rfl
    · simp only [ℓ, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
      rfl
  set G : Fin 4 → Fin r → L²(UnitAddTorus (Fin 4)) := fun μ j =>
    (hPj j μ).memLp_lim.toLp (fun y => (((ρ (A₀ μ y) (Ψ₀ y)) j : ℝ) : ℂ))
  have hGconv : ∀ j μ, Tendsto (fun k => pcLp (coordGrid j (P (φ k) μ))) atTop (𝓝 (G μ j)) :=
    fun j μ => tendsto_iff_norm_sub_tendsto_zero.2
      (norm_pcLp_of_lpTendsto (n := fun k => n (φ k)) (hPj j μ))
  -- `lem:native-critical-grid`: weak limits of the forward differences
  have hwk := fun j => weak_limit_of_bounded hnφ (u := fun k => u j (φ k)) (B := B₀)
    (fun k => huB j (φ k)) (fun k μ => huD j (φ k) μ) (hf j)
  refine ⟨φ, hφ, Ψ₀, f, G, hH2, hH₀4, hPconv, fun j => ⟨?_, (hwk j).1, fun μ => ?_,
    (hwk j).2.1, fun μ g => ?_, (hwk j).2.2.1, ⟨_, fun k => ((hwk j).2.2.2.1 k).trans
      (add_le_add (pow_le_pow_left₀ (gridNorm_nonneg _) (huB j (φ k)) 2) le_rfl)⟩,
    (hwk j).2.2.2.2⟩⟩
  · filter_upwards [hreal j] with y hy
    rw [hy, hH₀j]
  · exact (hPj j μ).memLp_lim.coeFn_toLp
  · have hsplit : ∀ k, pcLp (coordGrid j (higgsLink (n (φ k)) ρ (A (φ k)) (Ψ (φ k)) μ)) =
        pcLp (Dp μ (u j (φ k))) + pcLp (coordGrid j (P (φ k) μ)) := by
      intro k
      have e : higgsLink (n (φ k)) ρ (A (φ k)) (Ψ (φ k)) μ = DpV μ (Ψ (φ k)) + P (φ k) μ := by
        funext x
        rw [Pi.add_apply, DpV_eq_higgsLink_sub ρ (A (φ k)) (Ψ (φ k)) μ x]
        simp [P]
      rw [e, coordGrid_add, pcLp_add]
      simp only [u]
      rw [Dp_coordGrid]
    have h1 := (hwk j).2.1 μ g
    have h2 := (tendsto_const_nhds (x := g)).inner (𝕜 := ℂ) (hGconv j μ)
    have h3 := h1.add h2
    rw [← inner_add_right] at h3
    refine h3.congr fun k => ?_
    rw [hsplit k, inner_add_right]

end Main

/-! ### Joint extraction for a spinor and a dual spinor; undifferentiated bilinears -/

section Pair

variable {r' : ℕ} [NeZero r] [NeZero r'] {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- **Spinor and dual-spinor graphs together** (`prop:native-spinor-variation`, first assertion,
joint form).  For a spinor `Ψ_h` (representation `ρ`) and a dual spinor `Ψ̄_h` (representation
`ρ'`, e.g. the contragredient one), both with bounded positive internal-link graphs and unitary
links, along one common subsequence both converge strongly in `L²` (limits in `L⁴` with all frame
components in `H¹`), and for every bounded bilinear map `β` (the undifferentiated spinor
bilinears) `β(R_h^0 Ψ_h, R_h^0 Ψ̄_h) → β(Ψ, Ψ̄)` strongly in `L¹`, while staying bounded in
`L²`. -/
theorem native_spinor_pair_bilinear (hn : Tendsto n atTop atTop)
    (ρ : E →L[ℝ] (EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r)))
    (ρ' : E →L[ℝ] (EuclideanSpace ℝ (Fin r') →L[ℝ] EuclideanSpace ℝ (Fin r')))
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → E}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → E}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ))
    (hU : ∀ k x μ (v : EuclideanSpace ℝ (Fin r)),
      ‖NormedSpace.exp ((n k : ℝ)⁻¹ • ρ (A k x μ)) v‖ = ‖v‖)
    (hU' : ∀ k x μ (v : EuclideanSpace ℝ (Fin r')),
      ‖NormedSpace.exp ((n k : ℝ)⁻¹ • ρ' (A k x μ)) v‖ = ‖v‖)
    {Ψ : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → EuclideanSpace ℝ (Fin r)}
    {Ψb : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → EuclideanSpace ℝ (Fin r')} {B : ℝ}
    (hΨ : ∀ k, gridNorm (Ψ k) ≤ B) (hK : ∀ k μ, gridNorm (higgsLink (n k) ρ (A k) (Ψ k) μ) ≤ B)
    (hΨb : ∀ k, gridNorm (Ψb k) ≤ B)
    (hKb : ∀ k μ, gridNorm (higgsLink (n k) ρ' (A k) (Ψb k) μ) ≤ B)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (β : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r') →L[ℝ] X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ψ₀ : UnitAddTorus (Fin 4) → EuclideanSpace ℝ (Fin r),
      ∃ Ψb₀ : UnitAddTorus (Fin 4) → EuclideanSpace ℝ (Fin r'),
      LpTendsto volume 2 (fun k => pc (Ψ (φ k))) Ψ₀ ∧ MemLp Ψ₀ 4 volume ∧
      LpTendsto volume 2 (fun k => pc (Ψb (φ k))) Ψb₀ ∧ MemLp Ψb₀ 4 volume ∧
      (∀ j, ∃ f : L²(UnitAddTorus (Fin 4)),
        ((f : UnitAddTorus (Fin 4) → ℂ) =ᵐ[volume] fun y => ((Ψ₀ y j : ℝ) : ℂ)) ∧ MemH 1 f) ∧
      (∀ j, ∃ f : L²(UnitAddTorus (Fin 4)),
        ((f : UnitAddTorus (Fin 4) → ℂ) =ᵐ[volume] fun y => ((Ψb₀ y j : ℝ) : ℂ)) ∧ MemH 1 f) ∧
      LpTendsto volume 1 (fun k y => β (pc (Ψ (φ k)) y) (pc (Ψb (φ k)) y))
        (fun y => β (Ψ₀ y) (Ψb₀ y)) ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ k,
        eLpNorm (fun y => β (pc (Ψ (φ k)) y) (pc (Ψb (φ k)) y)) 2 volume ≤ C := by
  obtain ⟨φ₁, hφ₁, Ψ₀, f, G, h2, h4, -, hj⟩ :=
    native_spinor_weak_compactness hn ρ hA hU hΨ hK
  have hnφ₁ : Tendsto (fun k => n (φ₁ k)) atTop atTop := hn.comp hφ₁.tendsto_atTop
  obtain ⟨φ₂, hφ₂, Ψb₀, fb, Gb, hb2, hb4, -, hbj⟩ :=
    native_spinor_weak_compactness (n := fun k => n (φ₁ k)) hnφ₁ ρ' (A := fun k => A (φ₁ k))
      (fun μ => (hA μ).comp_strictMono hφ₁) (fun k => hU' (φ₁ k)) (Ψ := fun k => Ψb (φ₁ k))
      (fun k => hΨb (φ₁ k)) (fun k μ => hKb (φ₁ k) μ)
  have hΨφ := h2.comp_strictMono hφ₂
  -- `L⁴` bounds along the extraction (covariant grid Sobolev)
  have hb : 0 ≤ B := (gridNorm_nonneg _).trans (hΨ 0)
  have hL4 : ∀ k, eLpNorm (pc (Ψ k)) 4 volume ≤ ENNReal.ofReal (3 * (4 * B) + 4 * B) := by
    intro k
    refine (eLpNorm_pc_four_le_graph ρ (A k) (Ψ k) (hU k)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hs : ∑ μ, gridNorm (higgsLink (n k) ρ (A k) (Ψ k) μ) ≤ 4 * B := by
      have := Finset.sum_le_sum (fun μ (_ : μ ∈ (Finset.univ : Finset (Fin 4))) => hK k μ)
      simpa using this
    nlinarith [hΨ k]
  have hL4b : ∀ k, eLpNorm (pc (Ψb k)) 4 volume ≤ ENNReal.ofReal (3 * (4 * B) + 4 * B) := by
    intro k
    refine (eLpNorm_pc_four_le_graph ρ' (A k) (Ψb k) (hU' k)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hs : ∑ μ, gridNorm (higgsLink (n k) ρ' (A k) (Ψb k) μ) ≤ 4 * B := by
      have := Finset.sum_le_sum (fun μ (_ : μ ∈ (Finset.univ : Finset (Fin 4))) => hKb k μ)
      simpa using this
    nlinarith [hΨb k]
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, Ψ₀, Ψb₀, hΨφ, h4, hb2, hb4,
    fun j => ⟨f j, (hj j).1, (hj j).2.1⟩, fun j => ⟨fb j, (hbj j).1, (hbj j).2.1⟩,
    LpTendsto.bilin (p := 2) (q := 2) (r := 1) β hΨφ hb2, ?_⟩
  refine ⟨‖β‖₊ * ENNReal.ofReal (3 * (4 * B) + 4 * B) * ENNReal.ofReal (3 * (4 * B) + 4 * B),
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top, fun k => ?_⟩
  refine (eLpNorm_bilin_le' (p := 4) (q := 4) β (stronglyMeasurable_pc _).aestronglyMeasurable
    (stronglyMeasurable_pc _).aestronglyMeasurable).trans ?_
  gcongr
  · exact hL4 _
  · exact hL4b _

end Pair

/-! ### Non-vacuity -/

section NonVacuity

/-- Non-vacuity of `native_spinor_weak_compactness`: zero connection (trivial representation) and
zero spinor field on the grids `N = k + 1`. -/
example : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ψ₀ : UnitAddTorus (Fin 4) → EuclideanSpace ℝ (Fin 1),
    LpTendsto volume 2 (fun k => pc (fun _ : LatticeTorusPlancherel.Grid 4 (φ k + 1) =>
      (0 : EuclideanSpace ℝ (Fin 1)))) Ψ₀ := by
  have hA : ∀ μ : Fin 4, LpTendsto volume 4 (fun k => pc (fun _ : LatticeTorusPlancherel.Grid 4
      (k + 1) => (0 : ℝ))) (fun _ => (0 : ℝ)) := fun μ => by
    rw [show (fun k => pc (fun _ : LatticeTorusPlancherel.Grid 4 (k + 1) => (0 : ℝ))) =
      fun _ => 0 from funext fun k => pc_zero_fun]
    exact LpTendsto.const MemLp.zero
  obtain ⟨φ, hφ, Ψ₀, -, -, h2, -⟩ := native_spinor_weak_compactness (n := fun k => k + 1)
    (tendsto_add_atTop_nat 1)
    (0 : ℝ →L[ℝ] (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)))
    (A := fun k _ _ => (0 : ℝ)) (A₀ := fun _ _ => 0) hA
    (fun k x μ v => by
      rw [ContinuousLinearMap.zero_apply, smul_zero, NormedSpace.exp_zero,
        ContinuousLinearMap.one_apply])
    (Ψ := fun k _ => 0) (BΨ := 0) (BK := 0)
    (fun k => by rw [gridNorm, Finset.sum_eq_zero (fun _ _ => by simp)]; simp)
    (fun k μ => by
      rw [gridNorm, Finset.sum_eq_zero (fun _ _ => by simp [higgsLink])]; simp)
  exact ⟨φ, hφ, Ψ₀, h2⟩

end NonVacuity

end

end RenewalGeometry.NativeSpinor
