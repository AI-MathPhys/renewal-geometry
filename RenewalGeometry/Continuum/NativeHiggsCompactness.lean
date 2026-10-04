/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeGridLpCalculus

/-!
# Native Higgs graph compactness (`prop:native-Higgs-compactness`, Einstein–SM action closure)

Setting (unit-torus rendering of the paper's periodic box, see
`Continuum/TorusTrigReconstruction.lean`): the grid `(ℤ/N)⁴`, mesh `h = 1/N`.  The Higgs field is
read in one fixed (orthonormal, real) frame of its fibre, `H_h(x) ∈ V = ℝ^r` (a complex Higgs
multiplet is its realification; the paper's `Re⟨·,·⟩`); the connection takes values in a real
normed space `E` (the Lie algebra) and acts through a bounded linear map
`ρ : E → End(V)`; the internal links are `ρ(U_μ(x)) = e^{h ρ(A_μ(x))}` and are assumed unitary
(norm preserving, `hU`), as for a unitary representation of a compact gauge group.

* `higgsLink` — the literal Higgs-link packet `K_{μ,h} = 𝒟^U_{μ,h} H_h = (ρ(U_μ) T_{μ,1} H_h - H_h)/h`;
* `DpV` — the forward difference `D⁺_{μ,h}` of a `V`-valued field;
* `DpV_eq_higgsLink_sub` — the exact graph identity `D⁺_h H_h = K_h - B^ρ_h T H_h`,
  `B^ρ_h = (ρ(U) - I)/h`;
* `native_Higgs_compactness` (**`prop:native-Higgs-compactness`**): if `R_h^0 A_h → A` strongly in
  `L⁴`, `sup_h ‖H_h‖_{2,h} < ∞` and `R_h^0 K_h → K` strongly in `L²`, then after extraction
  `R_h^0 H_h → H` strongly in `L⁴`, `R_h^0 D⁺_h H_h → dH` strongly in `L²`,
  `𝓘_h^trig H_h → H` strongly in `H¹` (each frame component), and `K = D_A H`, i.e.
  `∂_μ H = K_μ - ρ(A_μ) H` (weak derivatives of the frame components).

The proof is the paper's: the covariant (Kato) grid Sobolev inequality
(`GridSobolev.grid_sobolev_L4_covariant`) bounds `‖H_h‖_{4,h}` by the graph norm; the graph
identity, the link-coefficient convergence `R_h^0 B^ρ_h → ρ(A)` in `L⁴`
(`NativeCriticalGrid.tendsto_linkCoeff`) and Hölder bound the ordinary discrete `H¹` norm;
discrete Rellich (componentwise) extracts `R_h^0 H_h → H` in `L²`; one-step shifts have the same
limit and the critical product `B^ρ_h T H_h → ρ(A) H` passes in `L²` by approximating `ρ(A)` in
`L⁴` by bounded coefficients (`NativeGridLp.lpTendsto_bilin_of_bdd`); then the graph identity
gives strong convergence of the forward differences, and
`lem:native-reconstruction-identification` (`native_reconstruction_identification`) identifies
the derivative and gives the strong `H¹` and `L⁴` conclusions.
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.NativeHiggs

open TorusTrigReconstruction NativeCriticalGrid TorusPiecewiseConstantTranslation
  NativeYMIdentification NativeGridLp TorusSobolev

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

local instance fact_one_le_four_h : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_two_h : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance holder442_h : ENNReal.HolderTriple 4 4 2 := TorusSobolev.holderTriple_four_four_two

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Higgs fibre in a fixed orthonormal real frame. -/
local notation "V" => EuclideanSpace ℝ (Fin r)

/-! ### The literal Higgs-link packet and the graph identity -/

section Graph

variable {N : ℕ}

/-- The forward difference `D⁺_μ v (x) = N (v(x + e_μ) - v(x))` of a vector field. -/
def DpV {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (μ : Fin 4)
    (v : LatticeTorusPlancherel.Grid 4 N → F) (x : LatticeTorusPlancherel.Grid 4 N) : F :=
  (N : ℝ) • (v (x + Pi.single μ 1) - v x)

/-- **The literal Higgs-link packet** `K_μ = 𝒟^U_μ H = (ρ(U_μ) T_μ H - H)/h`,
`ρ(U_μ(x)) = e^{h ρ(A_μ(x))}`, `h = 1/N` (`eq:native-internal-graph`). -/
def higgsLink (N : ℕ) (ρ : E →L[ℝ] (V →L[ℝ] V)) (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → E)
    (H : LatticeTorusPlancherel.Grid 4 N → V) (μ : Fin 4) (x : LatticeTorusPlancherel.Grid 4 N) :
    V :=
  (N : ℝ) • (NormedSpace.exp ((N : ℝ)⁻¹ • ρ (A x μ)) (H (x + Pi.single μ 1)) - H x)

/-- **The exact graph identity** `D⁺_μ H = K_μ - B^ρ_μ T_μ H`, `B^ρ = (ρ(U) - I)/h`. -/
theorem DpV_eq_higgsLink_sub (ρ : E →L[ℝ] (V →L[ℝ] V))
    (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → E) (H : LatticeTorusPlancherel.Grid 4 N → V)
    (μ : Fin 4) (x : LatticeTorusPlancherel.Grid 4 N) :
    DpV μ H x = higgsLink N ρ A H μ x - linkCoeff N (ρ (A x μ)) (H (x + Pi.single μ 1)) := by
  simp only [DpV, higgsLink, linkCoeff, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]
  rw [← smul_sub]
  congr 1
  abel

/-- The frame components of a grid field, as complex scalars. -/
def coordGrid (j : Fin r) (H : LatticeTorusPlancherel.Grid 4 N → V) :
    LatticeTorusPlancherel.Grid 4 N → ℂ :=
  fun x => ((H x j : ℝ) : ℂ)

theorem Dp_coordGrid [NeZero N] (μ : Fin 4) (j : Fin r) (H : LatticeTorusPlancherel.Grid 4 N → V) :
    Dp μ (coordGrid j H) = coordGrid j (DpV μ H) := by
  funext x
  simp only [Dp_apply, coordGrid, DpV, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  push_cast
  ring

theorem gridNorm_coordGrid_le [NeZero N] (j : Fin r) (H : LatticeTorusPlancherel.Grid 4 N → V) :
    gridNorm (coordGrid j H) ≤ gridNorm H :=
  gridNorm_mono fun x => by
    rw [coordGrid, Complex.norm_real]
    exact norm_coord_le (H x) j

end Graph

/-! ### Uniform bounds -/

section Bounds

variable {N : ℕ} [NeZero N]

/-- **Covariant grid Sobolev for the Higgs graph** (`eq:native-grid-Sobolev-b`, unit torus):
`‖R_h^0 H‖_{L⁴} ≤ 3 Σ_μ ‖K_μ‖_{2,h} + 4 ‖H‖_{2,h}` for unitary links. -/
theorem eLpNorm_pc_four_le_graph (ρ : E →L[ℝ] (V →L[ℝ] V))
    (A : LatticeTorusPlancherel.Grid 4 N → Fin 4 → E) (H : LatticeTorusPlancherel.Grid 4 N → V)
    (hU : ∀ x μ (v : V), ‖NormedSpace.exp ((N : ℝ)⁻¹ • ρ (A x μ)) v‖ = ‖v‖) :
    eLpNorm (pc H) 4 (volume : Measure (UnitAddTorus (Fin 4))) ≤
      ENNReal.ofReal (3 * ∑ μ, gridNorm (higgsLink N ρ A H μ) + 4 * gridNorm H) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [eLpNorm_pc_four_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := GridSobolev.grid_sobolev_L4_covariant (inv_pos.2 hN) (Fintype.card_fin 4)
    (fun x μ (v : V) => NormedSpace.exp ((N : ℝ)⁻¹ • ρ (A x μ)) v) (fun x μ v => hU x μ v) H
  rw [mul_inv_cancel₀ hN.ne', div_one] at h
  have hcov : ∀ μ, GridSobolev.gridCovFwd ((N : ℝ)⁻¹)
      (fun x μ (v : V) => NormedSpace.exp ((N : ℝ)⁻¹ • ρ (A x μ)) v) μ H = higgsLink N ρ A H μ := by
    intro μ; funext x
    simp only [GridSobolev.gridCovFwd, higgsLink, inv_inv, GridSobolev.gridStep]
  simp only [hcov, gridL2Norm_inv_eq_gridNorm] at h
  exact h

end Bounds

/-! ### Main theorem -/

section Main

variable [NeZero r] {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem _root_.RenewalGeometry.LpTendsto.comp_strictMono {X F : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup F] {p : ℝ≥0∞} {u : ℕ → X → F} {u' : X → F} (hu : LpTendsto ν p u u')
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : LpTendsto ν p (fun k => u (φ k)) u' :=
  ⟨fun k => hu.memLp (φ k), hu.memLp_lim, hu.tendsto.comp hφ.tendsto_atTop⟩

theorem toReal_le_of_le {a : ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞) (h : a ≤ C) : a.toReal ≤ C.toReal :=
  ENNReal.toReal_mono hC h

/-- A complex function whose strong `L²` approximants are real is real. -/
theorem ae_eq_re_of_lpTendsto {u : ℕ → UnitAddTorus (Fin 4) → ℂ} {f : UnitAddTorus (Fin 4) → ℂ}
    (h : LpTendsto volume 2 u f) (hre : ∀ k y, (u k y).im = 0) :
    f =ᵐ[volume] fun y => ((f y).re : ℂ) := by
  have him := h.clm Complex.imCLM
  have h0 : (fun k y => Complex.imCLM (u k y)) = fun _ _ => (0 : ℝ) := by
    funext k y; simp only [Complex.imCLM_apply, hre k y]
  rw [h0] at him
  have hz : eLpNorm (fun y => Complex.imCLM (f y)) 2 volume = 0 := by
    have := him.tendsto
    have e : ((fun _ => (0 : ℝ)) - fun y => Complex.imCLM (f y)) =
        -(fun y => Complex.imCLM (f y)) := by funext y; simp
    simp only [e, eLpNorm_neg] at this
    exact tendsto_nhds_unique tendsto_const_nhds this
  have := (eLpNorm_eq_zero_iff (Complex.imCLM.continuous.comp_aestronglyMeasurable h.memLp_lim.1)
    (by norm_num)).1 hz
  filter_upwards [this] with y hy
  apply Complex.ext <;> simp_all

/-- **`prop:native-Higgs-compactness`** (unit-torus rendering, Higgs field in a fixed orthonormal
real frame `V = ℝ^r`).  Let `R_h^0 A_h → A` strongly in `L⁴`, let the internal links
`e^{h ρ(A_h)}` be unitary, `sup_h ‖H_h‖_{2,h} < ∞`, and let the literal Higgs-link packet satisfy
`R_h^0 K_h → K` strongly in `L²`.  Then after extraction there is `H` with
* `R_h^0 H_h → H` strongly in `L⁴`;
* `R_h^0 D⁺_μ H_h → K_μ - ρ(A_μ) H` strongly in `L²`;
* for every frame component `j`, the component `H^j` (as `f j ∈ L²`) lies in `H¹`, its weak
  derivative is `∂_μ H^j = (K_μ - ρ(A_μ) H)^j` — i.e. `R_h^0 D⁺H_h → dH` and **`K = D_A H`** — and
  the trigonometric reconstructions converge strongly in `H¹`:
  `‖𝓘_h^trig H^j_h - H^j‖_{H¹} → 0`. -/
theorem native_Higgs_compactness (hn : Tendsto n atTop atTop) (ρ : E →L[ℝ] (V →L[ℝ] V))
    {A : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → Fin 4 → E}
    {A₀ : Fin 4 → UnitAddTorus (Fin 4) → E}
    (hA : ∀ μ, LpTendsto volume 4 (fun k => pc (fun x => A k x μ)) (A₀ μ))
    (hU : ∀ k x μ (v : V), ‖NormedSpace.exp ((n k : ℝ)⁻¹ • ρ (A k x μ)) v‖ = ‖v‖)
    {H : ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → V} {BH : ℝ} (hH : ∀ k, gridNorm (H k) ≤ BH)
    {K₀ : Fin 4 → UnitAddTorus (Fin 4) → V}
    (hK : ∀ μ, LpTendsto volume 2 (fun k => pc (higgsLink (n k) ρ (A k) (H k) μ)) (K₀ μ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H₀ : UnitAddTorus (Fin 4) → V, ∃ f : Fin r → L²(UnitAddTorus (Fin 4)),
      LpTendsto volume 4 (fun k => pc (H (φ k))) H₀ ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (DpV μ (H (φ k))))
        (fun y => K₀ μ y - ρ (A₀ μ y) (H₀ y))) ∧
      ∀ j, ((f j : UnitAddTorus (Fin 4) → ℂ) =ᵐ[volume] fun y => ((H₀ y j : ℝ) : ℂ)) ∧
        MemH 1 (f j) ∧
        (∀ μ, (weakDeriv μ (f j) : UnitAddTorus (Fin 4) → ℂ) =ᵐ[volume]
          fun y => (((K₀ μ y - ρ (A₀ μ y) (H₀ y)) j : ℝ) : ℂ)) ∧
        Tendsto (fun k => sobSq 1 ⇑(trigLp (coordGrid j (H (φ k))) - f j)) atTop (𝓝 0) := by
  -- the bounded linear "application" map
  set App : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.id ℝ (V →L[ℝ] V)
  have hApp : ‖App‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe]; exact ContinuousLinearMap.norm_id_le
  -- bounds on the packets
  have hKb : ∀ μ, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ k,
      eLpNorm (pc (higgsLink (n k) ρ (A k) (H k) μ)) 2 volume ≤ C :=
    fun μ => exists_bound_of_lpTendsto (hK μ)
  choose CK hCK hCKb using hKb
  set BK : ℝ := ∑ μ, (CK μ).toReal
  have hBK : ∀ k μ, gridNorm (higgsLink (n k) ρ (A k) (H k) μ) ≤ (CK μ).toReal := by
    intro k μ
    have := hCKb μ k
    rw [eLpNorm_pc_two_eq] at this
    have := ENNReal.toReal_mono (hCK μ) this
    rwa [ENNReal.toReal_ofReal (gridNorm_nonneg _)] at this
  have hBH0 : 0 ≤ BH := (gridNorm_nonneg _).trans (hH 0)
  -- the `L⁴` bound
  set C4 : ℝ≥0∞ := ENNReal.ofReal (3 * BK + 4 * BH)
  have hC4 : C4 ≠ ∞ := ENNReal.ofReal_ne_top
  have hH4 : ∀ k, eLpNorm (pc (H k)) 4 volume ≤ C4 := by
    intro k
    refine (eLpNorm_pc_four_le_graph ρ (A k) (H k) (hU k)).trans (ENNReal.ofReal_le_ofReal ?_)
    have : ∑ μ, gridNorm (higgsLink (n k) ρ (A k) (H k) μ) ≤ BK :=
      Finset.sum_le_sum fun μ _ => hBK k μ
    nlinarith [hH k]
  have hTH4 : ∀ k μ, eLpNorm (pc (T μ (H k))) 4 volume ≤ C4 := fun k μ => by
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
  -- the product `B T H`
  set P : ∀ k, Fin 4 → LatticeTorusPlancherel.Grid 4 (n k) → V := fun k μ x =>
    linkCoeff (n k) (ρ (A k x μ)) (H k (x + Pi.single μ 1))
  have hPpc : ∀ k μ, pc (P k μ) = fun y => App (pc (fun x => linkCoeff (n k) (ρ (A k x μ))) y)
      (pc (T μ (H k)) y) := fun k μ => rfl
  have hP2 : ∀ k μ, eLpNorm (pc (P k μ)) 2 volume ≤ CB μ * C4 := by
    intro k μ
    rw [hPpc]
    refine (eLpNorm_bilin_le' (p := 4) (q := 4) App (stronglyMeasurable_pc _).aestronglyMeasurable
      (stronglyMeasurable_pc _).aestronglyMeasurable).trans ?_
    calc (‖App‖₊ : ℝ≥0∞) * eLpNorm (pc fun x => linkCoeff (n k) (ρ (A k x μ))) 4 volume *
          eLpNorm (pc (T μ (H k))) 4 volume ≤ 1 * CB μ * C4 := by
          gcongr
          · exact_mod_cast hApp
          · exact hCBb μ k
          · exact hTH4 k μ
      _ = CB μ * C4 := by rw [one_mul]
  -- discrete `H¹` bound
  set BD : ℝ := BK + ∑ μ, (CB μ * C4).toReal
  have hDb : ∀ k μ, gridNorm (DpV μ (H k)) ≤ BD := by
    intro k μ
    have e : DpV μ (H k) = higgsLink (n k) ρ (A k) (H k) μ - P k μ := by
      funext x; exact DpV_eq_higgsLink_sub ρ (A k) (H k) μ x
    rw [e]
    have hsub : gridNorm (higgsLink (n k) ρ (A k) (H k) μ - P k μ) ≤
        gridNorm (higgsLink (n k) ρ (A k) (H k) μ) + gridNorm (P k μ) := by
      have := gridNorm_add_le (higgsLink (n k) ρ (A k) (H k) μ) (-P k μ)
      rwa [← sub_eq_add_neg, show gridNorm (-P k μ) = gridNorm (P k μ) by
        unfold gridNorm; simp [norm_neg]] at this
    have hP : gridNorm (P k μ) ≤ (CB μ * C4).toReal := by
      have := hP2 k μ
      rw [eLpNorm_pc_two_eq] at this
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (hCB μ) hC4) this
      rwa [ENNReal.toReal_ofReal (gridNorm_nonneg _)] at this
    have h1 : (CK μ).toReal ≤ BK := Finset.single_le_sum (f := fun μ => (CK μ).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ μ)
    have h2 : (CB μ * C4).toReal ≤ ∑ μ, (CB μ * C4).toReal :=
      Finset.single_le_sum (f := fun μ => (CB μ * C4).toReal) (fun _ _ => ENNReal.toReal_nonneg)
        (Finset.mem_univ μ)
    linarith [hBK k μ]
  -- discrete Rellich for the frame components
  set u : Fin r → ∀ k, LatticeTorusPlancherel.Grid 4 (n k) → ℂ := fun j k => coordGrid j (H k)
  set B₀ := max BH BD
  obtain ⟨φ, hφ, f, hf⟩ := exists_subseq_tendsto_pcLp_family r hn u (B := B₀)
    (fun j k => (gridNorm_coordGrid_le j (H k)).trans ((hH k).trans (le_max_left _ _)))
    (fun j k μ => by
      simp only [u]; rw [Dp_coordGrid]
      exact (gridNorm_coordGrid_le j _).trans ((hDb k μ).trans (le_max_right _ _)))
  have hnφ : Tendsto (fun k => n (φ k)) atTop atTop := hn.comp hφ.tendsto_atTop
  have hfL : ∀ j, LpTendsto volume 2 (fun k => pc (u j (φ k))) (f j : UnitAddTorus (Fin 4) → ℂ) :=
    fun j => lpTendsto_of_norm_pcLp (n := fun k => n (φ k)) (hf j)
  have hreal : ∀ j, (f j : UnitAddTorus (Fin 4) → ℂ) =ᵐ[volume] fun y => (((f j) y).re : ℂ) :=
    fun j => ae_eq_re_of_lpTendsto (hfL j) fun k y => by simp [u, pc, coordGrid]
  -- the limit field
  set H₀ : UnitAddTorus (Fin 4) → V := fun y => ∑ j, ((f j) y).re • EuclideanSpace.single j 1
  have hH₀j : ∀ y j, H₀ y j = ((f j) y).re := by
    intro y j
    simp [H₀, Pi.single_apply]
  have hmemH₀ : ∀ p : ℝ≥0∞, (∀ j, MemLp (f j : UnitAddTorus (Fin 4) → ℂ) p volume) →
      MemLp H₀ p volume := by
    intro p hp
    have : H₀ = ∑ j, fun y => ((f j) y).re • (EuclideanSpace.single j 1 : V) := by
      funext y; simp [H₀, Finset.sum_apply]
    rw [this]
    exact memLp_finset_sum' _ fun j _ =>
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j 1 : V)).comp_memLp'
        (Complex.reCLM.comp_memLp' (hp j))
  -- strong `L²` convergence of the values
  have hH2 : LpTendsto volume 2 (fun k => pc (H (φ k))) H₀ := by
    refine lpTendsto_of_coord (fun k => memLp_pc_gen _ 2) (hmemH₀ 2 fun j => Lp.memLp (f j))
      fun j => ?_
    refine ((hfL j).clm Complex.reCLM).congr (fun k => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · simp [u, pc, coordGrid]
    · simp [hH₀j]
  have hH₀4 : MemLp H₀ 4 volume := hH2.memLp_of_bound (by norm_num) hC4 fun k => hH4 (φ k)
  -- the critical product `B^ρ T H → ρ(A) H`
  have hPconv : ∀ μ, LpTendsto volume 2 (fun k => pc (P (φ k) μ))
      (fun y => ρ (A₀ μ y) (H₀ y)) := by
    intro μ
    have hTH2 : LpTendsto volume 2 (fun k => pc (T μ (H (φ k)))) H₀ :=
      hH2.shift hnφ (by norm_num) μ
    have hQ := lpTendsto_bilin_of_bdd App (hB μ).memLp_lim hTH2 hC4 (fun k => hTH4 (φ k) μ)
      (fun k => memLp_pc_gen _ 4)
    have hBφ := (hB μ).comp_strictMono hφ
    refine ⟨fun k => memLp_pc_gen _ 2, hQ.memLp_lim, ?_⟩
    have hdiff : Tendsto (fun k => eLpNorm (pc (P (φ k) μ) -
        fun y => App (ρ (A₀ μ y)) (pc (T μ (H (φ k))) y)) 2 volume) atTop (𝓝 0) := by
      have hup : Tendsto (fun k => eLpNorm (pc (fun x => linkCoeff (n (φ k)) (ρ (A (φ k) x μ))) -
          fun y => ρ (A₀ μ y)) 4 volume * C4) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.mul_const hBφ.tendsto (Or.inr hC4)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => zero_le)
        fun k => ?_
      have e : pc (P (φ k) μ) - (fun y => App (ρ (A₀ μ y)) (pc (T μ (H (φ k))) y)) =
          fun y => App ((pc (fun x => linkCoeff (n (φ k)) (ρ (A (φ k) x μ))) -
            fun y => ρ (A₀ μ y)) y) (pc (T μ (H (φ k))) y) := by
        funext y; rw [hPpc]; simp only [Pi.sub_apply, map_sub, ContinuousLinearMap.sub_apply]
      rw [e]
      refine (eLpNorm_bilin_le' (p := 4) (q := 4) App
        (((hBφ.memLp k).1.sub hBφ.memLp_lim.1)) (stronglyMeasurable_pc _).aestronglyMeasurable).trans ?_
      calc (‖App‖₊ : ℝ≥0∞) * eLpNorm (pc (fun x => linkCoeff (n (φ k)) (ρ (A (φ k) x μ))) -
            fun y => ρ (A₀ μ y)) 4 volume * eLpNorm (pc (T μ (H (φ k)))) 4 volume
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
    have e : pc (P (φ k) μ) - (fun y => ρ (A₀ μ y) (H₀ y)) =
        (pc (P (φ k) μ) - fun y => App (ρ (A₀ μ y)) (pc (T μ (H (φ k))) y)) +
          ((fun y => App (ρ (A₀ μ y)) (pc (T μ (H (φ k))) y)) - fun y => App (ρ (A₀ μ y)) (H₀ y)) := by
      funext y; simp [App]
    rw [e]
    exact eLpNorm_add_le ((memLp_pc_gen _ 2).1.sub (hQ.memLp k).1)
      ((hQ.memLp k).1.sub hQ.memLp_lim.1) (by norm_num)
  -- strong convergence of the forward differences (the graph identity)
  have hDconv : ∀ μ, LpTendsto volume 2 (fun k => pc (DpV μ (H (φ k))))
      (fun y => K₀ μ y - ρ (A₀ μ y) (H₀ y)) := by
    intro μ
    refine (((hK μ).comp_strictMono hφ).sub (hPconv μ)).congr
      (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => rfl)
    simp only [Pi.sub_apply, pc]
    exact (DpV_eq_higgsLink_sub ρ (A (φ k)) (H (φ k)) μ _).symm
  -- frame components of the forward differences
  set ℓ : Fin r → V →L[ℝ] ℂ := fun j => Complex.ofRealCLM.comp (EuclideanSpace.proj j)
  have hDj : ∀ j μ, LpTendsto volume 2 (fun k => pc (Dp μ (u j (φ k))))
      (fun y => (((K₀ μ y - ρ (A₀ μ y) (H₀ y)) j : ℝ) : ℂ)) := by
    intro j μ
    refine ((hDconv μ).clm (ℓ j)).congr (fun k => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · simp only [u, Dp_coordGrid, pc, coordGrid, ℓ, ContinuousLinearMap.comp_apply,
        Complex.ofRealCLM_apply]
      rfl
    · simp only [ℓ, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
      rfl
  -- `lem:native-reconstruction-identification`, componentwise
  have hid := fun j => native_reconstruction_identification hnφ (u := fun k => u j (φ k))
    (hf j) (fun μ => norm_pcLp_of_lpTendsto (hDj j μ))
  -- the `L⁴` convergence of the vectors
  have hH4conv : LpTendsto volume 4 (fun k => pc (H (φ k))) H₀ := by
    refine lpTendsto_of_coord (fun k => memLp_pc_gen _ 4) hH₀4 fun j => ?_
    have h4 : LpTendsto volume 4 (fun k => pc (u j (φ k))) (f j : UnitAddTorus (Fin 4) → ℂ) :=
      ⟨fun k => memLp_pc_gen _ 4, (hid j).2.2.2.1, (hid j).2.2.2.2⟩
    refine (h4.clm Complex.reCLM).congr (fun k => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · simp [u, pc, coordGrid]
    · simp [hH₀j]
  refine ⟨φ, hφ, H₀, f, hH4conv, hDconv, fun j => ⟨?_, (hid j).2.1, fun μ => ?_, (hid j).2.2.1⟩⟩
  · filter_upwards [hreal j] with y hy
    rw [hy, hH₀j]
  · rw [(hid j).1 μ]
    exact (hDj j μ).memLp_lim.coeFn_toLp

end Main

/-! ### Non-vacuity -/

section NonVacuity

theorem pc_zero_fun {F : Type*} [NormedAddCommGroup F] {N : ℕ} [NeZero N] :
    pc (fun _ : LatticeTorusPlancherel.Grid 4 N => (0 : F)) = 0 := by
  funext y; rfl

/-- Non-vacuity of `native_Higgs_compactness`: the zero connection (with the trivial
representation) and the zero Higgs field on the grids `N = k + 1` satisfy all its hypotheses. -/
example : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H₀ : UnitAddTorus (Fin 4) → EuclideanSpace ℝ (Fin 1),
    ∃ f : Fin 1 → L²(UnitAddTorus (Fin 4)),
    LpTendsto volume 4 (fun k => pc (fun _ : LatticeTorusPlancherel.Grid 4 (k + 1) =>
      (0 : EuclideanSpace ℝ (Fin 1)))) H₀ ∧ ∀ j, MemH 1 (f j) := by
  have hK : ∀ μ, LpTendsto volume 2 (fun k => pc (higgsLink (k + 1)
      (0 : ℝ →L[ℝ] (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)))
      (fun _ _ => (0 : ℝ)) (fun _ => 0) μ)) (fun _ => 0) := by
    intro μ
    have : (fun k => pc (higgsLink (k + 1)
        (0 : ℝ →L[ℝ] (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)))
        (fun _ _ => (0 : ℝ)) (fun _ => 0) μ)) = fun _ => 0 := by
      funext k y; simp [pc, higgsLink]
    rw [this]; exact LpTendsto.const MemLp.zero
  have hA : ∀ μ : Fin 4, LpTendsto volume 4 (fun k => pc (fun _ : LatticeTorusPlancherel.Grid 4 (k + 1) =>
      (0 : ℝ))) (fun _ => (0 : ℝ)) := fun μ => by
    rw [show (fun k => pc (fun _ : LatticeTorusPlancherel.Grid 4 (k + 1) => (0 : ℝ))) =
      fun _ => 0 from funext fun k => pc_zero_fun]
    exact LpTendsto.const MemLp.zero
  obtain ⟨φ, hφ, H₀, f, h4, -, hj⟩ := native_Higgs_compactness (n := fun k => k + 1)
    (tendsto_add_atTop_nat 1) 0 (A := fun k _ _ => (0 : ℝ)) (A₀ := fun _ _ => 0) hA
    (fun k x μ v => by
      rw [ContinuousLinearMap.zero_apply, smul_zero, NormedSpace.exp_zero,
        ContinuousLinearMap.one_apply])
    (H := fun k _ => 0) (BH := 0) (fun k => by
      rw [gridNorm, Finset.sum_eq_zero (fun _ _ => by simp)]; simp) hK
  exact ⟨φ, hφ, H₀, f, h4, fun j => (hj j).2.1⟩

end NonVacuity

end

end RenewalGeometry.NativeHiggs
