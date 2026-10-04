/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.CovariantWilsonCoreConsistencyExact
import RenewalGeometry.Analysis.LatticeCellL2Estimates
import RenewalGeometry.Spectralization.DensitySymmetricSpinDiracExact
import RenewalGeometry.DiscreteAnalysis.ExactSpinTransportLinks

/-!
# `L²` smooth-core consistency of the covariant Wilson operator with cell-average sampling

Paper `predictive_spectral_geometry`, label `lem:supp-general-core`
(`eq:supp-general-core`, `eq:Wilson-core-smallness`), in the `L²`/Sobolev form with the
cell-average sampling `S_h = (𝒥⁰_h)^*`.

Setting (whole coordinate space `ℝᵈ`, lattice `hℤᵈ`, cell weight `hᵈ`): the lattice operator is
the covariant doubled Wilson operator `covariantWilson h ϖ c U Γ` of
`CovariantWilsonCoreConsistencyExact` (`eq:supp-general-Wilson`, spin links `U`), applied to the
cell averages `S_h ψ = cellAvg h ψ`; its piecewise-constant reconstruction `𝒥⁰_h` is
`y ↦ (·)(cellIdx h y)`.  The continuum operator is the density-symmetric Dirac operator
`-(i/2) Σ_j (M_{c^j} ∇_j + ∇_j M_{c^j})` of `lem:supp-density-symmetric`.

* `covariantWilson_cellAvg`: the lattice operator on cell averages is the cell average of the
  lattice operator on translated point samples (exact identity, `eq`-form of "Taylor's formula
  applied to spin-parallel translated cell averages").
* `covariantWilson_sample_sub_frozenSym` and `norm_covariantWilson_sample_sub_frozenSym_le`: on
  point samples the operator differs from the density-symmetric operator with coefficients frozen
  at the lattice point by explicit local errors (centred differences, coefficient variation by the
  discrete Leibniz rule, Wilson term), bounded by line integrals `∫_{-h}^{h} ‖D^k φ‖` (`k = 1, 2`)
  and `h ‖φ(p ± h e_j)‖` (Taylor with integral remainder; no sup norms of `ψ`).
* `densitySymmetricDirac_eq_frozenSym`: the Leibniz rule `∇_j(c^j ψ) = c'^j ψ + c^j ∇_j ψ` from the
  coefficient hypotheses `CoeffBounds` (bounded, Lipschitz `c^j`, `Ω_j`; derivative `c'^j` of
  `c^j` along `e_j`, bounded and Lipschitz) — no bounds on the products `c^j ψ` are assumed.
* `enorm_core_error_le`: pointwise in `y`, the error is at most `h` times local averages of `|ψ|`,
  `|Dψ|`, `|D²ψ|` over the ball of radius `2h`, plus the cell-averaging errors of `ψ`, `Dψ`.
* **`lintegral_covariantWilson_cellAvg_sub_densitySymmetricDirac_le`** (`eq:supp-general-core`):
  `‖𝒥⁰_h D̃ S_h ψ - (-(i/2) Σ_j (c^j ∇_j + ∇_j c^j)) ψ‖²_{L²} ≤ K h² ‖ψ‖²_{H²}`, `K` depending only on
  `d` and the coefficient/connection/link/Wilson bounds (`coreL2Constant`), for every `C²` spinor
  on `ℝᵈ` and `0 < h ≤ 1`.
* **`wilsonCore_smallness`** (`eq:Wilson-core-smallness`): `hᵈ Σ_x ‖W^Ω_h S_h ψ (x)‖² ≤ K h² ‖ψ‖²_{H²}`
  (`lintegral_comp_cellIdx`: `𝒥⁰_h` is isometric for the cell weight `hᵈ`).
* `lintegral_covariantWilson_cellAvg_sub_geometricDirac_le`, **`supp_general_core_exactTransport`**:
  composed with `lem:supp-density-symmetric` (`ρ^{1/2} D_g ρ^{-1/2}` with the Levi-Civita spin
  connection) and with exact spin parallel transport links (`IsExactInverseTransport`), both
  clauses with `‖ψ‖_{H³}` (resp. `‖ψ‖_{H²}`) on the right.

The estimates are stated on the whole coordinate space `ℝᵈ` with the lattice `hℤᵈ` (coefficients
and frame defined and bounded on `ℝᵈ`, e.g. the smooth periodic extension of the paper); for `ψ`
supported in the interior of the periodic box and small `h` the periodic and whole-space
quantities coincide.  Fibres `ℂ^N` carry the sup norm (equivalent to the Euclidean norm).
-/

open MeasureTheory Set Filter Finset Matrix
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.CovariantWilsonCoreL2

open CovariantWilsonCoreConsistency FrozenWilsonCoreConsistency LatticeCellL2
open FrozenWilsonSymbol

variable {d N : ℕ}

/-! ### Stencil form of the lattice operator -/

/-- The nearest-neighbour stencil `{0} ∪ {± e_j}`. -/
abbrev Stencil (d : ℕ) := Option (Bool × Fin d)

/-- The values of a lattice section on the stencil around `x`. -/
def stencilValues (u : LatticeSection d N) (x : Fin d → ℤ) : Stencil d → (Fin N → ℂ)
  | none => u x
  | some (true, j) => u (x + Pi.single j 1)
  | some (false, j) => u (x - Pi.single j 1)

/-- The covariant Wilson operator at `x` as an explicit function of the stencil values. -/
def stencilForm (h ϖ : ℝ) (c : Coefficients d N) (U : Links d N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (x : Fin d → ℤ) (a : Stencil d → (Fin N → ℂ)) :
    Fin N → ℂ :=
  (2 : ℂ)⁻¹ • ∑ j, (c j (latticePoint h x) *ᵥ ((2 * Complex.I * (h : ℂ))⁻¹ •
        (U j x *ᵥ a (some (true, j)) - (U j (x - Pi.single j 1))ᴴ *ᵥ a (some (false, j)))) +
      (2 * Complex.I * (h : ℂ))⁻¹ •
        (U j x *ᵥ (c j (latticePoint h (x + Pi.single j 1)) *ᵥ a (some (true, j))) -
          (U j (x - Pi.single j 1))ᴴ *ᵥ
            (c j (latticePoint h (x - Pi.single j 1)) *ᵥ a (some (false, j))))) +
    (ϖ : ℂ) • Γ *ᵥ ((2 * (h : ℂ))⁻¹ • ∑ j, ((2 : ℂ) • a none - U j x *ᵥ a (some (true, j)) -
      (U j (x - Pi.single j 1))ᴴ *ᵥ a (some (false, j))))

theorem covariantWilson_eq_stencilForm (h ϖ : ℝ) (c : Coefficients d N) (U : Links d N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (u : LatticeSection d N) (x : Fin d → ℤ) :
    covariantWilson h ϖ c U Γ u x = stencilForm h ϖ c U Γ x (stencilValues u x) := rfl

/-- The stencil form is `ℂ`-linear in the stencil values. -/
def stencilLin (h ϖ : ℝ) (c : Coefficients d N) (U : Links d N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (x : Fin d → ℤ) :
    (Stencil d → (Fin N → ℂ)) →ₗ[ℂ] (Fin N → ℂ) where
  toFun := stencilForm h ϖ c U Γ x
  map_add' a b := by
    simp only [stencilForm, Pi.add_apply, Matrix.mulVec_add, Matrix.mulVec_sub, smul_add,
      smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel
  map_smul' r a := by
    simp only [stencilForm, Pi.smul_apply, Matrix.mulVec_smul, Matrix.mulVec_sub,
      Matrix.mulVec_add, smul_add, smul_sub, Finset.smul_sum, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, smul_smul, RingHom.id_apply, mul_comm r, mul_assoc,
      Matrix.mulVec_sum]

/-! ### Cell averages of the lattice operator -/

theorem latticePoint_add (h : ℝ) (x v : Fin d → ℤ) :
    latticePoint h (x + v) = latticePoint h x + latticeVec h v := by
  funext i
  simp [latticePoint, latticeVec, mul_add]

theorem cellIdx_latticePoint {h : ℝ} (hh : 0 < h) (x : Fin d → ℤ) :
    cellIdx h (latticePoint h x) = x := by
  funext i
  simp only [cellIdx, latticePoint]
  rw [mul_div_cancel_left₀ _ hh.ne', Int.floor_intCast]

theorem latticePoint_mem_cell {h : ℝ} (hh : 0 < h) (x : Fin d → ℤ) :
    latticePoint h x ∈ cell h x := cellIdx_latticePoint hh x

theorem norm_sub_latticePoint_lt {h : ℝ} (hh : 0 < h) {x : Fin d → ℤ} {y : Fin d → ℝ}
    (hy : y ∈ cell h x) : ‖y - latticePoint h x‖ < h :=
  norm_sub_lt_of_mem_cell hh (latticePoint_mem_cell hh x) hy

theorem cell_subset_closedBall {h : ℝ} (hh : 0 < h) (x : Fin d → ℤ) :
    cell h x ⊆ Metric.closedBall (latticePoint h x) h := by
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact (norm_sub_latticePoint_lt hh hy).le

theorem integrableOn_cell {E : Type*} [NormedAddCommGroup E] {h : ℝ} (hh : 0 < h)
    {f : (Fin d → ℝ) → E} (hf : Continuous f) (x : Fin d → ℤ) :
    IntegrableOn f (cell h x) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
    (cell_subset_closedBall hh x)

/-- The translated point sample `x' ↦ ψ(z + h(x' - x))` (point samples of `ψ` along the lattice
through `z`, indexed so that `x` corresponds to `z`). -/
def transSample (h : ℝ) (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (x : Fin d → ℤ) (z : Fin d → ℝ) :
    LatticeSection d N :=
  sample h (fun q => ψ (q + (z - latticePoint h x)))

theorem stencilValues_cellAvg {h : ℝ} (hh : 0 < h) (ψ : (Fin d → ℝ) → (Fin N → ℂ))
    (hψ : Continuous ψ) (x : Fin d → ℤ) :
    stencilValues (cellAvg h ψ) x =
      (h ^ d)⁻¹ • ∫ z in cell h x, stencilValues (transSample h ψ x z) x := by
  have hF : ∀ k, Integrable (fun z => stencilValues (transSample h ψ x z) x k)
      (volume.restrict (cell h x)) := by
    intro k
    refine integrableOn_cell hh ?_ x
    rcases k with _ | ⟨b, j⟩
    · exact hψ.comp (continuous_const.add (continuous_id.sub continuous_const))
    · cases b
      · exact hψ.comp (continuous_const.add (continuous_id.sub continuous_const))
      · exact hψ.comp (continuous_const.add (continuous_id.sub continuous_const))
  funext k
  rw [Pi.smul_apply, eval_integral hF]
  rcases k with _ | ⟨b, j⟩
  · simp only [stencilValues, transSample, sample, cellAvg, add_sub_cancel]
  · cases b
    · simp only [stencilValues, transSample, sample]
      rw [sub_eq_add_neg, cellAvg_add hh]
      congr 1
      refine setIntegral_congr_fun (measurableSet_cell h x) fun z _ => ?_
      simp only [latticePoint_add]
      congr 1
      abel
    · simp only [stencilValues, transSample, sample]
      rw [cellAvg_add hh]
      congr 1
      refine setIntegral_congr_fun (measurableSet_cell h x) fun z _ => ?_
      simp only [latticePoint_add]
      congr 1
      abel

/-- **The lattice operator on cell averages** is the cell average of the lattice operator on
translated point samples: `D̃ (S_h ψ)(x) = h^{-d} ∫_{cell x} D̃ (ψ(z + h(· - x)))(x) dz`. -/
theorem covariantWilson_cellAvg (h ϖ : ℝ) (hh : 0 < h) (c : Coefficients d N) (U : Links d N)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (hψ : Continuous ψ)
    (x : Fin d → ℤ) :
    covariantWilson h ϖ c U Γ (cellAvg h ψ) x =
      (h ^ d)⁻¹ • ∫ z in cell h x, covariantWilson h ϖ c U Γ (transSample h ψ x z) x := by
  have hF : Integrable (fun z => stencilValues (transSample h ψ x z) x)
      (volume.restrict (cell h x)) := by
    refine Integrable.of_eval fun k => ?_
    refine integrableOn_cell hh ?_ x
    rcases k with _ | ⟨b, j⟩
    · exact hψ.comp (continuous_const.add (continuous_id.sub continuous_const))
    · cases b
      · exact hψ.comp (continuous_const.add (continuous_id.sub continuous_const))
      · exact hψ.comp (continuous_const.add (continuous_id.sub continuous_const))
  set L : (Stencil d → (Fin N → ℂ)) →L[ℂ] (Fin N → ℂ) :=
    LinearMap.toContinuousLinearMap (stencilLin h ϖ c U Γ x)
  rw [covariantWilson_eq_stencilForm, stencilValues_cellAvg hh ψ hψ x]
  have h1 : stencilForm h ϖ c U Γ x ((h ^ d)⁻¹ • ∫ z in cell h x,
      stencilValues (transSample h ψ x z) x) =
      L ((h ^ d)⁻¹ • ∫ z in cell h x, stencilValues (transSample h ψ x z) x) := rfl
  rw [h1, L.map_smul_of_tower, ← L.integral_comp_comm hF]
  rfl

/-! ### The frozen density-symmetric operator -/

/-- The first-order jet `(ψ(q), ∂_1 ψ(q), …, ∂_d ψ(q))`. -/
def jet (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (q : Fin d → ℝ) : Option (Fin d) → (Fin N → ℂ)
  | none => ψ q
  | some j => fderiv ℝ ψ q (dir j)

/-- The density-symmetric operator with coefficients frozen at `p`, acting on a jet `a`:
`-(i/2) Σ_j (c^j(p)(a_j + Ω_j(p) a_0) + c'^j(p) a_0 + c^j(p) a_j + Ω_j(p) c^j(p) a_0)`, where
`c'^j = ∂_j c^j`.  On the jet of `ψ` at `p` it is `-(i/2) Σ_j (c^j ∇_j ψ + ∇_j (c^j ψ))(p)`. -/
def frozenSym (c c' Ω : Coefficients d N) (p : Fin d → ℝ) (a : Option (Fin d) → (Fin N → ℂ)) :
    Fin N → ℂ :=
  (-(Complex.I / 2)) • ∑ j, (c j p *ᵥ (a (some j) + Ω j p *ᵥ a none) +
    (c' j p *ᵥ a none + c j p *ᵥ a (some j) + Ω j p *ᵥ (c j p *ᵥ a none)))

/-- `frozenSym` is linear in the jet. -/
def frozenSymLin (c c' Ω : Coefficients d N) (p : Fin d → ℝ) :
    (Option (Fin d) → (Fin N → ℂ)) →ₗ[ℂ] (Fin N → ℂ) where
  toFun := frozenSym c c' Ω p
  map_add' a b := by
    simp only [frozenSym, Pi.add_apply, Matrix.mulVec_add, smul_add, Finset.sum_add_distrib]
    abel
  map_smul' r a := by
    simp only [frozenSym, Pi.smul_apply, Matrix.mulVec_add, Matrix.mulVec_smul, smul_add,
      Finset.smul_sum, Finset.sum_add_distrib, smul_smul, RingHom.id_apply, mul_comm r, mul_assoc]

/-- The coefficient hypotheses: `c^j` bounded and Lipschitz, with derivative `c'^j` along `e_j`
that is bounded and Lipschitz; `Ω_j` bounded and Lipschitz (operator form, sup norms). -/
structure CoeffBounds (c c' Ω : Coefficients d N) (C0 C1 C2 B0 B1 : ℝ) : Prop where
  c_bound : ∀ j y (v : Fin N → ℂ), ‖c j y *ᵥ v‖ ≤ C0 * ‖v‖
  c_lip : ∀ j y z (v : Fin N → ℂ), ‖(c j y - c j z) *ᵥ v‖ ≤ C1 * ‖y - z‖ * ‖v‖
  c'_bound : ∀ j y (v : Fin N → ℂ), ‖c' j y *ᵥ v‖ ≤ C1 * ‖v‖
  c'_lip : ∀ j y z (v : Fin N → ℂ), ‖(c' j y - c' j z) *ᵥ v‖ ≤ C2 * ‖y - z‖ * ‖v‖
  c_deriv : ∀ j y (v : Fin N → ℂ),
    HasDerivAt (fun t : ℝ => c j (y + t • dir j) *ᵥ v) (c' j y *ᵥ v) 0
  Ω_bounds : ConnectionBounds Ω B0 B1

/-- **Leibniz rule**: `∂_j (c^j ψ) = c'^j ψ + c^j ∂_j ψ`. -/
theorem hasLineDerivAt_mulVec {c c' : Coefficients d N} (j : Fin d)
    (hcd : ∀ y (v : Fin N → ℂ),
      HasDerivAt (fun t : ℝ => c j (y + t • dir j) *ᵥ v) (c' j y *ᵥ v) 0)
    {ψ : (Fin d → ℝ) → (Fin N → ℂ)} (hψ : Differentiable ℝ ψ) (y : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ => c j (y + t • dir j) *ᵥ ψ (y + t • dir j))
      (c' j y *ᵥ ψ y + c j y *ᵥ fderiv ℝ ψ y (dir j)) 0 := by
  have hψl : HasDerivAt (fun t : ℝ => ψ (y + t • dir j)) (fderiv ℝ ψ y (dir j)) 0 := by
    have := LatticeCellL2.hasDerivAt_line hψ y (dir j) 0
    simpa using this
  rw [hasDerivAt_pi]
  intro a
  have hentry : ∀ k : Fin N, HasDerivAt (fun t : ℝ => c j (y + t • dir j) a k) (c' j y a k) 0 := by
    intro k
    have h1 := (hasDerivAt_pi.mp (hcd y (Pi.single k 1))) a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
  have hcomp : ∀ k : Fin N, HasDerivAt (fun t : ℝ => ψ (y + t • dir j) k)
      (fderiv ℝ ψ y (dir j) k) 0 := fun k => (hasDerivAt_pi.mp hψl) k
  have hk : ∀ k : Fin N, HasDerivAt (fun t : ℝ => c j (y + t • dir j) a k * ψ (y + t • dir j) k)
      (c' j y a k * ψ y k + c j y a k * fderiv ℝ ψ y (dir j) k) 0 := by
    intro k
    have := (hentry k).mul (hcomp k)
    simp only [zero_smul, add_zero] at this
    exact this
  have hsum := HasDerivAt.sum (u := Finset.univ) (A := fun k (t : ℝ) =>
    c j (y + t • dir j) a k * ψ (y + t • dir j) k) fun k _ => hk k
  convert hsum using 1
  · funext t
    simp [Matrix.mulVec, dotProduct]
  · simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib]

/-- **The density-symmetric operator is the frozen operator on the jet**:
`-(i/2) Σ_j (M_{c^j} ∇_j + ∇_j M_{c^j}) ψ (y) = frozenSym c c' Ω y (jet ψ y)`. -/
theorem densitySymmetricDirac_eq_frozenSym {c c' Ω : Coefficients d N}
    (hcd : ∀ j y (v : Fin N → ℂ),
      HasDerivAt (fun t : ℝ => c j (y + t • dir j) *ᵥ v) (c' j y *ᵥ v) 0)
    {ψ : (Fin d → ℝ) → (Fin N → ℂ)} (hψ : Differentiable ℝ ψ) (y : Fin d → ℝ) :
    densitySymmetricDirac c Ω ψ y = frozenSym c c' Ω y (jet ψ y) := by
  unfold densitySymmetricDirac frozenSym covDeriv
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : lineDeriv ℝ ψ y (dir j) = fderiv ℝ ψ y (dir j) := (hψ y).lineDeriv_eq_fderiv
  have h2 : lineDeriv ℝ (fun z => c j z *ᵥ ψ z) y (dir j) =
      c' j y *ᵥ ψ y + c j y *ᵥ fderiv ℝ ψ y (dir j) :=
    (show HasLineDerivAt ℝ (fun z => c j z *ᵥ ψ z)
      (c' j y *ᵥ ψ y + c j y *ᵥ fderiv ℝ ψ y (dir j)) y (dir j) from
      hasLineDerivAt_mulVec j (hcd j) hψ y).lineDeriv
  rw [h1, h2]
  simp only [jet]

/-- Elementary operator-norm bound for `frozenSym`. -/
theorem norm_frozenSym_le {c c' Ω : Coefficients d N} {C0 C1 C2 B0 B1 : ℝ}
    (hb : CoeffBounds c c' Ω C0 C1 C2 B0 B1) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hB0 : 0 ≤ B0)
    (p : Fin d → ℝ) (a : Option (Fin d) → (Fin N → ℂ)) :
    ‖frozenSym c c' Ω p a‖ ≤
      ∑ j, (C0 * ‖a (some j)‖ + (C0 * B0 + C1) * ‖a none‖) := by
  unfold frozenSym
  rw [norm_smul]
  have hI : ‖-(Complex.I / 2)‖ = 1 / 2 := by
    rw [norm_neg, norm_div, Complex.norm_I]
    norm_num
  rw [hI]
  have hj : ∀ j, ‖c j p *ᵥ (a (some j) + Ω j p *ᵥ a none) +
      (c' j p *ᵥ a none + c j p *ᵥ a (some j) + Ω j p *ᵥ (c j p *ᵥ a none))‖ ≤
      2 * (C0 * ‖a (some j)‖ + (C0 * B0 + C1) * ‖a none‖) := by
    intro j
    have e1 := hb.c_bound j p (a (some j) + Ω j p *ᵥ a none)
    have e2 := hb.Ω_bounds.1 j p (a none)
    have e3 := hb.c'_bound j p (a none)
    have e4 := hb.c_bound j p (a (some j))
    have e5 := hb.Ω_bounds.1 j p (c j p *ᵥ a none)
    have e6 := hb.c_bound j p (a none)
    have e7 := norm_add_le (a (some j)) (Ω j p *ᵥ a none)
    calc _ ≤ ‖c j p *ᵥ (a (some j) + Ω j p *ᵥ a none)‖ +
          (‖c' j p *ᵥ a none‖ + ‖c j p *ᵥ a (some j)‖ + ‖Ω j p *ᵥ (c j p *ᵥ a none)‖) := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ C0 * (‖a (some j)‖ + B0 * ‖a none‖) +
          (C1 * ‖a none‖ + C0 * ‖a (some j)‖ + B0 * (C0 * ‖a none‖)) := by
          gcongr
          · exact e1.trans (mul_le_mul_of_nonneg_left (e7.trans (add_le_add le_rfl e2)) hC0)
          · exact e5.trans (mul_le_mul_of_nonneg_left e6 hB0)
      _ ≤ 2 * (C0 * ‖a (some j)‖ + (C0 * B0 + C1) * ‖a none‖) := by
          nlinarith [mul_nonneg hC1 (norm_nonneg (a none))]
  calc 1 / 2 * ‖∑ j, (c j p *ᵥ (a (some j) + Ω j p *ᵥ a none) +
        (c' j p *ᵥ a none + c j p *ᵥ a (some j) + Ω j p *ᵥ (c j p *ᵥ a none)))‖
      ≤ 1 / 2 * ∑ j, 2 * (C0 * ‖a (some j)‖ + (C0 * B0 + C1) * ‖a none‖) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hj j)
    _ = _ := by
        rw [← Finset.mul_sum]
        ring

theorem norm_add7_le {E : Type*} [SeminormedAddCommGroup E] (a1 a2 a3 a4 a5 a6 a7 : E) :
    ‖a1 + a2 + a3 + a4 + a5 + a6 + a7‖ ≤
      ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖a4‖ + ‖a5‖ + ‖a6‖ + ‖a7‖ := by
  have h1 := norm_add_le (a1 + a2 + a3 + a4 + a5 + a6) a7
  have h2 := norm_add_le (a1 + a2 + a3 + a4 + a5) a6
  have h3 := norm_add_le (a1 + a2 + a3 + a4) a5
  have h4 := norm_add_le (a1 + a2 + a3) a4
  have h5 := norm_add_le (a1 + a2) a3
  have h6 := norm_add_le a1 a2
  linarith

/-- **Coefficient freezing**: `frozenSym` at `p` and at `q` differ by `O(‖p - q‖)`. -/
theorem norm_frozenSym_sub_le {c c' Ω : Coefficients d N} {C0 C1 C2 B0 B1 : ℝ}
    (hb : CoeffBounds c c' Ω C0 C1 C2 B0 B1) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (p q : Fin d → ℝ) (a : Option (Fin d) → (Fin N → ℂ)) :
    ‖frozenSym c c' Ω p a - frozenSym c c' Ω q a‖ ≤
      ‖p - q‖ * ∑ j, (C1 * ‖a (some j)‖ + (C1 * B0 + C0 * B1 + C2) * ‖a none‖) := by
  unfold frozenSym
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul]
  have hI : ‖-(Complex.I / 2)‖ = 1 / 2 := by
    rw [norm_neg, norm_div, Complex.norm_I]
    norm_num
  rw [hI]
  set δ := ‖p - q‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have hj : ∀ j, ‖(c j p *ᵥ (a (some j) + Ω j p *ᵥ a none) +
      (c' j p *ᵥ a none + c j p *ᵥ a (some j) + Ω j p *ᵥ (c j p *ᵥ a none))) -
      (c j q *ᵥ (a (some j) + Ω j q *ᵥ a none) +
      (c' j q *ᵥ a none + c j q *ᵥ a (some j) + Ω j q *ᵥ (c j q *ᵥ a none)))‖ ≤
      2 * (δ * (C1 * ‖a (some j)‖ + (C1 * B0 + C0 * B1 + C2) * ‖a none‖)) := by
    intro j
    set a0 := a none
    set aj := a (some j)
    have hdec : (c j p *ᵥ (aj + Ω j p *ᵥ a0) +
        (c' j p *ᵥ a0 + c j p *ᵥ aj + Ω j p *ᵥ (c j p *ᵥ a0))) -
        (c j q *ᵥ (aj + Ω j q *ᵥ a0) +
        (c' j q *ᵥ a0 + c j q *ᵥ aj + Ω j q *ᵥ (c j q *ᵥ a0))) =
        (c j p - c j q) *ᵥ aj + (c j p - c j q) *ᵥ (Ω j p *ᵥ a0) +
          c j q *ᵥ ((Ω j p - Ω j q) *ᵥ a0) + (c' j p - c' j q) *ᵥ a0 +
          (c j p - c j q) *ᵥ aj + (Ω j p - Ω j q) *ᵥ (c j p *ᵥ a0) +
          Ω j q *ᵥ ((c j p - c j q) *ᵥ a0) := by
      simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_add]
      abel
    rw [hdec]
    have f1 := hb.c_lip j p q aj
    have f2 := hb.c_lip j p q (Ω j p *ᵥ a0)
    have f2' := hb.Ω_bounds.1 j p a0
    have f3 := hb.c_bound j q ((Ω j p - Ω j q) *ᵥ a0)
    have f3' := hb.Ω_bounds.2 j p q a0
    have f4 := hb.c'_lip j p q a0
    have f5 := hb.Ω_bounds.2 j p q (c j p *ᵥ a0)
    have f5' := hb.c_bound j p a0
    have f6 := hb.Ω_bounds.1 j q ((c j p - c j q) *ᵥ a0)
    have f6' := hb.c_lip j p q a0
    have g2 : ‖(c j p - c j q) *ᵥ (Ω j p *ᵥ a0)‖ ≤ C1 * δ * (B0 * ‖a0‖) :=
      f2.trans (mul_le_mul_of_nonneg_left f2' (by positivity))
    have g3 : ‖c j q *ᵥ ((Ω j p - Ω j q) *ᵥ a0)‖ ≤ C0 * (B1 * δ * ‖a0‖) :=
      f3.trans (mul_le_mul_of_nonneg_left f3' hC0)
    have g5 : ‖(Ω j p - Ω j q) *ᵥ (c j p *ᵥ a0)‖ ≤ B1 * δ * (C0 * ‖a0‖) :=
      f5.trans (mul_le_mul_of_nonneg_left f5' (by positivity))
    have g6 : ‖Ω j q *ᵥ ((c j p - c j q) *ᵥ a0)‖ ≤ B0 * (C1 * δ * ‖a0‖) :=
      f6.trans (mul_le_mul_of_nonneg_left f6' hB0)
    refine (norm_add7_le _ _ _ _ _ _ _).trans ?_
    have ha0 := norm_nonneg a0
    have haj := norm_nonneg aj
    nlinarith [mul_nonneg (mul_nonneg hC2 hδ) ha0]
  calc 1 / 2 * ‖∑ j, ((c j p *ᵥ (a (some j) + Ω j p *ᵥ a none) +
        (c' j p *ᵥ a none + c j p *ᵥ a (some j) + Ω j p *ᵥ (c j p *ᵥ a none))) -
      (c j q *ᵥ (a (some j) + Ω j q *ᵥ a none) +
        (c' j q *ᵥ a none + c j q *ᵥ a (some j) + Ω j q *ᵥ (c j q *ᵥ a none))))‖
      ≤ 1 / 2 * ∑ j, 2 * (δ * (C1 * ‖a (some j)‖ + (C1 * B0 + C0 * B1 + C2) * ‖a none‖)) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hj j)
    _ = _ := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-! ### The three local error terms (abstract matrices) -/

section pieces

/-- The error of the covariant centred difference on `M φ`:
`(2ih)⁻¹ (U₊ M φ₊ - U₋ M φ₋) - (-i)(M ∂φ + Ω₀ M φ₀)`. -/
def errCD (h : ℝ) (Up Um M Ω0 : Matrix (Fin N) (Fin N) ℂ) (φp φm φ0 dφ : Fin N → ℂ) :
    Fin N → ℂ :=
  (2 * Complex.I * (h : ℂ))⁻¹ • (Up *ᵥ (M *ᵥ φp) - Um *ᵥ (M *ᵥ φm)) -
    (-Complex.I) • (M *ᵥ dφ + Ω0 *ᵥ (M *ᵥ φ0))

/-- The coefficient-variation error `(2ih)⁻¹ (U₊ (c₊ - c₀) φ₊ - U₋ (c₋ - c₀) φ₋) - (-i) c'₀ φ₀`. -/
def errV (h : ℝ) (Up Um cp cm c0 c'0 : Matrix (Fin N) (Fin N) ℂ) (φp φm φ0 : Fin N → ℂ) :
    Fin N → ℂ :=
  (2 * Complex.I * (h : ℂ))⁻¹ • (Up *ᵥ ((cp - c0) *ᵥ φp) - Um *ᵥ ((cm - c0) *ᵥ φm)) -
    (-Complex.I) • (c'0 *ᵥ φ0)

/-- The Wilson term on one direction `(2h)⁻¹ (2 φ₀ - U₊ φ₊ - U₋ φ₋)`. -/
def errW (h : ℝ) (Up Um : Matrix (Fin N) (Fin N) ℂ) (φp φm φ0 : Fin N → ℂ) : Fin N → ℂ :=
  (2 * (h : ℂ))⁻¹ • ((2 : ℂ) • φ0 - Up *ᵥ φp - Um *ᵥ φm)

theorem norm_A_eq {h : ℝ} (hh : 0 < h) : ‖(2 * Complex.I * (h : ℂ))⁻¹‖ = (2 * h)⁻¹ :=
  norm_inv_two_I_mul h hh

theorem A_mul_h {h : ℝ} (hh : 0 < h) :
    (2 * Complex.I * (h : ℂ))⁻¹ * (h : ℂ) = (2 * Complex.I)⁻¹ := by
  have : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  field_simp

theorem negI_eq {h : ℝ} (hh : 0 < h) :
    -Complex.I = (2 * Complex.I * (h : ℂ))⁻¹ * (2 * (h : ℂ)) := by
  have : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  field_simp
  rw [Complex.I_sq]
  ring

theorem norm_half_I : ‖(2 * Complex.I)⁻¹‖ = 1 / 2 := norm_inv_two_I

theorem norm_errCD_le {h : ℝ} (hh : 0 < h) (Up Um M Ω0 Ωm : Matrix (Fin N) (Fin N) ℂ)
    (φp φm φ0 dφ : Fin N → ℂ) {CU CM B0 B1 T1 T2 : ℝ} (hCM : 0 ≤ CM) (hB0 : 0 ≤ B0)
    (hCU : 0 ≤ CU) (hB1 : 0 ≤ B1)
    (hUp : ∀ v, ‖(Up - 1 - (h : ℂ) • Ω0) *ᵥ v‖ ≤ CU * h ^ 2 * ‖v‖)
    (hUm : ∀ v, ‖(Um - 1 + (h : ℂ) • Ωm) *ᵥ v‖ ≤ CU * h ^ 2 * ‖v‖)
    (hM : ∀ v, ‖M *ᵥ v‖ ≤ CM * ‖v‖) (hΩ0 : ∀ v, ‖Ω0 *ᵥ v‖ ≤ B0 * ‖v‖)
    (hΩd : ∀ v, ‖(Ωm - Ω0) *ᵥ v‖ ≤ B1 * h * ‖v‖)
    (hT2 : ‖φp - φm - (2 * h) • dφ‖ ≤ T2) (hT1p : ‖φp - φ0‖ ≤ T1) (hT1m : ‖φm - φ0‖ ≤ T1) :
    ‖errCD h Up Um M Ω0 φp φm φ0 dφ‖ ≤
      CM * T2 / (2 * h) + B0 * CM * T1 + h * CM * (B1 + CU) / 2 * (‖φp‖ + ‖φm‖) := by
  set A : ℂ := (2 * Complex.I * (h : ℂ))⁻¹ with hA
  have hdec : errCD h Up Um M Ω0 φp φm φ0 dφ =
      A • (M *ᵥ (φp - φm - (2 * h) • dφ)) +
      (A * (h : ℂ)) • (Ω0 *ᵥ (M *ᵥ (φp - φ0)) + Ω0 *ᵥ (M *ᵥ (φm - φ0)) +
        (Ωm - Ω0) *ᵥ (M *ᵥ φm)) +
      A • ((Up - 1 - (h : ℂ) • Ω0) *ᵥ (M *ᵥ φp) - (Um - 1 + (h : ℂ) • Ωm) *ᵥ (M *ᵥ φm)) := by
    unfold errCD
    rw [negI_eq hh, ← hA, RCLike.real_smul_eq_coe_smul (K := ℂ) (2 * h) dφ]
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul]
    push_cast
    module
  rw [hdec]
  have n1 : ‖A • (M *ᵥ (φp - φm - (2 * h) • dφ))‖ ≤ (2 * h)⁻¹ * (CM * T2) := by
    rw [norm_smul, norm_A_eq hh]
    exact mul_le_mul_of_nonneg_left ((hM _).trans (mul_le_mul_of_nonneg_left hT2 hCM))
      (by positivity)
  have n2 : ‖(A * (h : ℂ)) • (Ω0 *ᵥ (M *ᵥ (φp - φ0)) + Ω0 *ᵥ (M *ᵥ (φm - φ0)) +
      (Ωm - Ω0) *ᵥ (M *ᵥ φm))‖ ≤ 1 / 2 * (B0 * (CM * T1) + B0 * (CM * T1) +
        B1 * h * (CM * ‖φm‖)) := by
    rw [norm_smul, A_mul_h hh, norm_half_I]
    refine mul_le_mul_of_nonneg_left ((norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_))
      (by norm_num)
    · exact (hΩ0 _).trans (mul_le_mul_of_nonneg_left ((hM _).trans
        (mul_le_mul_of_nonneg_left hT1p hCM)) hB0)
    · exact (hΩ0 _).trans (mul_le_mul_of_nonneg_left ((hM _).trans
        (mul_le_mul_of_nonneg_left hT1m hCM)) hB0)
    · exact (hΩd _).trans (mul_le_mul_of_nonneg_left (hM _) (by positivity))
  have n3 : ‖A • ((Up - 1 - (h : ℂ) • Ω0) *ᵥ (M *ᵥ φp) -
      (Um - 1 + (h : ℂ) • Ωm) *ᵥ (M *ᵥ φm))‖ ≤
      (2 * h)⁻¹ * (CU * h ^ 2 * (CM * ‖φp‖) + CU * h ^ 2 * (CM * ‖φm‖)) := by
    rw [norm_smul, norm_A_eq hh]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ ?_))
      (by positivity)
    · exact (hUp _).trans (mul_le_mul_of_nonneg_left (hM _) (by positivity))
    · exact (hUm _).trans (mul_le_mul_of_nonneg_left (hM _) (by positivity))
  have hφp := norm_nonneg φp
  have hφm := norm_nonneg φm
  calc _ ≤ _ := norm_add₃_le
    _ ≤ (2 * h)⁻¹ * (CM * T2) + 1 / 2 * (B0 * (CM * T1) + B0 * (CM * T1) +
          B1 * h * (CM * ‖φm‖)) +
        (2 * h)⁻¹ * (CU * h ^ 2 * (CM * ‖φp‖) + CU * h ^ 2 * (CM * ‖φm‖)) :=
        add_le_add (add_le_add n1 n2) n3
    _ ≤ _ := by
        have e1 : (2 * h)⁻¹ * (CM * T2) = CM * T2 / (2 * h) := by field_simp
        have e2 : (2 * h)⁻¹ * (CU * h ^ 2 * (CM * ‖φp‖) + CU * h ^ 2 * (CM * ‖φm‖)) =
            h * CM * CU / 2 * (‖φp‖ + ‖φm‖) := by field_simp
        rw [e1, e2]
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hh.le hCM) hB1) hφp]

theorem norm_errV_le {h : ℝ} (hh : 0 < h) (Up Um cp cm c0 c'0 : Matrix (Fin N) (Fin N) ℂ)
    (φp φm φ0 : Fin N → ℂ) {C1 C2 CV CW T1 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hCV : 0 ≤ CV)
    (hCW : 0 ≤ CW)
    (hQp : ∀ v, ‖(cp - c0 - (h : ℂ) • c'0) *ᵥ v‖ ≤ C2 * h ^ 2 * ‖v‖)
    (hQm : ∀ v, ‖(cm - c0 + (h : ℂ) • c'0) *ᵥ v‖ ≤ C2 * h ^ 2 * ‖v‖)
    (hVp : ∀ v, ‖(Up - 1) *ᵥ v‖ ≤ CV * h * ‖v‖) (hVm : ∀ v, ‖(Um - 1) *ᵥ v‖ ≤ CV * h * ‖v‖)
    (hWp : ∀ v, ‖Up *ᵥ v‖ ≤ CW * ‖v‖) (hWm : ∀ v, ‖Um *ᵥ v‖ ≤ CW * ‖v‖)
    (hc' : ∀ v, ‖c'0 *ᵥ v‖ ≤ C1 * ‖v‖)
    (hT1p : ‖φp - φ0‖ ≤ T1) (hT1m : ‖φm - φ0‖ ≤ T1) :
    ‖errV h Up Um cp cm c0 c'0 φp φm φ0‖ ≤
      C1 * T1 + h * (CV * C1 + CW * C2) / 2 * (‖φp‖ + ‖φm‖) := by
  set A : ℂ := (2 * Complex.I * (h : ℂ))⁻¹ with hA
  have hdec : errV h Up Um cp cm c0 c'0 φp φm φ0 =
      (A * (h : ℂ)) • ((Up - 1) *ᵥ (c'0 *ᵥ φp) + (Um - 1) *ᵥ (c'0 *ᵥ φm) +
        c'0 *ᵥ (φp - φ0) + c'0 *ᵥ (φm - φ0)) +
      A • (Up *ᵥ ((cp - c0 - (h : ℂ) • c'0) *ᵥ φp) - Um *ᵥ ((cm - c0 + (h : ℂ) • c'0) *ᵥ φm)) := by
    unfold errV
    rw [negI_eq hh, ← hA]
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul]
    module
  rw [hdec]
  have hφp := norm_nonneg φp
  have hφm := norm_nonneg φm
  have n1 : ‖(A * (h : ℂ)) • ((Up - 1) *ᵥ (c'0 *ᵥ φp) + (Um - 1) *ᵥ (c'0 *ᵥ φm) +
      c'0 *ᵥ (φp - φ0) + c'0 *ᵥ (φm - φ0))‖ ≤
      1 / 2 * (CV * h * (C1 * ‖φp‖) + CV * h * (C1 * ‖φm‖) + C1 * T1 + C1 * T1) := by
    rw [norm_smul, A_mul_h hh, norm_half_I]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have a1 := (hVp (c'0 *ᵥ φp)).trans (mul_le_mul_of_nonneg_left (hc' φp) (by positivity))
    have a2 := (hVm (c'0 *ᵥ φm)).trans (mul_le_mul_of_nonneg_left (hc' φm) (by positivity))
    have a3 := (hc' (φp - φ0)).trans (mul_le_mul_of_nonneg_left hT1p hC1)
    have a4 := (hc' (φm - φ0)).trans (mul_le_mul_of_nonneg_left hT1m hC1)
    have t1 := norm_add_le ((Up - 1) *ᵥ (c'0 *ᵥ φp) + (Um - 1) *ᵥ (c'0 *ᵥ φm) +
      c'0 *ᵥ (φp - φ0)) (c'0 *ᵥ (φm - φ0))
    have t2 := norm_add₃_le (a := (Up - 1) *ᵥ (c'0 *ᵥ φp)) (b := (Um - 1) *ᵥ (c'0 *ᵥ φm))
      (c := c'0 *ᵥ (φp - φ0))
    linarith
  have n2 : ‖A • (Up *ᵥ ((cp - c0 - (h : ℂ) • c'0) *ᵥ φp) -
      Um *ᵥ ((cm - c0 + (h : ℂ) • c'0) *ᵥ φm))‖ ≤
      (2 * h)⁻¹ * (CW * (C2 * h ^ 2 * ‖φp‖) + CW * (C2 * h ^ 2 * ‖φm‖)) := by
    rw [norm_smul, norm_A_eq hh]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ ?_))
      (by positivity)
    · exact (hWp _).trans (mul_le_mul_of_nonneg_left (hQp _) hCW)
    · exact (hWm _).trans (mul_le_mul_of_nonneg_left (hQm _) hCW)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 1 / 2 * (CV * h * (C1 * ‖φp‖) + CV * h * (C1 * ‖φm‖) + C1 * T1 + C1 * T1) +
        (2 * h)⁻¹ * (CW * (C2 * h ^ 2 * ‖φp‖) + CW * (C2 * h ^ 2 * ‖φm‖)) := add_le_add n1 n2
    _ = _ := by field_simp; ring

theorem norm_errW_le {h : ℝ} (hh : 0 < h) (Up Um Ω0 Ωm : Matrix (Fin N) (Fin N) ℂ)
    (φp φm φ0 : Fin N → ℂ) {CU B0 B1 T1 T2 : ℝ} (hB0 : 0 ≤ B0) (hCU : 0 ≤ CU) (hB1 : 0 ≤ B1)
    (hUp : ∀ v, ‖(Up - 1 - (h : ℂ) • Ω0) *ᵥ v‖ ≤ CU * h ^ 2 * ‖v‖)
    (hUm : ∀ v, ‖(Um - 1 + (h : ℂ) • Ωm) *ᵥ v‖ ≤ CU * h ^ 2 * ‖v‖)
    (hΩ0 : ∀ v, ‖Ω0 *ᵥ v‖ ≤ B0 * ‖v‖) (hΩd : ∀ v, ‖(Ωm - Ω0) *ᵥ v‖ ≤ B1 * h * ‖v‖)
    (hT2 : ‖(2 : ℝ) • φ0 - φp - φm‖ ≤ T2) (hT1p : ‖φp - φ0‖ ≤ T1) (hT1m : ‖φm - φ0‖ ≤ T1) :
    ‖errW h Up Um φp φm φ0‖ ≤
      T2 / (2 * h) + B0 * T1 + h * (B1 + CU) / 2 * (‖φp‖ + ‖φm‖) := by
  have hdec : errW h Up Um φp φm φ0 =
      (2 * (h : ℂ))⁻¹ • ((2 : ℝ) • φ0 - φp - φm) -
      (2 : ℂ)⁻¹ • (Ω0 *ᵥ (φp - φ0) - Ω0 *ᵥ (φm - φ0) - (Ωm - Ω0) *ᵥ φm) -
      (2 * (h : ℂ))⁻¹ • ((Up - 1 - (h : ℂ) • Ω0) *ᵥ φp + (Um - 1 + (h : ℂ) • Ωm) *ᵥ φm) := by
    unfold errW
    have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    have e : (2 : ℂ)⁻¹ = (2 * (h : ℂ))⁻¹ * (h : ℂ) := by field_simp
    rw [e, RCLike.real_smul_eq_coe_smul (K := ℂ) (2 : ℝ) φ0]
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul]
    push_cast
    module
  rw [hdec]
  have hφp := norm_nonneg φp
  have hφm := norm_nonneg φm
  have h2h : ‖(2 * (h : ℂ))⁻¹‖ = (2 * h)⁻¹ := norm_inv_two_mul h hh
  have n1 : ‖(2 * (h : ℂ))⁻¹ • ((2 : ℝ) • φ0 - φp - φm)‖ ≤ (2 * h)⁻¹ * T2 := by
    rw [norm_smul, h2h]
    exact mul_le_mul_of_nonneg_left hT2 (by positivity)
  have n2 : ‖(2 : ℂ)⁻¹ • (Ω0 *ᵥ (φp - φ0) - Ω0 *ᵥ (φm - φ0) - (Ωm - Ω0) *ᵥ φm)‖ ≤
      1 / 2 * (B0 * T1 + B0 * T1 + B1 * h * ‖φm‖) := by
    rw [norm_smul, norm_inv_two]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have a1 := (hΩ0 (φp - φ0)).trans (mul_le_mul_of_nonneg_left hT1p hB0)
    have a2 := (hΩ0 (φm - φ0)).trans (mul_le_mul_of_nonneg_left hT1m hB0)
    have a3 := hΩd φm
    have t1 := norm_sub_le (Ω0 *ᵥ (φp - φ0) - Ω0 *ᵥ (φm - φ0)) ((Ωm - Ω0) *ᵥ φm)
    have t2 := norm_sub_le (Ω0 *ᵥ (φp - φ0)) (Ω0 *ᵥ (φm - φ0))
    linarith
  have n3 : ‖(2 * (h : ℂ))⁻¹ • ((Up - 1 - (h : ℂ) • Ω0) *ᵥ φp +
      (Um - 1 + (h : ℂ) • Ωm) *ᵥ φm)‖ ≤ (2 * h)⁻¹ * (CU * h ^ 2 * ‖φp‖ + CU * h ^ 2 * ‖φm‖) := by
    rw [norm_smul, h2h]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hUp _) (hUm _)))
      (by positivity)
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (2 * h)⁻¹ * T2 + 1 / 2 * (B0 * T1 + B0 * T1 + B1 * h * ‖φm‖) +
        (2 * h)⁻¹ * (CU * h ^ 2 * ‖φp‖ + CU * h ^ 2 * ‖φm‖) := add_le_add (add_le_add n1 n2) n3
    _ ≤ _ := by
        have e1 : (2 * h)⁻¹ * T2 = T2 / (2 * h) := by field_simp
        have e2 : (2 * h)⁻¹ * (CU * h ^ 2 * ‖φp‖ + CU * h ^ 2 * ‖φm‖) =
            h * CU / 2 * (‖φp‖ + ‖φm‖) := by field_simp
        rw [e1, e2]
        nlinarith [mul_nonneg (mul_nonneg hh.le hB1) hφp]

end pieces

/-! ### The pointwise decomposition on translated samples -/

/-- **Exact decomposition.**  On point samples, the covariant Wilson operator minus the frozen
density-symmetric operator at the lattice point is a sum over directions of the three local
errors (centred differences of `φ` and of `c^j(hx) φ`, coefficient variation, Wilson term). -/
theorem covariantWilson_sample_sub_frozenSym (h ϖ : ℝ) (c c' Ω : Coefficients d N)
    (U : Links d N) (Γ : Matrix (Fin N) (Fin N) ℂ) (φ : (Fin d → ℝ) → (Fin N → ℂ))
    (x : Fin d → ℤ) :
    covariantWilson h ϖ c U Γ (sample h φ) x -
        frozenSym c c' Ω (latticePoint h x) (jet φ (latticePoint h x)) =
      ∑ j, ((2 : ℂ)⁻¹ • (c j (latticePoint h x) *ᵥ
          errCD h (U j x) (U j (x - Pi.single j 1))ᴴ 1 (Ω j (latticePoint h x))
            (sample h φ (x + Pi.single j 1)) (sample h φ (x - Pi.single j 1)) (sample h φ x)
            (fderiv ℝ φ (latticePoint h x) (dir j)) +
        errCD h (U j x) (U j (x - Pi.single j 1))ᴴ (c j (latticePoint h x))
            (Ω j (latticePoint h x))
            (sample h φ (x + Pi.single j 1)) (sample h φ (x - Pi.single j 1)) (sample h φ x)
            (fderiv ℝ φ (latticePoint h x) (dir j)) +
        errV h (U j x) (U j (x - Pi.single j 1))ᴴ (c j (latticePoint h (x + Pi.single j 1)))
            (c j (latticePoint h (x - Pi.single j 1))) (c j (latticePoint h x))
            (c' j (latticePoint h x))
            (sample h φ (x + Pi.single j 1)) (sample h φ (x - Pi.single j 1)) (sample h φ x)) +
        (ϖ : ℂ) • (Γ *ᵥ errW h (U j x) (U j (x - Pi.single j 1))ᴴ
            (sample h φ (x + Pi.single j 1)) (sample h φ (x - Pi.single j 1))
            (sample h φ x))) := by
  rw [covariantWilson_eq_stencilForm]
  unfold stencilForm frozenSym
  simp only [stencilValues, jet]
  simp only [Finset.smul_sum, Matrix.mulVec_smul, Matrix.mulVec_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold errCD errV errW
  simp only [Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul, smul_sub, smul_add]
  have hs : sample h φ x = φ (latticePoint h x) := rfl
  rw [hs]
  module

/-- **Second-order Taylor bound for the coefficients** along `e_j`, from the Lipschitz bound on
`c'^j`: `‖(c^j(p + t e_j) - c^j(p) - t c'^j(p)) v‖ ≤ C₂ t² ‖v‖`. -/
theorem norm_coeff_taylor_le {c c' Ω : Coefficients d N} {C0 C1 C2 B0 B1 : ℝ}
    (hb : CoeffBounds c c' Ω C0 C1 C2 B0 B1) (hC2 : 0 ≤ C2) (j : Fin d) (p : Fin d → ℝ)
    (t : ℝ) (v : Fin N → ℂ) :
    ‖(c j (p + t • dir j) - c j p - (t : ℂ) • c' j p) *ᵥ v‖ ≤ C2 * t ^ 2 * ‖v‖ := by
  set g : ℝ → (Fin N → ℂ) := fun s => c j (p + s • dir j) *ᵥ v - (s : ℂ) • (c' j p *ᵥ v)
  have hg : ∀ s, HasDerivAt g (c' j (p + s • dir j) *ᵥ v - c' j p *ᵥ v) s := by
    intro s
    have h0 : HasDerivAt (fun t : ℝ => c j (p + s • dir j + t • dir j) *ᵥ v)
        (c' j (p + s • dir j) *ᵥ v) (s - s) := by
      rw [sub_self]
      exact hb.c_deriv j _ v
    have h1 := h0.comp_sub_const s s
    have h1' : HasDerivAt (fun s' : ℝ => c j (p + s' • dir j) *ᵥ v)
        (c' j (p + s • dir j) *ᵥ v) s := by
      have hfeq : (fun s' : ℝ => c j (p + s' • dir j) *ᵥ v) =
          (fun x : ℝ => c j (p + s • dir j + (x - s) • dir j) *ᵥ v) := by
        funext s'
        rw [add_assoc, ← add_smul, add_sub_cancel]
      rw [hfeq]
      exact h1
    have h2 : HasDerivAt (fun s' : ℝ => (s' : ℂ) • (c' j p *ᵥ v)) (c' j p *ᵥ v) s := by
      have := ((hasDerivAt_id s).ofReal_comp).smul_const (c' j p *ᵥ v)
      simpa using this
    exact h1'.sub h2
  have hbound : ∀ s ∈ Set.uIcc 0 t, ‖c' j (p + s • dir j) *ᵥ v - c' j p *ᵥ v‖ ≤
      C2 * |t| * ‖v‖ := by
    intro s hs
    rw [← Matrix.sub_mulVec]
    refine (hb.c'_lip j _ _ v).trans ?_
    rw [add_sub_cancel_left, norm_smul, norm_dir, mul_one, Real.norm_eq_abs]
    have : |s| ≤ |t| := by
      rcases le_total 0 t with h0 | h0
      · rw [Set.uIcc_of_le h0] at hs
        rw [abs_of_nonneg hs.1, abs_of_nonneg h0]
        exact hs.2
      · rw [Set.uIcc_of_ge h0] at hs
        rw [abs_of_nonpos hs.2, abs_of_nonpos h0]
        linarith [hs.1]
    gcongr
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hg s).hasDerivWithinAt) hbound (convex_uIcc 0 t)
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hg0 : g 0 = c j p *ᵥ v := by simp [g]
  have hgt : g t - g 0 = (c j (p + t • dir j) - c j p - (t : ℂ) • c' j p) *ᵥ v := by
    rw [hg0]
    simp only [g, Matrix.sub_mulVec, Matrix.smul_mulVec]
    abel
  rw [← hgt]
  calc ‖g t - g 0‖ ≤ C2 * |t| * ‖v‖ * ‖t - 0‖ := hmv
    _ = C2 * t ^ 2 * ‖v‖ := by
        rw [sub_zero, Real.norm_eq_abs, mul_assoc, mul_comm ‖v‖, ← mul_assoc, mul_assoc C2,
          ← sq, sq_abs]

/-! ### Real line integrals and the pointwise bound -/

/-- `∫_{-h}^{h} ‖D^k φ(p + s e_j)‖ ds` (`k = 1, 2`) as real numbers. -/
def lineInt1 (φ : (Fin d → ℝ) → (Fin N → ℂ)) (p : Fin d → ℝ) (j : Fin d) (h : ℝ) : ℝ :=
  ∫ s in Icc (-h) h, ‖fderiv ℝ φ (p + s • dir j)‖

def lineInt2 (φ : (Fin d → ℝ) → (Fin N → ℂ)) (p : Fin d → ℝ) (j : Fin d) (h : ℝ) : ℝ :=
  ∫ s in Icc (-h) h, ‖iteratedFDeriv ℝ 2 φ (p + s • dir j)‖

theorem ofReal_setIntegral_Icc {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ s, 0 ≤ g s)
    (a b : ℝ) : ENNReal.ofReal (∫ s in Icc a b, g s) = ∫⁻ s in Icc a b, ENNReal.ofReal (g s) :=
  ofReal_integral_eq_lintegral_ofReal (hg.integrableOn_Icc) (Eventually.of_forall hg0)

theorem lineInt1_nonneg (φ : (Fin d → ℝ) → (Fin N → ℂ)) (p : Fin d → ℝ) (j : Fin d) (h : ℝ) :
    0 ≤ lineInt1 φ p j h := setIntegral_nonneg measurableSet_Icc fun _ _ => norm_nonneg _

theorem lineInt2_nonneg (φ : (Fin d → ℝ) → (Fin N → ℂ)) (p : Fin d → ℝ) (j : Fin d) (h : ℝ) :
    0 ≤ lineInt2 φ p j h := setIntegral_nonneg measurableSet_Icc fun _ _ => norm_nonneg _

theorem ofReal_lineInt1 {φ : (Fin d → ℝ) → (Fin N → ℂ)} (hφ : ContDiff ℝ 1 φ) (p : Fin d → ℝ)
    (j : Fin d) (h : ℝ) :
    ENNReal.ofReal (lineInt1 φ p j h) = ∫⁻ s in Icc (-h) h, ‖fderiv ℝ φ (p + s • dir j)‖ₑ := by
  unfold lineInt1
  rw [ofReal_setIntegral_Icc (g := fun s => ‖fderiv ℝ φ (p + s • dir j)‖)
    ((hφ.continuous_fderiv (by norm_num)).comp (continuous_const.add
    (continuous_id.smul continuous_const))).norm (fun _ => norm_nonneg _)]
  simp only [ofReal_norm]

theorem ofReal_lineInt2 {φ : (Fin d → ℝ) → (Fin N → ℂ)} (hφ : ContDiff ℝ 2 φ) (p : Fin d → ℝ)
    (j : Fin d) (h : ℝ) :
    ENNReal.ofReal (lineInt2 φ p j h) =
      ∫⁻ s in Icc (-h) h, ‖iteratedFDeriv ℝ 2 φ (p + s • dir j)‖ₑ := by
  unfold lineInt2
  rw [ofReal_setIntegral_Icc (g := fun s => ‖iteratedFDeriv ℝ 2 φ (p + s • dir j)‖)
    ((hφ.continuous_iteratedFDeriv (by norm_num)).comp
    (continuous_const.add (continuous_id.smul continuous_const))).norm (fun _ => norm_nonneg _)]
  simp only [ofReal_norm]

theorem norm_le_of_enorm_le_ofReal {v : Fin N → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ‖v‖ₑ ≤ ENNReal.ofReal r) : ‖v‖ ≤ r := by
  rw [← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff hr).mp h

/-- Real first-order line bound. -/
theorem norm_line_sub_le {φ : (Fin d → ℝ) → (Fin N → ℂ)} (hφ : ContDiff ℝ 2 φ) (p : Fin d → ℝ)
    (j : Fin d) {h t : ℝ} (ht : |t| ≤ h) :
    ‖φ (p + t • dir j) - φ p‖ ≤ lineInt1 φ p j h := by
  refine norm_le_of_enorm_le_ofReal (lineInt1_nonneg _ _ _ _) ?_
  rw [ofReal_lineInt1 (hφ.of_le (by norm_num))]
  exact LatticeCellL2.enorm_sub_le_lintegral_fderiv (hφ.of_le (by norm_num)) p (dir j)
    (norm_dir j).le ht

/-- Real first-order Taylor bound. -/
theorem norm_line_taylor_le {φ : (Fin d → ℝ) → (Fin N → ℂ)} (hφ : ContDiff ℝ 2 φ)
    (p : Fin d → ℝ) (j : Fin d) {h t : ℝ} (ht : |t| ≤ h) :
    ‖φ (p + t • dir j) - φ p - t • fderiv ℝ φ p (dir j)‖ ≤ |t| * lineInt2 φ p j h := by
  refine norm_le_of_enorm_le_ofReal (by positivity [lineInt2_nonneg φ p j h]) ?_
  rw [ENNReal.ofReal_mul (abs_nonneg t), ofReal_lineInt2 hφ]
  exact LatticeCellL2.enorm_taylor_one_le hφ p (dir j) (norm_dir j).le ht

/-- The aggregated pointwise constants. -/
def K2 (C0 G0 ϖ : ℝ) : ℝ := C0 + |ϖ| * G0

def K1 (C0 C1 B0 G0 ϖ : ℝ) : ℝ := C0 * B0 + C1 + |ϖ| * G0 * B0

def K0 (C0 C1 C2 B0 B1 CU G0 ϖ : ℝ) : ℝ :=
  C0 * (B1 + CU) + (B0 + CU) * C1 + (1 + B0 + CU) * C2 + |ϖ| * G0 * (B1 + CU)

set_option maxHeartbeats 1000000 in
/-- **Pointwise consistency with integral remainders.**  For `0 < h ≤ 1`, a `C²` map `φ`, and the
lattice point `p = h x`: `‖D̃ (S φ)(x) - frozenSym(p)(jet φ p)‖ ≤ Σ_j (K₂ I₂ⱼ + K₁ I₁ⱼ +
K₀ h (‖φ(p + h e_j)‖ + ‖φ(p - h e_j)‖))` with `I_{kj} = ∫_{-h}^{h} ‖D^k φ(p + s e_j)‖ ds`. -/
theorem norm_covariantWilson_sample_sub_frozenSym_le {h ϖ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {c c' Ω : Coefficients d N} {C0 C1 C2 B0 B1 CU G0 : ℝ}
    (hb : CoeffBounds c c' Ω C0 C1 C2 B0 B1) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hCU : 0 ≤ CU) (hG0 : 0 ≤ G0) {U : Links d N}
    (hU : LinkExpansion h U Ω CU) {Γ : Matrix (Fin N) (Fin N) ℂ}
    (hΓ : ∀ v, ‖Γ *ᵥ v‖ ≤ G0 * ‖v‖) {φ : (Fin d → ℝ) → (Fin N → ℂ)} (hφ : ContDiff ℝ 2 φ)
    (x : Fin d → ℤ) :
    ‖covariantWilson h ϖ c U Γ (sample h φ) x -
        frozenSym c c' Ω (latticePoint h x) (jet φ (latticePoint h x))‖ ≤
      ∑ j, (K2 C0 G0 ϖ * lineInt2 φ (latticePoint h x) j h +
        K1 C0 C1 B0 G0 ϖ * lineInt1 φ (latticePoint h x) j h +
        K0 C0 C1 C2 B0 B1 CU G0 ϖ * h *
          (‖φ (latticePoint h x + h • dir j)‖ + ‖φ (latticePoint h x + (-h) • dir j)‖)) := by
  rw [covariantWilson_sample_sub_frozenSym]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  set p := latticePoint h x
  set e := dir j
  set φp := φ (p + h • e)
  set φm := φ (p + (-h) • e)
  set φ0 := φ p
  set dφ := fderiv ℝ φ p e
  set I1 := lineInt1 φ p j h
  set I2 := lineInt2 φ p j h
  have hsp : sample h φ (x + Pi.single j 1) = φp := by
    simp only [sample, latticePoint_add_single, φp, p, e]
  have hsm : sample h φ (x - Pi.single j 1) = φm := by
    simp only [sample, latticePoint_sub_single, φm, p, e]
  have hs0 : sample h φ x = φ0 := rfl
  rw [hsp, hsm, hs0]
  have hcp : c j (latticePoint h (x + Pi.single j 1)) = c j (p + h • e) := by
    rw [latticePoint_add_single]
  have hcm : c j (latticePoint h (x - Pi.single j 1)) = c j (p + (-h) • e) := by
    rw [latticePoint_sub_single]
  rw [hcp, hcm]
  have hI1 := lineInt1_nonneg φ p j h
  have hI2 := lineInt2_nonneg φ p j h
  have hφp := norm_nonneg φp
  have hφm := norm_nonneg φm
  have hah : |h| ≤ h := (abs_of_pos hh).le
  have hamh : |-h| ≤ h := by rw [abs_neg]; exact hah
  -- Taylor inputs
  have T1p : ‖φp - φ0‖ ≤ I1 := norm_line_sub_le hφ p j hah
  have T1m : ‖φm - φ0‖ ≤ I1 := norm_line_sub_le hφ p j hamh
  have Ap := norm_line_taylor_le hφ p j hah
  have Am := norm_line_taylor_le hφ p j hamh
  rw [abs_of_pos hh] at Ap
  rw [abs_neg, abs_of_pos hh] at Am
  have T2a : ‖φp - φm - (2 * h) • dφ‖ ≤ 2 * h * I2 := by
    have : φp - φm - (2 * h) • dφ = (φp - φ0 - h • dφ) - (φm - φ0 - (-h) • dφ) := by
      rw [two_mul, add_smul, neg_smul]
      abel
    rw [this]
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ h * I2 + h * I2 := add_le_add Ap Am
      _ = 2 * h * I2 := by ring
  have T2b : ‖(2 : ℝ) • φ0 - φp - φm‖ ≤ 2 * h * I2 := by
    have : (2 : ℝ) • φ0 - φp - φm = -((φp - φ0 - h • dφ) + (φm - φ0 - (-h) • dφ)) := by
      rw [two_smul, neg_smul]
      abel
    rw [this, norm_neg]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ h * I2 + h * I2 := add_le_add Ap Am
      _ = 2 * h * I2 := by ring
  -- link and coefficient hypotheses
  have hUp : ∀ v, ‖(U j x - 1 - (h : ℂ) • Ω j p) *ᵥ v‖ ≤ CU * h ^ 2 * ‖v‖ :=
    fun v => (hU j x v).1
  have hUm : ∀ v, ‖((U j (x - Pi.single j 1))ᴴ - 1 + (h : ℂ) • Ω j (p + (-h) • e)) *ᵥ v‖ ≤
      CU * h ^ 2 * ‖v‖ := by
    intro v
    have := (hU j (x - Pi.single j 1) v).2
    rwa [latticePoint_sub_single] at this
  have hΩ0 : ∀ v, ‖Ω j p *ᵥ v‖ ≤ B0 * ‖v‖ := fun v => hb.Ω_bounds.1 j p v
  have hΩd : ∀ v, ‖(Ω j (p + (-h) • e) - Ω j p) *ᵥ v‖ ≤ B1 * h * ‖v‖ := by
    intro v
    refine (hb.Ω_bounds.2 j _ _ v).trans (le_of_eq ?_)
    rw [add_sub_cancel_left, norm_neg_smul_dir, abs_of_pos hh]
  have hM1 : ∀ v : Fin N → ℂ, ‖(1 : Matrix (Fin N) (Fin N) ℂ) *ᵥ v‖ ≤ 1 * ‖v‖ := by
    intro v; rw [Matrix.one_mulVec, one_mul]
  have hMc : ∀ v, ‖c j p *ᵥ v‖ ≤ C0 * ‖v‖ := fun v => hb.c_bound j p v
  have hQp : ∀ v, ‖(c j (p + h • e) - c j p - (h : ℂ) • c' j p) *ᵥ v‖ ≤ C2 * h ^ 2 * ‖v‖ :=
    fun v => norm_coeff_taylor_le hb hC2 j p h v
  have hQm : ∀ v, ‖(c j (p + (-h) • e) - c j p + (h : ℂ) • c' j p) *ᵥ v‖ ≤
      C2 * h ^ 2 * ‖v‖ := by
    intro v
    have := norm_coeff_taylor_le hb hC2 j p (-h) v
    have heq : c j (p + (-h) • e) - c j p + (h : ℂ) • c' j p =
        c j (p + (-h) • e) - c j p - ((-h : ℝ) : ℂ) • c' j p := by
      rw [Complex.ofReal_neg, neg_smul (h : ℂ) (c' j p), sub_neg_eq_add]
    rw [heq]
    rw [neg_sq] at this
    exact this
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have hVp : ∀ v, ‖(U j x - 1) *ᵥ v‖ ≤ (B0 + CU) * h * ‖v‖ := by
    intro v
    have e1 : (U j x - 1) *ᵥ v = (U j x - 1 - (h : ℂ) • Ω j p) *ᵥ v + (h : ℂ) • (Ω j p *ᵥ v) := by
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec]; abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    have := hUp v
    have := hΩ0 v
    have hv := norm_nonneg v
    nlinarith [mul_nonneg hCU hv, mul_nonneg hB0 hv]
  have hVm : ∀ v, ‖((U j (x - Pi.single j 1))ᴴ - 1) *ᵥ v‖ ≤ (B0 + CU) * h * ‖v‖ := by
    intro v
    have e1 : ((U j (x - Pi.single j 1))ᴴ - 1) *ᵥ v =
        ((U j (x - Pi.single j 1))ᴴ - 1 + (h : ℂ) • Ω j (p + (-h) • e)) *ᵥ v -
          (h : ℂ) • (Ω j (p + (-h) • e) *ᵥ v) := by
      simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec]; abel
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    have := hUm v
    have := hb.Ω_bounds.1 j (p + (-h) • e) v
    have hv := norm_nonneg v
    nlinarith [mul_nonneg hCU hv, mul_nonneg hB0 hv]
  have hWp : ∀ v, ‖U j x *ᵥ v‖ ≤ (1 + B0 + CU) * ‖v‖ := by
    intro v
    have e1 : U j x *ᵥ v = v + (U j x - 1) *ᵥ v := by
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1]
    have := hVp v
    have hv := norm_nonneg v
    have : (B0 + CU) * h * ‖v‖ ≤ (B0 + CU) * ‖v‖ := by
      have := mul_nonneg (add_nonneg hB0 hCU) hv
      nlinarith
    linarith [norm_add_le v ((U j x - 1) *ᵥ v)]
  have hWm : ∀ v, ‖(U j (x - Pi.single j 1))ᴴ *ᵥ v‖ ≤ (1 + B0 + CU) * ‖v‖ := by
    intro v
    have e1 : (U j (x - Pi.single j 1))ᴴ *ᵥ v = v + ((U j (x - Pi.single j 1))ᴴ - 1) *ᵥ v := by
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1]
    have := hVm v
    have hv := norm_nonneg v
    have : (B0 + CU) * h * ‖v‖ ≤ (B0 + CU) * ‖v‖ := by
      have := mul_nonneg (add_nonneg hB0 hCU) hv
      nlinarith
    linarith [norm_add_le v (((U j (x - Pi.single j 1))ᴴ - 1) *ᵥ v)]
  have hc' : ∀ v, ‖c' j p *ᵥ v‖ ≤ C1 * ‖v‖ := fun v => hb.c'_bound j p v
  -- the four pieces
  have E1 := norm_errCD_le hh (U j x) (U j (x - Pi.single j 1))ᴴ 1 (Ω j p) (Ω j (p + (-h) • e))
    φp φm φ0 dφ zero_le_one hB0 hCU hB1 hUp hUm hM1 hΩ0 hΩd T2a T1p T1m
  have E2 := norm_errCD_le hh (U j x) (U j (x - Pi.single j 1))ᴴ (c j p) (Ω j p)
    (Ω j (p + (-h) • e)) φp φm φ0 dφ hC0 hB0 hCU hB1 hUp hUm hMc hΩ0 hΩd T2a T1p T1m
  have E3 := norm_errV_le hh (U j x) (U j (x - Pi.single j 1))ᴴ (c j (p + h • e))
    (c j (p + (-h) • e)) (c j p) (c' j p) φp φm φ0 hC1 hC2 (add_nonneg hB0 hCU)
    (by positivity) hQp hQm hVp hVm hWp hWm hc' T1p T1m
  have E4 := norm_errW_le hh (U j x) (U j (x - Pi.single j 1))ᴴ (Ω j p) (Ω j (p + (-h) • e))
    φp φm φ0 hB0 hCU hB1 hUp hUm hΩ0 hΩd T2b T1p T1m
  have hc0e := hMc (errCD h (U j x) (U j (x - Pi.single j 1))ᴴ 1 (Ω j p) φp φm φ0 dφ)
  have hΓe := hΓ (errW h (U j x) (U j (x - Pi.single j 1))ᴴ φp φm φ0)
  have hdiv : 2 * h * I2 / (2 * h) = I2 := by field_simp
  rw [hdiv] at E4
  have hdiv' : 1 * (2 * h * I2) / (2 * h) = I2 := by field_simp
  rw [hdiv'] at E1
  have hdiv'' : C0 * (2 * h * I2) / (2 * h) = C0 * I2 := by field_simp
  rw [hdiv''] at E2
  set S := ‖φp‖ + ‖φm‖ with hS
  have hS0 : 0 ≤ S := add_nonneg hφp hφm
  -- assemble
  have hfirst : ‖(2 : ℂ)⁻¹ • (c j p *ᵥ errCD h (U j x) (U j (x - Pi.single j 1))ᴴ 1 (Ω j p)
      φp φm φ0 dφ + errCD h (U j x) (U j (x - Pi.single j 1))ᴴ (c j p) (Ω j p) φp φm φ0 dφ +
      errV h (U j x) (U j (x - Pi.single j 1))ᴴ (c j (p + h • e)) (c j (p + (-h) • e)) (c j p)
        (c' j p) φp φm φ0)‖ ≤
      1 / 2 * (C0 * (I2 + B0 * 1 * I1 + h * 1 * (B1 + CU) / 2 * S) +
        (C0 * I2 + B0 * C0 * I1 + h * C0 * (B1 + CU) / 2 * S) +
        (C1 * I1 + h * ((B0 + CU) * C1 + (1 + B0 + CU) * C2) / 2 * S)) := by
    rw [norm_smul, norm_inv_two]
    refine mul_le_mul_of_nonneg_left ((norm_add₃_le).trans (add_le_add (add_le_add ?_ E2) E3))
      (by norm_num)
    exact hc0e.trans (mul_le_mul_of_nonneg_left E1 hC0)
  have hsecond : ‖(ϖ : ℂ) • (Γ *ᵥ errW h (U j x) (U j (x - Pi.single j 1))ᴴ φp φm φ0)‖ ≤
      |ϖ| * (G0 * (I2 + B0 * I1 + h * (B1 + CU) / 2 * S)) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hΓe.trans (mul_le_mul_of_nonneg_left E4 hG0))
      (abs_nonneg ϖ)
  refine (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans ?_)
  have hϖ := abs_nonneg ϖ
  have key : K2 C0 G0 ϖ * I2 + K1 C0 C1 B0 G0 ϖ * I1 + K0 C0 C1 C2 B0 B1 CU G0 ϖ * h * S -
      (1 / 2 * (C0 * (I2 + B0 * 1 * I1 + h * 1 * (B1 + CU) / 2 * S) +
        (C0 * I2 + B0 * C0 * I1 + h * C0 * (B1 + CU) / 2 * S) +
        (C1 * I1 + h * ((B0 + CU) * C1 + (1 + B0 + CU) * C2) / 2 * S)) +
      |ϖ| * (G0 * (I2 + B0 * I1 + h * (B1 + CU) / 2 * S))) =
      C1 * I1 / 2 + h * S * (C0 * (B1 + CU) / 2 +
        3 * ((B0 + CU) * C1 + (1 + B0 + CU) * C2) / 4 + |ϖ| * G0 * (B1 + CU) / 2) := by
    unfold K2 K1 K0
    ring
  have hpos : 0 ≤ C1 * I1 / 2 + h * S * (C0 * (B1 + CU) / 2 +
      3 * ((B0 + CU) * C1 + (1 + B0 + CU) * C2) / 4 + |ϖ| * G0 * (B1 + CU) / 2) := by
    positivity
  linarith

/-! ### Translation invariance of the local quantities -/

theorem jet_translate (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (p w : Fin d → ℝ) :
    jet (fun q => ψ (q + w)) p = jet ψ (p + w) := by
  funext k
  rcases k with _ | j
  · rfl
  · simp only [jet]
    rw [fderiv_comp_add_right]

theorem lineInt1_translate (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (p w : Fin d → ℝ) (j : Fin d)
    (h : ℝ) : lineInt1 (fun q => ψ (q + w)) p j h = lineInt1 ψ (p + w) j h := by
  unfold lineInt1
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  rw [fderiv_comp_add_right]
  congr 2
  abel

theorem lineInt2_translate (ψ : (Fin d → ℝ) → (Fin N → ℂ)) (p w : Fin d → ℝ) (j : Fin d)
    (h : ℝ) : lineInt2 (fun q => ψ (q + w)) p j h = lineInt2 ψ (p + w) j h := by
  unfold lineInt2
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  rw [iteratedFDeriv_comp_add_right]
  congr 2
  abel

/-- The coefficient-freezing constant. -/
def K3 (C0 C1 C2 B0 B1 : ℝ) : ℝ := C1 * B0 + C0 * B1 + C2

/-- **Local error on a translated sample**: for `z` and `y` in the cell of `x`,
`‖D̃ (ψ(z + h(· - x)))(x) - frozenSym(y)(jet ψ z)‖` is bounded by line integrals of `Dψ`, `D²ψ`
through `z` and by `h` times the values of `ψ`, `Dψ` near `z`. -/
theorem norm_transSample_sub_frozenSym_le {h ϖ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {c c' Ω : Coefficients d N} {C0 C1 C2 B0 B1 CU G0 : ℝ}
    (hb : CoeffBounds c c' Ω C0 C1 C2 B0 B1) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hCU : 0 ≤ CU) (hG0 : 0 ≤ G0) {U : Links d N}
    (hU : LinkExpansion h U Ω CU) {Γ : Matrix (Fin N) (Fin N) ℂ}
    (hΓ : ∀ v, ‖Γ *ᵥ v‖ ≤ G0 * ‖v‖) {ψ : (Fin d → ℝ) → (Fin N → ℂ)} (hψ : ContDiff ℝ 2 ψ)
    {x : Fin d → ℤ} {y z : Fin d → ℝ} (hy : y ∈ cell h x) :
    ‖covariantWilson h ϖ c U Γ (transSample h ψ x z) x - frozenSym c c' Ω y (jet ψ z)‖ ≤
      ∑ j, (K2 C0 G0 ϖ * lineInt2 ψ z j h + K1 C0 C1 B0 G0 ϖ * lineInt1 ψ z j h +
        K0 C0 C1 C2 B0 B1 CU G0 ϖ * h * (‖ψ (z + h • dir j)‖ + ‖ψ (z + (-h) • dir j)‖) +
        h * (C1 * ‖fderiv ℝ ψ z‖ + K3 C0 C1 C2 B0 B1 * ‖ψ z‖)) := by
  set p := latticePoint h x with hpdef
  set w := z - p
  have hpw : p + w = z := by simp [w]
  have hφ : ContDiff ℝ 2 (fun q => ψ (q + w)) := hψ.comp (contDiff_id.add contDiff_const)
  have h1 := norm_covariantWilson_sample_sub_frozenSym_le (ϖ := ϖ) hh hh1 hb hC0 hC1 hC2 hB0
    hB1 hCU hG0 hU hΓ hφ x
  rw [← hpdef] at h1
  have hjet : jet (fun q => ψ (q + w)) p = jet ψ z := by rw [jet_translate, hpw]
  have hts : transSample h ψ x z = sample h (fun q => ψ (q + w)) := rfl
  rw [hjet] at h1
  simp only [lineInt1_translate, lineInt2_translate, hpw] at h1
  have hpts : ∀ (t : ℝ) (j : Fin d), ψ (p + t • dir j + w) = ψ (z + t • dir j) := by
    intro t j
    rw [← hpw]
    congr 1
    abel
  simp only [hpts] at h1
  have h2 := norm_frozenSym_sub_le hb hC0 hC1 hC2 hB0 hB1 p y (jet ψ z)
  have hpy : ‖p - y‖ ≤ h := by
    rw [norm_sub_rev]
    exact (norm_sub_latticePoint_lt hh hy).le
  have h3 : ‖p - y‖ * ∑ j, (C1 * ‖jet ψ z (some j)‖ + (C1 * B0 + C0 * B1 + C2) * ‖jet ψ z none‖)
      ≤ ∑ _j : Fin d, h * (C1 * ‖fderiv ℝ ψ z‖ + K3 C0 C1 C2 B0 B1 * ‖ψ z‖) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul hpy (Finset.sum_le_sum fun j _ => ?_)
      (Finset.sum_nonneg fun j _ => by positivity) hh.le
    simp only [jet, K3]
    gcongr
    calc ‖fderiv ℝ ψ z (dir j)‖ ≤ ‖fderiv ℝ ψ z‖ * ‖dir j‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ ψ z‖ := by rw [norm_dir, mul_one]
  have hsplit : covariantWilson h ϖ c U Γ (transSample h ψ x z) x - frozenSym c c' Ω y (jet ψ z) =
      (covariantWilson h ϖ c U Γ (sample h (fun q => ψ (q + w))) x - frozenSym c c' Ω p (jet ψ z)) +
      (frozenSym c c' Ω p (jet ψ z) - frozenSym c c' Ω y (jet ψ z)) := by
    rw [hts]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [Finset.sum_add_distrib]
  exact add_le_add h1 (h2.trans h3)

/-! ### Cell integrals dominated by local averages -/

theorem lintegral_cell_segment_le {h : ℝ} (hh : 0 < h) {x : Fin d → ℤ} {y : Fin d → ℝ}
    (hy : y ∈ cell h x) (j : Fin d) {g : (Fin d → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z in cell h x, ∫⁻ s in Icc (-h) h, g (z + s • dir j) ≤
      ENNReal.ofReal (2 * h) *
        ∫⁻ τ in Metric.closedBall (0 : Fin d → ℝ) (2 * h), g (y + τ) := by
  have hm : Measurable fun q : (Fin d → ℝ) × ℝ => g (q.1 + q.2 • dir j) :=
    hg.comp (measurable_fst.add (measurable_snd.smul_const _))
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc ∫⁻ s in Icc (-h) h, ∫⁻ z in cell h x, g (z + s • dir j)
      ≤ ∫⁻ _ in Icc (-h) h, ∫⁻ τ in Metric.closedBall (0 : Fin d → ℝ) (2 * h), g (y + τ) := by
        refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        refine lintegral_cell_shift_le hh hy _ ?_
        rw [norm_smul, norm_dir, mul_one, Real.norm_eq_abs, abs_le]
        exact ⟨hs.1, hs.2⟩
    _ = _ := by
        rw [setLIntegral_const, Real.volume_Icc, mul_comm]
        congr 2
        ring

theorem measurable_lintegral_segment (j : Fin d) (h : ℝ) {g : (Fin d → ℝ) → ℝ≥0∞}
    (hg : Measurable g) :
    Measurable fun z : Fin d → ℝ => ∫⁻ s in Icc (-h) h, g (z + s • dir j) :=
  (hg.comp (measurable_fst.add (measurable_snd.smul_const _))).lintegral_prod_right'

/-- The local average `h^{-d} ∫_{‖τ‖ ≤ 2h} g(y + τ)`. -/
def ballAvg (h : ℝ) (g : (Fin d → ℝ) → ℝ≥0∞) (y : Fin d → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (h ^ d))⁻¹ * ∫⁻ τ in Metric.closedBall (0 : Fin d → ℝ) (2 * h), g (y + τ)

theorem measurable_ballAvg (h : ℝ) {g : (Fin d → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    Measurable (ballAvg h g) :=
  ((hg.comp (measurable_fst.add measurable_snd)).lintegral_prod_right').const_mul _

/-! ### The pointwise bound at a continuum point -/

theorem continuous_stencilValues_transSample {h : ℝ} {ψ : (Fin d → ℝ) → (Fin N → ℂ)}
    (hψ : Continuous ψ) (x : Fin d → ℤ) :
    Continuous fun z => stencilValues (transSample h ψ x z) x := by
  refine continuous_pi fun k => ?_
  rcases k with _ | ⟨b, j⟩
  · exact hψ.comp (continuous_const.add (continuous_id.sub continuous_const))
  · cases b
    · exact hψ.comp (continuous_const.add (continuous_id.sub continuous_const))
    · exact hψ.comp (continuous_const.add (continuous_id.sub continuous_const))

theorem continuous_covariantWilson_transSample (h ϖ : ℝ) (c : Coefficients d N)
    (U : Links d N) (Γ : Matrix (Fin N) (Fin N) ℂ) {ψ : (Fin d → ℝ) → (Fin N → ℂ)}
    (hψ : Continuous ψ) (x : Fin d → ℤ) :
    Continuous fun z => covariantWilson h ϖ c U Γ (transSample h ψ x z) x := by
  have e : (fun z => covariantWilson h ϖ c U Γ (transSample h ψ x z) x) =
      fun z => stencilLin h ϖ c U Γ x (stencilValues (transSample h ψ x z) x) :=
    funext fun z => covariantWilson_eq_stencilForm h ϖ c U Γ _ x
  rw [e]
  exact (stencilLin h ϖ c U Γ x).continuous_of_finiteDimensional.comp
    (continuous_stencilValues_transSample hψ x)

theorem continuous_jet {ψ : (Fin d → ℝ) → (Fin N → ℂ)} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (jet ψ) := by
  refine continuous_pi fun k => ?_
  rcases k with _ | j
  · exact hψ.continuous
  · exact (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem sq_add_le_two_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at h
  have h2 : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  rwa [h2] at h

theorem lintegral_add5 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f1 f2 f3 f4 f5 : X → ℝ≥0∞} (h1 : Measurable f1) (h2 : Measurable f2) (h3 : Measurable f3)
    (h4 : Measurable f4) :
    ∫⁻ z, (f1 z + f2 z + f3 z + f4 z + f5 z) ∂μ =
      ∫⁻ z, f1 z ∂μ + ∫⁻ z, f2 z ∂μ + ∫⁻ z, f3 z ∂μ + ∫⁻ z, f4 z ∂μ + ∫⁻ z, f5 z ∂μ := by
  have m4 : Measurable fun z => f1 z + f2 z + f3 z + f4 z := ((h1.add h2).add h3).add h4
  have m3 : Measurable fun z => f1 z + f2 z + f3 z := (h1.add h2).add h3
  have m2 : Measurable fun z => f1 z + f2 z := h1.add h2
  rw [lintegral_add_left m4, lintegral_add_left m3, lintegral_add_left m2, lintegral_add_left h1]

/-- The aggregated constants of the `L²` estimate. -/
def Kα (d : ℕ) (C0 C1 C2 B0 B1 CU G0 ϖ : ℝ) : ℝ :=
  d * (2 * K2 C0 G0 ϖ + 2 * K1 C0 C1 B0 G0 ϖ + C1 + 2 * K0 C0 C1 C2 B0 B1 CU G0 ϖ +
    K3 C0 C1 C2 B0 B1)

def Kβ (d : ℕ) (C0 C1 B0 : ℝ) : ℝ := d * (C0 + C0 * B0 + C1)

set_option maxHeartbeats 1000000 in
/-- **Pointwise bound at a continuum point** `y` (in the cell of `x = cellIdx h y`): the error
`D̃ (S_h ψ)(x) - frozenSym(y)(jet ψ y)` is bounded by `h` times local averages of `|ψ|`, `|Dψ|`,
`|D²ψ|` over the ball of radius `2h` around `y`, plus the cell-averaging errors of `ψ` and `Dψ`
at `y`. -/
theorem enorm_core_error_le {h ϖ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {c c' Ω : Coefficients d N} {C0 C1 C2 B0 B1 CU G0 : ℝ}
    (hb : CoeffBounds c c' Ω C0 C1 C2 B0 B1) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hCU : 0 ≤ CU) (hG0 : 0 ≤ G0) {U : Links d N}
    (hU : LinkExpansion h U Ω CU) {Γ : Matrix (Fin N) (Fin N) ℂ}
    (hΓ : ∀ v, ‖Γ *ᵥ v‖ ≤ G0 * ‖v‖) {ψ : (Fin d → ℝ) → (Fin N → ℂ)} (hψ : ContDiff ℝ 2 ψ)
    (y : Fin d → ℝ) :
    ‖covariantWilson h ϖ c U Γ (cellAvg h ψ) (cellIdx h y) - frozenSym c c' Ω y (jet ψ y)‖ₑ ≤
      ENNReal.ofReal (h * Kα d C0 C1 C2 B0 B1 CU G0 ϖ) *
        (ballAvg h (fun q => ‖ψ q‖ₑ) y + ballAvg h (fun q => ‖fderiv ℝ ψ q‖ₑ) y +
          ballAvg h (fun q => ‖iteratedFDeriv ℝ 2 ψ q‖ₑ) y) +
      ENNReal.ofReal (Kβ d C0 C1 B0) *
        (‖cellAvg h ψ (cellIdx h y) - ψ y‖ₑ +
          ‖cellAvg h (fderiv ℝ ψ) (cellIdx h y) - fderiv ℝ ψ y‖ₑ) := by
  set x := cellIdx h y with hxdef
  have hy : y ∈ cell h x := mem_cell_cellIdx h y
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hhd : 0 < h ^ d := pow_pos hh d
  set L : (Option (Fin d) → (Fin N → ℂ)) →L[ℂ] (Fin N → ℂ) :=
    LinearMap.toContinuousLinearMap (frozenSymLin c c' Ω y)
  have hLapp : ∀ a, L a = frozenSym c c' Ω y a := fun a => rfl
  -- integrability on the cell
  have hCWi : Integrable (fun z => covariantWilson h ϖ c U Γ (transSample h ψ x z) x)
      (volume.restrict (cell h x)) :=
    integrableOn_cell hh (continuous_covariantWilson_transSample h ϖ c U Γ hψ.continuous x) x
  have hJi : Integrable (fun z => jet ψ z) (volume.restrict (cell h x)) :=
    integrableOn_cell hh (continuous_jet hψ1) x
  have hLJi : Integrable (fun z => L (jet ψ z)) (volume.restrict (cell h x)) :=
    L.integrable_comp hJi
  set avgJet : Option (Fin d) → (Fin N → ℂ) := (h ^ d)⁻¹ • ∫ z in cell h x, jet ψ z
  have hLavg : L avgJet = (h ^ d)⁻¹ • ∫ z in cell h x, L (jet ψ z) := by
    simp only [avgJet]
    rw [L.map_smul_of_tower, ← L.integral_comp_comm hJi]
  -- decomposition
  have hdec : covariantWilson h ϖ c U Γ (cellAvg h ψ) x - frozenSym c c' Ω y (jet ψ y) =
      (h ^ d)⁻¹ • (∫ z in cell h x, (covariantWilson h ϖ c U Γ (transSample h ψ x z) x -
        L (jet ψ z))) + L (avgJet - jet ψ y) := by
    have hsub : ∫ z in cell h x, (covariantWilson h ϖ c U Γ (transSample h ψ x z) x -
        L (jet ψ z)) = (∫ z in cell h x, covariantWilson h ϖ c U Γ (transSample h ψ x z) x) -
        ∫ z in cell h x, L (jet ψ z) := integral_sub hCWi hLJi
    rw [covariantWilson_cellAvg h ϖ hh c U Γ ψ hψ.continuous x, hsub,
      smul_sub, map_sub, hLavg, ← hLapp]
    abel
  rw [hdec]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the cell integral of the local error
    set g0 : (Fin d → ℝ) → ℝ≥0∞ := fun q => ‖ψ q‖ₑ
    set g1 : (Fin d → ℝ) → ℝ≥0∞ := fun q => ‖fderiv ℝ ψ q‖ₑ
    set g2 : (Fin d → ℝ) → ℝ≥0∞ := fun q => ‖iteratedFDeriv ℝ 2 ψ q‖ₑ
    have hg0 : Measurable g0 := hψ.continuous.enorm.measurable
    have hg1 : Measurable g1 := (hψ.continuous_fderiv (by norm_num)).enorm.measurable
    have hg2 : Measurable g2 := (hψ.continuous_iteratedFDeriv (by norm_num)).enorm.measurable
    set I0 := ∫⁻ τ in Metric.closedBall (0 : Fin d → ℝ) (2 * h), g0 (y + τ)
    set I1 := ∫⁻ τ in Metric.closedBall (0 : Fin d → ℝ) (2 * h), g1 (y + τ)
    set I2 := ∫⁻ τ in Metric.closedBall (0 : Fin d → ℝ) (2 * h), g2 (y + τ)
    set k2 := K2 C0 G0 ϖ
    set k1 := K1 C0 C1 B0 G0 ϖ
    set k0 := K0 C0 C1 C2 B0 B1 CU G0 ϖ
    set k3 := K3 C0 C1 C2 B0 B1
    have hk2 : 0 ≤ k2 := by simp only [k2, K2]; positivity
    have hk1 : 0 ≤ k1 := by simp only [k1, K1]; positivity
    have hk0 : 0 ≤ k0 := by simp only [k0, K0]; positivity
    have hk3 : 0 ≤ k3 := by simp only [k3, K3]; positivity
    -- pointwise ENNReal bound on the cell
    set T : (Fin d → ℝ) → ℝ≥0∞ := fun z => ∑ j : Fin d,
      (ENNReal.ofReal k2 * (∫⁻ s in Icc (-h) h, g2 (z + s • dir j)) +
        ENNReal.ofReal k1 * (∫⁻ s in Icc (-h) h, g1 (z + s • dir j)) +
        ENNReal.ofReal (k0 * h) * (g0 (z + h • dir j) + g0 (z + (-h) • dir j)) +
        ENNReal.ofReal (h * C1) * g1 z + ENNReal.ofReal (h * k3) * g0 z)
    have hpt : ∀ z ∈ cell h x,
        ‖covariantWilson h ϖ c U Γ (transSample h ψ x z) x - L (jet ψ z)‖ₑ ≤ T z := by
      intro z _
      have h1 := norm_transSample_sub_frozenSym_le (ϖ := ϖ) hh hh1 hb hC0 hC1 hC2 hB0 hB1
        hCU hG0 hU hΓ hψ (z := z) hy
      rw [← hLapp] at h1
      rw [← ofReal_norm]
      refine (ENNReal.ofReal_le_ofReal h1).trans ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by
        have := lineInt1_nonneg ψ z j h
        have := lineInt2_nonneg ψ z j h
        positivity)]
      refine Finset.sum_le_sum fun j _ => ?_
      have l1 := lineInt1_nonneg ψ z j h
      have l2 := lineInt2_nonneg ψ z j h
      have n1 := norm_nonneg (ψ (z + h • dir j))
      have n2 := norm_nonneg (ψ (z + (-h) • dir j))
      have n3 := norm_nonneg (fderiv ℝ ψ z)
      have n4 := norm_nonneg (ψ z)
      have e : k2 * lineInt2 ψ z j h + k1 * lineInt1 ψ z j h +
          k0 * h * (‖ψ (z + h • dir j)‖ + ‖ψ (z + (-h) • dir j)‖) +
          h * (C1 * ‖fderiv ℝ ψ z‖ + k3 * ‖ψ z‖) =
          k2 * lineInt2 ψ z j h + k1 * lineInt1 ψ z j h +
          k0 * h * (‖ψ (z + h • dir j)‖ + ‖ψ (z + (-h) • dir j)‖) +
          h * C1 * ‖fderiv ℝ ψ z‖ + h * k3 * ‖ψ z‖ := by ring
      rw [e]
      have hk0h : 0 ≤ k0 * h := mul_nonneg hk0 hh.le
      have hC1h : 0 ≤ h * C1 := mul_nonneg hh.le hC1
      have hk3h : 0 ≤ h * k3 := mul_nonneg hh.le hk3
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul hk2, ofReal_lineInt2 hψ, ENNReal.ofReal_mul hk1, ofReal_lineInt1 hψ1,
        ENNReal.ofReal_mul hk0h, ENNReal.ofReal_add n1 n2, ENNReal.ofReal_mul hC1h,
        ENNReal.ofReal_mul hk3h]
      simp only [ofReal_norm]
      exact le_rfl
    have hTj : ∀ j : Fin d, Measurable fun z =>
        ENNReal.ofReal k2 * (∫⁻ s in Icc (-h) h, g2 (z + s • dir j)) +
          ENNReal.ofReal k1 * (∫⁻ s in Icc (-h) h, g1 (z + s • dir j)) +
          ENNReal.ofReal (k0 * h) * (g0 (z + h • dir j) + g0 (z + (-h) • dir j)) +
          ENNReal.ofReal (h * C1) * g1 z + ENNReal.ofReal (h * k3) * g0 z := by
      intro j
      have a1 : Measurable fun z => ENNReal.ofReal k2 * (∫⁻ s in Icc (-h) h, g2 (z + s • dir j)) :=
        (measurable_lintegral_segment j h hg2).const_mul _
      have a2 : Measurable fun z => ENNReal.ofReal k1 * (∫⁻ s in Icc (-h) h, g1 (z + s • dir j)) :=
        (measurable_lintegral_segment j h hg1).const_mul _
      have a3 : Measurable fun z =>
          ENNReal.ofReal (k0 * h) * (g0 (z + h • dir j) + g0 (z + (-h) • dir j)) :=
        ((hg0.comp (measurable_add_const _)).add (hg0.comp (measurable_add_const _))).const_mul _
      have a4 : Measurable fun z => ENNReal.ofReal (h * C1) * g1 z := hg1.const_mul _
      have a5 : Measurable fun z => ENNReal.ofReal (h * k3) * g0 z := hg0.const_mul _
      exact (((a1.add a2).add a3).add a4).add a5
    -- integrate over the cell
    have hint : ∫⁻ z in cell h x, T z ≤ ∑ _j : Fin d,
        (ENNReal.ofReal k2 * (ENNReal.ofReal (2 * h) * I2) +
          ENNReal.ofReal k1 * (ENNReal.ofReal (2 * h) * I1) +
          ENNReal.ofReal (k0 * h) * (I0 + I0) + ENNReal.ofReal (h * C1) * I1 +
          ENNReal.ofReal (h * k3) * I0) := by
      simp only [T]
      rw [lintegral_finset_sum _ (fun j _ => hTj j)]
      refine Finset.sum_le_sum fun j _ => ?_
      have hp1 : ‖h • dir j‖ ≤ h := by
        rw [norm_smul, norm_dir, mul_one, Real.norm_eq_abs, abs_of_pos hh]
      have hp2 : ‖(-h) • dir j‖ ≤ h := by
        rw [norm_neg_smul_dir, abs_of_pos hh]
      have hp0 : ‖(0 : Fin d → ℝ)‖ ≤ h := by rw [norm_zero]; exact hh.le
      have e0 : ∫⁻ z in cell h x, g0 z ≤ I0 := by
        have := lintegral_cell_shift_le hh hy 0 hp0 (G := g0)
        simpa using this
      have e1 : ∫⁻ z in cell h x, g1 z ≤ I1 := by
        have := lintegral_cell_shift_le hh hy 0 hp0 (G := g1)
        simpa using this
      have s1 := lintegral_cell_segment_le hh hy j hg2
      have s2 := lintegral_cell_segment_le hh hy j hg1
      have p1 := lintegral_cell_shift_le hh hy (h • dir j) hp1 (G := g0)
      have p2 := lintegral_cell_shift_le hh hy ((-h) • dir j) hp2 (G := g0)
      calc ∫⁻ z in cell h x, (ENNReal.ofReal k2 * (∫⁻ s in Icc (-h) h, g2 (z + s • dir j)) +
            ENNReal.ofReal k1 * (∫⁻ s in Icc (-h) h, g1 (z + s • dir j)) +
            ENNReal.ofReal (k0 * h) * (g0 (z + h • dir j) + g0 (z + (-h) • dir j)) +
            ENNReal.ofReal (h * C1) * g1 z + ENNReal.ofReal (h * k3) * g0 z)
          = (∫⁻ z in cell h x, ENNReal.ofReal k2 * (∫⁻ s in Icc (-h) h, g2 (z + s • dir j))) +
            (∫⁻ z in cell h x, ENNReal.ofReal k1 * (∫⁻ s in Icc (-h) h, g1 (z + s • dir j))) +
            (∫⁻ z in cell h x,
              ENNReal.ofReal (k0 * h) * (g0 (z + h • dir j) + g0 (z + (-h) • dir j))) +
            (∫⁻ z in cell h x, ENNReal.ofReal (h * C1) * g1 z) +
            (∫⁻ z in cell h x, ENNReal.ofReal (h * k3) * g0 z) :=
            lintegral_add5 (μ := volume.restrict (cell h x))
              ((measurable_lintegral_segment j h hg2).const_mul _)
              ((measurable_lintegral_segment j h hg1).const_mul _)
              (((hg0.comp (measurable_add_const _)).add
                (hg0.comp (measurable_add_const _))).const_mul _) (hg1.const_mul _)
        _ ≤ _ := by
            have mpp : Measurable fun z => g0 (z + h • dir j) + g0 (z + (-h) • dir j) :=
              (hg0.comp (measurable_add_const _)).add (hg0.comp (measurable_add_const _))
            have mp1 : Measurable fun z => g0 (z + h • dir j) := hg0.comp (measurable_add_const _)
            rw [lintegral_const_mul _ (measurable_lintegral_segment j h hg2),
              lintegral_const_mul _ (measurable_lintegral_segment j h hg1),
              lintegral_const_mul _ mpp, lintegral_const_mul _ hg1, lintegral_const_mul _ hg0,
              lintegral_add_left mp1]
            gcongr
    -- conclude
    have hcell : ‖(h ^ d)⁻¹ • ∫ z in cell h x, (covariantWilson h ϖ c U Γ (transSample h ψ x z) x -
        L (jet ψ z))‖ₑ ≤ (ENNReal.ofReal (h ^ d))⁻¹ * ∫⁻ z in cell h x, T z := by
      rw [enorm_smul, ← ofReal_norm, Real.norm_eq_abs, abs_inv, abs_of_pos hhd,
        ENNReal.ofReal_inv_of_pos hhd]
      exact mul_le_mul' le_rfl ((enorm_integral_le_lintegral_enorm _).trans
        (setLIntegral_mono' (measurableSet_cell h x) hpt))
    refine hcell.trans ?_
    refine (mul_le_mul' le_rfl hint).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold ballAvg
    set a := (ENNReal.ofReal (h ^ d))⁻¹
    -- coefficient comparison
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have eK : Kα d C0 C1 C2 B0 B1 CU G0 ϖ = d * (2 * k2 + 2 * k1 + C1 + 2 * k0 + k3) := rfl
    have hdE : (d : ℝ≥0∞) = ENNReal.ofReal d := (ENNReal.ofReal_natCast d).symm
    have c2 : (d : ℝ≥0∞) * (ENNReal.ofReal k2 * ENNReal.ofReal (2 * h)) ≤
        ENNReal.ofReal (h * Kα d C0 C1 C2 B0 B1 CU G0 ϖ) := by
      rw [hdE, ← ENNReal.ofReal_mul hk2, ← ENNReal.ofReal_mul hd]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [eK]
      nlinarith [mul_nonneg (mul_nonneg hd hh.le)
        (by positivity : (0 : ℝ) ≤ 2 * k1 + C1 + 2 * k0 + k3)]
    have c1 : (d : ℝ≥0∞) * (ENNReal.ofReal k1 * ENNReal.ofReal (2 * h) +
        ENNReal.ofReal (h * C1)) ≤ ENNReal.ofReal (h * Kα d C0 C1 C2 B0 B1 CU G0 ϖ) := by
      rw [hdE, ← ENNReal.ofReal_mul hk1, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul hd]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [eK]
      nlinarith [mul_nonneg (mul_nonneg hd hh.le)
        (by positivity : (0 : ℝ) ≤ 2 * k2 + 2 * k0 + k3)]
    have c0 : (d : ℝ≥0∞) * (ENNReal.ofReal (k0 * h) + ENNReal.ofReal (k0 * h) +
        ENNReal.ofReal (h * k3)) ≤ ENNReal.ofReal (h * Kα d C0 C1 C2 B0 B1 CU G0 ϖ) := by
      rw [hdE, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hd]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [eK]
      nlinarith [mul_nonneg (mul_nonneg hd hh.le)
        (by positivity : (0 : ℝ) ≤ 2 * k2 + 2 * k1 + C1)]
    calc a * ((d : ℝ≥0∞) * (ENNReal.ofReal k2 * (ENNReal.ofReal (2 * h) * I2) +
          ENNReal.ofReal k1 * (ENNReal.ofReal (2 * h) * I1) +
          ENNReal.ofReal (k0 * h) * (I0 + I0) + ENNReal.ofReal (h * C1) * I1 +
          ENNReal.ofReal (h * k3) * I0))
        = (d : ℝ≥0∞) * (ENNReal.ofReal k2 * ENNReal.ofReal (2 * h)) * (a * I2) +
          (d : ℝ≥0∞) * (ENNReal.ofReal k1 * ENNReal.ofReal (2 * h) + ENNReal.ofReal (h * C1)) *
            (a * I1) +
          (d : ℝ≥0∞) * (ENNReal.ofReal (k0 * h) + ENNReal.ofReal (k0 * h) +
            ENNReal.ofReal (h * k3)) * (a * I0) := by ring
      _ ≤ ENNReal.ofReal (h * Kα d C0 C1 C2 B0 B1 CU G0 ϖ) * (a * I2) +
          ENNReal.ofReal (h * Kα d C0 C1 C2 B0 B1 CU G0 ϖ) * (a * I1) +
          ENNReal.ofReal (h * Kα d C0 C1 C2 B0 B1 CU G0 ϖ) * (a * I0) := by gcongr
      _ = _ := by ring
  · -- the cell-averaging error of the jet
    have hJe : ∀ k, Integrable (fun z => jet ψ z k) (volume.restrict (cell h x)) := hJi.eval
    have hDi : Integrable (fun z => fderiv ℝ ψ z) (volume.restrict (cell h x)) :=
      integrableOn_cell hh (hψ.continuous_fderiv (by norm_num)) x
    have hA0 : avgJet none = cellAvg h ψ x := by
      simp only [avgJet, Pi.smul_apply]
      rw [eval_integral hJe]
      rfl
    have hA1 : ∀ j, avgJet (some j) = cellAvg h (fderiv ℝ ψ) x (dir j) := by
      intro j
      simp only [avgJet, Pi.smul_apply, cellAvg, ContinuousLinearMap.smul_apply]
      rw [eval_integral hJe, ContinuousLinearMap.integral_apply hDi]
      rfl
    set P0 := ‖cellAvg h ψ x - ψ y‖
    set P1 := ‖cellAvg h (fderiv ℝ ψ) x - fderiv ℝ ψ y‖
    have hP0 : 0 ≤ P0 := norm_nonneg _
    have hP1 : 0 ≤ P1 := norm_nonneg _
    have hb1 := norm_frozenSym_le hb hC0 hC1 hB0 y (avgJet - jet ψ y)
    have hj : ∀ j : Fin d, C0 * ‖(avgJet - jet ψ y) (some j)‖ +
        (C0 * B0 + C1) * ‖(avgJet - jet ψ y) none‖ ≤ C0 * P1 + (C0 * B0 + C1) * P0 := by
      intro j
      rw [Pi.sub_apply, Pi.sub_apply, hA0, hA1 j]
      simp only [jet]
      gcongr
      rw [← ContinuousLinearMap.sub_apply]
      calc ‖(cellAvg h (fderiv ℝ ψ) x - fderiv ℝ ψ y) (dir j)‖
          ≤ ‖cellAvg h (fderiv ℝ ψ) x - fderiv ℝ ψ y‖ * ‖dir j‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = P1 := by rw [norm_dir, mul_one]
    have hreal : ‖L (avgJet - jet ψ y)‖ ≤ Kβ d C0 C1 B0 * (P0 + P1) := by
      rw [hLapp]
      refine hb1.trans ((Finset.sum_le_sum fun j _ => hj j).trans ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold Kβ
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith [mul_nonneg hd (mul_nonneg hC0 hP0), mul_nonneg hd (mul_nonneg (mul_nonneg hC0 hB0) hP1),
        mul_nonneg hd (mul_nonneg hC1 hP1)]
    have hKβ : 0 ≤ Kβ d C0 C1 B0 := by unfold Kβ; positivity
    rw [← ofReal_norm]
    calc ENNReal.ofReal ‖L (avgJet - jet ψ y)‖ ≤ ENNReal.ofReal (Kβ d C0 C1 B0 * (P0 + P1)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
          rw [ENNReal.ofReal_mul hKβ, ENNReal.ofReal_add hP0 hP1, ofReal_norm, ofReal_norm]

/-! ### The `L²` estimates -/

/-- The squared Sobolev norm `‖ψ‖²_{H²} = Σ_{k ≤ 2} ∫ ‖D^k ψ‖²` (with the operator norms of the
Fréchet derivatives; equivalent to the sum over multi-indices `|α| ≤ 2` of `‖∂^α ψ‖²_{L²}`). -/
def sobolevSqH2 (ψ : (Fin d → ℝ) → (Fin N → ℂ)) : ℝ≥0∞ :=
  (∫⁻ y, ‖ψ y‖ₑ ^ 2) + (∫⁻ y, ‖fderiv ℝ ψ y‖ₑ ^ 2) + (∫⁻ y, ‖iteratedFDeriv ℝ 2 ψ y‖ₑ ^ 2)

/-- The squared Sobolev norm `‖ψ‖²_{H³} = Σ_{k ≤ 3} ∫ ‖D^k ψ‖²`. -/
def sobolevSqH3 (ψ : (Fin d → ℝ) → (Fin N → ℂ)) : ℝ≥0∞ :=
  sobolevSqH2 ψ + (∫⁻ y, ‖iteratedFDeriv ℝ 3 ψ y‖ₑ ^ 2)

theorem sobolevSqH2_le_H3 (ψ : (Fin d → ℝ) → (Fin N → ℂ)) : sobolevSqH2 ψ ≤ sobolevSqH3 ψ :=
  le_self_add

theorem sq_add3_le (a b c : ℝ≥0∞) : (a + b + c) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  calc (a + b + c) ^ 2 ≤ 2 * ((a + b) ^ 2 + c ^ 2) := sq_add_le_two_mul _ _
    _ ≤ 2 * (2 * (a ^ 2 + b ^ 2) + 2 * c ^ 2) := by
        gcongr
        · exact sq_add_le_two_mul _ _
        · exact le_mul_of_one_le_left bot_le (by norm_num)
    _ = 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring

/-- The final constant of `eq:supp-general-core`. -/
def coreL2Constant (d : ℕ) (C0 C1 C2 B0 B1 CU G0 ϖ : ℝ) : ℝ≥0∞ :=
  8 * 16 ^ d * ENNReal.ofReal (Kα d C0 C1 C2 B0 B1 CU G0 ϖ) ^ 2 +
    4 * 2 ^ d * ENNReal.ofReal (Kβ d C0 C1 B0) ^ 2

set_option maxHeartbeats 1000000 in
/-- **`lem:supp-general-core`, `eq:supp-general-core`** (`L²` form, cell-average sampling).
For `0 < h ≤ 1`, the covariant doubled Wilson operator with spin links `U` (second-order link
expansion `U_j = I + hΩ_j + O(h²)`), sampled Clifford coefficients `c^j(hx)` and Wilson term
`ϖ Γ W^Ω`, applied to the cell averages `S_h ψ` of a `C²` spinor and reconstructed piecewise
constantly (`𝒥⁰_h`, i.e. evaluated at `cellIdx h y`), approximates the density-symmetric Dirac
operator `-(i/2) Σ_j (M_{c^j} ∇_j + ∇_j M_{c^j})` in `L²(ℝᵈ)`:
`‖𝒥⁰_h D̃ S_h ψ - (-(i/2) Σ_j (c^j ∇_j + ∇_j c^j)) ψ‖²_{L²} ≤ K h² ‖ψ‖²_{H²}`, with `K`
depending only on `d` and on the coefficient, connection, link and Wilson bounds. -/
theorem lintegral_covariantWilson_cellAvg_sub_densitySymmetricDirac_le {h ϖ : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) {c c' Ω : Coefficients d N} {C0 C1 C2 B0 B1 CU G0 : ℝ}
    (hb : CoeffBounds c c' Ω C0 C1 C2 B0 B1) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hCU : 0 ≤ CU) (hG0 : 0 ≤ G0) {U : Links d N}
    (hU : LinkExpansion h U Ω CU) {Γ : Matrix (Fin N) (Fin N) ℂ}
    (hΓ : ∀ v, ‖Γ *ᵥ v‖ ≤ G0 * ‖v‖) {ψ : (Fin d → ℝ) → (Fin N → ℂ)} (hψ : ContDiff ℝ 2 ψ) :
    ∫⁻ y, ‖covariantWilson h ϖ c U Γ (cellAvg h ψ) (cellIdx h y) -
        densitySymmetricDirac c Ω ψ y‖ₑ ^ 2 ≤
      coreL2Constant d C0 C1 C2 B0 B1 CU G0 ϖ * ENNReal.ofReal (h ^ 2) * sobolevSqH2 ψ := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  set g0 : (Fin d → ℝ) → ℝ≥0∞ := fun q => ‖ψ q‖ₑ
  set g1 : (Fin d → ℝ) → ℝ≥0∞ := fun q => ‖fderiv ℝ ψ q‖ₑ
  set g2 : (Fin d → ℝ) → ℝ≥0∞ := fun q => ‖iteratedFDeriv ℝ 2 ψ q‖ₑ
  have hg0 : Measurable g0 := hψ.continuous.enorm.measurable
  have hg1 : Measurable g1 := (hψ.continuous_fderiv (by norm_num)).enorm.measurable
  have hg2 : Measurable g2 := (hψ.continuous_iteratedFDeriv (by norm_num)).enorm.measurable
  set p0 : (Fin d → ℝ) → ℝ≥0∞ := fun y => ‖cellAvg h ψ (cellIdx h y) - ψ y‖ₑ
  set p1 : (Fin d → ℝ) → ℝ≥0∞ :=
    fun y => ‖cellAvg h (fderiv ℝ ψ) (cellIdx h y) - fderiv ℝ ψ y‖ₑ
  have hp0 : Measurable p0 :=
    (((measurable_of_countable (cellAvg h ψ)).comp (measurable_cellIdx h)).sub
      hψ.continuous.measurable).enorm
  have hp1 : Measurable p1 :=
    (((measurable_of_countable (cellAvg h (fderiv ℝ ψ))).comp (measurable_cellIdx h)).sub
      (hψ.continuous_fderiv (by norm_num)).measurable).enorm
  set cA := ENNReal.ofReal (h * Kα d C0 C1 C2 B0 B1 CU G0 ϖ)
  set cB := ENNReal.ofReal (Kβ d C0 C1 B0)
  have hpt : ∀ y, ‖covariantWilson h ϖ c U Γ (cellAvg h ψ) (cellIdx h y) -
      densitySymmetricDirac c Ω ψ y‖ₑ ^ 2 ≤
      8 * cA ^ 2 * (ballAvg h g0 y ^ 2 + ballAvg h g1 y ^ 2 + ballAvg h g2 y ^ 2) +
        4 * cB ^ 2 * (p0 y ^ 2 + p1 y ^ 2) := by
    intro y
    rw [densitySymmetricDirac_eq_frozenSym hb.c_deriv (hψ.differentiable (by norm_num)) y]
    have h1 := enorm_core_error_le (ϖ := ϖ) hh hh1 hb hC0 hC1 hC2 hB0 hB1 hCU hG0 hU hΓ hψ y
    refine (pow_le_pow_left₀ bot_le h1 2).trans ?_
    refine (sq_add_le_two_mul _ _).trans ?_
    have a1 : (cA * (ballAvg h g0 y + ballAvg h g1 y + ballAvg h g2 y)) ^ 2 ≤
        cA ^ 2 * (4 * (ballAvg h g0 y ^ 2 + ballAvg h g1 y ^ 2 + ballAvg h g2 y ^ 2)) := by
      rw [mul_pow]
      gcongr
      exact sq_add3_le _ _ _
    have a2 : (cB * (p0 y + p1 y)) ^ 2 ≤ cB ^ 2 * (2 * (p0 y ^ 2 + p1 y ^ 2)) := by
      rw [mul_pow]
      gcongr
      exact sq_add_le_two_mul _ _
    calc 2 * ((cA * (ballAvg h g0 y + ballAvg h g1 y + ballAvg h g2 y)) ^ 2 +
          (cB * (p0 y + p1 y)) ^ 2)
        ≤ 2 * (cA ^ 2 * (4 * (ballAvg h g0 y ^ 2 + ballAvg h g1 y ^ 2 + ballAvg h g2 y ^ 2)) +
          cB ^ 2 * (2 * (p0 y ^ 2 + p1 y ^ 2))) := by gcongr
      _ = _ := by ring
  have mb0 := (measurable_ballAvg h hg0).pow_const 2
  have mb1 := (measurable_ballAvg h hg1).pow_const 2
  have mb2 := (measurable_ballAvg h hg2).pow_const 2
  have I0 := lintegral_sq_ballAverage_le hh hg0
  have I1 := lintegral_sq_ballAverage_le hh hg1
  have I2 := lintegral_sq_ballAverage_le hh hg2
  have P0 := lintegral_cellAvg_sub_sq_le hψ1 hh
  have P1 := lintegral_cellAvg_sub_sq_le (hψ.fderiv_right (m := 1) (by norm_num)) hh
  have hD2 : ∫⁻ y, ‖fderiv ℝ (fderiv ℝ ψ) y‖ₑ ^ 2 = ∫⁻ y, g2 y ^ 2 := by
    refine lintegral_congr fun y => ?_
    simp only [g2]
    rw [← ofReal_norm, ← ofReal_norm, LatticeCellL2.norm_fderiv_fderiv_eq]
  rw [hD2] at P1
  calc ∫⁻ y, ‖covariantWilson h ϖ c U Γ (cellAvg h ψ) (cellIdx h y) -
        densitySymmetricDirac c Ω ψ y‖ₑ ^ 2
      ≤ ∫⁻ y, (8 * cA ^ 2 * (ballAvg h g0 y ^ 2 + ballAvg h g1 y ^ 2 + ballAvg h g2 y ^ 2) +
        4 * cB ^ 2 * (p0 y ^ 2 + p1 y ^ 2)) := lintegral_mono hpt
    _ = 8 * cA ^ 2 * ((∫⁻ y, ballAvg h g0 y ^ 2) + (∫⁻ y, ballAvg h g1 y ^ 2) +
          (∫⁻ y, ballAvg h g2 y ^ 2)) +
        4 * cB ^ 2 * ((∫⁻ y, p0 y ^ 2) + (∫⁻ y, p1 y ^ 2)) := by
        have mb0' : Measurable fun y => ballAvg h g0 y ^ 2 := mb0
        have mS2 : Measurable fun y => ballAvg h g0 y ^ 2 + ballAvg h g1 y ^ 2 := mb0.add mb1
        have mS : Measurable fun y => ballAvg h g0 y ^ 2 + ballAvg h g1 y ^ 2 +
            ballAvg h g2 y ^ 2 := (mb0.add mb1).add mb2
        have mA : Measurable fun y => 8 * cA ^ 2 * (ballAvg h g0 y ^ 2 + ballAvg h g1 y ^ 2 +
            ballAvg h g2 y ^ 2) := mS.const_mul _
        have mp0 : Measurable fun y => p0 y ^ 2 := hp0.pow_const 2
        have mP : Measurable fun y => p0 y ^ 2 + p1 y ^ 2 := (hp0.pow_const 2).add (hp1.pow_const 2)
        rw [lintegral_add_left mA, lintegral_const_mul _ mS, lintegral_const_mul _ mP,
          lintegral_add_left mS2, lintegral_add_left mb0', lintegral_add_left mp0]
    _ ≤ 8 * cA ^ 2 * (16 ^ d * (∫⁻ y, g0 y ^ 2) + 16 ^ d * (∫⁻ y, g1 y ^ 2) +
          16 ^ d * (∫⁻ y, g2 y ^ 2)) +
        4 * cB ^ 2 * (2 ^ d * ENNReal.ofReal (h ^ 2) * (∫⁻ y, g1 y ^ 2) +
          2 ^ d * ENNReal.ofReal (h ^ 2) * (∫⁻ y, g2 y ^ 2)) := by
        gcongr
        · exact I0
        · exact I1
        · exact I2
    _ ≤ coreL2Constant d C0 C1 C2 B0 B1 CU G0 ϖ * ENNReal.ofReal (h ^ 2) * sobolevSqH2 ψ := by
        have hcA : cA ^ 2 = ENNReal.ofReal (h ^ 2) * ENNReal.ofReal (Kα d C0 C1 C2 B0 B1 CU G0 ϖ) ^ 2 := by
          simp only [cA]
          rw [ENNReal.ofReal_mul hh.le, mul_pow, ENNReal.ofReal_pow hh.le]
        rw [hcA]
        unfold coreL2Constant sobolevSqH2
        set G0' := ∫⁻ y, g0 y ^ 2
        set G1' := ∫⁻ y, g1 y ^ 2
        set G2' := ∫⁻ y, g2 y ^ 2
        set hq := ENNReal.ofReal (h ^ 2)
        set kα := ENNReal.ofReal (Kα d C0 C1 C2 B0 B1 CU G0 ϖ)
        have e : 8 * (hq * kα ^ 2) * (16 ^ d * G0' + 16 ^ d * G1' + 16 ^ d * G2') +
            4 * cB ^ 2 * (2 ^ d * hq * G1' + 2 ^ d * hq * G2') ≤
            (8 * 16 ^ d * kα ^ 2 + 4 * 2 ^ d * cB ^ 2) * hq * (G0' + G1' + G2') := by
          have : 4 * cB ^ 2 * (2 ^ d * hq * G1' + 2 ^ d * hq * G2') ≤
              4 * 2 ^ d * cB ^ 2 * hq * (G0' + G1' + G2') := by
            calc 4 * cB ^ 2 * (2 ^ d * hq * G1' + 2 ^ d * hq * G2') =
                  4 * 2 ^ d * cB ^ 2 * hq * (G1' + G2') := by ring
              _ ≤ 4 * 2 ^ d * cB ^ 2 * hq * (G0' + G1' + G2') := by
                  gcongr
                  exact le_add_self
          calc _ ≤ 8 * (hq * kα ^ 2) * (16 ^ d * G0' + 16 ^ d * G1' + 16 ^ d * G2') +
                4 * 2 ^ d * cB ^ 2 * hq * (G0' + G1' + G2') := by gcongr
            _ = _ := by ring
        exact e

/-! ### The Wilson-term smallness `eq:Wilson-core-smallness` -/

/-- The covariant Wilson term is the covariant Wilson operator with zero Clifford coefficients,
`Γ = 1`, `ϖ = 1`. -/
theorem covWilsonTerm_eq_covariantWilson (h : ℝ) (U : Links d N) (u : LatticeSection d N)
    (x : Fin d → ℤ) :
    covWilsonTerm h U u x = covariantWilson h 1 (fun _ _ => 0) U 1 u x := by
  simp [covariantWilson, varMul, covSymmetricDifference, covShift, covShiftAdj]

theorem coeffBounds_zero (Ω : Coefficients d N) {B0 B1 : ℝ} (hΩ : ConnectionBounds Ω B0 B1) :
    CoeffBounds (fun _ _ => 0) (fun _ _ => 0) Ω 0 0 0 B0 B1 where
  c_bound j y v := by simp
  c_lip j y z v := by simp
  c'_bound j y v := by simp
  c'_lip j y z v := by simp
  c_deriv j y v := by simpa using hasDerivAt_const (0 : ℝ) (0 : Fin N → ℂ)
  Ω_bounds := hΩ

theorem densitySymmetricDirac_zero (Ω : Coefficients d N) (ψ : (Fin d → ℝ) → (Fin N → ℂ))
    (y : Fin d → ℝ) : densitySymmetricDirac (fun _ _ => 0) Ω ψ y = 0 := by
  simp [densitySymmetricDirac, covDeriv, lineDeriv]

/-- **`lem:supp-general-core`, `eq:Wilson-core-smallness`** (`L²` form, cell-average sampling):
`‖𝒥⁰_h W^Ω_h S_h ψ‖²_{L²} ≤ K h² ‖ψ‖²_{H²}`, i.e. `‖W^Ω_h S_h ψ‖_h ≤ √K h ‖ψ‖_{H²}` (the
`ℓ²` norm with cell weight `hᵈ`, see `lintegral_comp_cellIdx`). -/
theorem lintegral_covWilsonTerm_cellAvg_le {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {Ω : Coefficients d N} {B0 B1 CU : ℝ} (hΩ : ConnectionBounds Ω B0 B1) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hCU : 0 ≤ CU) {U : Links d N} (hU : LinkExpansion h U Ω CU)
    {ψ : (Fin d → ℝ) → (Fin N → ℂ)} (hψ : ContDiff ℝ 2 ψ) :
    ∫⁻ y, ‖covWilsonTerm h U (cellAvg h ψ) (cellIdx h y)‖ₑ ^ 2 ≤
      coreL2Constant d 0 0 0 B0 B1 CU 1 1 * ENNReal.ofReal (h ^ 2) * sobolevSqH2 ψ := by
  have h1 := lintegral_covariantWilson_cellAvg_sub_densitySymmetricDirac_le (ϖ := 1) hh hh1
    (coeffBounds_zero Ω hΩ) le_rfl le_rfl le_rfl hB0 hB1 hCU zero_le_one hU
    (Γ := 1) (fun v => by rw [Matrix.one_mulVec, one_mul]) hψ
  simp only [densitySymmetricDirac_zero, sub_zero] at h1
  simpa only [covWilsonTerm_eq_covariantWilson] using h1

/-! ### The discrete `ℓ²` norm with cell weight `hᵈ` -/

theorem iUnion_cell {h : ℝ} : (⋃ x : Fin d → ℤ, cell h x) = univ := by
  ext y
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨cellIdx h y, mem_cell_cellIdx h y⟩

theorem pairwise_disjoint_cell (h : ℝ) :
    Pairwise (Function.onFun Disjoint (cell (d := d) h)) := by
  intro x x' hxx'
  rw [Function.onFun, Set.disjoint_left]
  intro y hy hy'
  exact hxx' (hy.symm.trans hy')

/-- **The piecewise-constant reconstruction is isometric**: `∫ G(cellIdx h y) dy = hᵈ Σ_x G(x)`;
in particular `‖𝒥⁰_h u‖²_{L²} = hᵈ Σ_x ‖u(x)‖² = ‖u‖²_h`. -/
theorem lintegral_comp_cellIdx {h : ℝ} (hh : 0 < h) (G : (Fin d → ℤ) → ℝ≥0∞) :
    ∫⁻ y, G (cellIdx h y) = ENNReal.ofReal (h ^ d) * ∑' x, G x := by
  rw [← setLIntegral_univ, ← iUnion_cell (h := h),
    lintegral_iUnion (measurableSet_cell h) (pairwise_disjoint_cell h), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [setLIntegral_congr_fun (measurableSet_cell h x) (g := fun _ => G x)
    (fun y hy => by rw [show cellIdx h y = x from hy]), setLIntegral_const, volume_cell hh,
    mul_comm]

/-- **`eq:Wilson-core-smallness` in the paper's discrete norm**:
`hᵈ Σ_x ‖W^Ω_h S_h ψ (x)‖² ≤ K h² ‖ψ‖²_{H²}`. -/
theorem wilsonCore_smallness {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {Ω : Coefficients d N} {B0 B1 CU : ℝ} (hΩ : ConnectionBounds Ω B0 B1) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hCU : 0 ≤ CU) {U : Links d N} (hU : LinkExpansion h U Ω CU)
    {ψ : (Fin d → ℝ) → (Fin N → ℂ)} (hψ : ContDiff ℝ 2 ψ) :
    ENNReal.ofReal (h ^ d) * ∑' x, ‖covWilsonTerm h U (cellAvg h ψ) x‖ₑ ^ 2 ≤
      coreL2Constant d 0 0 0 B0 B1 CU 1 1 * ENNReal.ofReal (h ^ 2) * sobolevSqH2 ψ := by
  rw [← lintegral_comp_cellIdx hh (fun x => ‖covWilsonTerm h U (cellAvg h ψ) x‖ₑ ^ 2)]
  exact lintegral_covWilsonTerm_cellAvg_le hh hh1 hΩ hB0 hB1 hCU hU hψ

/-! ### Composition with the density-symmetric identity -/

/-- **`lem:supp-general-core`, `eq:supp-general-core`, geometric form.**  For the Clifford
coefficients `c^j = E_a^j γ_a` of a frame `E` (coframe `e = E⁻¹`, positive volume density) and the
Levi-Civita spin connection `Ω` of the frame, the cell-averaged covariant Wilson operator
approximates the density-conjugated geometric Dirac operator `U_ρ D_g U_ρ⁻¹ = ρ^{1/2} D_g ρ^{-1/2}`
in `L²` with error `O(h) ‖ψ‖_{H²}`. -/
theorem lintegral_covariantWilson_cellAvg_sub_geometricDirac_le {h ϖ : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) (E e : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (γ : Fin d → Matrix (Fin N) (Fin N) ℂ) (c' : Coefficients d N) {C0 C1 C2 B0 B1 CU G0 : ℝ}
    (hb : CoeffBounds (DensitySymmetricSpinDirac.cliffordField E γ) c'
      (DensitySymmetricSpinDirac.spinConnectionField E e γ) C0 C1 C2 B0 B1)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hCU : 0 ≤ CU) (hG0 : 0 ≤ G0) {U : Links d N}
    (hU : LinkExpansion h U (DensitySymmetricSpinDirac.spinConnectionField E e γ) CU)
    {Γ : Matrix (Fin N) (Fin N) ℂ} (hΓ : ∀ v, ‖Γ *ᵥ v‖ ≤ G0 * ‖v‖)
    (hEe : ∀ y, E y * e y = 1) (hE : ∀ a b, Differentiable ℝ (fun y => E y a b))
    (he : ∀ a b, Differentiable ℝ (fun y => e y a b)) (hdet : ∀ y, 0 < (e y).det)
    (hγ : DensitySymmetricSpinDirac.IsClifford γ)
    {ψ : (Fin d → ℝ) → (Fin N → ℂ)} (hψ : ContDiff ℝ 2 ψ) :
    ∫⁻ y, ‖covariantWilson h ϖ (DensitySymmetricSpinDirac.cliffordField E γ) U Γ
        (cellAvg h ψ) (cellIdx h y) -
        ((DensitySymmetricSpinDirac.halfDensity e y : ℝ) : ℂ) •
          DensitySymmetricSpinDirac.geometricDirac E e γ
            (fun z => (((DensitySymmetricSpinDirac.halfDensity e z)⁻¹ : ℝ) : ℂ) • ψ z) y‖ₑ ^ 2 ≤
      coreL2Constant d C0 C1 C2 B0 B1 CU G0 ϖ * ENNReal.ofReal (h ^ 2) * sobolevSqH2 ψ := by
  have h1 := lintegral_covariantWilson_cellAvg_sub_densitySymmetricDirac_le (ϖ := ϖ) hh hh1 hb
    hC0 hC1 hC2 hB0 hB1 hCU hG0 hU hΓ hψ
  refine le_of_eq_of_le (lintegral_congr fun y => ?_) h1
  rw [DensitySymmetricSpinDirac.densitySymmetric_identity (E := E) (e := e) (γ := γ)
    isOpen_univ (mem_univ y) (fun z _ => hEe z) (fun a b => (hE a b) y) (fun a b => (he a b) y)
    (hdet y) hγ ψ ((hψ.differentiable (by norm_num)) y)]

open scoped Matrix.Norms.Operator in
/-- **`lem:supp-general-core`, both clauses, with exact spin parallel transport links**
(`eq:supp-covariant-differences`: `U_j(x)` is the exact inverse transport of the anti-Hermitian
Levi-Civita spin connection along the lattice edge).  The second-order link expansion is derived
(`ExactSpinTransport.linkExpansion_of_exactTransport`), and both `eq:supp-general-core` (against
`ρ^{1/2} D_g ρ^{-1/2}`) and `eq:Wilson-core-smallness` (in the discrete norm with cell weight
`hᵈ`) hold with `O(h)` errors in the Sobolev norm `‖ψ‖_{H²} ≤ ‖ψ‖_{H³}`. -/
theorem supp_general_core_exactTransport {h ϖ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (E e : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (γ : Fin d → Matrix (Fin N) (Fin N) ℂ) (c' : Coefficients d N) {C0 C1 C2 B0 B1 G0 : ℝ}
    (hb : CoeffBounds (DensitySymmetricSpinDirac.cliffordField E γ) c'
      (DensitySymmetricSpinDirac.spinConnectionField E e γ) C0 C1 C2 B0 B1)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hG0 : 0 ≤ G0)
    (hanti : ∀ j y, (DensitySymmetricSpinDirac.spinConnectionField E e γ j y)ᴴ =
      -DensitySymmetricSpinDirac.spinConnectionField E e γ j y)
    {U : Links d N}
    (hU : ExactSpinTransport.IsExactInverseTransport h U
      (DensitySymmetricSpinDirac.spinConnectionField E e γ))
    {Γ : Matrix (Fin N) (Fin N) ℂ} (hΓ : ∀ v, ‖Γ *ᵥ v‖ ≤ G0 * ‖v‖)
    (hEe : ∀ y, E y * e y = 1) (hE : ∀ a b, Differentiable ℝ (fun y => E y a b))
    (he : ∀ a b, Differentiable ℝ (fun y => e y a b)) (hdet : ∀ y, 0 < (e y).det)
    (hγ : DensitySymmetricSpinDirac.IsClifford γ)
    {ψ : (Fin d → ℝ) → (Fin N → ℂ)} (hψ : ContDiff ℝ 2 ψ) :
    (∫⁻ y, ‖covariantWilson h ϖ (DensitySymmetricSpinDirac.cliffordField E γ) U Γ
        (cellAvg h ψ) (cellIdx h y) -
        ((DensitySymmetricSpinDirac.halfDensity e y : ℝ) : ℂ) •
          DensitySymmetricSpinDirac.geometricDirac E e γ
            (fun z => (((DensitySymmetricSpinDirac.halfDensity e z)⁻¹ : ℝ) : ℂ) • ψ z) y‖ₑ ^ 2 ≤
      coreL2Constant d C0 C1 C2 B0 B1 (ExactSpinTransport.transportConstant N B0 B1) G0 ϖ *
        ENNReal.ofReal (h ^ 2) * sobolevSqH3 ψ) ∧
    ENNReal.ofReal (h ^ d) * ∑' x, ‖covWilsonTerm h U (cellAvg h ψ) x‖ₑ ^ 2 ≤
      coreL2Constant d 0 0 0 B0 B1 (ExactSpinTransport.transportConstant N B0 B1) 1 1 *
        ENNReal.ofReal (h ^ 2) * sobolevSqH2 ψ := by
  have hCU : 0 ≤ ExactSpinTransport.transportConstant N B0 B1 := by
    unfold ExactSpinTransport.transportConstant
    positivity
  have hL := ExactSpinTransport.linkExpansion_of_exactTransport h hh hh1 U _ B0 B1 hB0 hB1
    hb.Ω_bounds hanti hU
  refine ⟨?_, wilsonCore_smallness hh hh1 hb.Ω_bounds hB0 hB1 hCU hL hψ⟩
  refine (lintegral_covariantWilson_cellAvg_sub_geometricDirac_le hh hh1 E e γ c' hb hC0 hC1 hC2
    hB0 hB1 hCU hG0 hL hΓ hEe hE he hdet hγ hψ).trans ?_
  gcongr
  exact sobolevSqH2_le_H3 ψ

/-! ### Non-vacuity -/

/-- Non-vacuity of the hypotheses of the `L²` core estimate: the flat operator with
`c^j = 1`, trivial transport and `Γ = 1` on `ℝ²` (any `0 < h ≤ 1`, any `C²` spinor). -/
example {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {ψ : (Fin 2 → ℝ) → (Fin 2 → ℂ)}
    (hψ : ContDiff ℝ 2 ψ) :
    ∫⁻ y, ‖covariantWilson h 1 (fun _ _ => 1) (fun _ _ => 1) 1 (cellAvg h ψ) (cellIdx h y) -
        densitySymmetricDirac (fun _ _ => 1) (fun _ _ => 0) ψ y‖ₑ ^ 2 ≤
      coreL2Constant 2 1 0 0 0 0 0 1 1 * ENNReal.ofReal (h ^ 2) * sobolevSqH2 ψ := by
  have hb : CoeffBounds (d := 2) (N := 2) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0)
      1 0 0 0 0 :=
    { c_bound := fun j y v => by simp
      c_lip := fun j y z v => by simp
      c'_bound := fun j y v => by simp
      c'_lip := fun j y z v => by simp
      c_deriv := fun j y v => by simpa using hasDerivAt_const (0 : ℝ) v
      Ω_bounds := ⟨fun j y v => by simp, fun j y z v => by simp⟩ }
  have hU : LinkExpansion (d := 2) (N := 2) h (fun _ _ => 1) (fun _ _ => 0) 0 :=
    fun j x v => ⟨by simp, by simp⟩
  exact lintegral_covariantWilson_cellAvg_sub_densitySymmetricDirac_le hh hh1 hb zero_le_one
    le_rfl le_rfl le_rfl le_rfl le_rfl zero_le_one hU (fun v => by rw [Matrix.one_mulVec, one_mul])
    hψ

end RenewalGeometry.CovariantWilsonCoreL2
