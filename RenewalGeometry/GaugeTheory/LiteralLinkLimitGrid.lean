/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.LiteralLinkLimitPassage
import RenewalGeometry.Analysis.PlaquetteBCHExpansion

/-!
# Grid identities and cutoff-uniform bounds for the literal-link limit
  (infrastructure for `thm:main-literal-link-compactness`; emergent-spacetime manuscript)

Complex `n × n` matrix arrays on the periodic grid `(ℤ/N)³` (`h = 1/N`, Frobenius norm), as in
`LiteralLink`.

* `sobSq_one_eq`: `‖u‖²_{1,h} = ‖u‖_h² + Σ_i ‖D_i⁺u‖_h²`.
* `gp k u g = h³ Σ_x u(x) e_k(x/N) g(x)`: the grid product tested against a Fourier mode.
* `StrongSeq`, `WeakSeq`: strongly / weakly convergent sequences of time-dependent grid arrays on
  `(0,T] × 𝕋³` with cutoff-uniform bounds; `tendsto_gp` is the weak–strong passage
  (`tendsto_pairing_modChar`) in this language; `StrongSeq.one`, `StrongSeq.smul_zero`,
  `StrongSeq.shiftBack`, `StrongSeq.toWeak`, `StrongSeq.comp`, `WeakSeq.comp`.
* The literal records: `linkU A = exp(hA)`, `linkZ A = (U − I)/h`, the electric record
  `elecRec` (`E U = (∂ₜU + A₀U − U S_iA₀)/h`) and the magnetic record `magRec`
  (`h⁻²`-logarithmic plaquette coefficient).
* `gp_linkTime`: the tested **exact electric identity**
  `⟨∂ₜZ⟩ = ⟨E⟩ + Σ_c⟨hZ_{cb} E_{ac}⟩ + N(ζ̄ − 1)⟨A₀⟩ + ζ̄ Σ_c⟨(S_i⁻¹Z_{ac}) A₀_{cb}⟩ − Σ_c⟨Z_{cb} A₀_{ac}⟩`
  (`ζ = e_k(e_i/N)`); `gp_magRec`: the tested **plaquette decomposition**
  `⟨F_{ij}⟩ = N(ζ̄_i − 1)⟨A_j⟩ − N(ζ̄_j − 1)⟨A_i⟩ + Σ_c⟨A_i A_j⟩ − Σ_c⟨A_j A_i⟩ + ⟨R⟩`.
* `sum_norm_magRem_le`, `sum_norm_cube_le`: `h³Σ_x ‖R‖ ≤ h · C(‖A‖²_{1,h} + Σ‖A‖³_{L³_h})` and
  `‖A‖³_{L³_h} ≤ ‖A‖_h · n√K ‖A‖²_{1,h}` on the chart `h‖A‖ ≤ 1/16`.
-/

open MeasureTheory Filter Topology UnitAddTorus
open scoped ComplexConjugate Matrix.Norms.Frobenius

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.LiteralLinkLimit

open PeriodicGridSobolev LatticeTorusPlancherel GridAubinLions LiteralLink LiteralLinkCompactness

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### The grid `H¹` norm -/

theorem multiIndices_one : multiIndices 1 =
    {0, Pi.single 0 1, Pi.single 1 1, Pi.single 2 1} := by
  ext α
  rw [mem_multiIndices]
  simp only [Finset.mem_insert, Finset.mem_singleton, deg]
  constructor
  · intro h
    have h0 : α 0 ≤ 1 := by omega
    have h1 : α 1 ≤ 1 := by omega
    have h2 : α 2 ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h0 with a | a <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with b | b <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with c | c
    all_goals first
      | omega
      | (left; funext i; fin_cases i <;> simp [a, b, c] <;> done)
      | (right; left; funext i; fin_cases i <;> simp [a, b, c] <;> done)
      | (right; right; left; funext i; fin_cases i <;> simp [a, b, c] <;> done)
      | (right; right; right; funext i; fin_cases i <;> simp [a, b, c] <;> done)
  · rintro (rfl | rfl | rfl | rfl) <;> simp

variable {N : ℕ} [NeZero N] {n : ℕ}

theorem gridWeight_one (k : Grid N) : gridWeight 1 k = 1 + ∑ i, ‖sym i k‖ ^ 2 := by
  rw [gridWeight, multiIndices_one]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [dsym, Fin.sum_univ_three]
  ring

/-- `‖u‖²_{1,h} = ‖u‖_h² + Σ_i ‖D_i⁺u‖_h²`. -/
theorem sobSq_one_eq (u : Grid N → ℂ) : sobSq 1 u = gridNormSq u + coordForm u := by
  rw [sobSq_eq_weight, gridNormSq_eq_sum_dft, coordForm_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gridWeight_one]; ring

theorem sum_sobSq_one_eq (A : MatArr N n) :
    ∑ a, ∑ b, sobSq 1 (entry A a b) = matNormSq A + ∑ j, matNormSq (matDp j A) := by
  simp only [sobSq_one_eq, Finset.sum_add_distrib]
  congr 1
  have := sum_entry_coordForm A
  rw [Fintype.sum_prod_type] at this
  exact this

/-! ### Elementary arrays -/

/-- The constant grid array `1`. -/
def oneArr : Grid N → ℂ := fun _ => 1

theorem interp_oneArr : interp (oneArr (N := N)) = 1 := by
  have h := interp_latticeChar (N := N) 0
  have e : (fun x => latticeChar (0 : Grid N) x) = oneArr := by
    funext x; simp [latticeChar, oneArr]
  rw [e] at h
  rw [h]
  have : freqVec (0 : Grid N) = 0 := by funext i; simp [freqVec, freq]
  rw [this, mFourier_zero]

theorem coordForm_oneArr : coordForm (oneArr (N := N)) = 0 := by
  simp [coordForm, gridNormSq, Dp_apply, oneArr]

theorem gridNormSq_oneArr : gridNormSq (oneArr (N := N)) = 1 := by
  simp only [gridNormSq, oneArr, norm_one, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  have : (Fintype.card (Grid N) : ℝ) = (N : ℝ) ^ 3 := by
    simp [Fintype.card_fun, ZMod.card]
  rw [this, inv_mul_cancel₀ (by have := NeZero.ne N; positivity)]

/-- The backward shift `(S_i⁻¹ u)(x) = u(x − e_i)`. -/
def shiftBack (i : Fin 3) (u : Grid N → ℂ) : Grid N → ℂ := fun x => u (x - unit i)

theorem sum_sub_reindex (f : Grid N → ℝ) (a : Grid N) : ∑ x, f (x - a) = ∑ x, f x :=
  (Equiv.subRight a).sum_comp f

theorem gridNormSq_shiftBack (i : Fin 3) (u : Grid N → ℂ) :
    gridNormSq (shiftBack i u) = gridNormSq u := by
  simp only [gridNormSq, shiftBack]
  rw [sum_sub_reindex (fun x => ‖u x‖ ^ 2)]

theorem Dp_shiftBack (i j : Fin 3) (u : Grid N → ℂ) :
    Dp j (shiftBack i u) = shiftBack i (Dp j u) := by
  funext x
  simp only [Dp_apply, shiftBack]
  congr 2
  abel_nf

theorem coordForm_shiftBack (i : Fin 3) (u : Grid N → ℂ) :
    coordForm (shiftBack i u) = coordForm u := by
  simp only [coordForm, Dp_shiftBack, gridNormSq_shiftBack]

theorem gridNormSq_shiftBack_sub (i : Fin 3) (u : Grid N → ℂ) :
    gridNormSq (shiftBack i u - u) = ((N : ℝ) ^ 2)⁻¹ * gridNormSq (Dp i u) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hpt : ∀ x, ‖(shiftBack i u - u) x‖ ^ 2 = ((N : ℝ) ^ 2)⁻¹ * ‖Dp i u (x - unit i)‖ ^ 2 := by
    intro x
    simp only [Pi.sub_apply, shiftBack, Dp_apply, sub_add_cancel, norm_mul, Complex.norm_natCast,
      mul_pow]
    rw [norm_sub_rev]
    field_simp
  simp only [gridNormSq, hpt, ← Finset.mul_sum]
  rw [sum_sub_reindex (fun x => ‖Dp i u x‖ ^ 2)]
  ring

theorem gridNormSq_Dp_le_coordForm (i : Fin 3) (u : Grid N → ℂ) :
    gridNormSq (Dp i u) ≤ coordForm u :=
  Finset.single_le_sum (f := fun i => gridNormSq (Dp i u)) (fun _ _ => gridNormSq_nonneg _)
    (Finset.mem_univ i)

/-! ### Tested grid products -/

/-- The grid product tested against a Fourier mode: `h³ Σ_x u(x) e_k(x/N) g(x)`. -/
def gp (k : Fin 3 → ℤ) (u g : Grid N → ℂ) : ℂ :=
  ((N : ℂ) ^ 3)⁻¹ * ∑ x, u x * modChar k x * g x

theorem IsL2Grid.const {T : ℝ} (c : Grid N → ℂ) : IsL2Grid T (fun _ => c) :=
  ⟨fun _ => aestronglyMeasurable_const, integrableOn_const (by simp) (by simp)⟩

/-- The tested product of `L²` grid arrays is integrable in time (odd grid). -/
theorem integrableOn_gp (hN : Odd N) {T : ℝ} {u g : ℝ → Grid N → ℂ} (hu : IsL2Grid T u)
    (hg : IsL2Grid T g) {χ : ℝ → ℂ} (hχm : AEStronglyMeasurable χ (volume.restrict (Set.Ioc 0 T)))
    {C : ℝ} (hχ : ∀ t, ‖χ t‖ ≤ C) (k : Fin 3 → ℤ) :
    IntegrableOn (fun t => χ t * gp k (u t) (g t)) (Set.Ioc 0 T) := by
  have hu' := hu.mul_modChar k
  have hint : Integrable (fun p => χ p.1 * field (fun t x => u t x * modChar k x) p *
      field g p) (cylMeasure T) := by
    have h := (memLp_field_of_isL2Grid hu').integrable_mul (memLp_field_of_isL2Grid hg)
    have hb : Integrable (fun p => χ p.1 * (field (fun t x => u t x * modChar k x) p *
        field g p)) (cylMeasure T) :=
      h.bdd_mul (c := C) hχm.comp_fst (ae_of_all _ fun p => hχ p.1)
    exact hb.congr (ae_of_all _ fun p => by simp only [Pi.mul_apply]; ring)
  have h2 := hint.integral_prod_left
  refine h2.congr (ae_of_all _ fun t => ?_)
  simp only [field]
  have e : ∀ x : UnitAddTorus (Fin 3), χ t * interp (fun x => u t x * modChar k x) x *
      interp (g t) x = χ t * (interp (fun x => u t x * modChar k x) x * interp (g t) x) :=
    fun x => by ring
  simp only [e]
  rw [integral_const_mul, integral_interp_mul hN]
  rfl

/-! ### Strongly and weakly convergent sequences of grid arrays -/

section Seq

variable (Nm : ℕ → ℕ) [∀ m, NeZero (Nm m)] (T : ℝ)

/-- A sequence of time-dependent grid arrays on the grids `N_m` whose interpolants converge
strongly in `L²((0,T] × 𝕋³)` to `U`, with cutoff-uniform `L²_t L²_h` and `L²_t Ḣ¹_h` bounds. -/
structure StrongSeq (u : ∀ m, ℝ → Grid (Nm m) → ℂ) (U : ℝ × UnitAddTorus (Fin 3) → ℂ) :
    Prop where
  isL2 : ∀ m, IsL2Grid T (u m)
  memLp : MemLp U 2 (cylMeasure T)
  tendsto : Tendsto (fun m => ∫ p, ‖field (u m) p - U p‖ ^ 2 ∂cylMeasure T) atTop (𝓝 0)
  cfInt : ∀ m, IntegrableOn (fun t => coordForm (u m t)) (Set.Ioc 0 T)
  cfBdd : ∃ B, ∀ m, ∫ t in Set.Ioc 0 T, coordForm (u m t) ≤ B
  l2Bdd : ∃ B, ∀ m, ∫ t in Set.Ioc 0 T, gridNormSq (u m t) ≤ B

/-- A sequence of time-dependent grid arrays whose interpolants converge weakly in
`L²((0,T] × 𝕋³)` to `G`, with a cutoff-uniform `L²_t L²_h` bound. -/
structure WeakSeq (g : ∀ m, ℝ → Grid (Nm m) → ℂ) (G : ℝ × UnitAddTorus (Fin 3) → ℂ) :
    Prop where
  isL2 : ∀ m, IsL2Grid T (g m)
  weak : WeakL2 (cylMeasure T) (fun m => field (g m)) G
  l2Bdd : ∃ B, ∀ m, ∫ t in Set.Ioc 0 T, gridNormSq (g m t) ≤ B

variable {Nm T}

theorem StrongSeq.toWeak {u : ∀ m, ℝ → Grid (Nm m) → ℂ} {U} (h : StrongSeq Nm T u U) :
    WeakSeq Nm T u U :=
  ⟨h.isL2, weakL2_of_strong (fun m => memLp_field_of_isL2Grid (h.isL2 m)) h.memLp h.tendsto,
    h.l2Bdd⟩

theorem StrongSeq.comp {u : ∀ m, ℝ → Grid (Nm m) → ℂ} {U} (h : StrongSeq Nm T u U)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrongSeq (fun m => Nm (φ m)) T (fun m => u (φ m)) U := by
  obtain ⟨B1, hB1⟩ := h.cfBdd
  obtain ⟨B2, hB2⟩ := h.l2Bdd
  exact ⟨fun m => h.isL2 (φ m), h.memLp, h.tendsto.comp hφ.tendsto_atTop, fun m => h.cfInt (φ m),
    ⟨B1, fun m => hB1 (φ m)⟩, ⟨B2, fun m => hB2 (φ m)⟩⟩

theorem WeakSeq.comp {g : ∀ m, ℝ → Grid (Nm m) → ℂ} {G} (h : WeakSeq Nm T g G)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WeakSeq (fun m => Nm (φ m)) T (fun m => g (φ m)) G := by
  obtain ⟨B, hB⟩ := h.l2Bdd
  exact ⟨fun m => h.isL2 (φ m), h.weak.comp hφ, ⟨B, fun m => hB (φ m)⟩⟩

theorem memLp_one_cyl : MemLp (fun _ : ℝ × UnitAddTorus (Fin 3) => (1 : ℂ)) 2 (cylMeasure T) :=
  memLp_const 1

/-- The constant array `1` (whose interpolant is `1`). -/
theorem StrongSeq.one : StrongSeq Nm T (fun m _ => oneArr) (fun _ => 1) := by
  refine ⟨fun m => IsL2Grid.const _, memLp_one_cyl, ?_, fun m => ?_, ⟨0, fun m => ?_⟩,
    ⟨T ⊔ 0, fun m => ?_⟩⟩
  · have : ∀ m, ∫ p, ‖field (fun _ => (oneArr : Grid (Nm m) → ℂ)) p - 1‖ ^ 2 ∂cylMeasure T = 0 :=
      fun m => by simp [field, interp_oneArr]
    simp only [this, tendsto_const_nhds]
  · simp only [coordForm_oneArr]; exact integrableOn_const (by simp) (by simp)
  · simp [coordForm_oneArr]
  · simp only [gridNormSq_oneArr, MeasureTheory.integral_const, smul_eq_mul, mul_one]
    rcases le_total T 0 with hT | hT
    · simp [Set.Ioc_eq_empty_of_le hT]
    · simp [Real.volume_real_Ioc_of_le hT, hT]

theorem StrongSeq.cfBdd' {u : ∀ m, ℝ → Grid (Nm m) → ℂ} {U} (h : StrongSeq Nm T u U) :
    ∃ B, 0 ≤ B ∧ ∀ m, ∫ t in Set.Ioc 0 T, coordForm (u m t) ≤ B := by
  obtain ⟨B, hB⟩ := h.cfBdd
  exact ⟨B ⊔ 0, le_sup_right, fun m => (hB m).trans le_sup_left⟩

theorem StrongSeq.l2Bdd' {u : ∀ m, ℝ → Grid (Nm m) → ℂ} {U} (h : StrongSeq Nm T u U) :
    ∃ B, 0 ≤ B ∧ ∀ m, ∫ t in Set.Ioc 0 T, gridNormSq (u m t) ≤ B := by
  obtain ⟨B, hB⟩ := h.l2Bdd
  exact ⟨B ⊔ 0, le_sup_right, fun m => (hB m).trans le_sup_left⟩

theorem coordForm_smul (c : ℂ) (u : Grid N → ℂ) :
    coordForm (fun x => c * u x) = ‖c‖ ^ 2 * coordForm u := by
  simp only [coordForm, gridNormSq, Dp_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  rw [show (N : ℂ) * (c * u (x + unit i) - c * u x) = c * (N * (u (x + unit i) - u x)) by ring,
    norm_mul, mul_pow]
  ring

theorem gridNormSq_smul (c : ℂ) (u : Grid N → ℂ) :
    gridNormSq (fun x => c * u x) = ‖c‖ ^ 2 * gridNormSq u := by
  simp only [gridNormSq, norm_mul, mul_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

/-- Multiplying by scalars `c_m → 0` with `|c_m| ≤ 1` gives a sequence converging strongly to `0`. -/
theorem StrongSeq.smul_zero {u : ∀ m, ℝ → Grid (Nm m) → ℂ} {U} (h : StrongSeq Nm T u U)
    (c : ℕ → ℂ) (hc : Tendsto c atTop (𝓝 0)) (hc1 : ∀ m, ‖c m‖ ≤ 1) :
    StrongSeq Nm T (fun m t x => c m * u m t x) (fun _ => 0) := by
  obtain ⟨B1, hB1p, hB1⟩ := h.cfBdd'
  obtain ⟨B2, hB2p, hB2⟩ := h.l2Bdd'
  have hc2 : ∀ m, ‖c m‖ ^ 2 ≤ 1 := fun m => by
    have := hc1 m; have := norm_nonneg (c m); nlinarith
  have hisL2 : ∀ m, IsL2Grid T (fun t x => c m * u m t x) := fun m => by
    refine ⟨fun x => ((h.isL2 m).1 x).const_mul _, ?_⟩
    simp only [gridNormSq_smul]
    exact (h.isL2 m).2.const_mul _
  have hfield : ∀ m p, field (fun t x => c m * u m t x) p = c m * field (u m) p := by
    intro m p
    simp only [field, interp]
    simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (fun x => c m * u m p.1 x) = c m • u m p.1 from rfl, dft_smul, smul_eq_mul]
    ring
  refine ⟨hisL2, memLp_const 0, ?_, fun m => ?_, ⟨B1, fun m => ?_⟩, ⟨B2, fun m => ?_⟩⟩
  · have e : ∀ m, ∫ p, ‖field (fun t x => c m * u m t x) p - 0‖ ^ 2 ∂cylMeasure T =
        ‖c m‖ ^ 2 * ∫ t in Set.Ioc 0 T, gridNormSq (u m t) := by
      intro m
      simp only [hfield, sub_zero, norm_mul, mul_pow]
      rw [integral_const_mul, integral_norm_field_sq (h.isL2 m)]
    simp only [e]
    have h0 : Tendsto (fun m => ‖c m‖ ^ 2 * B2) atTop (𝓝 0) := by
      simpa using ((hc.norm).pow 2).mul_const B2
    refine squeeze_zero (fun m => mul_nonneg (sq_nonneg _) ?_) (fun m => ?_) h0
    · exact integral_nonneg fun _ => gridNormSq_nonneg _
    · exact mul_le_mul_of_nonneg_left (hB2 m) (sq_nonneg _)
  · simp only [coordForm_smul]; exact (h.cfInt m).const_mul _
  · simp only [coordForm_smul]
    rw [integral_const_mul]
    calc ‖c m‖ ^ 2 * ∫ t in Set.Ioc 0 T, coordForm (u m t) ≤ 1 * B1 :=
          mul_le_mul (hc2 m) (hB1 m) (integral_nonneg fun _ => coordForm_nonneg _) zero_le_one
      _ = B1 := one_mul _
  · simp only [gridNormSq_smul]
    rw [integral_const_mul]
    calc ‖c m‖ ^ 2 * ∫ t in Set.Ioc 0 T, gridNormSq (u m t) ≤ 1 * B2 :=
          mul_le_mul (hc2 m) (hB2 m) (integral_nonneg fun _ => gridNormSq_nonneg _) zero_le_one
      _ = B2 := one_mul _

/-- Backward shifts of a strongly convergent sequence converge to the same limit. -/
theorem StrongSeq.shiftBack {u : ∀ m, ℝ → Grid (Nm m) → ℂ} {U} (h : StrongSeq Nm T u U)
    (hN : Tendsto Nm atTop atTop) (i : Fin 3) :
    StrongSeq Nm T (fun m t => LiteralLinkLimit.shiftBack i (u m t)) U := by
  obtain ⟨B1, hB1p, hB1⟩ := h.cfBdd'
  have hisL2 : ∀ m, IsL2Grid T (fun t => LiteralLinkLimit.shiftBack i (u m t)) := fun m => by
    refine ⟨fun x => (h.isL2 m).1 _, ?_⟩
    simp only [gridNormSq_shiftBack]; exact (h.isL2 m).2
  refine ⟨hisL2, h.memLp, ?_, fun m => ?_, ⟨B1, fun m => ?_⟩, ?_⟩
  · -- `‖field (S⁻¹u) − field u‖² = h² ∫ ‖D_i⁺u‖_h² ≤ h² B₁`
    have hd : ∀ m, ∫ p, ‖field (fun t => LiteralLinkLimit.shiftBack i (u m t)) p -
        field (u m) p‖ ^ 2 ∂cylMeasure T ≤ ((Nm m : ℝ) ^ 2)⁻¹ * B1 := by
      intro m
      have hsub := (hisL2 m).sub (h.isL2 m)
      have e := integral_norm_field_sq hsub
      rw [field_sub] at e
      rw [e]
      simp only [gridNormSq_shiftBack_sub]
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (integral_mono_of_nonneg (ae_of_all _ fun _ => gridNormSq_nonneg _) (h.cfInt m)
        (ae_of_all _ fun t => gridNormSq_Dp_le_coordForm i _)).trans (hB1 m)
    have h0 : Tendsto (fun m => 2 * (((Nm m : ℝ) ^ 2)⁻¹ * B1) +
        2 * ∫ p, ‖field (u m) p - U p‖ ^ 2 ∂cylMeasure T) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m => ((Nm m : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp
          (tendsto_natCast_atTop_atTop.comp hN))
      simpa using ((h1.mul_const B1).const_mul 2).add (h.tendsto.const_mul 2)
    refine squeeze_zero (fun m => integral_nonneg fun _ => by positivity) (fun m => ?_) h0
    have htri := integral_norm_sub_sq_le (memLp_field_of_isL2Grid (hisL2 m))
      (memLp_field_of_isL2Grid (h.isL2 m)) h.memLp
    linarith [hd m]
  · simp only [coordForm_shiftBack]; exact h.cfInt m
  · simp only [coordForm_shiftBack]; exact hB1 m
  · obtain ⟨B2, hB2⟩ := h.l2Bdd
    exact ⟨B2, fun m => by simp only [gridNormSq_shiftBack]; exact hB2 m⟩

/-- **Weak–strong passage** for tested grid products of a strongly and a weakly convergent
sequence (odd grids `N_m → ∞`). -/
theorem tendsto_gp (hodd : ∀ m, Odd (Nm m)) (hN : Tendsto Nm atTop atTop)
    {u g : ∀ m, ℝ → Grid (Nm m) → ℂ} {U G : ℝ × UnitAddTorus (Fin 3) → ℂ}
    (hs : StrongSeq Nm T u U) (hw : WeakSeq Nm T g G) {χ : ℝ → ℂ}
    (hχm : AEStronglyMeasurable χ (volume.restrict (Set.Ioc 0 T))) {C : ℝ} (hC : 0 ≤ C)
    (hχ : ∀ t, ‖χ t‖ ≤ C) (k : Fin 3 → ℤ) :
    Tendsto (fun m => ∫ t in Set.Ioc 0 T, χ t * gp k (u m t) (g m t)) atTop
      (𝓝 (∫ p, χ p.1 * (mFourier k p.2 * U p) * G p ∂cylMeasure T)) := by
  obtain ⟨B1, -, hB1⟩ := hs.cfBdd'
  obtain ⟨B2, hB2⟩ := hw.l2Bdd
  exact tendsto_pairing_modChar hodd hN u g hs.isL2 hw.isL2 hs.memLp hs.tendsto (B := B1 ⊔ B2)
    hs.cfInt (fun m => (hB1 m).trans le_sup_left) hw.weak (fun m => (hB2 m).trans le_sup_right)
    hχm hC hχ k

end Seq

/-! ### The literal records -/

/-- The links `U(x) = exp(h A(x))`, `h = 1/N`. -/
def linkU (A : MatArr N n) : MatArr N n := fun x => NormedSpace.exp (((N : ℝ)⁻¹) • A x)

/-- The link coordinate `Z = (U − I)/h` (`eq:main-link-coordinate`). -/
def linkZ (A : MatArr N n) : MatArr N n := fun x => ((N : ℝ)⁻¹)⁻¹ • (linkU A x - 1)

/-- The literal electric record in direction `i`, defined by the exact link identity
`E U = (∂ₜU + A₀ U − U S_iA₀)/h` (`eq:supp-literal-electric-definition`, in the normalization of
`LiteralLink.electricRecord`), for links `U = exp(hA)` with time derivative `U'`. -/
def elecRec (i : Fin 3) (A U' A₀ : MatArr N n) : MatArr N n :=
  electricRecord ((N : ℝ)⁻¹) (unit i) (linkU A) U' A₀

/-- The literal magnetic record: the `h⁻²` logarithmic coefficient of the plaquette holonomy
`U_i(x) U_j(x+e_i) U_i(x+e_j)⁻¹ U_j(x)⁻¹` on the identity chart. -/
def magRec (i j : Fin 3) (Ai Aj : MatArr N n) : MatArr N n :=
  LogBCH.PlaquetteBCH.plaquetteRecord ((N : ℝ)⁻¹) (unit i) (unit j) Ai Aj

theorem linkZ_eq_linkCoord (A : MatArr N n) (x : Grid N) :
    linkZ A x = linkCoord ((N : ℝ)⁻¹) (A x) := rfl

theorem hN_pos : (0 : ℝ) < (N : ℝ)⁻¹ :=
  inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N)))

/-- The exact link evolution (`eq:supp-literal-Z-equation`) with `E U = E + h E Z`:
`h⁻¹ U' = E + h (E Z) + D_i⁺A₀ + Z S_iA₀ − A₀ Z`. -/
theorem linkTime_eq (i : Fin 3) (A U' A₀ : MatArr N n) (x : Grid N) :
    ((N : ℝ)⁻¹)⁻¹ • U' x = elecRec i A U' A₀ x + (N : ℝ)⁻¹ • (elecRec i A U' A₀ x * linkZ A x)
      + matDp i A₀ x + linkZ A x * A₀ (x + unit i) - A₀ x * linkZ A x := by
  have hunit : IsUnit (linkU A x) := by unfold linkU; exact NormedSpace.isUnit_exp _
  have h := link_Z_identity ((N : ℝ)⁻¹) (unit i) (linkU A) U' (elecRec i A U' A₀) A₀ x
    (electricRecord_mul hunit)
  rw [h]
  have hU : linkU A x = 1 + (N : ℝ)⁻¹ • linkZ A x := by
    simp only [linkZ, smul_smul, mul_inv_cancel₀ (hN_pos (N := N)).ne', one_smul]
    abel
  simp only [linkZ] at hU ⊢
  rw [show elecRec i A U' A₀ x * linkU A x =
      elecRec i A U' A₀ x * (1 + (N : ℝ)⁻¹ • (((N : ℝ)⁻¹)⁻¹ • (linkU A x - 1))) by
    rw [← hU]]
  simp only [mul_add, mul_one, mul_smul_comm]
  rfl

/-! ### Tested identities -/

theorem sum_shift_entry (f : Grid N → ℂ) (k : Fin 3 → ℤ) (i : Fin 3) :
    ∑ x, modChar k x * f (x + unit i) =
      conj (modChar (N := N) k (unit i)) * ∑ x, modChar k x * f x := by
  have := sum_shift_mul_modChar f k i
  simp only [mul_comm (modChar k _)] at this ⊢
  exact this

/-- **Tested exact electric identity** (entry `(a,b)` of `eq:supp-literal-Z-equation`, tested
against `e_k`): with `ζ = e_k(e_i/N)`,
`⟨h⁻¹U'⟩ = ⟨E⟩ + Σ_c ⟨h Z_{cb}, E_{ac}⟩ + N(ζ̄ − 1)⟨A₀⟩ + ζ̄ Σ_c ⟨S_i⁻¹Z_{ac}, A₀_{cb}⟩
  − Σ_c ⟨Z_{cb}, A₀_{ac}⟩`. -/
theorem gp_linkTime (k : Fin 3 → ℤ) (i : Fin 3) (A U' A₀ : MatArr N n) (a b : Fin n) :
    gp k oneArr (entry (fun x => ((N : ℝ)⁻¹)⁻¹ • U' x) a b) =
      gp k oneArr (entry (elecRec i A U' A₀) a b)
      + ∑ c, gp k (fun x => (N : ℂ)⁻¹ * entry (linkZ A) c b x) (entry (elecRec i A U' A₀) a c)
      + (N : ℂ) * (conj (modChar (N := N) k (unit i)) - 1) * gp k oneArr (entry A₀ a b)
      + conj (modChar (N := N) k (unit i)) *
          ∑ c, gp k (shiftBack i (entry (linkZ A) a c)) (entry A₀ c b)
      - ∑ c, gp k (entry (linkZ A) c b) (entry A₀ a c) := by
  set E := elecRec i A U' A₀
  set Z := linkZ A
  set ζ := conj (modChar (N := N) k (unit i))
  have hNc : ((((N : ℝ)⁻¹)⁻¹ : ℝ) : ℂ) = (N : ℂ) := by push_cast; simp
  have hpt : ∀ x, entry (fun x => ((N : ℝ)⁻¹)⁻¹ • U' x) a b x =
      E x a b + (N : ℂ)⁻¹ * ∑ c, E x a c * Z x c b + (N : ℂ) * (A₀ (x + unit i) a b - A₀ x a b)
      + ∑ c, Z x a c * A₀ (x + unit i) c b - ∑ c, A₀ x a c * Z x c b := by
    intro x
    simp only [entry]
    rw [linkTime_eq i A U' A₀ x]
    simp only [matDp, LiteralLink.fwdDiff, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.mul_apply, Complex.real_smul, hNc]
    push_cast
    ring
  have hS3 : ∑ x, oneArr x * modChar k x * ((N : ℂ) * (A₀ (x + unit i) a b - A₀ x a b)) =
      (N : ℂ) * (ζ - 1) * ∑ x, oneArr x * modChar k x * A₀ x a b := by
    have := sum_shift_entry (entry A₀ a b) k i
    simp only [entry] at this
    simp only [oneArr, one_mul, mul_sub, Finset.sum_sub_distrib]
    rw [show ∑ x, modChar k x * ((N : ℂ) * A₀ (x + unit i) a b) =
        (N : ℂ) * ∑ x, modChar k x * A₀ (x + unit i) a b by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring]
    rw [show ∑ x, modChar k x * ((N : ℂ) * A₀ x a b) = (N : ℂ) * ∑ x, modChar k x * A₀ x a b by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring]
    rw [this]; ring
  have hS4 : ∀ c, ∑ x, oneArr x * modChar k x * (Z x a c * A₀ (x + unit i) c b) =
      ζ * ∑ x, shiftBack i (entry Z a c) x * modChar k x * entry A₀ c b x := by
    intro c
    have := sum_shift_entry (fun y => Z (y - unit i) a c * A₀ y c b) k i
    simp only [add_sub_cancel_right] at this
    simp only [oneArr, one_mul, shiftBack, entry]
    rw [this, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  unfold gp
  simp only [hpt]
  have e1 : ∀ x, oneArr x * modChar k x * (E x a b + (N : ℂ)⁻¹ * ∑ c, E x a c * Z x c b +
      (N : ℂ) * (A₀ (x + unit i) a b - A₀ x a b) + ∑ c, Z x a c * A₀ (x + unit i) c b -
      ∑ c, A₀ x a c * Z x c b) =
      oneArr x * modChar k x * E x a b
      + ∑ c, ((N : ℂ)⁻¹ * Z x c b) * modChar k x * E x a c
      + oneArr x * modChar k x * ((N : ℂ) * (A₀ (x + unit i) a b - A₀ x a b))
      + ∑ c, oneArr x * modChar k x * (Z x a c * A₀ (x + unit i) c b)
      - ∑ c, Z x c b * modChar k x * A₀ x a c := by
    intro x
    simp only [oneArr, one_mul, Finset.mul_sum, mul_add, mul_sub]
    congr 1
    · congr 1
      · congr 1
        · congr 1
          exact Finset.sum_congr rfl fun c _ => by ring
    · exact Finset.sum_congr rfl fun c _ => by ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hS3]
  rw [Finset.sum_comm (f := fun x c => (N : ℂ)⁻¹ * Z x c b * modChar k x * E x a c),
    Finset.sum_comm (f := fun x c => oneArr x * modChar k x * (Z x a c * A₀ (x + unit i) c b)),
    Finset.sum_comm (f := fun x c => Z x c b * modChar k x * A₀ x a c)]
  simp only [hS4]
  simp only [entry, mul_add, mul_sub, Finset.mul_sum]
  ring_nf

/-- The plaquette remainder `R = F_{ij} − (D_i⁺A_j − D_j⁺A_i + [A_i, A_j])`. -/
def magRem (i j : Fin 3) (Ai Aj : MatArr N n) : MatArr N n := fun x =>
  magRec i j Ai Aj x - (matDp i Aj x - matDp j Ai x + (Ai x * Aj x - Aj x * Ai x))

/-- **Tested plaquette decomposition**: with `ζ_l = e_k(e_l/N)`,
`⟨F_{ij}⟩ = N(ζ̄_i − 1)⟨A_j⟩ − N(ζ̄_j − 1)⟨A_i⟩ + Σ_c ⟨A_{i,ac}, A_{j,cb}⟩ − Σ_c ⟨A_{j,ac}, A_{i,cb}⟩
  + ⟨R⟩`. -/
theorem gp_magRec (k : Fin 3 → ℤ) (i j : Fin 3) (Ai Aj : MatArr N n) (a b : Fin n) :
    gp k oneArr (entry (magRec i j Ai Aj) a b) =
      (N : ℂ) * (conj (modChar (N := N) k (unit i)) - 1) * gp k oneArr (entry Aj a b)
      - (N : ℂ) * (conj (modChar (N := N) k (unit j)) - 1) * gp k oneArr (entry Ai a b)
      + ∑ c, gp k (entry Ai a c) (entry Aj c b) - ∑ c, gp k (entry Aj a c) (entry Ai c b)
      + gp k oneArr (entry (magRem i j Ai Aj) a b) := by
  have hNc : ((((N : ℝ)⁻¹)⁻¹ : ℝ) : ℂ) = (N : ℂ) := by push_cast; simp
  have hpt : ∀ x, entry (magRec i j Ai Aj) a b x =
      (N : ℂ) * (Aj (x + unit i) a b - Aj x a b) - (N : ℂ) * (Ai (x + unit j) a b - Ai x a b)
      + ∑ c, Ai x a c * Aj x c b - ∑ c, Aj x a c * Ai x c b + entry (magRem i j Ai Aj) a b x := by
    intro x
    simp only [entry, magRem, matDp, LiteralLink.fwdDiff, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.mul_apply, Complex.real_smul, hNc]
    ring
  have hsh : ∀ (f : Grid N → ℂ) (l : Fin 3), ∑ x, oneArr x * modChar k x *
      ((N : ℂ) * (f (x + unit l) - f x)) =
      (N : ℂ) * (conj (modChar (N := N) k (unit l)) - 1) * ∑ x, oneArr x * modChar k x * f x := by
    intro f l
    have := sum_shift_entry f k l
    simp only [oneArr, one_mul, mul_sub, Finset.sum_sub_distrib]
    rw [show ∑ x, modChar k x * ((N : ℂ) * f (x + unit l)) =
        (N : ℂ) * ∑ x, modChar k x * f (x + unit l) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring]
    rw [show ∑ x, modChar k x * ((N : ℂ) * f x) = (N : ℂ) * ∑ x, modChar k x * f x by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring]
    rw [this]; ring
  unfold gp
  simp only [hpt]
  have e1 : ∀ x, oneArr x * modChar k x *
      ((N : ℂ) * (Aj (x + unit i) a b - Aj x a b) - (N : ℂ) * (Ai (x + unit j) a b - Ai x a b)
      + ∑ c, Ai x a c * Aj x c b - ∑ c, Aj x a c * Ai x c b + entry (magRem i j Ai Aj) a b x) =
      oneArr x * modChar k x * ((N : ℂ) * (Aj (x + unit i) a b - Aj x a b))
      - oneArr x * modChar k x * ((N : ℂ) * (Ai (x + unit j) a b - Ai x a b))
      + ∑ c, Ai x a c * modChar k x * Aj x c b - ∑ c, Aj x a c * modChar k x * Ai x c b
      + oneArr x * modChar k x * entry (magRem i j Ai Aj) a b x := by
    intro x
    simp only [oneArr, one_mul, Finset.mul_sum, mul_add, mul_sub]
    congr 1
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun c _ => by ring
    · exact Finset.sum_congr rfl fun c _ => by ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsh (fun y => Aj y a b) i, hsh (fun y => Ai y a b) j]
  rw [Finset.sum_comm (f := fun x c => Ai x a c * modChar k x * Aj x c b),
    Finset.sum_comm (f := fun x c => Aj x a c * modChar k x * Ai x c b)]
  simp only [entry, mul_add, mul_sub, Finset.mul_sum]
  ring_nf

/-! ### Cutoff-uniform bounds -/

/-- `(y₁ + y₂ + y₃ + y₄)³ ≤ 16 (y₁³ + y₂³ + y₃³ + y₄³)` for nonnegative reals. -/
theorem cube_sum_four_le {y₁ y₂ y₃ y₄ : ℝ} (h₁ : 0 ≤ y₁) (h₂ : 0 ≤ y₂) (h₃ : 0 ≤ y₃)
    (h₄ : 0 ≤ y₄) :
    (y₁ + y₂ + y₃ + y₄) ^ 3 ≤ 16 * (y₁ ^ 3 + y₂ ^ 3 + y₃ ^ 3 + y₄ ^ 3) := by
  have two : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := fun a b ha hb => by
    nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]
  have e1 := two y₁ y₂ h₁ h₂
  have e2 := two y₃ y₄ h₃ h₄
  have e3 := two (y₁ + y₂) (y₃ + y₄) (add_nonneg h₁ h₂) (add_nonneg h₃ h₄)
  calc (y₁ + y₂ + y₃ + y₄) ^ 3 = ((y₁ + y₂) + (y₃ + y₄)) ^ 3 := by ring
    _ ≤ 4 * ((y₁ + y₂) ^ 3 + (y₃ + y₄) ^ 3) := e3
    _ ≤ 4 * (4 * (y₁ ^ 3 + y₂ ^ 3) + 4 * (y₃ ^ 3 + y₄ ^ 3)) := by gcongr
    _ = _ := by ring

/-- Pointwise bound on the plaquette remainder on the chart `h‖A‖ ≤ 1/16` (`h ≤ 1`). -/
theorem norm_magRem_le (i j : Fin 3) (Ai Aj : MatArr N n)
    (hAi : ∀ x, (N : ℝ)⁻¹ * ‖Ai x‖ ≤ 1 / 16) (hAj : ∀ x, (N : ℝ)⁻¹ * ‖Aj x‖ ≤ 1 / 16)
    (x : Grid N) :
    ‖magRem i j Ai Aj x‖ ≤ (N : ℝ)⁻¹ * (6 * (‖matDp j Ai x‖ ^ 2 + ‖matDp i Aj x‖ ^ 2)
      + 2 * (‖Ai x‖ ^ 2 + ‖Aj x‖ ^ 2) + 96 * kappa (Matrix (Fin n) (Fin n) ℂ) *
        (‖Ai x‖ ^ 3 + ‖Aj x‖ ^ 3 + ‖Ai (x + unit j)‖ ^ 3 + ‖Aj (x + unit i)‖ ^ 3)) := by
  set h : ℝ := (N : ℝ)⁻¹ with hh
  have hpos : 0 < h := hN_pos
  have hle1 : h ≤ 1 := by
    rw [hh]; exact inv_le_one_of_one_le₀ (Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hs : h * (‖Ai x‖ + ‖Aj x‖ + ‖Ai (x + unit j)‖ + ‖Aj (x + unit i)‖) ≤ 1 / 4 := by
    have := hAi x; have := hAj x; have := hAi (x + unit j); have := hAj (x + unit i)
    nlinarith
  have key := LogBCH.PlaquetteBCH.norm_plaquetteRecord_sub_le hpos (unit i) (unit j) Ai Aj x hs
  have e : magRem i j Ai Aj x = LogBCH.PlaquetteBCH.plaquetteRecord h (unit i) (unit j) Ai Aj x -
      (LogBCH.PlaquetteBCH.fwd h (unit i) Aj x - LogBCH.PlaquetteBCH.fwd h (unit j) Ai x +
        (Ai x * Aj x - Aj x * Ai x)) := rfl
  have ea : LogBCH.PlaquetteBCH.fwd h (unit j) Ai x = matDp j Ai x := rfl
  have eb : LogBCH.PlaquetteBCH.fwd h (unit i) Aj x = matDp i Aj x := rfl
  rw [e]
  rw [ea, eb] at key ⊢
  refine key.trans ?_
  set a := ‖matDp j Ai x‖
  set b := ‖matDp i Aj x‖
  set c := ‖Ai x‖
  set d := ‖Aj x‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hκ : 1 ≤ max ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ 1 := le_max_right _ _
  have hcube := cube_sum_four_le hc hd (norm_nonneg (Ai (x + unit j)))
    (norm_nonneg (Aj (x + unit i)))
  have t1 : 2 * h * (a + b) * (c + d + h * a + h * b) ≤
      h * (6 * (a ^ 2 + b ^ 2) + 2 * (c ^ 2 + d ^ 2)) := by
    have hab : h * a + h * b ≤ a + b := by nlinarith
    have u1 : 2 * (a + b) * (c + d) ≤ 2 * (a ^ 2 + b ^ 2) + 2 * (c ^ 2 + d ^ 2) := by
      nlinarith [sq_nonneg (a + b - (c + d)), sq_nonneg (a - b), sq_nonneg (c - d)]
    have u2 : 2 * (a + b) * (h * a + h * b) ≤ 4 * (a ^ 2 + b ^ 2) := by
      have := mul_le_mul_of_nonneg_left hab (by positivity : (0 : ℝ) ≤ 2 * (a + b))
      nlinarith [sq_nonneg (a - b)]
    have u3 : 2 * (a + b) * (c + d + h * a + h * b) ≤ 6 * (a ^ 2 + b ^ 2) + 2 * (c ^ 2 + d ^ 2) := by
      have e : 2 * (a + b) * (c + d + h * a + h * b) =
          2 * (a + b) * (c + d) + 2 * (a + b) * (h * a + h * b) := by ring
      rw [e]; linarith
    calc 2 * h * (a + b) * (c + d + h * a + h * b) = h * (2 * (a + b) * (c + d + h * a + h * b)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left u3 hpos.le
  have t2 : 6 * max ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ 1 * h *
      (c + d + ‖Ai (x + unit j)‖ + ‖Aj (x + unit i)‖) ^ 3
      ≤ h * (96 * kappa (Matrix (Fin n) (Fin n) ℂ) *
        (c ^ 3 + d ^ 3 + ‖Ai (x + unit j)‖ ^ 3 + ‖Aj (x + unit i)‖ ^ 3)) := by
    have hk : kappa (Matrix (Fin n) (Fin n) ℂ) = max ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ 1 := rfl
    rw [hk]
    have := mul_le_mul_of_nonneg_left hcube
      (by positivity : (0 : ℝ) ≤ 6 * max ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ 1 * h)
    refine this.trans (le_of_eq ?_)
    ring
  refine (add_le_add t1 t2).trans (le_of_eq ?_)
  ring

/-- `h³ Σ_x ‖A(x)‖³ ≤ ‖A‖_h · n√K · Σ_{a,b} ‖A_{ab}‖²_{1,h}`. -/
theorem sum_norm_cube_le (A : MatArr N n) :
    ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖A x‖ ^ 3 ≤
      matNorm A * ((n : ℝ) * Real.sqrt Kprod * ∑ a, ∑ b, sobSq 1 (entry A a b)) := by
  have hcs := grid_cs (N := N) (fun x => ‖A x‖) (fun x => ‖A x‖ ^ 2)
  have h4 := sum_norm_pow_four_le A
  have hsqrt4 : Real.sqrt (((N : ℝ) ^ 3)⁻¹ * ∑ x, (‖A x‖ ^ 2) ^ 2) ≤
      (n : ℝ) * Real.sqrt Kprod * ∑ a, ∑ b, sobSq 1 (entry A a b) := by
    have e : ∀ x, (‖A x‖ ^ 2) ^ 2 = ‖A x‖ ^ 4 := fun x => by ring
    simp only [e]
    have hS : 0 ≤ ∑ a, ∑ b, sobSq 1 (entry A a b) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sobSq_nonneg _ _
    refine Real.sqrt_le_iff.2 ⟨by have := Real.sqrt_nonneg Kprod; positivity, ?_⟩
    rw [mul_pow, mul_pow, Real.sq_sqrt Kprod_nonneg]
    exact h4
  have e3 : ∀ x, ‖A x‖ ^ 3 = ‖A x‖ * ‖A x‖ ^ 2 := fun x => by ring
  simp only [e3]
  refine hcs.trans ?_
  rw [← matNorm_eq]
  exact mul_le_mul_of_nonneg_left hsqrt4 (matNorm_nonneg A)

theorem sum_shift_norm_pow (A : MatArr N n) (e : Grid N) (p : ℕ) :
    ∑ x, ‖A (x + e)‖ ^ p = ∑ x, ‖A x‖ ^ p :=
  Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)

/-- **Summed plaquette remainder** (`eq:supp-literal-magnetic-limit`, error terms):
`h³ Σ_x ‖R(x)‖ ≤ h · (6(‖D_j⁺A_i‖² + ‖D_i⁺A_j‖²) + 2(‖A_i‖² + ‖A_j‖²)
  + 192κ (h³Σ‖A_i‖³ + h³Σ‖A_j‖³))` on the chart `h‖A‖ ≤ 1/16`. -/
theorem sum_norm_magRem_le (i j : Fin 3) (Ai Aj : MatArr N n)
    (hAi : ∀ x, (N : ℝ)⁻¹ * ‖Ai x‖ ≤ 1 / 16) (hAj : ∀ x, (N : ℝ)⁻¹ * ‖Aj x‖ ≤ 1 / 16) :
    ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖magRem i j Ai Aj x‖ ≤ (N : ℝ)⁻¹ *
      (6 * (matNormSq (matDp j Ai) + matNormSq (matDp i Aj)) + 2 * (matNormSq Ai + matNormSq Aj)
        + 192 * kappa (Matrix (Fin n) (Fin n) ℂ) *
          (((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖Ai x‖ ^ 3 + ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖Aj x‖ ^ 3)) := by
  have hN3 : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ =>
    norm_magRem_le i j Ai Aj hAi hAj x) hN3).trans (le_of_eq ?_)
  rw [matNormSq_eq, matNormSq_eq, matNormSq_eq, matNormSq_eq]
  have s1 := sum_shift_norm_pow Ai (unit j) 3
  have s2 := sum_shift_norm_pow Aj (unit i) 3
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, s1, s2]
  ring

/-- `‖Z‖_h² ≤ (κ²e^δ)² ‖A‖_h²` on the chart `h‖A‖ ≤ δ`. -/
theorem matNormSq_linkZ_le {δ : ℝ} (A : MatArr N n) (hchart : ∀ x, (N : ℝ)⁻¹ * ‖A x‖ ≤ δ) :
    matNormSq (linkZ A) ≤
      (kappa (Matrix (Fin n) (Fin n) ℂ) ^ 2 * Real.exp δ) ^ 2 * matNormSq A := by
  rw [matNormSq_eq, matNormSq_eq]
  calc ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖linkZ A x‖ ^ 2
      ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, (kappa (Matrix (Fin n) (Fin n) ℂ) ^ 2 * Real.exp δ) ^ 2 * ‖A x‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by positivity)
        rw [linkZ_eq_linkCoord, ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (chart_bounds hN_pos (hchart x)).1 2
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- `‖D_j⁺Z‖_h² ≤ (κ²e^δ)² ‖D_j⁺A‖_h²` on the chart. -/
theorem matNormSq_matDp_linkZ_le {δ : ℝ} (A : MatArr N n)
    (hchart : ∀ x, (N : ℝ)⁻¹ * ‖A x‖ ≤ δ) (j : Fin 3) :
    matNormSq (matDp j (linkZ A)) ≤
      (kappa (Matrix (Fin n) (Fin n) ℂ) ^ 2 * Real.exp δ) ^ 2 * matNormSq (matDp j A) := by
  rw [matNormSq_eq, matNormSq_eq]
  calc ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖matDp j (linkZ A) x‖ ^ 2
      ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, (kappa (Matrix (Fin n) (Fin n) ℂ) ^ 2 * Real.exp δ) ^ 2 *
          ‖matDp j A x‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by positivity)
        rw [← mul_pow]
        have := norm_fwdDiff_linkCoord_le hN_pos (unit j) A x (hchart x) (hchart (x + unit j))
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The logarithmic chart error `‖Z − A‖_h² ≤ C²δh n√K ‖A‖_h ‖A‖²_{1,h}`. -/
theorem matNormSq_linkZ_sub_le {δ : ℝ} (A : MatArr N n) (hchart : ∀ x, (N : ℝ)⁻¹ * ‖A x‖ ≤ δ) :
    matNormSq (fun x => linkZ A x - A x) ≤
      (kappa (Matrix (Fin n) (Fin n) ℂ) ^ 2 * Real.exp δ) ^ 2 * δ * (N : ℝ)⁻¹ *
        ((n : ℝ) * Real.sqrt Kprod) * matNorm A * ∑ a, ∑ b, sobSq 1 (entry A a b) := by
  have hC : 0 ≤ kappa (Matrix (Fin n) (Fin n) ℂ) ^ 2 * Real.exp δ := by
    have := kappa_pos (𝔸 := Matrix (Fin n) (Fin n) ℂ); positivity
  exact matNormSq_sub_le_of_chart A (linkZ A) hC (fun x => by
    rw [linkZ_eq_linkCoord]
    exact (chart_bounds hN_pos (hchart x)).2.1) hchart

/-- The negative-norm time bound of `lem:supp-literal-link-evolution` for `∂ₜZ = h⁻¹U'`. -/
theorem negSobNorm2_linkTime {δ : ℝ} (i : Fin 3) (A U' A₀ : MatArr N n)
    (hchart : ∀ x, (N : ℝ)⁻¹ * ‖A x‖ ≤ δ) :
    negSobNorm2 (fun x => ((N : ℝ)⁻¹)⁻¹ • U' x) ≤
      timeConst (kappa (Matrix (Fin n) (Fin n) ℂ) * Real.exp δ) *
        (matNorm (elecRec i A U' A₀) + (1 + matNorm (linkZ A)) * matNorm A₀) := by
  have hunit : ∀ x, IsUnit (linkU A x) := fun x => by
    unfold linkU; exact NormedSpace.isUnit_exp _
  have e : (fun x => ((N : ℝ)⁻¹)⁻¹ • U' x) = fun x => elecRec i A U' A₀ x * linkU A x +
      matDp i A₀ x + linkZ A x * A₀ (x + unit i) - A₀ x * linkZ A x := by
    funext x
    exact link_Z_identity ((N : ℝ)⁻¹) (unit i) (linkU A) U' (elecRec i A U' A₀) A₀ x
      (electricRecord_mul (hunit x))
  rw [e]
  exact negSobNorm2_linkTime_le i _ (linkU A) (linkZ A) A₀ fun x =>
    (chart_bounds hN_pos (hchart x)).2.2

end RenewalGeometry.LiteralLinkLimit
