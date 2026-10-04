/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Fields, fibres and the physical variation space on the comparison cylinder
  (`def:tests`, Einstein–Standard-Model action-closure manuscript)

Section "Fields, bundles and physical tests" of the manuscript works on the spin cylinder
`M = (0,T) × Σ` (`eq:cylinder`), `Σ` a closed three-manifold, with trivialisable bundles in a
fixed finite atlas and positive comparison data.  This file fixes the **rendering** used by the
encodings of `def:tests`, `def:regulator`, `def:reduced-topology`, `def:reduced-certificate`,
`def:compactness-certificate` and `def:strong-packet`:

* **cylinder.** `Σ = 𝕋³` (the setting of the manuscript's quantitative theorems), so
  `M = (0,T) × 𝕋³ ⊂ ℝ × UnitAddTorus (Fin 3)`.  A field or test on `M` is represented by its
  lift to `E4 = ℝ⁴ = Fin 4 → ℝ` (coordinate `0` = time), required to be invariant under the
  spatial integer translations `spatialShift n` (`n : ℤ³`), i.e. to descend along
  `cylProj : ℝ⁴ → ℝ × 𝕋³` (`cylProj_add_spatialShift`).  The comparison metric `r` and density
  `dV₀` are the flat ones (Lebesgue measure on the lift); the atlas is the standard one of `𝕋³`.
* **bundles.** All bundles are trivialised ("after fixed local gauge and spin-frame
  identifications"), so sections are functions into finite-dimensional fibres:
  - coframes and metric tests: `CoframeFibre = Fin 4 → Fin 4 → ℝ` (`e a μ = e^a_μ`,
    `k μ ν = k^{μν} = δg^{μν}`);
  - `ad P`-valued forms: `ConnFibre = Fin 4 → LieFibre`, `LieFibre = Fin 5 → Fin 5 → ℂ`, with
    values in the Lie algebra `smLie = 𝔰(𝔲(3) ⊕ 𝔲(2))` of `G_SM = S(U(3)×U(2))` in its defining
    block representation on `ℂ³ ⊕ ℂ²` (block-diagonal, skew-Hermitian, total trace `0`);
  - Higgs: `HiggsFibre = Fin 2 → ℂ`, with `ρ_H(X) = ` the `𝔲(2)` block of `X` (`higgsAct`),
    the Lie-algebra form of the library's `higgsRep` (`G_SM ∋ (U₃,U₂) ↦ U₂`);
  - spinors: `SpinorFibre C = Fin 4 → C → ℂ` (Dirac index `⊗` a finite fermion-carrier index
    type `C` collecting chiral, internal and generation indices).  The chiral bundle is cut out
    by `IsChiral left` / `IsCoChiral left`: a carrier row `c` with `left c = true` carries only
    the two `γ₅ = +1` components (and its dual variable only the `γ₅ = -1` components), and
    conversely for right-handed rows (Weyl basis, `γ₅ = diag(1,1,-1,-1)`).
* **norms.** Fibre norms are the sup norms of the `Pi` types (uniformly equivalent to the fixed
  bundle metrics, as the manuscript allows).

## `def:tests`

For a compact region `K ⋐ M` (`CylRegion T`: a compact subset of `(0,T) × 𝕋³`),
`testSubmodule left K` is the space `𝒱_K` of tuples `v = (k, a, η_H, η_Ψ, η_Ψ̄)` of smooth
(`C^∞`), spatially periodic, compactly supported sections with `tsupport ⊆ cylProj⁻¹ K`, with
`k` symmetric, `a` `smLie`-valued and the spinor entries in the chiral bundles.  The `C^r` test
norm is `testNorm r v = Σ_{components} crNorm r`, `crNorm r f = Σ_{j ≤ r} sup_x ‖D^j f(x)‖`
(Mathlib `iteratedFDeriv`), and `CrTest r K` is `𝒱_K` with this norm: a genuine
`NormedAddCommGroup` / `NormedSpace ℝ` (`IsCylTest.bddAbove_norm_iteratedFDeriv` shows the
suprema are finite; definiteness comes from the `j = 0` term).  The completion
`𝒱_K^r = CrTestCompletion r K` is `UniformSpace.Completion (CrTest r K)` (the abstract
completion, a Banach space), and `IsDeterminingCore r K S` says that the subspace `S` is dense
in it.  Non-vacuity: `bumpTest` is a nonzero element of `𝒱_K` for `K = [T/4, 3T/4] × 𝕋³`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

noncomputable section

namespace RenewalGeometry
namespace EinsteinSM

/-! ### The cylinder `M = (0,T) × 𝕋³` and its lift -/

/-- Lifted spacetime coordinates `ℝ⁴ = Fin 4 → ℝ`; coordinate `0` is time. -/
abbrev E4 := Fin 4 → ℝ

/-- The spatial integer translation by `n ∈ ℤ³` (zero time component). -/
def spatialShift (n : Fin 3 → ℤ) : E4 := Fin.cons 0 (fun i => (n i : ℝ))

@[simp] theorem spatialShift_zero (n : Fin 3 → ℤ) : spatialShift n 0 = 0 := rfl

@[simp] theorem spatialShift_succ (n : Fin 3 → ℤ) (i : Fin 3) :
    spatialShift n i.succ = n i := rfl

/-- The covering map `ℝ⁴ → ℝ × 𝕋³`, `x ↦ (x⁰, [x¹], [x²], [x³])`. -/
def cylProj (x : E4) : ℝ × UnitAddTorus (Fin 3) :=
  (x 0, fun i => ((x i.succ : ℝ) : UnitAddCircle))

/-- Spatially periodic functions descend to `ℝ × 𝕋³`: `cylProj` is invariant under the spatial
integer translations. -/
theorem cylProj_add_spatialShift (x : E4) (n : Fin 3 → ℤ) :
    cylProj (x + spatialShift n) = cylProj x := by
  refine Prod.ext (by simp [cylProj]) (funext fun i => ?_)
  simp only [cylProj, Pi.add_apply, spatialShift_succ, AddCircle.coe_add]
  rw [add_eq_left, AddCircle.coe_eq_zero_iff]
  exact ⟨n i, by simp⟩

/-- A compact region `K ⋐ M = (0,T) × 𝕋³`. -/
structure CylRegion (T : ℝ) where
  /-- the region, as a subset of `ℝ × 𝕋³` -/
  carrier : Set (ℝ × UnitAddTorus (Fin 3))
  isCompact : IsCompact carrier
  /-- `K ⊂ M = (0,T) × 𝕋³` -/
  subset : carrier ⊆ Ioo 0 T ×ˢ univ

/-- The lifted region `cylProj⁻¹ K ⊂ ℝ⁴`. -/
def CylRegion.lift {T : ℝ} (K : CylRegion T) : Set E4 := cylProj ⁻¹' K.carrier

theorem CylRegion.time_mem {T : ℝ} (K : CylRegion T) {x : E4} (hx : x ∈ K.lift) :
    x 0 ∈ Ioo 0 T := (K.subset hx).1

/-! ### Fibres -/

/-- Coframe / metric-test fibre `Fin 4 → Fin 4 → ℝ`. -/
abbrev CoframeFibre := Fin 4 → Fin 4 → ℝ
/-- Lie-algebra fibre: `5 × 5` complex matrices (defining block representation of `G_SM`). -/
abbrev LieFibre := Fin 5 → Fin 5 → ℂ
/-- Connection fibre: Lie-algebra-valued one-forms `A_μ`. -/
abbrev ConnFibre := Fin 4 → LieFibre
/-- Higgs-doublet fibre `ℂ²`. -/
abbrev HiggsFibre := Fin 2 → ℂ
/-- Spinor fibre `ℂ⁴ ⊗ ℂ^C` (Dirac index, fermion-carrier index). -/
abbrev SpinorFibre (C : Type) := Fin 4 → C → ℂ

/-- Matrix product on `ι → ι → ℂ`. -/
def mmul {ι : Type*} [Fintype ι] (X Y : ι → ι → ℂ) : ι → ι → ℂ :=
  fun i j => ∑ k, X i k * Y k j

/-- Commutator `[X, Y] = XY - YX`. -/
def comm {ι : Type*} [Fintype ι] (X Y : ι → ι → ℂ) : ι → ι → ℂ := mmul X Y - mmul Y X

/-- The colour/weak block label of an index of `ℂ³ ⊕ ℂ²`. -/
def colourBlock (i : Fin 5) : Bool := decide ((i : ℕ) < 3)

/-- **The Lie algebra `𝔰(𝔲(3) ⊕ 𝔲(2))` of `G_SM = S(U(3)×U(2))`** in the defining block
representation: skew-Hermitian, block-diagonal for `ℂ³ ⊕ ℂ²`, total trace zero. -/
def smLie : Submodule ℝ LieFibre where
  carrier := {X | (∀ i j, X j i = -star (X i j)) ∧
    (∀ i j, colourBlock i ≠ colourBlock j → X i j = 0) ∧ ∑ i, X i i = 0}
  add_mem' := by
    rintro X Y ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun i j => ?_, fun i j hij => ?_, ?_⟩
    · simp [h1 i j, k1 i j, star_add]; ring
    · simp [h2 i j hij, k2 i j hij]
    · simp [Finset.sum_add_distrib, h3, k3]
  zero_mem' := ⟨fun i j => by simp, fun i j _ => rfl, by simp⟩
  smul_mem' := by
    rintro r X ⟨h1, h2, h3⟩
    refine ⟨fun i j => ?_, fun i j hij => ?_, ?_⟩
    · simp only [Pi.smul_apply, h1 i j, Complex.real_smul, star_mul', Complex.star_def,
        Complex.conj_ofReal]
      ring
    · simp [h2 i j hij]
    · simp only [Pi.smul_apply]
      rw [← Finset.smul_sum, h3, smul_zero]

/-- The `𝔲(2)` block `ρ_H(X)` of `X ∈ smLie`, acting on the Higgs doublet:
`(ρ_H(X) v)_i = Σ_j X_{3+i,3+j} v_j`. -/
def higgsAct (X : LieFibre) (v : HiggsFibre) : HiggsFibre :=
  fun i => ∑ j, X (Fin.natAdd 3 i) (Fin.natAdd 3 j) * v j

/-- Chiral bundle condition on a spinor value: left-handed carrier rows carry only the
`γ₅ = +1` Dirac components `0, 1`, right-handed rows only the `γ₅ = -1` components `2, 3`. -/
def IsChiral {C : Type} (left : C → Bool) (ψ : SpinorFibre C) : Prop :=
  ∀ (s : Fin 4) (c : C), (if left c then 2 ≤ (s : ℕ) else (s : ℕ) < 2) → ψ s c = 0

/-- Dual chiral condition on the independent dual spinor `Ψ̄` (`Ψ̄ γ₅ = -χ Ψ̄`). -/
def IsCoChiral {C : Type} (left : C → Bool) (ψ : SpinorFibre C) : Prop :=
  ∀ (s : Fin 4) (c : C), (if left c then (s : ℕ) < 2 else 2 ≤ (s : ℕ)) → ψ s c = 0

/-! ### Field tuples -/

/-- Raw field (or variation) tuples `z = (e, A, H, Ψ, Ψ̄)` on the lift `ℝ⁴`. -/
abbrev FieldTuple (C : Type) :=
  (E4 → CoframeFibre) × (E4 → ConnFibre) × (E4 → HiggsFibre) × (E4 → SpinorFibre C) ×
    (E4 → SpinorFibre C)

namespace FieldTuple

variable {C : Type}

/-- Coframe (or metric test `k`) entry. -/
def e (z : FieldTuple C) : E4 → CoframeFibre := z.1
/-- Connection (or `a`) entry. -/
def A (z : FieldTuple C) : E4 → ConnFibre := z.2.1
/-- Higgs (or `η_H`) entry. -/
def H (z : FieldTuple C) : E4 → HiggsFibre := z.2.2.1
/-- Spinor (or `η_Ψ`) entry. -/
def Ψ (z : FieldTuple C) : E4 → SpinorFibre C := z.2.2.2.1
/-- Dual spinor (or `η_Ψ̄`) entry. -/
def Ψb (z : FieldTuple C) : E4 → SpinorFibre C := z.2.2.2.2

/-- Build a tuple from its five entries. -/
def mk (e : E4 → CoframeFibre) (A : E4 → ConnFibre) (H : E4 → HiggsFibre)
    (Ψ Ψb : E4 → SpinorFibre C) : FieldTuple C := (e, A, H, Ψ, Ψb)

end FieldTuple

/-! ### Compactly supported smooth sections over `K` -/

/-- `f` is a smooth section over `M` supported in the compact region `K`: `C^∞` on the lift,
spatially `ℤ³`-periodic (so it descends to `(0,T) × 𝕋³`), with `tsupport f ⊆ cylProj⁻¹ K`. -/
structure IsCylTest {T : ℝ} (K : CylRegion T) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E4 → F) : Prop where
  smooth : ContDiff ℝ ∞ f
  periodic : ∀ (n : Fin 3 → ℤ) (x : E4), f (x + spatialShift n) = f x
  support : tsupport f ⊆ K.lift

namespace IsCylTest

variable {T : ℝ} {K : CylRegion T} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem zero : IsCylTest K (0 : E4 → F) :=
  ⟨contDiff_const, fun _ _ => rfl, by simp⟩

theorem add {f g : E4 → F} (hf : IsCylTest K f) (hg : IsCylTest K g) : IsCylTest K (f + g) :=
  ⟨hf.smooth.add hg.smooth, fun n x => by simp [hf.periodic n x, hg.periodic n x],
    (tsupport_add f g).trans (union_subset hf.support hg.support)⟩

theorem smul {f : E4 → F} (hf : IsCylTest K f) (c : ℝ) : IsCylTest K (c • f) :=
  ⟨hf.smooth.const_smul c, fun n x => by simp [hf.periodic n x],
    (tsupport_smul_subset_right _ _).trans hf.support⟩

/-- Iterated derivatives of a spatially periodic function are spatially periodic. -/
theorem iteratedFDeriv_periodic {f : E4 → F} (hf : IsCylTest K f) (j : ℕ) (n : Fin 3 → ℤ)
    (x : E4) : iteratedFDeriv ℝ j f (x + spatialShift n) = iteratedFDeriv ℝ j f x := by
  rw [← iteratedFDeriv_comp_add_right]
  congr 1
  funext z
  exact hf.periodic n z

/-- **The `C^r` suprema are finite**: `x ↦ ‖D^j f(x)‖` is bounded for a test section (it is
continuous, periodic in space, and vanishes for `x⁰ ∉ (0,T)`, so its range is that of a compact
box). -/
theorem bddAbove_norm_iteratedFDeriv {f : E4 → F} (hf : IsCylTest K f) (j : ℕ) :
    BddAbove (range fun x => ‖iteratedFDeriv ℝ j f x‖) := by
  set g := iteratedFDeriv ℝ j f
  have hcont : Continuous g := hf.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  set B : Set E4 := univ.pi fun i => Icc (0 : ℝ) ((Fin.cons T (fun _ : Fin 3 => (1 : ℝ)) : E4) i)
  have hB : IsCompact B := isCompact_univ_pi fun i => isCompact_Icc
  obtain ⟨M, hM⟩ := (hB.image (continuous_norm.comp hcont)).bddAbove
  refine ⟨max M 0, ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hx : g x = 0
  · simp [hx]
  have hxK : x ∈ K.lift := hf.support (support_iteratedFDeriv_subset j hx)
  have ht := K.time_mem hxK
  set n : Fin 3 → ℤ := fun i => -⌊x i.succ⌋
  set y := x + spatialShift n
  have hy : g y = g x := hf.iteratedFDeriv_periodic j n x
  have hyB : y ∈ B := by
    intro i _
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [y, Pi.add_apply, spatialShift_zero, add_zero, Fin.cons_zero]
      exact ⟨ht.1.le, ht.2.le⟩
    · simp only [y, n, Pi.add_apply, spatialShift_succ, Fin.cons_succ, Int.cast_neg]
      have h1 := Int.fract_nonneg (x i.succ)
      have h2 := Int.fract_lt_one (x i.succ)
      rw [Int.fract] at h1 h2
      constructor <;> linarith
  have : ‖g y‖ ≤ M := hM ⟨y, hyB, rfl⟩
  show ‖g x‖ ≤ max M 0
  rw [← hy]
  exact this.trans (le_max_left _ _)

end IsCylTest

/-! ### The `C^r` norm -/

/-- The `C^r` norm `‖f‖_{C^r} = Σ_{j ≤ r} sup_x ‖D^j f(x)‖` (Mathlib `iteratedFDeriv`; the
supremum is the real `iSup`, finite on test sections by `bddAbove_norm_iteratedFDeriv`). -/
def crNorm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (r : ℕ) (f : E4 → F) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), ⨆ x, ‖iteratedFDeriv ℝ j f x‖

section crNorm

variable {T : ℝ} {K : CylRegion T} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem crNorm_nonneg (r : ℕ) (f : E4 → F) : 0 ≤ crNorm r f :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem crNorm_add_le {f g : E4 → F} (hf : IsCylTest K f) (hg : IsCylTest K g) (r : ℕ) :
    crNorm r (f + g) ≤ crNorm r f + crNorm r g := by
  unfold crNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ciSup_le fun x => ?_
  rw [iteratedFDeriv_add_apply (hf.smooth.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.smooth.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact (norm_add_le _ _).trans (add_le_add
    (le_ciSup (hf.bddAbove_norm_iteratedFDeriv j) x)
    (le_ciSup (hg.bddAbove_norm_iteratedFDeriv j) x))

theorem crNorm_smul {f : E4 → F} (hf : IsCylTest K f) (c : ℝ) (r : ℕ) :
    crNorm r (c • f) = |c| * crNorm r f := by
  unfold crNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.mul_iSup_of_nonneg (abs_nonneg c)]
  congr 1
  funext x
  rw [iteratedFDeriv_const_smul_apply (hf.smooth.contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs]

theorem eq_zero_of_crNorm_eq_zero {f : E4 → F} (hf : IsCylTest K f) (r : ℕ)
    (h : crNorm r f = 0) : f = 0 := by
  unfold crNorm at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Real.iSup_nonneg fun x => norm_nonneg (iteratedFDeriv ℝ j f x))).mp h 0
    (by simp)
  funext x
  have hx := le_ciSup (hf.bddAbove_norm_iteratedFDeriv 0) x
  rw [h0, norm_iteratedFDeriv_zero] at hx
  exact norm_le_zero_iff.mp hx

end crNorm

/-! ### The physical variation space `𝒱_K` (`def:tests`) -/

variable {C : Type} [Fintype C]

/-- **`def:tests`: the physical variation space `𝒱_K`** of smooth compactly supported tuples
`v = (k, a, η_H, η_Ψ, η_Ψ̄)` over the compact region `K`, `k` symmetric (`k^{μν} = δg^{μν}`),
`a` an `ad P`-valued one-form (`smLie`-valued), the spinor entries in the chiral bundles. -/
def testSubmodule {T : ℝ} (left : C → Bool) (K : CylRegion T) : Submodule ℝ (FieldTuple C) where
  carrier := {v | IsCylTest K v.e ∧ IsCylTest K v.A ∧ IsCylTest K v.H ∧ IsCylTest K v.Ψ ∧
    IsCylTest K v.Ψb ∧ (∀ x μ ν, v.e x μ ν = v.e x ν μ) ∧ (∀ x μ, v.A x μ ∈ smLie) ∧
    (∀ x, IsChiral left (v.Ψ x)) ∧ (∀ x, IsCoChiral left (v.Ψb x))}
  add_mem' := by
    rintro v w ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩
    refine ⟨h1.add k1, h2.add k2, h3.add k3, h4.add k4, h5.add k5, fun x μ ν => ?_,
      fun x μ => ?_, fun x s c hs => ?_, fun x s c hs => ?_⟩
    · change v.e x μ ν + w.e x μ ν = v.e x ν μ + w.e x ν μ
      rw [h6 x μ ν, k6 x μ ν]
    · exact smLie.add_mem (h7 x μ) (k7 x μ)
    · change v.Ψ x s c + w.Ψ x s c = 0
      rw [h8 x s c hs, k8 x s c hs, add_zero]
    · change v.Ψb x s c + w.Ψb x s c = 0
      rw [h9 x s c hs, k9 x s c hs, add_zero]
  zero_mem' := ⟨IsCylTest.zero, IsCylTest.zero, IsCylTest.zero, IsCylTest.zero, IsCylTest.zero,
    fun _ _ _ => rfl, fun _ _ => smLie.zero_mem, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  smul_mem' := by
    rintro c v ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    refine ⟨h1.smul c, h2.smul c, h3.smul c, h4.smul c, h5.smul c, fun x μ ν => ?_,
      fun x μ => ?_, fun x s c' hs => ?_, fun x s c' hs => ?_⟩
    · change c • v.e x μ ν = c • v.e x ν μ
      rw [h6 x μ ν]
    · exact smLie.smul_mem c (h7 x μ)
    · change c • v.Ψ x s c' = 0
      rw [h8 x s c' hs, smul_zero]
    · change c • v.Ψb x s c' = 0
      rw [h9 x s c' hs, smul_zero]

/-- The sum of the `C^r` norms of the five entries of a tuple (`def:tests`). -/
def testNorm (r : ℕ) (v : FieldTuple C) : ℝ :=
  crNorm r v.e + crNorm r v.A + crNorm r v.H + crNorm r v.Ψ + crNorm r v.Ψb

set_option linter.unusedVariables false in
/-- `𝒱_K` equipped with the `C^r` test norm (a type synonym of `testSubmodule left K`, so that
the norm is not confused with the ambient product topology). -/
def CrTest {T : ℝ} (left : C → Bool) (r : ℕ) (K : CylRegion T) : Type :=
  ↥(testSubmodule left K)

namespace CrTest

variable {T : ℝ} {left : C → Bool} {r : ℕ} {K : CylRegion T}

instance : AddCommGroup (CrTest left r K) := inferInstanceAs (AddCommGroup ↥(testSubmodule left K))
instance : Module ℝ (CrTest left r K) := inferInstanceAs (Module ℝ ↥(testSubmodule left K))

/-- The underlying test tuple. -/
def val (v : CrTest left r K) : FieldTuple C := (show ↥(testSubmodule left K) from v).1

theorem val_mem (v : CrTest left r K) : v.val ∈ testSubmodule left K :=
  (show ↥(testSubmodule left K) from v).2

@[simp] theorem val_add (v w : CrTest left r K) : (v + w).val = v.val + w.val := rfl
@[simp] theorem val_smul (c : ℝ) (v : CrTest left r K) : (c • v).val = c • v.val := rfl
@[simp] theorem val_zero : (0 : CrTest left r K).val = 0 := rfl

theorem val_injective : Function.Injective (val : CrTest left r K → FieldTuple C) :=
  fun _ _ h => Subtype.ext h

instance : Norm (CrTest left r K) := ⟨fun v => testNorm r v.val⟩

theorem norm_def (v : CrTest left r K) : ‖v‖ = testNorm r v.val := rfl

/-- The `C^r` test norm is a norm on `𝒱_K`. -/
theorem normedSpaceCore : NormedSpace.Core ℝ (CrTest left r K) where
  norm_nonneg v := by
    rw [norm_def, testNorm]
    have := crNorm_nonneg r v.val.e; have := crNorm_nonneg r v.val.A
    have := crNorm_nonneg r v.val.H; have := crNorm_nonneg r v.val.Ψ
    have := crNorm_nonneg r v.val.Ψb
    linarith
  norm_smul c v := by
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := v.val_mem
    simp only [norm_def, testNorm, val_smul, Real.norm_eq_abs]
    rw [show (c • v.val).e = c • v.val.e from rfl, show (c • v.val).A = c • v.val.A from rfl,
      show (c • v.val).H = c • v.val.H from rfl, show (c • v.val).Ψ = c • v.val.Ψ from rfl,
      show (c • v.val).Ψb = c • v.val.Ψb from rfl, crNorm_smul h1, crNorm_smul h2,
      crNorm_smul h3, crNorm_smul h4, crNorm_smul h5]
    ring
  norm_triangle v w := by
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := v.val_mem
    obtain ⟨k1, k2, k3, k4, k5, -⟩ := w.val_mem
    simp only [norm_def, testNorm, val_add]
    rw [show (v.val + w.val).e = v.val.e + w.val.e from rfl,
      show (v.val + w.val).A = v.val.A + w.val.A from rfl,
      show (v.val + w.val).H = v.val.H + w.val.H from rfl,
      show (v.val + w.val).Ψ = v.val.Ψ + w.val.Ψ from rfl,
      show (v.val + w.val).Ψb = v.val.Ψb + w.val.Ψb from rfl]
    have := crNorm_add_le h1 k1 r; have := crNorm_add_le h2 k2 r
    have := crNorm_add_le h3 k3 r; have := crNorm_add_le h4 k4 r
    have := crNorm_add_le h5 k5 r
    linarith
  norm_eq_zero_iff v := by
    constructor
    · intro hv
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := v.val_mem
      rw [norm_def, testNorm] at hv
      have n1 := crNorm_nonneg r v.val.e; have n2 := crNorm_nonneg r v.val.A
      have n3 := crNorm_nonneg r v.val.H; have n4 := crNorm_nonneg r v.val.Ψ
      have n5 := crNorm_nonneg r v.val.Ψb
      have z1 := eq_zero_of_crNorm_eq_zero h1 r (by linarith)
      have z2 := eq_zero_of_crNorm_eq_zero h2 r (by linarith)
      have z3 := eq_zero_of_crNorm_eq_zero h3 r (by linarith)
      have z4 := eq_zero_of_crNorm_eq_zero h4 r (by linarith)
      have z5 := eq_zero_of_crNorm_eq_zero h5 r (by linarith)
      apply val_injective
      rw [val_zero]
      change (v.val.e, v.val.A, v.val.H, v.val.Ψ, v.val.Ψb) = 0
      rw [z1, z2, z3, z4, z5]
      rfl
    · rintro rfl
      simp only [norm_def, testNorm, val_zero]
      simp [crNorm, FieldTuple.e, FieldTuple.A, FieldTuple.H, FieldTuple.Ψ, FieldTuple.Ψb]

/-- **`𝒱_K` with the `C^r` test norm is a normed group** (`def:tests`). -/
instance : NormedAddCommGroup (CrTest left r K) := NormedAddCommGroup.ofCore normedSpaceCore

/-- **`𝒱_K` with the `C^r` test norm is a real normed space** (`def:tests`). -/
instance : NormedSpace ℝ (CrTest left r K) := NormedSpace.ofCore normedSpaceCore

end CrTest

/-- **`def:tests`: the completed variation space `𝒱_K^r`**, the (abstract) completion of `𝒱_K`
in the `C^r` test norm; `r = r₀ ≥ 4` is the regulator convention (`RegulatorSequence.r0`). -/
abbrev CrTestCompletion {T : ℝ} (left : C → Bool) (r : ℕ) (K : CylRegion T) : Type :=
  UniformSpace.Completion (CrTest left r K)

example {T : ℝ} (left : C → Bool) (r : ℕ) (K : CylRegion T) :
    CompleteSpace (CrTestCompletion left r K) := inferInstance

example {T : ℝ} (left : C → Bool) (r : ℕ) (K : CylRegion T) :
    NormedSpace ℝ (CrTestCompletion left r K) := inferInstance

/-- **`def:tests`, determining core**: a subspace `S ⊂ 𝒱_K` dense in the completed test space
`𝒱_K^r` (bounds that are uniform on `S` then extend to the completion by continuity). -/
def IsDeterminingCore {T : ℝ} (left : C → Bool) (r : ℕ) (K : CylRegion T)
    (S : Submodule ℝ (CrTest left r K)) : Prop :=
  Dense ((fun v : CrTest left r K => (v : CrTestCompletion left r K)) '' (S : Set _))

/-- The whole of `𝒱_K` is a determining core (density of a space in its completion). -/
theorem isDeterminingCore_top {T : ℝ} (left : C → Bool) (r : ℕ) (K : CylRegion T) :
    IsDeterminingCore left r K ⊤ := by
  unfold IsDeterminingCore
  rw [Submodule.top_coe, Set.image_univ]
  exact UniformSpace.Completion.denseRange_coe

/-! ### Non-vacuity: a nonzero physical test -/

/-- The region `K = [T/4, 3T/4] × 𝕋³ ⋐ (0,T) × 𝕋³`. -/
def middleRegion (T : ℝ) (hT : 0 < T) : CylRegion T where
  carrier := Icc (T / 4) (3 * T / 4) ×ˢ univ
  isCompact := isCompact_Icc.prod isCompact_univ
  subset := by
    rintro ⟨t, y⟩ ⟨⟨h1, h2⟩, -⟩
    exact ⟨⟨by linarith, by linarith⟩, trivial⟩

/-- A smooth time bump supported in `[T/4, 3T/4]`. -/
def timeBump (T : ℝ) (hT : 0 < T) : ContDiffBump (T / 2) :=
  ⟨T / 8, T / 4, by positivity, by linarith⟩

theorem isCylTest_timeBump {T : ℝ} (hT : 0 < T) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (w : F) :
    IsCylTest (middleRegion T hT) (fun x : E4 => timeBump T hT (x 0) • w) := by
  refine ⟨((timeBump T hT).contDiff.comp (contDiff_apply ℝ ℝ 0)).smul contDiff_const,
    fun n x => by simp, ?_⟩
  intro x hx
  have hx' : x 0 ∈ tsupport (timeBump T hT) := by
    have hsub : Function.support (fun x : E4 => timeBump T hT (x 0) • w) ⊆
        (fun x : E4 => x 0) ⁻¹' Function.support (timeBump T hT) := fun y hy h0 =>
      hy (by simp only [h0, zero_smul])
    have := closure_mono hsub hx
    exact (closure_minimal (preimage_mono subset_closure)
      ((isClosed_closure).preimage (continuous_apply 0))) this
  rw [(timeBump T hT).tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hx'
  have h4 : (timeBump T hT).rOut = T / 4 := rfl
  rw [h4, abs_le] at hx'
  exact ⟨⟨(by linarith [hx'.1] : T / 4 ≤ x 0), (by linarith [hx'.2] : x 0 ≤ 3 * T / 4)⟩,
    trivial⟩

/-- **Non-vacuity of `def:tests`**: the pure metric test `k = φ(t) δ` (a time bump times the
identity, symmetric), all other entries zero, is a nonzero element of `𝒱_K`. -/
def bumpTest {T : ℝ} (hT : 0 < T) (left : C → Bool) (r : ℕ) :
    CrTest left r (middleRegion T hT) :=
  (⟨FieldTuple.mk (fun x => timeBump T hT (x 0) • (fun μ ν => if μ = ν then (1 : ℝ) else 0))
      0 0 0 0,
    isCylTest_timeBump hT _, IsCylTest.zero, IsCylTest.zero, IsCylTest.zero, IsCylTest.zero,
    fun x μ ν => by
      simp only [FieldTuple.mk, FieldTuple.e, Pi.smul_apply, smul_eq_mul]
      by_cases h : μ = ν <;> simp [h, eq_comm],
    fun _ _ => smLie.zero_mem, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩ :
    ↥(testSubmodule left (middleRegion T hT)))

theorem bumpTest_ne_zero {T : ℝ} (hT : 0 < T) (left : C → Bool) (r : ℕ) :
    bumpTest (C := C) hT left r ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : CrTest left r (middleRegion T hT) => v.val.e
    (Fin.cons (T / 2) 0) 0 0) h
  simp only [CrTest.val_zero] at h1
  change timeBump T hT (T / 2) • (1 : ℝ) = (0 : FieldTuple C).e (Fin.cons (T / 2) 0) 0 0 at h1
  rw [(timeBump T hT).one_of_mem_closedBall (by simp [(timeBump T hT).rIn_pos.le])] at h1
  simp [FieldTuple.e] at h1

theorem norm_bumpTest_pos {T : ℝ} (hT : 0 < T) (left : C → Bool) (r : ℕ) :
    0 < ‖bumpTest (C := C) hT left r‖ :=
  norm_pos_iff.mpr (bumpTest_ne_zero hT left r)

end EinsteinSM
end RenewalGeometry
