/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.UhlenbeckContinuity
import RenewalGeometry.Analysis.UhlenbeckOpenness

/-!
# Reflection classes on `𝕋⁴`: the Neumann theory of the cube as a symmetric torus theory
  (stage A1 of the cube rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (K. Uhlenbeck, CMP 83 (1982), Thm 1.3).

The four coordinate reflections `R_j : x_j ↦ -x_j` of the flat torus `𝕋⁴ = UnitAddTorus (Fin 4)`
(`UhlenbeckTorus.reflect`) generate a group `(ℤ/2)⁴` whose fundamental domain is the cube
`Q₀ = (0, 1/2)⁴` (mirrors `x_j = 0` and `x_j = 1/2`).  A function on `Q₀` extends to `𝕋⁴` with a
prescribed **parity pattern** `S ⊆ Fin 4` (odd under `R_j` for `j ∈ S`, even otherwise).  The
Neumann theory of `Q₀` is the torus theory restricted to these classes:

* scalars and gauge parameters: the **even class** `S = ∅` (cosine series; homogeneous Neumann
  condition `∂_ν ξ = 0`);
* one-forms with vanishing normal component on the faces (`a·ν = 0` on `∂Q₀`): the component `a_ν`
  has pattern `{ν}` (tangential components even, normal component odd), `IsNeumannForm`;
* two-forms (curvatures) `F_{μν}`: pattern `{μ} ∆ {ν}`.

Main results:

* `flip`, `mFourier_reflect`, `mFourierCoeff_comp_reflect`: `(f ∘ R_j)^(n) = f̂(flip_j n)`;
* `sym_flip`, `IsTPartial.comp_reflect`: torus derivatives commute with reflections up to the
  sign `dSign j μ = -1` iff `μ = j`;
* `HasParity S f` (a.e. parity under all four reflections), its **Fourier characterisation**
  `hasParity_iff_coeff` (`f̂(flip_j n) = ±f̂(n)`: cosine/sine series), closure under sums,
  scalar multiples, **products** (`HasParity.mul`, pattern `S ∆ T`) and **derivatives**
  (`HasParity.partial`, pattern `S ∆ {μ}`);
* `HasParity.mean_zero`: a function odd in some direction has mean zero;
* `neumann_harmonic_eq_zero` (**no harmonic one-forms with vanishing normal component**): a
  one-form with `L²` partials, `da = 0`, `d^*a = 0` and the Neumann parity pattern vanishes a.e.
  (on `𝕋⁴` the harmonic forms are the constants; the Neumann pattern kills their means).  This is
  why the cube a-priori estimate needs no mean-zero hypothesis.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace RenewalGeometry.CubeNeumann

open SobolevOpen TorusSobolev UhlenbeckTorus

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "𝕋⁴" => UnitAddTorus (Fin 4)

/-! ### Reflections and Fourier coefficients -/

/-- The reflection `n_j ↦ -n_j` of frequencies. -/
def flip (j : Fin 4) (n : Fin 4 → ℤ) : Fin 4 → ℤ := Function.update n j (-n j)

theorem flip_flip (j : Fin 4) (n : Fin 4 → ℤ) : flip j (flip j n) = n := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [flip]
  · simp [flip, Function.update_of_ne hi]

theorem flip_apply_self (j : Fin 4) (n : Fin 4 → ℤ) : flip j n j = -n j := by simp [flip]

theorem flip_apply_ne {j i : Fin 4} (h : i ≠ j) (n : Fin 4 → ℤ) : flip j n i = n i := by
  simp [flip, Function.update_of_ne h]

theorem flip_neg (j : Fin 4) (n : Fin 4 → ℤ) : flip j (-n) = -flip j n := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [flip]
  · simp [flip, Function.update_of_ne hi]

theorem flip_zero (j : Fin 4) : flip j 0 = 0 := by
  funext i; by_cases hi : i = j
  · subst hi; simp [flip]
  · simp [flip, Function.update_of_ne hi]

theorem flip_eq_zero_iff {j : Fin 4} {n : Fin 4 → ℤ} : flip j n = 0 ↔ n = 0 := by
  constructor
  · intro h; rw [← flip_flip j n, h, flip_zero]
  · rintro rfl; exact flip_zero j

theorem reflect_apply_self (j : Fin 4) (x : 𝕋⁴) : reflect j x j = -x j := by simp [reflect]

theorem reflect_apply_ne {j i : Fin 4} (h : i ≠ j) (x : 𝕋⁴) : reflect j x i = x i := by
  simp [reflect, Function.update_of_ne h]

theorem fourier_neg_arg (k : ℤ) (z : UnitAddCircle) :
    fourier k (-z) = fourier (-k) z := by
  rw [fourier_apply, fourier_apply, smul_neg, neg_smul]

/-- Characters under reflection: `e_n(R_j x) = e_{flip_j n}(x)`. -/
theorem mFourier_reflect (n : Fin 4 → ℤ) (j : Fin 4) (x : 𝕋⁴) :
    mFourier n (reflect j x) = mFourier (flip j n) x := by
  simp only [mFourier, ContinuousMap.coe_mk]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i = j
  · subst hi; rw [reflect_apply_self, flip_apply_self, fourier_neg_arg]
  · rw [reflect_apply_ne hi, flip_apply_ne hi]

/-- **Fourier coefficients of a reflected function**: `(f ∘ R_j)^(n) = f̂(flip_j n)`. -/
theorem mFourierCoeff_comp_reflect (f : 𝕋⁴ → ℂ) (j : Fin 4) (n : Fin 4 → ℤ) :
    mFourierCoeff (fun x => f (reflect j x)) n = mFourierCoeff f (flip j n) := by
  unfold mFourierCoeff
  have h := (measurePreserving_reflect j).integral_comp' (f := reflectEquiv j)
    (fun y => mFourier (-flip j n) y • f y)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show mFourier (-n) x • f (reflect j x) = mFourier (-flip j n) (reflect j x) • f (reflect j x)
  rw [mFourier_reflect, flip_neg, flip_flip]

/-- The sign of `∂_μ` under `R_j`: `-1` if `μ = j`, else `1`. -/
def dSign (j μ : Fin 4) : ℂ := if μ = j then -1 else 1

theorem dSign_mul_self (j μ : Fin 4) : dSign j μ * dSign j μ = 1 := by
  unfold dSign; split_ifs <;> norm_num

theorem norm_dSign (j μ : Fin 4) : ‖dSign j μ‖ = 1 := by
  unfold dSign; split_ifs <;> simp

theorem sym_flip (μ j : Fin 4) (n : Fin 4 → ℤ) : sym μ (flip j n) = dSign j μ * sym μ n := by
  unfold sym dSign
  by_cases h : μ = j
  · subst h; simp [flip_apply_self]
  · simp [flip_apply_ne h, h]

/-- **Derivatives under reflections**: `∂_μ (f ∘ R_j) = ±(∂_μ f) ∘ R_j`. -/
theorem IsTPartial.comp_reflect {μ : Fin 4} {f g : 𝕋⁴ → ℂ} (h : IsTPartial μ f g) (j : Fin 4) :
    IsTPartial μ (fun x => f (reflect j x)) (fun x => dSign j μ * g (reflect j x)) := by
  intro n
  rw [mFourierCoeff_const_mul, mFourierCoeff_comp_reflect, mFourierCoeff_comp_reflect, h,
    sym_flip, ← mul_assoc, ← mul_assoc, dSign_mul_self, one_mul]

theorem memLp_comp_reflect {f : 𝕋⁴ → ℂ} {p : ℝ≥0∞} (hf : MemLp f p volume) (j : Fin 4) :
    MemLp (fun x => f (reflect j x)) p volume :=
  hf.comp_measurePreserving (measurePreserving_reflect j)

theorem eLpNorm_comp_reflect {f : 𝕋⁴ → ℂ} {p : ℝ≥0∞} (hf : AEStronglyMeasurable f volume)
    (j : Fin 4) : eLpNorm (fun x => f (reflect j x)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_reflect j)

theorem integral_comp_reflect' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : 𝕋⁴ → E)
    (j : Fin 4) : ∫ x, f (reflect j x) = ∫ x, f x :=
  (measurePreserving_reflect j).integral_comp' (f := reflectEquiv j) f

theorem ae_comp_reflect {P : 𝕋⁴ → Prop} (h : ∀ᵐ x ∂volume, P x) (j : Fin 4) :
    ∀ᵐ x ∂volume, P (reflect j x) :=
  (measurePreserving_reflect j).quasiMeasurePreserving.ae h

/-! ### Parity classes -/

/-- The sign of the parity pattern `S` in direction `j`: `-1` if `j ∈ S`, else `1`. -/
def pSign (S : Finset (Fin 4)) (j : Fin 4) : ℂ := if j ∈ S then -1 else 1

theorem pSign_mul_self (S : Finset (Fin 4)) (j : Fin 4) : pSign S j * pSign S j = 1 := by
  unfold pSign; split_ifs <;> norm_num

theorem norm_pSign (S : Finset (Fin 4)) (j : Fin 4) : ‖pSign S j‖ = 1 := by
  unfold pSign; split_ifs <;> simp

theorem pSign_empty (j : Fin 4) : pSign ∅ j = 1 := by simp [pSign]

theorem pSign_symmDiff (S T : Finset (Fin 4)) (j : Fin 4) :
    pSign (symmDiff S T) j = pSign S j * pSign T j := by
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp [pSign, Finset.mem_symmDiff, hS, hT]

theorem pSign_singleton (μ j : Fin 4) : pSign {μ} j = dSign j μ := by
  unfold pSign dSign
  by_cases h : μ = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- `f` has **parity pattern `S`**: `f ∘ R_j = pSign S j · f` a.e., for every `j`.  The even class
(`S = ∅`) is the reflection of functions on the cube `Q₀ = (0,1/2)⁴` with the homogeneous Neumann
condition; the pattern `{ν}` is that of the `ν`-th component of a one-form with vanishing normal
component on `∂Q₀`. -/
def HasParity (S : Finset (Fin 4)) (f : 𝕋⁴ → ℂ) : Prop :=
  ∀ j, ∀ᵐ x ∂volume, f (reflect j x) = pSign S j * f x

/-- **Fourier characterisation of the parity classes** (cosine/sine series):
for `f ∈ L²`, `HasParity S f ↔ f̂(flip_j n) = pSign S j · f̂(n)` for all `j, n`. -/
theorem hasParity_iff_coeff {S : Finset (Fin 4)} {f : 𝕋⁴ → ℂ} (hf : MemLp f 2 volume) :
    HasParity S f ↔ ∀ j n, mFourierCoeff f (flip j n) = pSign S j * mFourierCoeff f n := by
  constructor
  · intro h j n
    rw [← mFourierCoeff_comp_reflect, ← mFourierCoeff_const_mul]
    unfold mFourierCoeff
    exact integral_congr_ae ((h j).mono fun x hx => by simp only [hx])
  · intro h j
    refine ae_eq_of_mFourierCoeff_eq (memLp_comp_reflect hf j) (hf.const_mul _) fun n => ?_
    rw [mFourierCoeff_comp_reflect, mFourierCoeff_const_mul, h]

theorem HasParity.congr_ae {S : Finset (Fin 4)} {f g : 𝕋⁴ → ℂ} (hf : HasParity S f)
    (hfg : f =ᵐ[volume] g) : HasParity S g := by
  intro j
  filter_upwards [hf j, hfg, ae_comp_reflect hfg j] with x h1 h2 h3
  rw [← h3, ← h2, h1]

theorem hasParity_zero (S : Finset (Fin 4)) : HasParity S (fun _ => 0) :=
  fun j => Eventually.of_forall fun x => by simp

theorem hasParity_const (z : ℂ) : HasParity ∅ (fun _ => z) :=
  fun j => Eventually.of_forall fun x => by simp [pSign]

theorem HasParity.add {S : Finset (Fin 4)} {f g : 𝕋⁴ → ℂ} (hf : HasParity S f)
    (hg : HasParity S g) : HasParity S (fun x => f x + g x) := fun j => by
  filter_upwards [hf j, hg j] with x h1 h2
  rw [h1, h2]; ring

theorem HasParity.sub {S : Finset (Fin 4)} {f g : 𝕋⁴ → ℂ} (hf : HasParity S f)
    (hg : HasParity S g) : HasParity S (fun x => f x - g x) := fun j => by
  filter_upwards [hf j, hg j] with x h1 h2
  rw [h1, h2]; ring

theorem HasParity.const_mul {S : Finset (Fin 4)} {f : 𝕋⁴ → ℂ} (hf : HasParity S f) (c : ℂ) :
    HasParity S (fun x => c * f x) := fun j => by
  filter_upwards [hf j] with x h1
  rw [h1]; ring

theorem HasParity.finset_sum {S : Finset (Fin 4)} {κ : Type*} (s : Finset κ)
    {f : κ → 𝕋⁴ → ℂ} (hf : ∀ k ∈ s, HasParity S (f k)) :
    HasParity S (fun x => ∑ k ∈ s, f k x) := by
  intro j
  have h : ∀ᵐ x ∂volume, ∀ k ∈ s, f k (reflect j x) = pSign S j * f k x := by
    exact (Filter.eventually_all_finset s).2 fun k hk => hf k hk j
  filter_upwards [h] with x hx
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k hk => hx k hk

/-- **Products**: patterns add modulo 2. -/
theorem HasParity.mul {S T : Finset (Fin 4)} {f g : 𝕋⁴ → ℂ} (hf : HasParity S f)
    (hg : HasParity T g) : HasParity (symmDiff S T) (fun x => f x * g x) := fun j => by
  filter_upwards [hf j, hg j] with x h1 h2
  rw [h1, h2, pSign_symmDiff]; ring

theorem HasParity.conj {S : Finset (Fin 4)} {f : 𝕋⁴ → ℂ} (hf : HasParity S f) :
    HasParity S (fun x => conj (f x)) := fun j => by
  filter_upwards [hf j] with x h1
  rw [h1, map_mul]
  congr 1
  unfold pSign; split_ifs <;> simp

/-- **Derivatives**: `∂_μ` maps the pattern `S` to `S ∆ {μ}`. -/
theorem HasParity.partial {S : Finset (Fin 4)} {μ : Fin 4} {f g : 𝕋⁴ → ℂ} (hf : HasParity S f)
    (hfm : MemLp f 2 volume) (hgm : MemLp g 2 volume) (hd : IsTPartial μ f g) :
    HasParity (symmDiff S {μ}) g := by
  rw [hasParity_iff_coeff hgm]
  intro j n
  rw [hd, hd, sym_flip, (hasParity_iff_coeff hfm).1 hf j n, pSign_symmDiff, pSign_singleton]
  ring

/-- A function odd in some direction has mean zero. -/
theorem HasParity.mean_zero {S : Finset (Fin 4)} {f : 𝕋⁴ → ℂ} (hf : HasParity S f) {j : Fin 4}
    (hj : j ∈ S) : mFourierCoeff f 0 = 0 :=
  mFourierCoeff_zero_eq_zero_of_odd ((hf j).mono fun x hx => by rw [hx]; simp [pSign, hj])

/-! ### Neumann one-forms -/

/-- A one-form on `𝕋⁴` is the reflection of a one-form on the cube with **vanishing normal
component** on the faces: each component `a_ν` has the parity pattern `{ν}` (odd under `R_ν`, even
under the other reflections). -/
def IsNeumannForm (a : Fin 4 → 𝕋⁴ → ℂ) : Prop := ∀ ν, HasParity {ν} (a ν)

/-- Matrix-valued Neumann one-forms (entrywise). -/
def IsNeumannMForm {m : ℕ} (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) : Prop :=
  ∀ ν c e, HasParity {ν} (a ν c e)

/-- The components of a Neumann one-form have mean zero. -/
theorem IsNeumannForm.mean_zero {a : Fin 4 → 𝕋⁴ → ℂ} (ha : IsNeumannForm a) (ν : Fin 4) :
    mFourierCoeff (a ν) 0 = 0 :=
  (ha ν).mean_zero (Finset.mem_singleton_self ν)

/-- **No harmonic one-forms with vanishing normal component on the cube.**  A one-form with `L²`
entries and `L²` partials `g ν μ = ∂_μ a_ν`, closed (`∂_μ a_ν = ∂_ν a_μ`) and co-closed
(`Σ_μ ∂_μ a_μ = 0`), with the Neumann parity pattern, vanishes a.e. -/
theorem neumann_harmonic_eq_zero {a : Fin 4 → 𝕋⁴ → ℂ} {g : Fin 4 → Fin 4 → 𝕋⁴ → ℂ}
    (ha : ∀ ν, MemLp (a ν) 2 volume) (hg : ∀ ν μ, MemLp (g ν μ) 2 volume)
    (hd : ∀ ν μ, IsTPartial μ (a ν) (g ν μ)) (hN : IsNeumannForm a)
    (hclosed : ∀ μ ν, g ν μ =ᵐ[volume] g μ ν) (hcoclosed : ∀ᵐ x ∂volume, ∑ μ, g μ μ x = 0) :
    ∀ ν, a ν =ᵐ[volume] 0 := by
  have hW := weitzenbock_torus hg hd
  have h1 : ∀ μ ν, ∫ x, ‖g ν μ x - g μ ν x‖ ^ 2 = 0 := fun μ ν => by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) ((hclosed μ ν).mono fun x hx => by
      simp only [hx, sub_self, norm_zero]; norm_num)]
    simp
  have h2 : ∫ x, ‖∑ μ, g μ μ x‖ ^ 2 = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (hcoclosed.mono fun x hx => by
      simp only [hx, norm_zero]; norm_num)]
    simp
  simp only [h1, h2, Finset.sum_const_zero, mul_zero, add_zero] at hW
  have hnn : ∀ μ ν, 0 ≤ ∫ x, ‖g ν μ x‖ ^ 2 := fun μ ν => integral_nonneg fun _ => by positivity
  have hzero : ∀ ν μ, ∫ x, ‖g ν μ x‖ ^ 2 = 0 := by
    intro ν μ
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => Finset.sum_nonneg fun ν _ =>
      hnn μ ν)).1 hW μ (Finset.mem_univ μ)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun ν _ => hnn μ ν)).1 hs ν (Finset.mem_univ ν)
  intro ν
  refine ae_eq_zero_of_mFourierCoeff_eq_zero (ha ν) fun n => ?_
  by_cases hn : n = 0
  · subst hn; exact hN.mean_zero ν
  · -- some component of `n` is nonzero
    obtain ⟨μ, hμ⟩ : ∃ μ, n μ ≠ 0 := by
      by_contra h; push Not at h; exact hn (funext h)
    have hgz : g ν μ =ᵐ[volume] 0 := by
      have hE : eLpNorm (g ν μ) 2 volume = 0 := by
        rw [eLpNorm_two_eq_sqrt (hg ν μ), hzero ν μ, Real.sqrt_zero, ENNReal.ofReal_zero]
      exact (eLpNorm_eq_zero_iff (hg ν μ).1 (by norm_num)).1 hE
    have hc : mFourierCoeff (g ν μ) n = 0 := by
      unfold mFourierCoeff
      rw [integral_congr_ae (hgz.mono fun x hx => by
        change mFourier (-n) x • g ν μ x = (fun _ => (0 : ℂ)) x
        rw [hx]; simp)]
      simp
    rw [hd ν μ n] at hc
    have hs : sym μ n ≠ 0 := by
      unfold sym
      have : (n μ : ℂ) ≠ 0 := by exact_mod_cast hμ
      have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      exact mul_ne_zero h2 this
    exact (mul_eq_zero.1 hc).resolve_left hs

/-! ### Non-vacuity -/

/-- The parity classes are non-trivial: `cos(2π x_0)` is even and `sin(2π x_0)` (as
`(e_{e₀} - e_{-e₀})/(2i)`) has pattern `{0}`; here checked on the characters' Fourier side:
the frequency `e₀` is moved to `-e₀` by `flip 0` and fixed by the other flips. -/
example : flip 0 (Pi.single 0 1) = -Pi.single 0 1 ∧ flip 1 (Pi.single 0 1) = Pi.single 0 1 := by
  refine ⟨?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp [flip]

/-- The zero one-form is a Neumann form. -/
example : IsNeumannForm (fun _ _ => (0 : ℂ)) := fun _ => hasParity_zero _

end RenewalGeometry.CubeNeumann
