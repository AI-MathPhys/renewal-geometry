/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.CartanInjectivityExact

/-!
# Connection stationarity and torsion in the coefficient model on a chart of `ℝ⁴`
  (`thm:supp-palatini-torsion`, emergent-spacetime manuscript)

Coefficient model.  On a chart `ℝ⁴` (`Pt = Fin 4 → ℝ`) a coframe is a field
`e : Pt → (Fin 4 → Fin 4 → ℝ)`, `e^I_μ`, a connection is `ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ`,
`ω^I_{Kμ}`, and internal-bivector-valued `p`-forms are coefficient arrays.  Partial derivatives
are Fréchet derivatives along the coordinate vectors (`pd`).

Internal algebra (Lorentzian `η = diag(-1, 1, 1, 1)`):

* `starC` — the internal Hodge star `(⋆B)^{IJ} = ½ ε^{IJ}{}_{KL} B^{KL}`, with the Levi-Civita
  symbol `leviCivita` computed from inversions; `star_star` : `⋆² = -1` on antisymmetric arrays;
* `palatiniC α β = α I + β ⋆` (`P_{α,β}`) and `inverseC α β = (α I - β ⋆)/(α² + β²)`;
  `inverseC_palatiniC`, `palatiniC_inverseC` : `eq:supp-palatini-inverse` on bivectors;
* `IsLorentz` (`ω_{IK} = η_{II} ω^I_K` antisymmetric) and `star_act_comm` : the star commutes
  with the infinitesimal action of every Lorentz connection coefficient.

Calculus:

* `torsion e ω = De`, `bivectorField e = e ∧ e`, `covD ω F` (exterior covariant derivative of an
  internal-bivector-valued two-form), `cartan e T = T ∧ e - e ∧ T` (`𝒦_e(T)`);
* `covD_bivectorField` — the Leibniz identity `D(e^I ∧ e^J) = T^I ∧ e^J - e^I ∧ T^J`;
* `covD_capply` / `covD_palatini_bivector` — for a constant internal map commuting with the
  connection action, `D(P B) = P D B`; hence `D(P_{α,β} B) = P_{α,β} 𝒦_e(T)` for Lorentz `ω`.

Injectivity and the conclusions:

* `cartan_injective_of_isUnit_det` — `𝒦_e` is injective for every nondegenerate coframe
  (change to the coframe basis and the index chase `CartanInjectivity.cartan_injective`);
* `torsion_eq_zero_of_euler` — the spinless connection Euler equation `D(P_{α,β} B) = 0` with
  `(α, β) ≠ (0, 0)` and a nondegenerate coframe forces `T = 0`;
* `norm_torsion_le_residual` — at finite cutoff, a lower singular-value bound
  `κ ‖v‖ ≤ ‖𝒦_e v‖` gives `‖T‖ ≤ κ⁻¹ ‖P_{α,β}^{-1}‖ ‖D(P_{α,β} B)‖` (the Euler residual).
-/

open scoped BigOperators

noncomputable section

namespace RenewalGeometry.PalatiniTorsionModel

/-! ## Internal algebra -/

/-- The Minkowski metric `η = diag(-1, 1, 1, 1)` (diagonal entries). -/
def eta (I : Fin 4) : ℝ := if I = 0 then -1 else 1

theorem eta_sq (I : Fin 4) : eta I * eta I = 1 := by
  unfold eta; split_ifs <;> norm_num

/-- Number of inversions of the index word `(a, b, c, d)`. -/
def inversions (a b c d : Fin 4) : ℕ :=
  (if b < a then 1 else 0) + (if c < a then 1 else 0) + (if d < a then 1 else 0) +
    (if c < b then 1 else 0) + (if d < b then 1 else 0) + (if d < c then 1 else 0)

/-- The Levi-Civita symbol `ε_{abcd}` (integer valued, `ε_{0123} = 1`). -/
def leviCivitaZ (a b c d : Fin 4) : ℤ :=
  if a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d then 0 else (-1) ^ inversions a b c d

/-- The Levi-Civita symbol as a real number. -/
def leviCivita (a b c d : Fin 4) : ℝ := (leviCivitaZ a b c d : ℝ)

/-- Internal coefficient tensors `c^{IJ}{}_{KL}`, acting on internal two-index arrays. -/
abbrev Coeff : Type := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- Action of a coefficient tensor: `(c b)^{IJ} = Σ_{KL} c^{IJ}{}_{KL} b^{KL}`. -/
def capply (c : Coeff) (b : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun I J => ∑ K, ∑ L, c I J K L * b K L

/-- The identity coefficient tensor `δ^I_K δ^J_L`. -/
def idC : Coeff := fun I J K L => (if I = K then 1 else 0) * (if J = L then 1 else 0)

/-- The internal Hodge star `(⋆B)^{IJ} = ½ ε^{IJ}{}_{KL} B^{KL}`, indices lowered with `η`. -/
def starC : Coeff := fun I J K L => leviCivita I J K L * eta K * eta L / 2

/-- `P_{α,β} = α I + β ⋆`. -/
def palatiniC (α β : ℝ) : Coeff := fun I J K L => α * idC I J K L + β * starC I J K L

/-- `(α I - β ⋆)/(α² + β²)`. -/
def inverseC (α β : ℝ) : Coeff :=
  fun I J K L => (α * idC I J K L - β * starC I J K L) / (α ^ 2 + β ^ 2)

/-- Antisymmetric internal arrays (bivectors). -/
def IsAntisymm (b : Fin 4 → Fin 4 → ℝ) : Prop := ∀ I J, b I J = -b J I

theorem capply_idC (b : Fin 4 → Fin 4 → ℝ) : capply idC b = b := by
  funext I J
  unfold capply idC
  rw [Finset.sum_eq_single I (fun K _ hK => by simp [Ne.symm hK]) (by simp)]
  rw [Finset.sum_eq_single J (fun L _ hL => by simp [Ne.symm hL]) (by simp)]
  simp

theorem capply_add (c c' : Coeff) (b : Fin 4 → Fin 4 → ℝ) :
    capply (fun I J K L => c I J K L + c' I J K L) b = capply c b + capply c' b := by
  funext I J
  simp only [capply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem capply_smul (r : ℝ) (c : Coeff) (b : Fin 4 → Fin 4 → ℝ) :
    capply (fun I J K L => r * c I J K L) b = r • capply c b := by
  funext I J
  simp only [capply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem capply_linear_add (c : Coeff) (b b' : Fin 4 → Fin 4 → ℝ) :
    capply c (b + b') = capply c b + capply c b' := by
  funext I J
  simp only [capply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem capply_linear_smul (c : Coeff) (r : ℝ) (b : Fin 4 → Fin 4 → ℝ) :
    capply c (r • b) = r • capply c b := by
  funext I J
  simp only [capply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => by ring

theorem leviCivitaZ_swap : ∀ a b c d : Fin 4, leviCivitaZ a b c d = -leviCivitaZ b a c d := by
  decide

/-- The star of any array is antisymmetric. -/
theorem capply_starC_antisymm (b : Fin 4 → Fin 4 → ℝ) : IsAntisymm (capply starC b) := by
  intro I J
  unfold capply starC leviCivita
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [leviCivitaZ_swap I J K L]
  push_cast
  ring

/-- The internal star written out on the `16` components (Lorentzian signature). -/
def starTable (b : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![0, (b 2 3 - b 3 2) / 2, (-b 1 3 + b 3 1) / 2, (b 1 2 - b 2 1) / 2],
    ![(-b 2 3 + b 3 2) / 2, 0, (-b 0 3 + b 3 0) / 2, (b 0 2 - b 2 0) / 2],
    ![(b 1 3 - b 3 1) / 2, (b 0 3 - b 3 0) / 2, 0, (-b 0 1 + b 1 0) / 2],
    ![(-b 1 2 + b 2 1) / 2, (-b 0 2 + b 2 0) / 2, (b 0 1 - b 1 0) / 2, 0]]

/-- `⋆ = ½ ε η η` evaluates to the explicit table. -/
theorem capply_starC_eq (b : Fin 4 → Fin 4 → ℝ) : capply starC b = starTable b := by
  funext I J
  fin_cases I <;> fin_cases J <;>
    simp only [capply, starC, leviCivita, Fin.sum_univ_four] <;>
    simp (config := {decide := true}) [leviCivitaZ, inversions, eta, starTable] <;> ring

/-- **`⋆² = -1` on Lorentzian bivectors.** -/
theorem star_star {b : Fin 4 → Fin 4 → ℝ} (hb : IsAntisymm b) :
    capply starC (capply starC b) = -b := by
  have h01 := hb 0 1; have h02 := hb 0 2; have h03 := hb 0 3; have h12 := hb 1 2
  have h13 := hb 1 3; have h23 := hb 2 3
  have d0 : b 0 0 = 0 := by have := hb 0 0; linarith
  have d1 : b 1 1 = 0 := by have := hb 1 1; linarith
  have d2 : b 2 2 = 0 := by have := hb 2 2; linarith
  have d3 : b 3 3 = 0 := by have := hb 3 3; linarith
  rw [capply_starC_eq, capply_starC_eq]
  funext I J
  fin_cases I <;> fin_cases J <;> simp [starTable] <;> linarith

/-- `idC` preserves antisymmetry. -/
theorem capply_idC_antisymm {b : Fin 4 → Fin 4 → ℝ} (hb : IsAntisymm b) :
    IsAntisymm (capply idC b) := by rw [capply_idC]; exact hb

theorem capply_palatiniC (α β : ℝ) (b : Fin 4 → Fin 4 → ℝ) :
    capply (palatiniC α β) b = α • b + β • capply starC b := by
  unfold palatiniC
  rw [capply_add, capply_smul, capply_smul, capply_idC]

theorem capply_linear_sub (c : Coeff) (b b' : Fin 4 → Fin 4 → ℝ) :
    capply c (b - b') = capply c b - capply c b' := by
  funext I J
  simp only [capply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem capply_inverseC (α β : ℝ) (b : Fin 4 → Fin 4 → ℝ) :
    capply (inverseC α β) b = (α ^ 2 + β ^ 2)⁻¹ • (α • b - β • capply starC b) := by
  have h : inverseC α β = fun I J K L => ((α ^ 2 + β ^ 2)⁻¹ * α) * idC I J K L +
      (-((α ^ 2 + β ^ 2)⁻¹ * β)) * starC I J K L := by
    funext I J K L; unfold inverseC; ring
  rw [h, capply_add, capply_smul, capply_smul, capply_idC]
  funext I J
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **`eq:supp-palatini-inverse`**: for `(α, β) ≠ (0, 0)`,
`P_{α,β}^{-1} = (α I - β ⋆)/(α² + β²)` on bivectors (left inverse). -/
theorem inverseC_palatiniC {α β : ℝ} (hαβ : α ^ 2 + β ^ 2 ≠ 0) {b : Fin 4 → Fin 4 → ℝ}
    (hb : IsAntisymm b) : capply (inverseC α β) (capply (palatiniC α β) b) = b := by
  rw [capply_inverseC, capply_palatiniC, capply_linear_add, capply_linear_smul,
    capply_linear_smul, star_star hb]
  funext I J
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
  field_simp
  ring

/-- **`eq:supp-palatini-inverse`** (right inverse). -/
theorem palatiniC_inverseC {α β : ℝ} (hαβ : α ^ 2 + β ^ 2 ≠ 0) {b : Fin 4 → Fin 4 → ℝ}
    (hb : IsAntisymm b) : capply (palatiniC α β) (capply (inverseC α β) b) = b := by
  rw [capply_palatiniC, capply_inverseC, capply_linear_smul, capply_linear_sub,
    capply_linear_smul, capply_linear_smul, star_star hb]
  funext I J
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
  field_simp
  ring

/-- `(α, β) ≠ (0, 0)` iff `α² + β² ≠ 0`. -/
theorem sq_add_sq_ne_zero {α β : ℝ} (h : (α, β) ≠ (0, 0)) : α ^ 2 + β ^ 2 ≠ 0 := by
  intro h0
  apply h
  have hα : α = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
  have hβ : β = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
  simp [hα, hβ]

/-! ### Lorentz connections commute with the star -/

/-- Infinitesimal action of a connection coefficient `w^I_K` on internal two-index arrays:
`(w · b)^{IJ} = w^I_K b^{KJ} + w^J_K b^{IK}`. -/
def act (w : Fin 4 → Fin 4 → ℝ) (b : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun I J => ∑ K, (w I K * b K J + w J K * b I K)

/-- `w` is a Lorentz (`so(1,3)`) coefficient: `w_{IK} = η_{II} w^I_K` is antisymmetric. -/
def IsLorentz (w : Fin 4 → Fin 4 → ℝ) : Prop := ∀ I K, eta I * w I K = -(eta K * w K I)

/-- Every Lorentz coefficient is `η_{II}(a_{IK} - a_{KI})` for some array `a`. -/
theorem isLorentz_param {w : Fin 4 → Fin 4 → ℝ} (hw : IsLorentz w) :
    w = fun I K => eta I * ((eta I * w I K / 2) - (eta K * w K I / 2)) := by
  funext I K
  have h' : eta K * w K I = -(eta I * w I K) := by linarith [hw I K]
  have hs := eta_sq I
  show w I K = eta I * (eta I * w I K / 2 - eta K * w K I / 2)
  rw [h']
  have : eta I * (eta I * w I K / 2 - -(eta I * w I K) / 2) = (eta I * eta I) * w I K := by ring
  rw [this, hs, one_mul]

theorem star_act_comm_param (a : Fin 4 → Fin 4 → ℝ) (b : Fin 4 → Fin 4 → ℝ) :
    capply starC (act (fun I K => eta I * (a I K - a K I)) b) =
      act (fun I K => eta I * (a I K - a K I)) (capply starC b) := by
  rw [capply_starC_eq, capply_starC_eq]
  funext I J
  fin_cases I <;> fin_cases J <;> simp [starTable, act, Fin.sum_univ_four, eta] <;> ring

/-- **The internal star commutes with every Lorentz connection coefficient.** -/
theorem star_act_comm {w : Fin 4 → Fin 4 → ℝ} (hw : IsLorentz w) (b : Fin 4 → Fin 4 → ℝ) :
    capply starC (act w b) = act w (capply starC b) := by
  rw [isLorentz_param hw]
  exact star_act_comm_param _ b

theorem act_add (w : Fin 4 → Fin 4 → ℝ) (b b' : Fin 4 → Fin 4 → ℝ) :
    act w (b + b') = act w b + act w b' := by
  funext I J
  simp only [act, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem act_smul (w : Fin 4 → Fin 4 → ℝ) (r : ℝ) (b : Fin 4 → Fin 4 → ℝ) :
    act w (r • b) = r • act w b := by
  funext I J
  simp only [act, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => by ring

/-- `P_{α,β}` commutes with every Lorentz connection coefficient. -/
theorem palatini_act_comm {w : Fin 4 → Fin 4 → ℝ} (hw : IsLorentz w) (α β : ℝ)
    (b : Fin 4 → Fin 4 → ℝ) :
    capply (palatiniC α β) (act w b) = act w (capply (palatiniC α β) b) := by
  rw [capply_palatiniC, capply_palatiniC, act_add, act_smul, act_smul, star_act_comm hw]

/-! ## Calculus on the chart `ℝ⁴` -/

/-- Chart points. -/
abbrev Pt : Type := Fin 4 → ℝ

/-- Coordinate partial derivative `∂_μ f(x)` (Fréchet derivative along `e_μ`). -/
def pd (μ : Fin 4) (f : Pt → ℝ) (x : Pt) : ℝ := fderiv ℝ f x (Pi.single μ 1)

theorem pd_add {f g : Pt → ℝ} {x : Pt} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    pd μ (fun y => f y + g y) x = pd μ f x + pd μ g x := by
  unfold pd; change fderiv ℝ (f + g) x _ = _; rw [(hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]; rfl

theorem pd_sub {f g : Pt → ℝ} {x : Pt} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    pd μ (fun y => f y - g y) x = pd μ f x - pd μ g x := by
  unfold pd; change fderiv ℝ (f - g) x _ = _; rw [(hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]; rfl

/-- The Leibniz rule `∂_μ (f g) = (∂_μ f) g + f ∂_μ g`. -/
theorem pd_mul {f g : Pt → ℝ} {x : Pt} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    pd μ (fun y => f y * g y) x = pd μ f x * g x + f x * pd μ g x := by
  unfold pd; change fderiv ℝ (f * g) x _ = _; rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem pd_const_mul {f : Pt → ℝ} {x : Pt} (hf : DifferentiableAt ℝ f x) (c : ℝ) (μ : Fin 4) :
    pd μ (fun y => c * f y) x = c * pd μ f x := by
  unfold pd; rw [(hf.hasFDerivAt.const_mul c).fderiv]; rfl

theorem pd_sum {ι : Type*} (s : Finset ι) {f : ι → Pt → ℝ} {x : Pt}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (μ : Fin 4) :
    pd μ (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, pd μ (f i) x := by
  unfold pd
  rw [(HasFDerivAt.fun_sum fun i hi => (hf i hi).hasFDerivAt).fderiv]
  simp

/-! ## Torsion, the coframe bivector and the exterior covariant derivative -/

/-- Torsion `T^I = De^I`:
`T^I_{μν} = ∂_μ e^I_ν - ∂_ν e^I_μ + ω^I_{Kμ} e^K_ν - ω^I_{Kν} e^K_μ`. -/
def torsion (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ) (x : Pt) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun I μ ν => pd μ (fun y => e y I ν) x - pd ν (fun y => e y I μ) x +
    ∑ K, (ω x I K μ * e x K ν - ω x I K ν * e x K μ)

/-- The coframe bivector two-form `B^{IJ} = e^I ∧ e^J`,
`B^{IJ}_{μν} = e^I_μ e^J_ν - e^I_ν e^J_μ`. -/
def bivectorField (e : Pt → Fin 4 → Fin 4 → ℝ) : Pt → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun y I J μ ν => e y I μ * e y J ν - e y I ν * e y J μ

/-- One cyclic term of the exterior covariant derivative of an internal-bivector-valued
two-form: `∂_μ F^{IJ}_{νρ} + ω^I_{Kμ} F^{KJ}_{νρ} + ω^J_{Kμ} F^{IK}_{νρ}` (an internal array). -/
def covTerm (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ) (F : Pt → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Pt) (μ ν ρ : Fin 4) : Fin 4 → Fin 4 → ℝ :=
  fun A C => pd μ (fun y => F y A C ν ρ) x + act (fun P Q => ω x P Q μ) (fun P Q => F x P Q ν ρ) A C

/-- The exterior covariant derivative `(DF)^{IJ}_{μνρ}` (cyclic sum of `covTerm`). -/
def covD (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ) (F : Pt → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Pt) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun I J μ ν ρ => covTerm ω F x μ ν ρ I J + covTerm ω F x ν ρ μ I J + covTerm ω F x ρ μ ν I J

/-- The Cartan map `𝒦_e(T)^{IJ} = T^I ∧ e^J - e^I ∧ T^J` (three-form components). -/
def cartan (E : Fin 4 → Fin 4 → ℝ) (T : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun I J μ ν ρ => (T I μ ν * E J ρ + T I ν ρ * E J μ + T I ρ μ * E J ν) -
    (E I μ * T J ν ρ + E I ν * T J ρ μ + E I ρ * T J μ ν)

theorem pd_bivectorField {e : Pt → Fin 4 → Fin 4 → ℝ} {x : Pt}
    (he : ∀ I μ, DifferentiableAt ℝ (fun y => e y I μ) x) (μ : Fin 4) (I J ν ρ : Fin 4) :
    pd μ (fun y => bivectorField e y I J ν ρ) x =
      (pd μ (fun y => e y I ν) x * e x J ρ + e x I ν * pd μ (fun y => e y J ρ) x) -
        (pd μ (fun y => e y I ρ) x * e x J ν + e x I ρ * pd μ (fun y => e y J ν) x) := by
  unfold bivectorField
  rw [pd_sub (f := fun y => e y I ν * e y J ρ) (g := fun y => e y I ρ * e y J ν)
    ((he I ν).mul (he J ρ)) ((he I ρ).mul (he J ν)), pd_mul (he I ν) (he J ρ),
    pd_mul (he I ρ) (he J ν)]

/-- **Leibniz identity** `D(e^I ∧ e^J) = T^I ∧ e^J - e^I ∧ T^J` (for any connection). -/
theorem covD_bivectorField (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Pt) (he : ∀ I μ, DifferentiableAt ℝ (fun y => e y I μ) x) :
    covD ω (bivectorField e) x = cartan (e x) (torsion e ω x) := by
  funext I J μ ν ρ
  simp only [covD, covTerm, pd_bivectorField he]
  simp only [cartan, torsion, act, bivectorField, Fin.sum_univ_four]
  ring

/-- Constant internal coefficient maps pass through the exterior covariant derivative when
they commute with the connection action: `D(c F) = c (D F)`. -/
theorem covD_capply (c : Coeff) (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (F : Pt → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (x : Pt)
    (hF : ∀ A C ν ρ, DifferentiableAt ℝ (fun y => F y A C ν ρ) x)
    (hc : ∀ μ b, capply c (act (fun P Q => ω x P Q μ) b) = act (fun P Q => ω x P Q μ) (capply c b)) :
    covD ω (fun y I J μ ν => capply c (fun A C => F y A C μ ν) I J) x =
      fun I J μ ν ρ => capply c (fun A C => covD ω F x A C μ ν ρ) I J := by
  have hterm : ∀ μ ν ρ, covTerm ω (fun y I J μ ν => capply c (fun A C => F y A C μ ν) I J) x μ ν ρ
      = capply c (covTerm ω F x μ ν ρ) := fun μ ν ρ => by
    have hpd : (fun A C => pd μ (fun y => capply c (fun P Q => F y P Q ν ρ) A C) x) =
        capply c (fun P Q => pd μ (fun y => F y P Q ν ρ) x) := by
      funext A C
      unfold capply
      rw [pd_sum _ (fun K _ => DifferentiableAt.fun_sum fun L _ =>
        (hF K L ν ρ).const_mul _)]
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [pd_sum _ (fun L _ => (hF K L ν ρ).const_mul _)]
      exact Finset.sum_congr rfl fun L _ => pd_const_mul (hF K L ν ρ) _ μ
    have hsplit : covTerm ω F x μ ν ρ = (fun P Q => pd μ (fun y => F y P Q ν ρ) x) +
        act (fun P Q => ω x P Q μ) (fun P Q => F x P Q ν ρ) := rfl
    rw [hsplit, capply_linear_add, hc μ, ← hpd]
    rfl
  funext I J μ ν ρ
  simp only [covD, hterm]
  simp only [capply, mul_add, Finset.sum_add_distrib]

/-- **`D(P_{α,β} B) = P_{α,β} 𝒦_e(T)`** for a Lorentz connection: the Leibniz identity and the
commutation of `P_{α,β}` with the connection action. -/
theorem covD_palatini_bivector (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ)
    (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ) (x : Pt)
    (he : ∀ I μ, DifferentiableAt ℝ (fun y => e y I μ) x)
    (hω : ∀ μ, IsLorentz (fun P Q => ω x P Q μ)) :
    covD ω (fun y I J μ ν => capply (palatiniC α β) (fun A C => bivectorField e y A C μ ν) I J) x =
      fun I J μ ν ρ => capply (palatiniC α β)
        (fun A C => cartan (e x) (torsion e ω x) A C μ ν ρ) I J := by
  have hB : ∀ A C ν ρ, DifferentiableAt ℝ (fun y => bivectorField e y A C ν ρ) x :=
    fun A C ν ρ => ((he A ν).mul (he C ρ)).sub ((he A ρ).mul (he C ν))
  rw [covD_capply (palatiniC α β) ω (bivectorField e) x hB
    (fun μ b => palatini_act_comm (hω μ) α β b), covD_bivectorField e ω x he]

/-! ## Injectivity of the Cartan map for a nondegenerate coframe -/

section Injectivity

open CartanInjectivity

private theorem tripleSum_A (f : Fin 4 → Fin 4 → ℝ) (g a b c : Fin 4 → ℝ) :
    ∑ μ, ∑ ν, ∑ ρ, f μ ν * g ρ * a μ * b ν * c ρ =
      (∑ μ, ∑ ν, f μ ν * a μ * b ν) * (∑ ρ, g ρ * c ρ) := by
  simp only [Fin.sum_univ_four]; ring

private theorem tripleSum_B (f : Fin 4 → Fin 4 → ℝ) (g a b c : Fin 4 → ℝ) :
    ∑ μ, ∑ ν, ∑ ρ, f ν ρ * g μ * a μ * b ν * c ρ =
      (∑ ν, ∑ ρ, f ν ρ * b ν * c ρ) * (∑ μ, g μ * a μ) := by
  simp only [Fin.sum_univ_four]; ring

private theorem tripleSum_C (f : Fin 4 → Fin 4 → ℝ) (g a b c : Fin 4 → ℝ) :
    ∑ μ, ∑ ν, ∑ ρ, f ρ μ * g ν * a μ * b ν * c ρ =
      (∑ ρ, ∑ μ, f ρ μ * c ρ * a μ) * (∑ ν, g ν * b ν) := by
  simp only [Fin.sum_univ_four]; ring

private theorem tripleSum_D (f : Fin 4 → Fin 4 → ℝ) (g a b c : Fin 4 → ℝ) :
    ∑ μ, ∑ ν, ∑ ρ, g μ * f ν ρ * a μ * b ν * c ρ =
      (∑ ν, ∑ ρ, f ν ρ * b ν * c ρ) * (∑ μ, g μ * a μ) := by
  simp only [Fin.sum_univ_four]; ring

private theorem tripleSum_E (f : Fin 4 → Fin 4 → ℝ) (g a b c : Fin 4 → ℝ) :
    ∑ μ, ∑ ν, ∑ ρ, g ν * f ρ μ * a μ * b ν * c ρ =
      (∑ ρ, ∑ μ, f ρ μ * c ρ * a μ) * (∑ ν, g ν * b ν) := by
  simp only [Fin.sum_univ_four]; ring

private theorem tripleSum_F (f : Fin 4 → Fin 4 → ℝ) (g a b c : Fin 4 → ℝ) :
    ∑ μ, ∑ ν, ∑ ρ, g ρ * f μ ν * a μ * b ν * c ρ =
      (∑ μ, ∑ ν, f μ ν * a μ * b ν) * (∑ ρ, g ρ * c ρ) := by
  simp only [Fin.sum_univ_four]; ring

private theorem quadSum (f : Fin 4 → Fin 4 → ℝ) (p q r s : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) :
    ∑ K, ∑ L, (∑ a, ∑ b, f a b * p a K * q b L) * r K μ * s L ν =
      ∑ a, ∑ b, f a b * (∑ K, p a K * r K μ) * (∑ L, q b L * s L ν) := by
  simp only [Fin.sum_univ_four]; ring

/-- Torsion coefficients in the coframe basis: `τ^I_{KL} = T^I_{μν} (e⁻¹)^μ_K (e⁻¹)^ν_L`. -/
def frameTorsion (E : Matrix (Fin 4) (Fin 4) ℝ) (T : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun I K L => ∑ μ, ∑ ν, T I μ ν * E⁻¹ μ K * E⁻¹ ν L

theorem sum_mul_inv_eq (E : Matrix (Fin 4) (Fin 4) ℝ) (hE : IsUnit E.det) (J M : Fin 4) :
    ∑ ρ, E J ρ * E⁻¹ ρ M = kd J M := by
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv E hE) J) M
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [h]; rfl

theorem sum_inv_mul_eq (E : Matrix (Fin 4) (Fin 4) ℝ) (hE : IsUnit E.det) (a μ : Fin 4) :
    ∑ K, E⁻¹ a K * E K μ = if a = μ then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul E hE) a) μ
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  exact h

/-- The coordinate Cartan map is the coframe-basis index chase `kart` after the change of
basis: `kart τ = 𝒦_e(T) (e⁻¹, e⁻¹, e⁻¹)`. -/
theorem kart_frameTorsion (E : Matrix (Fin 4) (Fin 4) ℝ) (hE : IsUnit E.det)
    (T : Fin 4 → Fin 4 → Fin 4 → ℝ) (I J K L M : Fin 4) :
    kart (frameTorsion E T) I J K L M =
      ∑ μ, ∑ ν, ∑ ρ, cartan E T I J μ ν ρ * E⁻¹ μ K * E⁻¹ ν L * E⁻¹ ρ M := by
  simp only [cartan, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [tripleSum_A (T I) (E J), tripleSum_B (T I) (E J), tripleSum_C (T I) (E J),
    tripleSum_D (T J) (E I), tripleSum_E (T J) (E I), tripleSum_F (T J) (E I)]
  simp only [sum_mul_inv_eq E hE, kart, frameTorsion]
  ring

/-- Reconstruction `T^I_{μν} = τ^I_{KL} e^K_μ e^L_ν`. -/
theorem torsion_eq_frameTorsion (E : Matrix (Fin 4) (Fin 4) ℝ) (hE : IsUnit E.det)
    (T : Fin 4 → Fin 4 → Fin 4 → ℝ) (I μ ν : Fin 4) :
    T I μ ν = ∑ K, ∑ L, frameTorsion E T I K L * E K μ * E L ν := by
  simp only [frameTorsion]
  rw [quadSum (T I) (E⁻¹ : Matrix (Fin 4) (Fin 4) ℝ) (E⁻¹ : Matrix (Fin 4) (Fin 4) ℝ) E E μ ν]
  simp only [sum_inv_mul_eq E hE, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- **The Cartan map is injective for every nondegenerate coframe** (`det e ≠ 0`): a torsion
array, antisymmetric in its form slots, with `𝒦_e(T) = 0` vanishes. -/
theorem cartan_injective_of_isUnit_det (E : Matrix (Fin 4) (Fin 4) ℝ) (hE : IsUnit E.det)
    {T : Fin 4 → Fin 4 → Fin 4 → ℝ} (hT : ∀ I μ ν, T I μ ν = -T I ν μ)
    (h : cartan E T = 0) : T = 0 := by
  have hτanti : ∀ I K L, frameTorsion E T I K L = -frameTorsion E T I L K := by
    intro I K L
    simp only [frameTorsion]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hT I ν μ]; ring
  have hkart : ∀ I J K L M, kart (frameTorsion E T) I J K L M = 0 := by
    intro I J K L M
    rw [kart_frameTorsion E hE T]
    simp [h]
  have hτ := cartan_injective hτanti hkart
  funext I μ ν
  rw [torsion_eq_frameTorsion E hE T I μ ν]
  simp [hτ]

end Injectivity

/-! ## Connection stationarity implies vanishing torsion; the finite-cutoff estimate -/

/-- The torsion two-form is antisymmetric in its form slots. -/
theorem torsion_antisymm (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Pt) (I μ ν : Fin 4) : torsion e ω x I μ ν = -torsion e ω x I ν μ := by
  simp only [torsion, Fin.sum_univ_four]; ring

/-- The Cartan image is antisymmetric in its internal indices. -/
theorem cartan_antisymm (E : Fin 4 → Fin 4 → ℝ) (T : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (μ ν ρ : Fin 4) : IsAntisymm (fun I J => cartan E T I J μ ν ρ) := by
  intro I J; simp only [cartan]; ring

/-- The internal action of `P_{α,β}` on three-form arrays. -/
def palatiniApply (α β : ℝ) (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun I J μ ν ρ => capply (palatiniC α β) (fun A B => C A B μ ν ρ) I J

/-- The internal action of `P_{α,β}^{-1}` on three-form arrays. -/
def inverseApply (α β : ℝ) (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun I J μ ν ρ => capply (inverseC α β) (fun A B => C A B μ ν ρ) I J

theorem inverseApply_palatiniApply_cartan {α β : ℝ} (hαβ : α ^ 2 + β ^ 2 ≠ 0)
    (E : Fin 4 → Fin 4 → ℝ) (T : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    inverseApply α β (palatiniApply α β (cartan E T)) = cartan E T := by
  funext I J μ ν ρ
  have := congrFun (congrFun (inverseC_palatiniC hαβ (cartan_antisymm E T μ ν ρ)) I) J
  exact this

/-- The spinless connection Euler residual `D(P_{α,β} B)` at `x`. -/
def eulerResidual (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Pt) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  covD ω (fun y I J μ ν => capply (palatiniC α β) (fun A C => bivectorField e y A C μ ν) I J) x

/-- `D(P_{α,β} B) = P_{α,β} 𝒦_e(T)` (packaged on three-form arrays). -/
theorem eulerResidual_eq (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ)
    (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ) (x : Pt)
    (he : ∀ I μ, DifferentiableAt ℝ (fun y => e y I μ) x)
    (hω : ∀ μ, IsLorentz (fun P Q => ω x P Q μ)) :
    eulerResidual α β e ω x = palatiniApply α β (cartan (e x) (torsion e ω x)) :=
  covD_palatini_bivector α β e ω x he hω

/-- **Connection stationarity implies `T = 0`.**  If `(α, β) ≠ (0, 0)`, the coframe is
nondegenerate at `x` and the connection is a Lorentz connection, the spinless connection Euler
equation `D(P_{α,β} B)(x) = 0` forces `T(x) = 0`. -/
theorem torsion_eq_zero_of_euler {α β : ℝ} (hαβ : (α, β) ≠ (0, 0))
    (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ) (x : Pt)
    (he : ∀ I μ, DifferentiableAt ℝ (fun y => e y I μ) x)
    (hdet : IsUnit (Matrix.det (e x : Matrix (Fin 4) (Fin 4) ℝ)))
    (hω : ∀ μ, IsLorentz (fun P Q => ω x P Q μ))
    (heuler : eulerResidual α β e ω x = 0) : torsion e ω x = 0 := by
  have hs := sq_add_sq_ne_zero hαβ
  have hcart : cartan (e x) (torsion e ω x) = 0 := by
    rw [← inverseApply_palatiniApply_cartan hs, ← eulerResidual_eq α β e ω x he hω, heuler]
    funext I J μ ν ρ
    simp [inverseApply, capply]
  exact cartan_injective_of_isUnit_det (e x) hdet (torsion_antisymm e ω x) hcart

/-- **Finite-cutoff estimate.**  If the Cartan map at the cutoff coframe has a lower
singular-value bound `κ ‖v‖ ≤ ‖𝒦_e v‖` (on torsion arrays antisymmetric in the form slots),
then the torsion is controlled by the connection Euler residual:
`‖T‖ ≤ κ⁻¹ ‖P_{α,β}^{-1}‖ ‖D(P_{α,β} B)‖`, where `‖P_{α,β}^{-1}‖` is the operator norm of
`inverseApply α β` (as a linear map, `inverseApplyCLM`). -/
theorem norm_torsion_le_residual {α β : ℝ} (hαβ : (α, β) ≠ (0, 0))
    (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ) (x : Pt)
    (he : ∀ I μ, DifferentiableAt ℝ (fun y => e y I μ) x)
    (hω : ∀ μ, IsLorentz (fun P Q => ω x P Q μ))
    (Pinv : (Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) →L[ℝ]
      (Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ))
    (hPinv : ∀ C, Pinv C = inverseApply α β C)
    (κ : ℝ) (hκ : 0 < κ)
    (hfloor : ∀ v : Fin 4 → Fin 4 → Fin 4 → ℝ, (∀ I μ ν, v I μ ν = -v I ν μ) →
      κ * ‖v‖ ≤ ‖cartan (e x) v‖) :
    ‖torsion e ω x‖ ≤ κ⁻¹ * (‖Pinv‖ * ‖eulerResidual α β e ω x‖) := by
  have hs := sq_add_sq_ne_zero hαβ
  have hK : cartan (e x) (torsion e ω x) = Pinv (eulerResidual α β e ω x) := by
    rw [hPinv, eulerResidual_eq α β e ω x he hω, inverseApply_palatiniApply_cartan hs]
  have h1 := hfloor _ (torsion_antisymm e ω x)
  rw [hK] at h1
  have h2 := Pinv.le_opNorm (eulerResidual α β e ω x)
  rw [le_inv_mul_iff₀ hκ]
  linarith

/-- `P_{α,β}^{-1}` acting on three-form arrays, as a continuous linear map. -/
def inverseApplyCLM (α β : ℝ) :
    (Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) →L[ℝ]
      (Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := inverseApply α β
      map_add' := fun C D => by
        funext I J μ ν ρ
        simp only [inverseApply, capply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r C => by
        funext I J μ ν ρ
        simp only [inverseApply, capply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => by ring }

/-- **Finite-cutoff estimate** with the concrete inverse:
`‖T‖ ≤ κ⁻¹ ‖P_{α,β}^{-1}‖ ‖D(P_{α,β} B)‖`. -/
theorem norm_torsion_le_residual' {α β : ℝ} (hαβ : (α, β) ≠ (0, 0))
    (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Fin 4 → Fin 4 → Fin 4 → ℝ) (x : Pt)
    (he : ∀ I μ, DifferentiableAt ℝ (fun y => e y I μ) x)
    (hω : ∀ μ, IsLorentz (fun P Q => ω x P Q μ)) (κ : ℝ) (hκ : 0 < κ)
    (hfloor : ∀ v : Fin 4 → Fin 4 → Fin 4 → ℝ, (∀ I μ ν, v I μ ν = -v I ν μ) →
      κ * ‖v‖ ≤ ‖cartan (e x) v‖) :
    ‖torsion e ω x‖ ≤ κ⁻¹ * (‖inverseApplyCLM α β‖ * ‖eulerResidual α β e ω x‖) :=
  norm_torsion_le_residual hαβ e ω x he hω (inverseApplyCLM α β) (fun _ => rfl) κ hκ hfloor

/-! ## Non-vacuity -/

/-- The boost generator `ω^0_1 = ω^1_0 = 1` is a (nonzero) Lorentz coefficient. -/
example : IsLorentz (fun I K => if (I = 0 ∧ K = 1) ∨ (I = 1 ∧ K = 0) then 1 else 0) := by
  intro I K
  fin_cases I <;> fin_cases K <;> simp [eta]

/-- The internal star is nontrivial: `⋆(e^0 ∧ e^1) = -(e^2 ∧ e^3)` in components. -/
example : capply starC (fun I J => if I = 0 ∧ J = 1 then 1 else if I = 1 ∧ J = 0 then -1 else 0)
    2 3 = -1 := by
  rw [capply_starC_eq]; simp [starTable]

/-- The hypotheses of `torsion_eq_zero_of_euler` are jointly satisfiable (identity coframe,
vanishing connection, `α = 1`, `β = 0`). -/
example (x : Pt) : torsion (fun _ I μ => if I = μ then 1 else 0) (fun _ _ _ _ => 0) x = 0 := by
  have he : ∀ I μ : Fin 4, DifferentiableAt ℝ (fun _ : Pt => if I = μ then (1 : ℝ) else 0) x :=
    fun I μ => differentiableAt_const (if I = μ then (1 : ℝ) else 0)
  have hT : torsion (fun _ I μ => if I = μ then 1 else 0) (fun _ _ _ _ => 0) x = 0 := by
    funext I μ ν
    simp [torsion, pd]
  refine torsion_eq_zero_of_euler (α := 1) (β := 0) (by simp) _ _ x he ?_ (fun μ I K => by simp)
    ?_
  · have : ((fun I μ => if I = μ then (1 : ℝ) else 0 : Fin 4 → Fin 4 → ℝ) :
        Matrix (Fin 4) (Fin 4) ℝ) = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
      ext I μ; rw [Matrix.one_apply]
    rw [this, Matrix.det_one]
    exact isUnit_one
  · rw [eulerResidual_eq 1 0 _ _ x he (fun μ I K => by simp), hT]
    funext I J μ ν ρ
    simp [palatiniApply, cartan, capply]

end RenewalGeometry.PalatiniTorsionModel
