/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SlabWaveEnergyHk

/-!
# Wave energy with the normal-derivative multiplier (nonzero shift) on `[0, T] × 𝕋³`

Generic infrastructure (no renewal notions) for `thm:hyperbolic` of the Einstein–Standard-Model
action-closure manuscript ("use the differentiated normal derivative as energy multiplier … The
uniformly spacelike slices and bounded lapse and shift give a positive wave energy").

For the normal form `∂ₜ²u = 2βⁱ∂ᵢ∂ₜu + γ^{ij}∂ᵢ∂ⱼu + L + F` the `∂ₜ`-multiplier energy
`|∂ₜu|² + γ^{ij}∂ᵢu∂ⱼu` of `SlabWaveEnergyHk.lean` is positive only when `γ` is positive, i.e. when
`∂ₜ` is timelike (small shift).  The principal operator is `D² - a^{ij}∂ᵢ∂ⱼ + (lower order)` with
the normal derivative `D = ∂ₜ - βⁱ∂ᵢ` and `a^{ij} = γ^{ij} + βⁱβʲ` (`= N² h^{ij}`: lapse squared
times the inverse induced metric of the slices), so the energy with the multiplier `Du`,

`E_S(t) = ∫_{[0,1]³} Σ_b ((∂ₜu_b - βᵏ∂ₖu_b)² + a^{ij}∂ᵢu_b∂ⱼu_b + u_b²)`,

is positive as soon as `a` is uniformly positive (uniformly spacelike slices), for any bounded
shift.  Space is `𝕋³` (`d = 3`, the setting of `thm:hyperbolic`).

* `shift_alg` — the pointwise energy identity `∂ₜe - Σᵢ∂ᵢJⁱ = G` (a polynomial identity checked by
  `ring`), `G` free of second derivatives.
* `ShL2Hyp`, **`ShL2Hyp.sqrt_energyS_le`** — `√E_S(t) ≤ (√E_S(0) + ∫₀ᵗ ‖F‖_{L²}) exp(½∫₀ᵗ k)`;
  `ShL2Hyp.sqrt_energyS_le_of_forcing` (forcing controlled by the energy).
* `SysHyp.toShL2Hyp`, **`hkS_energy`**, `hkS_energy_of_forcing` — the `H^k` version through the
  prolongation of `SlabWaveEnergyHk.lean` (`SysHyp` with *any* coercivity constant for `γ`, plus
  coercivity of `a = γ + ββ` and a bound for `∂ₜβ`).
* `energySK_ge`, `energySK_le_size`, **`energySK_tendsto_zero`** — the order-`k` shifted energy
  controls every word derivative, is controlled by the classical norms, and the convergence step
  of `thm:hyperbolic`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.SlabWaveShift

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk

set_option linter.unusedSectionVars false

/-- Space-time `ℝ^{1+3}`. -/
abbrev X3 := ST 3

/-! ### The pointwise algebra -/

/-- `∂ᵢ(Du)` in terms of the jets: `vxᵢ = ∂ᵢ∂ₜu - Σₖ(∂ᵢβᵏ ∂ₖu + βᵏ∂ᵢ∂ₖu)`. -/
def vxv (uxt β ux : Fin 3 → ℝ) (βx uxx : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  uxt i - ∑ k, (βx k i * ux k + β k * uxx k i)

/-- The time derivative of the energy density, in terms of the jets. -/
def etv (v ut utt u : ℝ) (β βt ux uxt : Fin 3 → ℝ) (a at' : Fin 3 → Fin 3 → ℝ) : ℝ :=
  2 * v * (utt - ∑ k, (βt k * ux k + β k * uxt k)) +
    ∑ i, ∑ j, (at' i j * ux i * ux j + a i j * uxt i * ux j + a i j * ux i * uxt j) + 2 * u * ut

/-- `∂ᵢJⁱ` (no summation) in terms of the jets, `Jⁱ = βⁱv² + 2v a^{ij}∂ⱼu + βⁱa^{jl}∂ⱼu∂ₗu`. -/
def dJv (v : ℝ) (β ux uxt : Fin 3 → ℝ) (βx a uxx : Fin 3 → Fin 3 → ℝ)
    (ax : Fin 3 → Fin 3 → Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  βx i i * v ^ 2 + β i * (2 * v * vxv uxt β ux βx uxx i) +
    (2 * vxv uxt β ux βx uxx i * ∑ j, a i j * ux j +
      2 * v * ∑ j, (ax i i j * ux j + a i j * uxx j i)) +
    (βx i i * ∑ j, ∑ l, a j l * ux j * ux l +
      β i * ∑ j, ∑ l, (ax i j l * ux j * ux l + a j l * uxx j i * ux l + a j l * ux j * uxx l i))

/-- The remainder `G` of the energy identity (first-order jets only). -/
def Gv (v ut u R : ℝ) (β βt ux : Fin 3 → ℝ) (βx a at' : Fin 3 → Fin 3 → ℝ)
    (ax : Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  2 * v * R - 2 * v * ∑ k, βt k * ux k + ∑ i, ∑ j, at' i j * ux i * ux j + 2 * u * ut -
    (∑ i, βx i i) * v ^ 2 + 2 * v * ∑ i, ∑ k, β i * βx k i * ux k +
    2 * ∑ i, ∑ j, ∑ k, a i j * βx k i * ux j * ux k - 2 * v * ∑ i, ∑ j, ax i i j * ux j -
    (∑ i, βx i i) * ∑ j, ∑ l, a j l * ux j * ux l - ∑ i, β i * ∑ j, ∑ l, ax i j l * ux j * ux l

set_option maxHeartbeats 4000000 in
/-- **The pointwise energy identity** for the normal-derivative multiplier:
`∂ₜe - Σᵢ ∂ᵢJⁱ = G` once `∂ₜ²u = 2βⁱ∂ᵢ∂ₜu + (a^{ij} - βⁱβʲ)∂ᵢ∂ⱼu + R`. -/
theorem shift_alg (v ut utt u R : ℝ) (β βt ux uxt : Fin 3 → ℝ)
    (βx a at' uxx : Fin 3 → Fin 3 → ℝ) (ax : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (ha : ∀ i j, a i j = a j i) (hu : ∀ i j, uxx i j = uxx j i)
    (heq : utt = 2 * ∑ i, β i * uxt i + ∑ i, ∑ j, (a i j - β i * β j) * uxx j i + R) :
    etv v ut utt u β βt ux uxt a at' - ∑ i, dJv v β ux uxt βx a uxx ax i =
      Gv v ut u R β βt ux βx a at' ax := by
  subst heq
  simp only [etv, dJv, Gv, vxv, Fin.sum_univ_three]
  rw [ha 1 0, ha 2 0, ha 2 1, hu 1 0, hu 2 0, hu 2 1]
  ring

/-! #### The bound of the remainder -/

theorem abs_sum3_le {f : Fin 3 → ℝ} {c : ℝ} (h : ∀ i, |f i| ≤ c) : |∑ i, f i| ≤ 3 * c := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |f i| ≤ ∑ _i : Fin 3, c := Finset.sum_le_sum fun i _ => h i
    _ = 3 * c := by simp

theorem abs_mul_le_of {p q P Q : ℝ} (hp : |p| ≤ P) (hq : |q| ≤ Q) : |p * q| ≤ P * Q := by
  rw [abs_mul]; exact mul_le_mul hp hq (abs_nonneg _) ((abs_nonneg _).trans hp)

/-- The constant of `Gv_le`. -/
def Kc (M A : ℝ) : ℝ := 2 + 9 * M + 18 * M ^ 2 + 27 * A + 108 * A * M

theorem Kc_nonneg {M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) : 0 ≤ Kc M A := by
  unfold Kc; positivity

/-- **The remainder is bounded by the squared jets**: with coefficients bounded by `M` (`β, ∂β`)
and `A` (`a, ∂a`) and first jets bounded by `r`, `G ≤ K r²` (no source). -/
theorem Gv_le (v ut u : ℝ) (β βt ux : Fin 3 → ℝ) (βx a at' : Fin 3 → Fin 3 → ℝ)
    (ax : Fin 3 → Fin 3 → Fin 3 → ℝ) {M A r : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hβ : ∀ k, |β k| ≤ M) (hβt : ∀ k, |βt k| ≤ M) (hβx : ∀ k i, |βx k i| ≤ M)
    (ha : ∀ i j, |a i j| ≤ A) (hat : ∀ i j, |at' i j| ≤ A) (hax : ∀ i j l, |ax i j l| ≤ A)
    (hv : |v| ≤ r) (hut : |ut| ≤ r) (hu : |u| ≤ r) (hux : ∀ k, |ux k| ≤ r) :
    Gv v ut u 0 β βt ux βx a at' ax ≤ Kc M A * r ^ 2 := by
  have hx2 : ∀ i j, |ux i * ux j| ≤ r * r := fun i j => abs_mul_le_of (hux i) (hux j)
  -- the groups
  have g1 : |2 * v * ∑ k, βt k * ux k| ≤ 2 * r * (3 * (M * r)) := by
    refine abs_mul_le_of ?_ (abs_sum3_le fun k => abs_mul_le_of (hβt k) (hux k))
    rw [abs_mul, abs_two]; linarith
  have g2 : |∑ i, ∑ j, at' i j * ux i * ux j| ≤ 3 * (3 * (A * (r * r))) :=
    abs_sum3_le fun i => abs_sum3_le fun j => by
      rw [mul_assoc]; exact abs_mul_le_of (hat i j) (hx2 i j)
  have g3 : |2 * u * ut| ≤ 2 * r * r := by
    refine abs_mul_le_of ?_ hut
    rw [abs_mul, abs_two]; linarith
  have hbd : |∑ i, βx i i| ≤ 3 * M := abs_sum3_le fun i => hβx i i
  have g4 : |(∑ i, βx i i) * v ^ 2| ≤ 3 * M * (r * r) :=
    abs_mul_le_of hbd (by rw [sq]; exact abs_mul_le_of hv hv)
  have g5 : |2 * v * ∑ i, ∑ k, β i * βx k i * ux k| ≤ 2 * r * (3 * (3 * (M * M * r))) := by
    refine abs_mul_le_of ?_ (abs_sum3_le fun i => abs_sum3_le fun k =>
      abs_mul_le_of (abs_mul_le_of (hβ i) (hβx k i)) (hux k))
    rw [abs_mul, abs_two]; linarith
  have g6 : |2 * ∑ i, ∑ j, ∑ k, a i j * βx k i * ux j * ux k| ≤
      2 * (3 * (3 * (3 * (A * M * (r * r))))) := by
    refine abs_mul_le_of (by rw [abs_two]) (abs_sum3_le fun i => abs_sum3_le fun j =>
      abs_sum3_le fun k => ?_)
    rw [mul_assoc]; exact abs_mul_le_of (abs_mul_le_of (ha i j) (hβx k i)) (hx2 j k)
  have g7 : |2 * v * ∑ i, ∑ j, ax i i j * ux j| ≤ 2 * r * (3 * (3 * (A * r))) := by
    refine abs_mul_le_of ?_ (abs_sum3_le fun i => abs_sum3_le fun j =>
      abs_mul_le_of (hax i i j) (hux j))
    rw [abs_mul, abs_two]; linarith
  have g8 : |(∑ i, βx i i) * ∑ j, ∑ l, a j l * ux j * ux l| ≤ 3 * M * (3 * (3 * (A * (r * r)))) :=
    abs_mul_le_of hbd (abs_sum3_le fun j => abs_sum3_le fun l => by
      rw [mul_assoc]; exact abs_mul_le_of (ha j l) (hx2 j l))
  have g9 : |∑ i, β i * ∑ j, ∑ l, ax i j l * ux j * ux l| ≤ 3 * (M * (3 * (3 * (A * (r * r))))) :=
    abs_sum3_le fun i => abs_mul_le_of (hβ i) (abs_sum3_le fun j => abs_sum3_le fun l => by
      rw [mul_assoc]; exact abs_mul_le_of (hax i j l) (hx2 j l))
  have e : Gv v ut u 0 β βt ux βx a at' ax =
      -(2 * v * ∑ k, βt k * ux k) + (∑ i, ∑ j, at' i j * ux i * ux j) + 2 * u * ut -
      (∑ i, βx i i) * v ^ 2 + 2 * v * ∑ i, ∑ k, β i * βx k i * ux k +
      2 * ∑ i, ∑ j, ∑ k, a i j * βx k i * ux j * ux k - 2 * v * ∑ i, ∑ j, ax i i j * ux j -
      (∑ i, βx i i) * ∑ j, ∑ l, a j l * ux j * ux l -
      ∑ i, β i * ∑ j, ∑ l, ax i j l * ux j * ux l := by
    unfold Gv; ring
  rw [e]
  have l1 := neg_abs_le (2 * v * ∑ k, βt k * ux k)
  have l2 := le_abs_self (∑ i, ∑ j, at' i j * ux i * ux j)
  have l3 := le_abs_self (2 * u * ut)
  have l4 := neg_abs_le ((∑ i, βx i i) * v ^ 2)
  have l5 := le_abs_self (2 * v * ∑ i, ∑ k, β i * βx k i * ux k)
  have l6 := le_abs_self (2 * ∑ i, ∑ j, ∑ k, a i j * βx k i * ux j * ux k)
  have l7 := neg_abs_le (2 * v * ∑ i, ∑ j, ax i i j * ux j)
  have l8 := neg_abs_le ((∑ i, βx i i) * ∑ j, ∑ l, a j l * ux j * ux l)
  have l9 := neg_abs_le (∑ i, β i * ∑ j, ∑ l, ax i j l * ux j * ux l)
  have hK : Kc M A * r ^ 2 = 2 * r * (3 * (M * r)) + 3 * (3 * (A * (r * r))) + 2 * r * r +
      3 * M * (r * r) + 2 * r * (3 * (3 * (M * M * r))) +
      2 * (3 * (3 * (3 * (A * M * (r * r))))) + 2 * r * (3 * (3 * (A * r))) +
      3 * M * (3 * (3 * (A * (r * r)))) + 3 * (M * (3 * (3 * (A * (r * r))))) := by
    unfold Kc; ring
  rw [hK]
  linarith

/-! ### Fields -/

variable {ι : Type*} [Fintype ι]

/-- The normal derivative `Du = ∂ₜu - βᵏ∂ₖu`. -/
def nder (β : Fin 3 → X3 → ℝ) (u : X3 → ℝ) (x : X3) : ℝ :=
  pd u 0 x - ∑ k : Fin 3, β k x * pd u k.succ x

/-- `a^{ij} = γ^{ij} + βⁱβʲ`. -/
def acoef (β : Fin 3 → X3 → ℝ) (γ : Fin 3 → Fin 3 → X3 → ℝ) (i j : Fin 3) (x : X3) : ℝ :=
  γ i j x + β i x * β j x

/-- `∂ₜa^{ij}`. -/
def acoefT (β : Fin 3 → X3 → ℝ) (γ : Fin 3 → Fin 3 → X3 → ℝ) (i j : Fin 3) (x : X3) : ℝ :=
  pd (γ i j) 0 x + pd (β i) 0 x * β j x + β i x * pd (β j) 0 x

/-- `∂ᵢa^{jl}`. -/
def acoefX (β : Fin 3 → X3 → ℝ) (γ : Fin 3 → Fin 3 → X3 → ℝ) (i j l : Fin 3) (x : X3) : ℝ :=
  pd (γ j l) i.succ x + pd (β j) i.succ x * β l x + β j x * pd (β l) i.succ x

/-- The energy density of one component, `(Du)² + a^{ij}∂ᵢu∂ⱼu + u²`. -/
def dens1 (β : Fin 3 → X3 → ℝ) (γ : Fin 3 → Fin 3 → X3 → ℝ) (u : X3 → ℝ) (x : X3) : ℝ :=
  nder β u x ^ 2 + ∑ i : Fin 3, ∑ j : Fin 3, acoef β γ i j x * pd u i.succ x * pd u j.succ x +
    u x ^ 2

/-- The energy density `Σ_b ((Du_b)² + a^{ij}∂ᵢu_b∂ⱼu_b + u_b²)`. -/
def densS (β : Fin 3 → X3 → ℝ) (γ : Fin 3 → Fin 3 → X3 → ℝ) (u : ι → X3 → ℝ) (x : X3) : ℝ :=
  ∑ b, dens1 β γ (u b) x

/-- **The energy with the normal-derivative multiplier**, `E_S(t) = ∫_{[0,1]³} densS(t, y) dy`. -/
def energyS (β : Fin 3 → X3 → ℝ) (γ : Fin 3 → Fin 3 → X3 → ℝ) (u : ι → X3 → ℝ) (t : ℝ) : ℝ :=
  ∫ y in Icc (0 : Fin 3 → ℝ) 1, densS β γ u (Fin.cons t y)

/-- The time derivative of the density of one component. -/
def densT1 (β : Fin 3 → X3 → ℝ) (γ : Fin 3 → Fin 3 → X3 → ℝ) (u : X3 → ℝ) (x : X3) : ℝ :=
  etv (nder β u x) (pd u 0 x) (pd (pd u 0) 0 x) (u x) (fun k => β k x) (fun k => pd (β k) 0 x)
    (fun k => pd u k.succ x) (fun i => pd (pd u 0) i.succ x) (fun i j => acoef β γ i j x)
    (fun i j => acoefT β γ i j x)

/-- The remainder of one component with source `R`. -/
def densG1 (β : Fin 3 → X3 → ℝ) (γ : Fin 3 → Fin 3 → X3 → ℝ) (u : X3 → ℝ) (R : ℝ) (x : X3) : ℝ :=
  Gv (nder β u x) (pd u 0 x) (u x) R (fun k => β k x) (fun k => pd (β k) 0 x)
    (fun k => pd u k.succ x) (fun k i => pd (β k) i.succ x) (fun i j => acoef β γ i j x)
    (fun i j => acoefT β γ i j x) (fun i j l => acoefX β γ i j l x)

/-- The spatial flux `Jⁱ = βⁱ(Du)² + 2(Du) a^{ij}∂ⱼu + βⁱ a^{jl}∂ⱼu∂ₗu`. -/
def flux (β : Fin 3 → X3 → ℝ) (γ : Fin 3 → Fin 3 → X3 → ℝ) (u : X3 → ℝ) (i : Fin 3) (x : X3) :
    ℝ :=
  β i x * nder β u x ^ 2 + 2 * nder β u x * ∑ j : Fin 3, acoef β γ i j x * pd u j.succ x +
    β i x * ∑ j : Fin 3, ∑ l : Fin 3, acoef β γ j l x * pd u j.succ x * pd u l.succ x

/-! ### The hypotheses of the `L²` estimate -/

/-- **Hypotheses of the shifted `L²` energy estimate** on `[0, T] × 𝕋³`: smooth spatially periodic
fields, the normal-form equation `∂ₜ²u_b = 2βⁱ∂ᵢ∂ₜu_b + γ^{ij}∂ᵢ∂ⱼu_b + L₀,b + F_b` on the slab,
`γ` symmetric, `a = γ + ββ` uniformly `λ`-coercive (uniformly spacelike slices), and the bounds
`|β|, |∂β|, |γ|, |∂γ| ≤ M` (bounded lapse and shift with `L^∞` derivatives), with a lower-order
part `Σ_b L₀,b² ≤ m(t)² Σ_b(|∂ₜu_b|² + |∇u_b|² + u_b²)`.  No sign of `γ` is assumed. -/
structure ShL2Hyp (β : Fin 3 → X3 → ℝ) (γ : Fin 3 → Fin 3 → X3 → ℝ) (u L₀ F : ι → X3 → ℝ)
    (m : ℝ → ℝ) (T lam M : ℝ) : Prop where
  su : ∀ b, ContDiff ℝ ∞ (u b)
  sβ : ∀ i, ContDiff ℝ ∞ (β i)
  sγ : ∀ i j, ContDiff ℝ ∞ (γ i j)
  cL : ∀ b, Continuous (L₀ b)
  cF : ∀ b, Continuous (F b)
  cm : Continuous m
  pu : ∀ b, IsSPeriodic (u b)
  pβ : ∀ i, IsSPeriodic (β i)
  pγ : ∀ i j, IsSPeriodic (γ i j)
  eqn : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ b, pd (pd (u b) 0) 0 x =
    2 * ∑ i : Fin 3, β i x * pd (pd (u b) 0) i.succ x +
      ∑ i : Fin 3, ∑ j : Fin 3, γ i j x * pd (pd (u b) j.succ) i.succ x + L₀ b x + F b x
  γ_symm : ∀ i j x, γ i j x = γ j i x
  lam_pos : 0 < lam
  coer : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
    lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, acoef β γ i j x * ξ i * ξ j
  M_nonneg : 0 ≤ M
  bβ : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ i, |β i x| ≤ M
  bβ1 : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ i (μ : Fin 4), |pd (β i) μ x| ≤ M
  bγ : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ i j, |γ i j x| ≤ M
  bγ1 : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ i j (μ : Fin 4), |pd (γ i j) μ x| ≤ M
  m_nonneg : ∀ t, 0 ≤ m t
  bL : ∀ x : X3, x 0 ∈ Icc 0 T → ∑ b, L₀ b x ^ 2 ≤ m (x 0) ^ 2 * size u x

namespace ShL2Hyp

variable {β : Fin 3 → X3 → ℝ} {γ : Fin 3 → Fin 3 → X3 → ℝ} {u L₀ F : ι → X3 → ℝ}
  {m : ℝ → ℝ} {T lam M : ℝ}

theorem spd (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) (μ : Fin 4) :
    ContDiff ℝ ∞ (pd (u b) μ) := contDiff_pd_top (h.su b) μ

theorem spd2 (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) (μ ν : Fin 4) :
    ContDiff ℝ ∞ (pd (pd (u b) μ) ν) := contDiff_pd_top (h.spd b μ) ν

theorem snder (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) : ContDiff ℝ ∞ (nder β (u b)) := by
  unfold nder
  exact (h.spd b 0).sub (ContDiff.sum fun k _ => (h.sβ k).mul (h.spd b _))

theorem sacoef (h : ShL2Hyp β γ u L₀ F m T lam M) (i j : Fin 3) :
    ContDiff ℝ ∞ (acoef β γ i j) := by
  unfold acoef
  exact (h.sγ i j).add ((h.sβ i).mul (h.sβ j))

theorem sdens1 (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) : ContDiff ℝ ∞ (dens1 β γ (u b)) := by
  unfold dens1
  exact (((h.snder b).pow 2).add (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    ((h.sacoef i j).mul (h.spd b _)).mul (h.spd b _))).add ((h.su b).pow 2)

theorem continuous_densS (h : ShL2Hyp β γ u L₀ F m T lam M) : Continuous (densS β γ u) := by
  unfold densS
  exact continuous_finsetSum _ fun b _ => (h.sdens1 b).continuous

theorem sflux (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) (i : Fin 3) :
    ContDiff ℝ ∞ (flux β γ (u b) i) := by
  unfold flux
  exact (((h.sβ i).mul ((h.snder b).pow 2)).add ((contDiff_const.mul (h.snder b)).mul
    (ContDiff.sum fun j _ => (h.sacoef i j).mul (h.spd b _)))).add ((h.sβ i).mul
      (ContDiff.sum fun j _ => ContDiff.sum fun l _ =>
        ((h.sacoef j l).mul (h.spd b _)).mul (h.spd b _)))

theorem pnder (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) : IsSPeriodic (nder β (u b)) :=
  fun k x => by
    simp only [nder, isSPeriodic_pd (h.pu b) 0 k x, fun j => (h.pβ j) k x,
      fun j : Fin 3 => isSPeriodic_pd (h.pu b) j.succ k x]

theorem pacoef (h : ShL2Hyp β γ u L₀ F m T lam M) (i j : Fin 3) : IsSPeriodic (acoef β γ i j) :=
  fun k x => by simp only [acoef, (h.pγ i j) k x, (h.pβ i) k x, (h.pβ j) k x]

theorem pflux (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) (i : Fin 3) :
    IsSPeriodic (flux β γ (u b) i) := fun k x => by
  simp only [flux, (h.pβ i) k x, h.pnder b k x, fun j l => h.pacoef j l k x,
    fun j : Fin 3 => isSPeriodic_pd (h.pu b) j.succ k x]

/-! #### Derivatives along the coordinate lines -/

/-- The derivative of the normal derivative along a line. -/
theorem hasDerivAt_nder_line (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) (x : X3) (μ : Fin 4) :
    HasDerivAt (fun s : ℝ => nder β (u b) (x + s • ev μ))
      (pd (pd (u b) 0) μ x - ∑ k : Fin 3, (pd (β k) μ x * pd (u b) k.succ x +
        β k x * pd (pd (u b) k.succ) μ x)) 0 := by
  unfold nder
  exact (hasDerivAt_line0 (h.spd b 0) x μ).sub (HasDerivAt.fun_sum fun k _ =>
    ((hasDerivAt_line0 (h.sβ k) x μ).fun_mul (hasDerivAt_line0 (h.spd b _) x μ)).congr_deriv
      (by simp only [zero_smul, add_zero]))

theorem hasDerivAt_acoef_line (h : ShL2Hyp β γ u L₀ F m T lam M) (i j : Fin 3) (x : X3)
    (μ : Fin 4) :
    HasDerivAt (fun s : ℝ => acoef β γ i j (x + s • ev μ))
      (pd (γ i j) μ x + (pd (β i) μ x * β j x + β i x * pd (β j) μ x)) 0 := by
  unfold acoef
  exact (hasDerivAt_line0 (h.sγ i j) x μ).fun_add
    (((hasDerivAt_line0 (h.sβ i) x μ).fun_mul (hasDerivAt_line0 (h.sβ j) x μ)).congr_deriv
      (by simp only [zero_smul, add_zero]))

/-- The time derivative of the density of one component. -/
theorem hasDerivAt_dens1 (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) (x : X3) :
    HasDerivAt (fun s : ℝ => dens1 β γ (u b) (x + s • ev 0)) (densT1 β γ (u b) x) 0 := by
  have hv := h.hasDerivAt_nder_line b x 0
  have hux : ∀ k : Fin 3, HasDerivAt (fun s : ℝ => pd (u b) k.succ (x + s • ev 0))
      (pd (pd (u b) 0) k.succ x) 0 := fun k => by
    have := hasDerivAt_line0 (h.spd b k.succ) x 0
    rwa [pd2_swap (h.su b) k.succ 0] at this
  have hsum : HasDerivAt (fun s : ℝ => ∑ i : Fin 3, ∑ j : Fin 3, acoef β γ i j (x + s • ev 0) *
      pd (u b) i.succ (x + s • ev 0) * pd (u b) j.succ (x + s • ev 0))
      (∑ i : Fin 3, ∑ j : Fin 3, (acoefT β γ i j x * pd (u b) i.succ x * pd (u b) j.succ x +
        acoef β γ i j x * pd (pd (u b) 0) i.succ x * pd (u b) j.succ x +
        acoef β γ i j x * pd (u b) i.succ x * pd (pd (u b) 0) j.succ x)) 0 := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    refine (((h.hasDerivAt_acoef_line i j x 0).fun_mul (hux i)).fun_mul (hux j)).congr_deriv ?_
    simp only [acoefT, zero_smul, add_zero]
    ring
  have hu := hasDerivAt_line0 (h.su b) x 0
  unfold dens1
  refine (((hv.fun_pow 2).fun_add hsum).fun_add (hu.fun_pow 2)).congr_deriv ?_
  simp only [densT1, etv, zero_smul, add_zero, Nat.cast_ofNat]
  have e : ∀ k : Fin 3, pd (pd (u b) k.succ) 0 x = pd (pd (u b) 0) k.succ x := fun k =>
    pd_pd_comm ((h.su b).of_le (by norm_cast)) k.succ 0 x
  simp only [e]
  ring

/-- The derivative of the flux along its own direction. -/
theorem hasDerivAt_flux (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) (i : Fin 3) (x : X3) :
    HasDerivAt (fun s : ℝ => flux β γ (u b) i (x + s • ev i.succ))
      (dJv (nder β (u b) x) (fun k => β k x) (fun k => pd (u b) k.succ x)
        (fun i => pd (pd (u b) 0) i.succ x) (fun k i => pd (β k) i.succ x)
        (fun i j => acoef β γ i j x) (fun k i => pd (pd (u b) k.succ) i.succ x)
        (fun i j l => acoefX β γ i j l x) i) 0 := by
  have hv := h.hasDerivAt_nder_line b x i.succ
  have hβi := hasDerivAt_line0 (h.sβ i) x i.succ
  have hux : ∀ k : Fin 3, HasDerivAt (fun s : ℝ => pd (u b) k.succ (x + s • ev i.succ))
      (pd (pd (u b) k.succ) i.succ x) 0 := fun k => hasDerivAt_line0 (h.spd b k.succ) x i.succ
  have ha := fun j l => h.hasDerivAt_acoef_line j l x i.succ
  have h1 : HasDerivAt (fun s : ℝ => ∑ j : Fin 3, acoef β γ i j (x + s • ev i.succ) *
      pd (u b) j.succ (x + s • ev i.succ))
      (∑ j : Fin 3, (acoefX β γ i i j x * pd (u b) j.succ x +
        acoef β γ i j x * pd (pd (u b) j.succ) i.succ x)) 0 :=
    HasDerivAt.fun_sum fun j _ => ((ha i j).fun_mul (hux j)).congr_deriv (by
      simp only [acoefX, zero_smul, add_zero]; ring)
  have h2 : HasDerivAt (fun s : ℝ => ∑ j : Fin 3, ∑ l : Fin 3, acoef β γ j l (x + s • ev i.succ) *
      pd (u b) j.succ (x + s • ev i.succ) * pd (u b) l.succ (x + s • ev i.succ))
      (∑ j : Fin 3, ∑ l : Fin 3, (acoefX β γ i j l x * pd (u b) j.succ x * pd (u b) l.succ x +
        acoef β γ j l x * pd (pd (u b) j.succ) i.succ x * pd (u b) l.succ x +
        acoef β γ j l x * pd (u b) j.succ x * pd (pd (u b) l.succ) i.succ x)) 0 :=
    HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun l _ =>
      (((ha j l).fun_mul (hux j)).fun_mul (hux l)).congr_deriv (by
        simp only [acoefX, zero_smul, add_zero]; ring)
  unfold flux
  refine (((hβi.fun_mul (hv.fun_pow 2)).fun_add ((hv.const_mul 2).fun_mul h1)).fun_add
    (hβi.fun_mul h2)).congr_deriv ?_
  simp only [dJv, vxv, Nat.cast_ofNat, zero_smul, add_zero]
  ring

/-- The flux derivative as a partial derivative. -/
theorem pd_flux (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) (i : Fin 3) (x : X3) :
    pd (flux β γ (u b) i) i.succ x =
      dJv (nder β (u b) x) (fun k => β k x) (fun k => pd (u b) k.succ x)
        (fun i => pd (pd (u b) 0) i.succ x) (fun k i => pd (β k) i.succ x)
        (fun i j => acoef β γ i j x) (fun k i => pd (pd (u b) k.succ) i.succ x)
        (fun i j l => acoefX β γ i j l x) i :=
  (hasDerivAt_line0 (h.sflux b i) x i.succ).unique (h.hasDerivAt_flux b i x)

/-- **The pointwise energy identity** at points of the slab. -/
theorem densT1_sub (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) {x : X3} (hx : x 0 ∈ Icc 0 T) :
    densT1 β γ (u b) x - densG1 β γ (u b) (L₀ b x + F b x) x =
      ∑ i : Fin 3, pd (flux β γ (u b) i) i.succ x := by
  simp only [h.pd_flux b]
  have := shift_alg (nder β (u b) x) (pd (u b) 0 x) (pd (pd (u b) 0) 0 x) (u b x)
    (L₀ b x + F b x) (fun k => β k x) (fun k => pd (β k) 0 x) (fun k => pd (u b) k.succ x)
    (fun i => pd (pd (u b) 0) i.succ x) (fun k i => pd (β k) i.succ x)
    (fun i j => acoef β γ i j x) (fun i j => acoefT β γ i j x)
    (fun k i => pd (pd (u b) k.succ) i.succ x) (fun i j l => acoefX β γ i j l x)
    (fun i j => by simp only [acoef, h.γ_symm i j x]; ring)
    (fun i j => pd_pd_comm ((h.su b).of_le (by norm_cast)) _ _ x)
    (by rw [h.eqn x hx b]; simp only [acoef]; ring)
  unfold densT1 densG1
  linarith

/-! #### The energy identity -/

theorem hasDerivAt_dens1_time (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) (t : ℝ)
    (y : Fin 3 → ℝ) :
    HasDerivAt (fun s => dens1 β γ (u b) (Fin.cons s y)) (densT1 β γ (u b) (Fin.cons t y)) t := by
  have := hasDerivAt_time y ((h.sdens1 b).differentiable (by simp) (Fin.cons t y))
  rwa [(hasDerivAt_line0 (h.sdens1 b) _ 0).unique (h.hasDerivAt_dens1 b _)] at this

theorem continuous_densT1 (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) :
    Continuous (densT1 β γ (u b)) := by
  have := fun μ => (h.spd b μ).continuous
  have := fun μ ν => (h.spd2 b μ ν).continuous
  have := (h.snder b).continuous
  have := fun i j => (h.sacoef i j).continuous
  have := fun i => (h.sβ i).continuous
  have := fun i μ => (contDiff_pd_top (h.sβ i) μ).continuous
  have := fun i j μ => (contDiff_pd_top (h.sγ i j) μ).continuous
  have := (h.su b).continuous
  unfold densT1 etv acoefT
  fun_prop

theorem continuous_densG1 (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) {R : X3 → ℝ}
    (hR : Continuous R) : Continuous fun x => densG1 β γ (u b) (R x) x := by
  have := fun μ => (h.spd b μ).continuous
  have := (h.snder b).continuous
  have := fun i j => (h.sacoef i j).continuous
  have := fun i => (h.sβ i).continuous
  have := fun i μ => (contDiff_pd_top (h.sβ i) μ).continuous
  have := fun i j μ => (contDiff_pd_top (h.sγ i j) μ).continuous
  have := (h.su b).continuous
  unfold densG1 Gv acoefT acoefX
  fun_prop

theorem continuous_energyS (h : ShL2Hyp β γ u L₀ F m T lam M) : Continuous (energyS β γ u) :=
  continuous_sliceInt h.continuous_densS

/-- **The energy is differentiable** with derivative `∫ Σ_b densT1`. -/
theorem hasDerivAt_energyS (h : ShL2Hyp β γ u L₀ F m T lam M) (t : ℝ) :
    HasDerivAt (energyS β γ u)
      (∫ y in Icc (0 : Fin 3 → ℝ) 1, ∑ b, densT1 β γ (u b) (Fin.cons t y)) t := by
  have hcT : Continuous fun x => ∑ b, densT1 β γ (u b) x :=
    continuous_finsetSum _ fun b _ => h.continuous_densT1 b
  set K : Set X3 := (fun p : ℝ × (Fin 3 → ℝ) => (Fin.cons p.1 p.2 : X3)) ''
    (Icc (t - 1) (t + 1) ×ˢ Icc 0 1)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image continuous_cons2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcT.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc (0 : Fin 3 → ℝ) 1))
    (F := fun s y => densS β γ u (Fin.cons s y))
    (F' := fun s y => ∑ b, densT1 β γ (u b) (Fin.cons s y))
    (x₀ := t) (bound := fun _ => C) (s := Ioo (t - 1) (t + 1))
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    (Eventually.of_forall fun s =>
      (h.continuous_densS.comp (continuous_cons s)).aestronglyMeasurable)
    (integrableOn_slice h.continuous_densS t)
    ((hcT.comp (continuous_cons t)).aestronglyMeasurable)
    (by
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall fun y hy s hs => ?_
      exact hC _ ⟨(s, y), ⟨Ioo_subset_Icc_self hs, hy⟩, rfl⟩)
    (integrable_const C)
    (Eventually.of_forall fun y s _ => by
      unfold densS
      exact HasDerivAt.fun_sum fun b _ => h.hasDerivAt_dens1_time b s y)
  exact key.2

/-- **The energy identity** `∫ Σ_b densT1 = ∫ Σ_b densG1` at slab times. -/
theorem integral_densT_eq (h : ShL2Hyp β γ u L₀ F m T lam M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, ∑ b, densT1 β γ (u b) (Fin.cons t y) =
      ∫ y in Icc (0 : Fin 3 → ℝ) 1, ∑ b, densG1 β γ (u b) (L₀ b (Fin.cons t y) +
        F b (Fin.cons t y)) (Fin.cons t y) := by
  have hq : ∀ b i, Continuous (pd (flux β γ (u b) i) i.succ) := fun b i =>
    (contDiff_pd_top (h.sflux b i) _).continuous
  have key : ∀ y : Fin 3 → ℝ, ∑ b, densT1 β γ (u b) (Fin.cons t y) =
      ∑ b, densG1 β γ (u b) (L₀ b (Fin.cons t y) + F b (Fin.cons t y)) (Fin.cons t y) +
        ∑ b, ∑ i : Fin 3, pd (flux β γ (u b) i) i.succ (Fin.cons t y) := fun y => by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← h.densT1_sub b (L2Hyp.cons_zero_mem ht y)]; ring
  simp_rw [key]
  have hI : ∀ {f : X3 → ℝ}, Continuous f →
      Integrable (fun y : Fin 3 → ℝ => f (Fin.cons t y)) (volume.restrict (Icc 0 1)) :=
    fun hf => integrableOn_slice hf t
  have hG : Continuous fun x => ∑ b, densG1 β γ (u b) (L₀ b x + F b x) x :=
    continuous_finsetSum _ fun b _ => h.continuous_densG1 b ((h.cL b).add (h.cF b))
  have hsum : ∫ y in Icc (0 : Fin 3 → ℝ) 1,
      ∑ b, ∑ i : Fin 3, pd (flux β γ (u b) i) i.succ (Fin.cons t y) = 0 := by
    rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun i _ => hI (hq b i)]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [integral_finsetSum _ fun i _ => hI (hq b i)]
    exact Finset.sum_eq_zero fun i _ =>
      integral_slice_pd_eq_zero ((h.sflux b i).of_le (by norm_cast)) (h.pflux b i) t i
  rw [integral_add (hI hG) (integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun i _ =>
    hI (hq b i)), hsum, add_zero]

/-! #### Pointwise bounds -/

/-- The squared first jets of one component, `(Du)² + |∂ₜu|² + u² + |∇u|²`. -/
def Wj (β : Fin 3 → X3 → ℝ) (u : X3 → ℝ) (x : X3) : ℝ :=
  nder β u x ^ 2 + pd u 0 x ^ 2 + u x ^ 2 + ∑ k : Fin 3, pd u k.succ x ^ 2

theorem Wj_nonneg (β : Fin 3 → X3 → ℝ) (u : X3 → ℝ) (x : X3) : 0 ≤ Wj β u x := by
  unfold Wj; positivity

/-- The coefficient bound `A = M + 2M²` for `a, ∂a`. -/
def Ab (M : ℝ) : ℝ := M + 2 * M ^ 2

theorem abs_acoef_le (h : ShL2Hyp β γ u L₀ F m T lam M) {x : X3} (hx : x 0 ∈ Icc 0 T)
    (i j : Fin 3) : |acoef β γ i j x| ≤ Ab M := by
  have hM := h.M_nonneg
  unfold acoef Ab
  refine (abs_add_le _ _).trans ?_
  have := h.bγ x hx i j
  have := abs_mul_le_of (h.bβ x hx i) (h.bβ x hx j)
  nlinarith [sq_nonneg M]

theorem abs_acoefT_le (h : ShL2Hyp β γ u L₀ F m T lam M) {x : X3} (hx : x 0 ∈ Icc 0 T)
    (i j : Fin 3) : |acoefT β γ i j x| ≤ Ab M := by
  unfold acoefT Ab
  refine (abs_add_three _ _ _).trans ?_
  have := h.bγ1 x hx i j 0
  have := abs_mul_le_of (h.bβ1 x hx i 0) (h.bβ x hx j)
  have := abs_mul_le_of (h.bβ x hx i) (h.bβ1 x hx j 0)
  nlinarith

theorem abs_acoefX_le (h : ShL2Hyp β γ u L₀ F m T lam M) {x : X3} (hx : x 0 ∈ Icc 0 T)
    (i j l : Fin 3) : |acoefX β γ i j l x| ≤ Ab M := by
  unfold acoefX Ab
  refine (abs_add_three _ _ _).trans ?_
  have := h.bγ1 x hx j l i.succ
  have := abs_mul_le_of (h.bβ1 x hx j i.succ) (h.bβ x hx l)
  have := abs_mul_le_of (h.bβ x hx j) (h.bβ1 x hx l i.succ)
  nlinarith

/-- **The remainder without source is bounded by the squared jets.** -/
theorem densG1_zero_le (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) {x : X3}
    (hx : x 0 ∈ Icc 0 T) : densG1 β γ (u b) 0 x ≤ Kc M (Ab M) * Wj β (u b) x := by
  have hM := h.M_nonneg
  have hW := Wj_nonneg β (u b) x
  set r := Real.sqrt (Wj β (u b) x)
  have hr2 : r ^ 2 = Wj β (u b) x := Real.sq_sqrt hW
  have hle : ∀ q : ℝ, q ^ 2 ≤ Wj β (u b) x → |q| ≤ r := fun q hq => Real.abs_le_sqrt hq
  have hS : ∀ k : Fin 3, pd (u b) k.succ x ^ 2 ≤ ∑ k : Fin 3, pd (u b) k.succ x ^ 2 := fun k =>
    Finset.single_le_sum (f := fun k : Fin 3 => pd (u b) k.succ x ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ k)
  have hS0 : 0 ≤ ∑ k : Fin 3, pd (u b) k.succ x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← hr2]
  refine Gv_le _ _ _ _ _ _ _ _ _ _ hM (by unfold Ab; positivity) (Real.sqrt_nonneg _)
    (fun k => h.bβ x hx k) (fun k => h.bβ1 x hx k 0) (fun k i => h.bβ1 x hx k i.succ)
    (fun i j => h.abs_acoef_le hx i j) (fun i j => h.abs_acoefT_le hx i j)
    (fun i j l => h.abs_acoefX_le hx i j l) (hle _ ?_) (hle _ ?_) (hle _ ?_)
    (fun k => hle _ ?_) <;> unfold Wj
  · nlinarith [sq_nonneg (pd (u b) 0 x), sq_nonneg (u b x)]
  · nlinarith [sq_nonneg (nder β (u b) x), sq_nonneg (u b x)]
  · nlinarith [sq_nonneg (nder β (u b) x), sq_nonneg (pd (u b) 0 x)]
  · nlinarith [sq_nonneg (nder β (u b) x), sq_nonneg (pd (u b) 0 x), sq_nonneg (u b x), hS k]

theorem densG1_eq (β : Fin 3 → X3 → ℝ) (γ : Fin 3 → Fin 3 → X3 → ℝ) (u : X3 → ℝ) (R : ℝ)
    (x : X3) : densG1 β γ u R x = densG1 β γ u 0 x + 2 * nder β u x * R := by
  unfold densG1 Gv; ring

theorem sq_sum3_le (p : Fin 3 → ℝ) : (∑ k, p k) ^ 2 ≤ 3 * ∑ k, p k ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (p 0 - p 1), sq_nonneg (p 0 - p 2), sq_nonneg (p 1 - p 2)]

/-- The constant `C_W = max(3, (1 + 6M²)/λ)` of `Wj_le_dens1`. -/
def Cw (M lam : ℝ) : ℝ := max 3 ((1 + 6 * M ^ 2) / lam)

theorem Cw_pos (M lam : ℝ) : 0 < Cw M lam := lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem quad_nonneg (h : ShL2Hyp β γ u L₀ F m T lam M) {x : X3} (hx : x 0 ∈ Icc 0 T)
    (ξ : Fin 3 → ℝ) : 0 ≤ ∑ i, ∑ j, acoef β γ i j x * ξ i * ξ j :=
  le_trans (mul_nonneg h.lam_pos.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (h.coer x hx ξ)

/-- **The energy density controls all first jets**: `Wj ≤ C_W dens1` on the slab. -/
theorem Wj_le_dens1 (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) {x : X3}
    (hx : x 0 ∈ Icc 0 T) : Wj β (u b) x ≤ Cw M lam * dens1 β γ (u b) x := by
  set v := nder β (u b) x
  set S := ∑ k : Fin 3, pd (u b) k.succ x ^ 2
  set Qd := ∑ i : Fin 3, ∑ j : Fin 3, acoef β γ i j x * pd (u b) i.succ x * pd (u b) j.succ x
  have hlam := h.lam_pos
  have hco : lam * S ≤ Qd := h.coer x hx fun k => pd (u b) k.succ x
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hP : (∑ k : Fin 3, β k x * pd (u b) k.succ x) ^ 2 ≤ 3 * M ^ 2 * S := by
    refine (sq_sum3_le _).trans ?_
    calc 3 * ∑ k : Fin 3, (β k x * pd (u b) k.succ x) ^ 2 ≤
        3 * ∑ k : Fin 3, M ^ 2 * pd (u b) k.succ x ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by norm_num)
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (sq_le_sq' (neg_le_of_abs_le (h.bβ x hx k))
            (le_of_abs_le (h.bβ x hx k))) (sq_nonneg _)
      _ = 3 * M ^ 2 * S := by rw [← Finset.mul_sum]; ring
  have hut : pd (u b) 0 x = v + ∑ k : Fin 3, β k x * pd (u b) k.succ x := by
    simp only [v, nder]; ring
  have hut2 : pd (u b) 0 x ^ 2 ≤ 2 * v ^ 2 + 6 * M ^ 2 * S := by
    rw [hut]; nlinarith [sq_nonneg (v - ∑ k : Fin 3, β k x * pd (u b) k.succ x)]
  have hQ0 : 0 ≤ Qd := le_trans (mul_nonneg hlam.le hS0) hco
  have hSQ : (1 + 6 * M ^ 2) * S ≤ (1 + 6 * M ^ 2) / lam * Qd := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    nlinarith [sq_nonneg M]
  have hC1 : 3 ≤ Cw M lam := le_max_left _ _
  have hC2 : (1 + 6 * M ^ 2) / lam ≤ Cw M lam := le_max_right _ _
  unfold Wj dens1
  change v ^ 2 + pd (u b) 0 x ^ 2 + u b x ^ 2 + S ≤ Cw M lam * (v ^ 2 + Qd + u b x ^ 2)
  nlinarith [sq_nonneg v, sq_nonneg (u b x), mul_le_mul_of_nonneg_right hC2 hQ0]

theorem dens1_nonneg (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) {x : X3}
    (hx : x 0 ∈ Icc 0 T) : 0 ≤ dens1 β γ (u b) x := by
  have := h.quad_nonneg hx (fun k => pd (u b) k.succ x)
  unfold dens1; positivity

theorem densS_nonneg (h : ShL2Hyp β γ u L₀ F m T lam M) {x : X3} (hx : x 0 ∈ Icc 0 T) :
    0 ≤ densS β γ u x := Finset.sum_nonneg fun b _ => h.dens1_nonneg b hx

theorem energyS_nonneg (h : ShL2Hyp β γ u L₀ F m T lam M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    0 ≤ energyS β γ u t :=
  setIntegral_nonneg measurableSet_Icc fun y _ => h.densS_nonneg (L2Hyp.cons_zero_mem ht y)

theorem nder_sq_le (h : ShL2Hyp β γ u L₀ F m T lam M) {x : X3} (hx : x 0 ∈ Icc 0 T) :
    ∑ b, nder β (u b) x ^ 2 ≤ densS β γ u x := by
  unfold densS
  refine Finset.sum_le_sum fun b _ => ?_
  have := h.quad_nonneg hx (fun k => pd (u b) k.succ x)
  unfold dens1; nlinarith [sq_nonneg (u b x)]

theorem size_le_Wj (β : Fin 3 → X3 → ℝ) (u : ι → X3 → ℝ) (x : X3) :
    size u x ≤ ∑ b, Wj β (u b) x := by
  unfold size Wj
  refine Finset.sum_le_sum fun b _ => ?_
  nlinarith [sq_nonneg (nder β (u b) x)]

/-- The growth rate `k(t) = K_c C_W + 2 m(t) √C_W`. -/
def kS (M lam : ℝ) (m : ℝ → ℝ) (t : ℝ) : ℝ :=
  Kc M (Ab M) * Cw M lam + 2 * m t * Real.sqrt (Cw M lam)

theorem Kc_Ab_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ Kc M (Ab M) :=
  Kc_nonneg hM (by unfold Ab; positivity)

theorem kS_nonneg (h : ShL2Hyp β γ u L₀ F m T lam M) (t : ℝ) : 0 ≤ kS M lam m t := by
  have := h.m_nonneg t
  have := Kc_Ab_nonneg h.M_nonneg
  have := Cw_pos M lam
  unfold kS
  positivity

/-- **The pointwise bound of the non-forcing part**: `Σ_b densG1(L₀) ≤ k(t) densS`. -/
theorem densG_L_le (h : ShL2Hyp β γ u L₀ F m T lam M) {x : X3} (hx : x 0 ∈ Icc 0 T) :
    ∑ b, densG1 β γ (u b) (L₀ b x) x ≤ kS M lam m (x 0) * densS β γ u x := by
  have hK := Kc_Ab_nonneg h.M_nonneg
  have hC := Cw_pos M lam
  have hD := h.densS_nonneg hx
  simp only [densG1_eq β γ _ (L₀ _ x) x, Finset.sum_add_distrib]
  have h1 : ∑ b, densG1 β γ (u b) 0 x ≤ Kc M (Ab M) * Cw M lam * densS β γ u x := by
    unfold densS
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    refine (h.densG1_zero_le b hx).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.Wj_le_dens1 b hx) hK
  have h2 : ∑ b, 2 * nder β (u b) x * L₀ b x ≤ 2 * m (x 0) * Real.sqrt (Cw M lam) *
      densS β γ u x := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun b => nder β (u b) x)
      (fun b => L₀ b x)
    have hv := h.nder_sq_le hx
    have hL : Real.sqrt (∑ b, L₀ b x ^ 2) ≤ m (x 0) * Real.sqrt (Cw M lam * densS β γ u x) := by
      rw [← Real.sqrt_sq (h.m_nonneg (x 0)), ← Real.sqrt_mul (sq_nonneg _)]
      refine Real.sqrt_le_sqrt ((h.bL x hx).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)))
      refine (size_le_Wj β u x).trans ?_
      unfold densS
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun b _ => h.Wj_le_dens1 b hx
    have e1 : ∑ b, 2 * nder β (u b) x * L₀ b x = 2 * ∑ b, nder β (u b) x * L₀ b x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    rw [e1]
    have hsD := Real.sqrt_nonneg (densS β γ u x)
    calc 2 * ∑ b, nder β (u b) x * L₀ b x ≤
        2 * (Real.sqrt (densS β γ u x) * (m (x 0) * Real.sqrt (Cw M lam * densS β γ u x))) := by
          refine mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hv) hL
            (Real.sqrt_nonneg _) hsD)) (by norm_num)
      _ = 2 * m (x 0) * Real.sqrt (Cw M lam) * densS β γ u x := by
          rw [Real.sqrt_mul hC.le]
          linear_combination (2 * m (x 0) * Real.sqrt (Cw M lam)) * Real.mul_self_sqrt hD
  unfold kS
  nlinarith

/-! #### The energy inequality and Gronwall -/

/-- **The forced energy inequality**: `E' ≤ k(t) E + 2‖F(t)‖_{L²} √E`. -/
theorem energyS_deriv_le (h : ShL2Hyp β γ u L₀ F m T lam M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, ∑ b, densT1 β γ (u b) (Fin.cons t y) ≤
      kS M lam m t * energyS β γ u t + 2 * l2norm F t * Real.sqrt (energyS β γ u t) := by
  have hint : ∀ {f : X3 → ℝ}, Continuous f →
      IntegrableOn (fun y : Fin 3 → ℝ => f (Fin.cons t y)) (Icc 0 1) :=
    fun hf => integrableOn_slice hf t
  have hcL : Continuous fun x => ∑ b, densG1 β γ (u b) (L₀ b x) x :=
    continuous_finsetSum _ fun b _ => h.continuous_densG1 b (h.cL b)
  have hcv : ∀ b, Continuous (nder β (u b)) := fun b => (h.snder b).continuous
  have hcW : Continuous fun x => ∑ b, nder β (u b) x * F b x := by
    have := hcv; have := h.cF; fun_prop
  rw [h.integral_densT_eq ht]
  have e : ∀ y : Fin 3 → ℝ, ∑ b, densG1 β γ (u b) (L₀ b (Fin.cons t y) + F b (Fin.cons t y))
      (Fin.cons t y) = ∑ b, densG1 β γ (u b) (L₀ b (Fin.cons t y)) (Fin.cons t y) +
        2 * ∑ b, nder β (u b) (Fin.cons t y) * F b (Fin.cons t y) := fun y => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [densG1_eq β γ _ (L₀ b _ + F b _), densG1_eq β γ _ (L₀ b _)]
    ring
  simp_rw [e]
  rw [integral_add (hint hcL) ((hint hcW).const_mul 2), integral_const_mul]
  have hA : ∫ y in Icc (0 : Fin 3 → ℝ) 1, ∑ b, densG1 β γ (u b) (L₀ b (Fin.cons t y))
      (Fin.cons t y) ≤ kS M lam m t * energyS β γ u t := by
    rw [energyS, ← integral_const_mul]
    exact setIntegral_mono_on (hint hcL) ((hint h.continuous_densS).const_mul _) measurableSet_Icc
      fun y _ => by
        have := h.densG_L_le (L2Hyp.cons_zero_mem ht y)
        simpa using this
  have hB : ∫ y in Icc (0 : Fin 3 → ℝ) 1, ∑ b, nder β (u b) (Fin.cons t y) * F b (Fin.cons t y) ≤
      l2norm F t * Real.sqrt (energyS β γ u t) := by
    have h1 := L2Hyp.integral_sum_mul_le_cube (f := fun y b => nder β (u b) (Fin.cons t y))
      (g := fun y b => F b (Fin.cons t y)) (fun b => (hcv b).comp (continuous_cons t))
      (fun b => (h.cF b).comp (continuous_cons t))
    have h2 : ∫ y in Icc (0 : Fin 3 → ℝ) 1, ∑ b, nder β (u b) (Fin.cons t y) ^ 2 ≤
        energyS β γ u t :=
      setIntegral_mono_on (hint (f := fun x => ∑ b, nder β (u b) x ^ 2) (by
        have := hcv; fun_prop)) (hint h.continuous_densS) measurableSet_Icc fun y _ =>
          h.nder_sq_le (L2Hyp.cons_zero_mem ht y)
    calc _ ≤ Real.sqrt (∫ y in Icc (0 : Fin 3 → ℝ) 1, ∑ b, nder β (u b) (Fin.cons t y) ^ 2) *
          l2norm F t := h1
      _ ≤ Real.sqrt (energyS β γ u t) * l2norm F t :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
      _ = _ := by ring
  nlinarith

/-- **The shifted `L²` energy bound with an `L¹_t L²_x` source**: for `t ∈ [0, T]`,
`√E_S(t) ≤ (√E_S(0) + ∫₀ᵗ ‖F‖_{L²}) exp(½ ∫₀ᵗ k)`. -/
theorem sqrt_energyS_le (h : ShL2Hyp β γ u L₀ F m T lam M) :
    ∀ t ∈ Icc 0 T, Real.sqrt (energyS β γ u t) ≤
      (Real.sqrt (energyS β γ u 0) + ∫ s in (0)..t, l2norm F s) *
        Real.exp ((∫ s in (0)..t, kS M lam m s) / 2) := by
  intro t ht
  refine TorusWaveEnergyForced.sqrt_energy_gronwall
    (E' := fun s => ∫ y in Icc (0 : Fin 3 → ℝ) 1, ∑ b, densT1 β γ (u b) (Fin.cons s y))
    h.continuous_energyS.continuousOn (fun s hs => h.energyS_nonneg hs)
    (fun s _ => h.hasDerivAt_energyS s) (by unfold kS; have := h.cm; fun_prop)
    (L2Hyp.continuous_l2norm h.cF) (fun s => h.kS_nonneg s) (fun s => Real.sqrt_nonneg _)
    (fun s hs => h.energyS_deriv_le (Ioo_subset_Icc_self hs)) t ht

/-- The shifted `L²` estimate when the forcing is controlled by the energy:
`‖F(t)‖_{L²} ≤ a(t)√E_S(t) + σ(t)` gives
`√E_S(t) ≤ (√E_S(0) + ∫₀ᵗ σ) exp(½∫₀ᵗ (k + 2a))`. -/
theorem sqrt_energyS_le_of_forcing (h : ShL2Hyp β γ u L₀ F m T lam M) {a σ : ℝ → ℝ}
    (ha : Continuous a) (hσ : Continuous σ) (ha0 : ∀ t, 0 ≤ a t) (hσ0 : ∀ t, 0 ≤ σ t)
    (hF : ∀ t ∈ Icc 0 T, l2norm F t ≤ a t * Real.sqrt (energyS β γ u t) + σ t) :
    ∀ t ∈ Icc 0 T, Real.sqrt (energyS β γ u t) ≤
      (Real.sqrt (energyS β γ u 0) + ∫ s in (0)..t, σ s) *
        Real.exp ((∫ s in (0)..t, (kS M lam m s + 2 * a s)) / 2) := by
  intro t ht
  refine TorusWaveEnergyForced.sqrt_energy_gronwall
    (E' := fun s => ∫ y in Icc (0 : Fin 3 → ℝ) 1, ∑ b, densT1 β γ (u b) (Fin.cons s y))
    h.continuous_energyS.continuousOn (fun s hs => h.energyS_nonneg hs)
    (fun s _ => h.hasDerivAt_energyS s)
    ((by unfold kS; have := h.cm; fun_prop : Continuous (kS M lam m)).add
      (continuous_const.mul ha)) hσ (fun s => ?_) hσ0 (fun s hs => ?_) t ht
  · have := h.kS_nonneg s; have := ha0 s
    show 0 ≤ kS M lam m s + 2 * a s
    linarith
  · have hsc := Ioo_subset_Icc_self hs
    have h1 := h.energyS_deriv_le hsc
    have hE := h.energyS_nonneg hsc
    have hsq := Real.mul_self_sqrt hE
    have h2 : 2 * l2norm F s * Real.sqrt (energyS β γ u s) ≤
        2 * a s * energyS β γ u s + 2 * σ s * Real.sqrt (energyS β γ u s) := by
      have := mul_le_mul_of_nonneg_left (hF s hsc)
        (mul_nonneg zero_le_two (Real.sqrt_nonneg _) : 0 ≤ 2 * Real.sqrt (energyS β γ u s))
      have e : 2 * Real.sqrt (energyS β γ u s) * (a s * Real.sqrt (energyS β γ u s) + σ s) =
          2 * a s * energyS β γ u s + 2 * σ s * Real.sqrt (energyS β γ u s) := by
        linear_combination (2 * a s) * hsq
      linarith
    show _ ≤ (kS M lam m s + 2 * a s) * energyS β γ u s + 2 * σ s * Real.sqrt (energyS β γ u s)
    nlinarith

end ShL2Hyp

/-! ### Upper bound of the density -/

namespace ShL2Hyp

variable {β : Fin 3 → X3 → ℝ} {γ : Fin 3 → Fin 3 → X3 → ℝ} {u L₀ F : ι → X3 → ℝ}
  {m : ℝ → ℝ} {T lam M : ℝ}

/-- The constant `C_U = 3 + 6M² + 3A` of `dens1_le`. -/
def Cu (M : ℝ) : ℝ := 3 + 6 * M ^ 2 + 3 * Ab M

theorem Cu_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ Cu M := by unfold Cu Ab; positivity

/-- **The density is controlled by the classical jets**: `dens1 ≤ C_U (|∂ₜu|² + |∇u|² + u²)`. -/
theorem dens1_le (h : ShL2Hyp β γ u L₀ F m T lam M) (b : ι) {x : X3} (hx : x 0 ∈ Icc 0 T) :
    dens1 β γ (u b) x ≤ Cu M * (pd (u b) 0 x ^ 2 + ∑ k : Fin 3, pd (u b) k.succ x ^ 2 +
      u b x ^ 2) := by
  have hM := h.M_nonneg
  set S := ∑ k : Fin 3, pd (u b) k.succ x ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hP : (∑ k : Fin 3, β k x * pd (u b) k.succ x) ^ 2 ≤ 3 * M ^ 2 * S := by
    refine (sq_sum3_le _).trans ?_
    calc 3 * ∑ k : Fin 3, (β k x * pd (u b) k.succ x) ^ 2 ≤
        3 * ∑ k : Fin 3, M ^ 2 * pd (u b) k.succ x ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by norm_num)
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (sq_le_sq' (neg_le_of_abs_le (h.bβ x hx k))
            (le_of_abs_le (h.bβ x hx k))) (sq_nonneg _)
      _ = 3 * M ^ 2 * S := by rw [← Finset.mul_sum]; ring
  have hv : nder β (u b) x ^ 2 ≤ 2 * pd (u b) 0 x ^ 2 + 6 * M ^ 2 * S := by
    unfold nder
    nlinarith [sq_nonneg (pd (u b) 0 x + ∑ k : Fin 3, β k x * pd (u b) k.succ x)]
  have hA : ∑ i : Fin 3, ∑ j : Fin 3, acoef β γ i j x * pd (u b) i.succ x * pd (u b) j.succ x ≤
      3 * Ab M * S := by
    have h1 : ∀ i j : Fin 3, acoef β γ i j x * pd (u b) i.succ x * pd (u b) j.succ x ≤
        Ab M * (pd (u b) i.succ x ^ 2 + pd (u b) j.succ x ^ 2) / 2 := fun i j =>
      TorusWaveEnergy.WaveData.abs_mul_le_half _ _ _ _ (h.abs_acoef_le hx i j)
    calc _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, Ab M * (pd (u b) i.succ x ^ 2 + pd (u b) j.succ x ^ 2) / 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = 3 * Ab M * S := by
          simp only [S, Fin.sum_univ_three]; ring
  unfold dens1 Cu
  have : 0 ≤ Ab M := by unfold Ab; positivity
  nlinarith [sq_nonneg (pd (u b) 0 x), sq_nonneg (u b x), mul_nonneg this hS0,
    mul_nonneg (sq_nonneg M) hS0]

/-- `E_S ≤ C_U ∫ size`. -/
theorem energyS_le_size (h : ShL2Hyp β γ u L₀ F m T lam M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    energyS β γ u t ≤ Cu M * ∫ y in Icc (0 : Fin 3 → ℝ) 1, size u (Fin.cons t y) := by
  have hcs : Continuous (size u) := by
    unfold size
    have := fun b => (h.su b).continuous; have := fun b μ => (h.spd b μ).continuous
    fun_prop
  rw [energyS, ← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_slice h.continuous_densS t)
    ((integrableOn_slice hcs t).const_mul _) measurableSet_Icc fun y _ => ?_
  unfold densS size
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => h.dens1_le b (L2Hyp.cons_zero_mem ht y)

/-- `∫ (|∂ₜu_b|² + |∇u_b|² + u_b²) ≤ C_W E_S` for each component. -/
theorem integral_comp_le (h : ShL2Hyp β γ u L₀ F m T lam M) {t : ℝ} (ht : t ∈ Icc 0 T)
    (b : ι) : ∫ y in Icc (0 : Fin 3 → ℝ) 1, (pd (u b) 0 (Fin.cons t y) ^ 2 +
      ∑ i : Fin 3, pd (u b) i.succ (Fin.cons t y) ^ 2 + u b (Fin.cons t y) ^ 2) ≤
      Cw M lam * energyS β γ u t := by
  have hc : Continuous fun x => pd (u b) 0 x ^ 2 + ∑ i : Fin 3, pd (u b) i.succ x ^ 2 +
      u b x ^ 2 := by
    have := (h.su b).continuous; have := fun μ => (h.spd b μ).continuous
    fun_prop
  rw [energyS, ← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_slice hc t)
    ((integrableOn_slice h.continuous_densS t).const_mul _) measurableSet_Icc fun y _ => ?_
  have hx := L2Hyp.cons_zero_mem ht y
  have h1 := h.Wj_le_dens1 b hx
  have h2 : dens1 β γ (u b) (Fin.cons t y) ≤ densS β γ u (Fin.cons t y) :=
    Finset.single_le_sum (f := fun b => dens1 β γ (u b) (Fin.cons t y))
      (fun b _ => h.dens1_nonneg b hx) (Finset.mem_univ b)
  have h3 := mul_le_mul_of_nonneg_left h2 (Cw_pos M lam).le
  unfold Wj at h1
  nlinarith [sq_nonneg (nder β (u b) (Fin.cons t y))]

end ShL2Hyp

/-! ### Systems and the `H^k` estimate -/

universe v

/-- **The order-`k` shifted energy** `E_{S,k}(t) = Σ_{w} E_S(∂^w u)(t)`: the shifted energy of the
`k`-fold prolongation. -/
def energySK (k : ℕ) {ι : Type v} [Fintype ι] (β : Fin 3 → X3 → ℝ)
    (γ : Fin 3 → Fin 3 → X3 → ℝ) (u : ι → X3 → ℝ) (t : ℝ) : ℝ :=
  energyS β γ (pUK k u) t

/-- **An order-`0` system with uniformly positive `a = γ + ββ` and bounded `∂ₜβ` satisfies the
shifted `L²` hypotheses.**  The coercivity constant of `SysHyp` for `γ` itself is arbitrary. -/
theorem SysHyp.toShL2Hyp {ι : Type v} [Fintype ι] [DecidableEq ι] {S : WaveSys 3 ι}
    {u F : ι → X3 → ℝ} {T lam lamS M : ℝ} (h : SysHyp S u F T lam M 0) (hlamS : 0 < lamS)
    (hco : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
      lamS * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, acoef S.β S.γ i j x * ξ i * ξ j)
    (hβt : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ i, |pd (S.β i) 0 x| ≤ M) :
    ShL2Hyp S.β S.γ u (S.lower u) F
      (fun _ => M * (Fintype.card ι + 1) ^ 2 * ((3 : ℕ) + 2)) T lamS M where
  su := h.su
  sβ := h.sβ
  sγ := h.sγ
  cL := h.toL2Hyp.cL
  cF := h.toL2Hyp.cF
  cm := continuous_const
  pu := h.pu
  pβ := h.pβ
  pγ := h.pγ
  eqn := h.toL2Hyp.eqn
  γ_symm := h.γ_symm
  lam_pos := hlamS
  coer := hco
  M_nonneg := h.M_nonneg
  bβ := fun x hx i => h.bβ i [] (Nat.zero_le _) x hx
  bβ1 := fun x hx i μ => by
    induction μ using Fin.cases with
    | zero => exact hβt x hx i
    | succ j => exact h.bβx x hx i j
  bγ := fun x hx i j => h.bγ i j [] (Nat.zero_le _) x hx
  bγ1 := h.bγ1
  m_nonneg := h.toL2Hyp.m_nonneg
  bL := h.toL2Hyp.bL

/-- The prolonged system inherits the shift hypotheses (the principal part is unchanged). -/
theorem SysHyp.toShL2HypK (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] {S : WaveSys 3 ι}
    {u F : ι → X3 → ℝ} {T lam lamS M : ℝ} (h : SysHyp S u F T lam M k) (hlamS : 0 < lamS)
    (hco : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
      lamS * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, acoef S.β S.γ i j x * ξ i * ξ j)
    (hβt : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ i, |pd (S.β i) 0 x| ≤ M) :
    ShL2Hyp S.β S.γ (pUK k u) ((prolongK k S).lower (pUK k u)) (pUK k F)
      (fun _ => mk 3 ι k M) T lamS (Mk k M) := by
  have hK := SysHyp.prolongK (r := 0) k (by rw [Nat.zero_add]; exact h)
  have hM := h.M_nonneg
  have hMk : M ≤ 3 ^ k * M := le_mul_of_one_le_left hM (one_le_pow₀ (by norm_num))
  have hL := SysHyp.toShL2Hyp hK hlamS (by rw [prolongK_β, prolongK_γ]; exact hco)
    (fun x hx i => by rw [prolongK_β]; exact (hβt x hx i).trans hMk)
  rw [prolongK_β, prolongK_γ] at hL
  exact hL

/-- **The linear `H^k` wave energy estimate with the normal-derivative multiplier** on
`[0, T] × 𝕋³`: for smooth periodic solutions of `∂ₜ²u = 2βⁱ∂ᵢ∂ₜu + γ^{ij}∂ᵢ∂ⱼu + (lower) + F`
with `L^∞_t W^{k,∞}_x` coefficients (`SysHyp … k`, any coercivity constant for `γ`), `a = γ + ββ`
uniformly `λ_S`-coercive and `|∂ₜβ| ≤ M`, the order-`k` shifted energy satisfies
`√E_{S,k}(t) ≤ (√E_{S,k}(0) + ∫₀ᵗ ‖F‖_{H^k}) exp(½∫₀ᵗ k_S)` with `k_S` depending only on
`|ι|, k, λ_S, M`. -/
theorem hkS_energy (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] {S : WaveSys 3 ι}
    {u F : ι → X3 → ℝ} {T lam lamS M : ℝ} (h : SysHyp S u F T lam M k) (hlamS : 0 < lamS)
    (hco : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
      lamS * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, acoef S.β S.γ i j x * ξ i * ξ j)
    (hβt : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ i, |pd (S.β i) 0 x| ≤ M) :
    ∀ t ∈ Icc 0 T, Real.sqrt (energySK k S.β S.γ u t) ≤
      (Real.sqrt (energySK k S.β S.γ u 0) + ∫ s in (0)..t, normK k F s) *
        Real.exp ((∫ s in (0)..t, ShL2Hyp.kS (Mk k M) lamS (fun _ => mk 3 ι k M) s) / 2) :=
  (SysHyp.toShL2HypK k h hlamS hco hβt).sqrt_energyS_le

/-- **`eq:hyperbolic-energy` with the normal-derivative multiplier (abstract form)**: when
`‖F(t)‖_{H^k} ≤ a(t)√E_{S,k}(t) + σ(t)`,
`√E_{S,k}(t) ≤ (√E_{S,k}(0) + ∫₀ᵗ σ) exp(½∫₀ᵗ (k_S + 2a))`. -/
theorem hkS_energy_of_forcing (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] {S : WaveSys 3 ι}
    {u F : ι → X3 → ℝ} {T lam lamS M : ℝ} (h : SysHyp S u F T lam M k) (hlamS : 0 < lamS)
    (hco : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
      lamS * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, acoef S.β S.γ i j x * ξ i * ξ j)
    (hβt : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ i, |pd (S.β i) 0 x| ≤ M)
    {a σ : ℝ → ℝ} (ha : Continuous a) (hσ : Continuous σ) (ha0 : ∀ t, 0 ≤ a t)
    (hσ0 : ∀ t, 0 ≤ σ t)
    (hF : ∀ t ∈ Icc 0 T, normK k F t ≤ a t * Real.sqrt (energySK k S.β S.γ u t) + σ t) :
    ∀ t ∈ Icc 0 T, Real.sqrt (energySK k S.β S.γ u t) ≤
      (Real.sqrt (energySK k S.β S.γ u 0) + ∫ s in (0)..t, σ s) *
        Real.exp ((∫ s in (0)..t, (ShL2Hyp.kS (Mk k M) lamS (fun _ => mk 3 ι k M) s +
          2 * a s)) / 2) :=
  (SysHyp.toShL2HypK k h hlamS hco hβt).sqrt_energyS_le_of_forcing ha hσ ha0 hσ0 hF

/-- **The order-`k` shifted energy controls all derivatives of order `≤ k`**:
`∫ (|∂ₜ∂^w u_b|² + |∇∂^w u_b|² + |∂^w u_b|²) ≤ C_W E_{S,k}` for every word `|w| ≤ k`. -/
theorem energySK_ge (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] {S : WaveSys 3 ι}
    {u F : ι → X3 → ℝ} {T lam lamS M : ℝ} (h : SysHyp S u F T lam M k) (hlamS : 0 < lamS)
    (hco : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
      lamS * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, acoef S.β S.γ i j x * ξ i * ξ j)
    (hβt : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ i, |pd (S.β i) 0 x| ≤ M) {t : ℝ}
    (ht : t ∈ Icc 0 T) (b : ι) (w : List (Fin 3)) (hw : w.length ≤ k) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1,
      (pd (dW (w.map Fin.succ) (u b)) 0 (Fin.cons t y) ^ 2 +
        ∑ i : Fin 3, pd (dW (w.map Fin.succ) (u b)) i.succ (Fin.cons t y) ^ 2 +
        dW (w.map Fin.succ) (u b) (Fin.cons t y) ^ 2) ≤
      ShL2Hyp.Cw (Mk k M) lamS * energySK k S.β S.γ u t := by
  obtain ⟨p, hp⟩ := exists_pUK_eq k u b w hw
  rw [← hp]
  exact (SysHyp.toShL2HypK k h hlamS hco hβt).integral_comp_le ht p

/-- `E_{S,k} ≤ C_U ∫ Σ_p size(∂^p u)`. -/
theorem energySK_le_size (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] {S : WaveSys 3 ι}
    {u F : ι → X3 → ℝ} {T lam lamS M : ℝ} (h : SysHyp S u F T lam M k) (hlamS : 0 < lamS)
    (hco : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
      lamS * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, acoef S.β S.γ i j x * ξ i * ξ j)
    (hβt : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ i, |pd (S.β i) 0 x| ≤ M) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    energySK k S.β S.γ u t ≤
      ShL2Hyp.Cu (Mk k M) * ∫ y in Icc (0 : Fin 3 → ℝ) 1, size (pUK k u) (Fin.cons t y) :=
  (SysHyp.toShL2HypK k h hlamS hco hβt).energyS_le_size ht

theorem energySK_nonneg (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι] {S : WaveSys 3 ι}
    {u F : ι → X3 → ℝ} {T lam lamS M : ℝ} (h : SysHyp S u F T lam M k) (hlamS : 0 < lamS)
    (hco : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
      lamS * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, acoef S.β S.γ i j x * ξ i * ξ j)
    (hβt : ∀ x : X3, x 0 ∈ Icc 0 T → ∀ i, |pd (S.β i) 0 x| ≤ M) {t : ℝ}
    (ht : t ∈ Icc 0 T) : 0 ≤ energySK k S.β S.γ u t :=
  (SysHyp.toShL2HypK k h hlamS hco hβt).energyS_nonneg ht

/-- **The convergence step of `thm:hyperbolic` with the normal-derivative multiplier**: for a
two-parameter family of difference systems with common constants (order `k`, `SysHyp` with any
`γ`-coercivity constant, `a = γ + ββ` uniformly `λ_S`-coercive, `|∂ₜβ| ≤ M`), forcing bounds
`‖F_{h,j}‖_{H^k} ≤ a_{h,j}√E_{S,k} + σ_{h,j}` with `∫₀ᵀ a_{h,j} ≤ A`, initial energies `→ 0` and
`∫₀ᵀ σ_{h,j} → 0`, the difference energies tend to zero uniformly on `[0, T]`. -/
theorem energySK_tendsto_zero (k : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι]
    {S : ℕ → ℕ → WaveSys 3 ι} {w F : ℕ → ℕ → ι → X3 → ℝ} {T lam lamS M A : ℝ}
    (h : ∀ i j, SysHyp (S i j) (w i j) (F i j) T lam M k) (hlamS : 0 < lamS) (hT : 0 ≤ T)
    (hco : ∀ i j, ∀ x : X3, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
      lamS * ∑ l, ξ l ^ 2 ≤ ∑ l, ∑ n, acoef (S i j).β (S i j).γ l n x * ξ l * ξ n)
    (hβt : ∀ i j, ∀ x : X3, x 0 ∈ Icc 0 T → ∀ l, |pd ((S i j).β l) 0 x| ≤ M)
    {a σ : ℕ → ℕ → ℝ → ℝ} (ha : ∀ i j, Continuous (a i j)) (hσ : ∀ i j, Continuous (σ i j))
    (ha0 : ∀ i j t, 0 ≤ a i j t) (hσ0 : ∀ i j t, 0 ≤ σ i j t)
    (hF : ∀ i j, ∀ t ∈ Icc 0 T, normK k (F i j) t ≤
      a i j t * Real.sqrt (energySK k (S i j).β (S i j).γ (w i j) t) + σ i j t)
    (hA : ∀ i j, ∫ s in (0)..T, a i j s ≤ A)
    (h0 : Tendsto (fun p : ℕ × ℕ => energySK k (S p.1 p.2).β (S p.1 p.2).γ (w p.1 p.2) 0) atTop
      (𝓝 0))
    (hσT : Tendsto (fun p : ℕ × ℕ => ∫ s in (0)..T, σ p.1 p.2 s) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ p : ℕ × ℕ in atTop, ∀ t ∈ Icc 0 T,
      Real.sqrt (energySK k (S p.1 p.2).β (S p.1 p.2).γ (w p.1 p.2) t) ≤ ε := by
  intro ε hε
  set K := ShL2Hyp.kS (Mk k M) lamS (fun _ => mk 3 ι k M) 0
  set B := Real.exp ((K * T + 2 * A) / 2)
  have hB : 0 < B := Real.exp_pos _
  have hlim : Tendsto (fun p : ℕ × ℕ => Real.sqrt (energySK k (S p.1 p.2).β (S p.1 p.2).γ
      (w p.1 p.2) 0) + ∫ s in (0)..T, σ p.1 p.2 s) atTop (𝓝 0) := by
    have := (h0.sqrt).add hσT
    simpa using this
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / B by positivity))] with p hp t ht
  have hL := SysHyp.toShL2HypK k (h p.1 p.2) hlamS (hco p.1 p.2) (hβt p.1 p.2)
  have hE := hkS_energy_of_forcing k (h p.1 p.2) hlamS (hco p.1 p.2) (hβt p.1 p.2) (ha p.1 p.2)
    (hσ p.1 p.2) (ha0 p.1 p.2) (hσ0 p.1 p.2) (hF p.1 p.2) t ht
  have hK0 : 0 ≤ K := hL.kS_nonneg 0
  have hint : ∫ s in (0)..t, (ShL2Hyp.kS (Mk k M) lamS (fun _ => mk 3 ι k M) s +
      2 * a p.1 p.2 s) ≤ K * T + 2 * A := by
    have hc1 : Continuous fun s : ℝ => ShL2Hyp.kS (Mk k M) lamS (fun _ => mk 3 ι k M) s :=
      continuous_const
    rw [intervalIntegral.integral_add
      (f := fun s => ShL2Hyp.kS (Mk k M) lamS (fun _ => mk 3 ι k M) s)
      (g := fun s => 2 * a p.1 p.2 s) (hc1.intervalIntegrable _ _)
      ((continuous_const.mul (ha p.1 p.2)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
    have e1 : ∫ s in (0)..t, ShL2Hyp.kS (Mk k M) lamS (fun _ => mk 3 ι k M) s = t * K := by
      simp [K, ShL2Hyp.kS]; ring
    have e2 : ∫ s in (0)..t, a p.1 p.2 s ≤ ∫ s in (0)..T, a p.1 p.2 s :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Eventually.of_forall fun s => ha0 p.1 p.2 s) ((ha p.1 p.2).intervalIntegrable _ _)
    rw [e1]
    have := hA p.1 p.2
    have : t * K ≤ T * K := mul_le_mul_of_nonneg_right ht.2 hK0
    nlinarith
  have hσt : ∫ s in (0)..t, σ p.1 p.2 s ≤ ∫ s in (0)..T, σ p.1 p.2 s :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Eventually.of_forall fun s => hσ0 p.1 p.2 s) ((hσ p.1 p.2).intervalIntegrable _ _)
  have hexp : Real.exp ((∫ s in (0)..t, (ShL2Hyp.kS (Mk k M) lamS (fun _ => mk 3 ι k M) s +
      2 * a p.1 p.2 s)) / 2) ≤ B := Real.exp_le_exp.2 (by linarith)
  have hX0 : 0 ≤ Real.sqrt (energySK k (S p.1 p.2).β (S p.1 p.2).γ (w p.1 p.2) 0) +
      ∫ s in (0)..t, σ p.1 p.2 s :=
    add_nonneg (Real.sqrt_nonneg _) (intervalIntegral.integral_nonneg ht.1 fun s _ =>
      hσ0 p.1 p.2 s)
  calc Real.sqrt (energySK k (S p.1 p.2).β (S p.1 p.2).γ (w p.1 p.2) t) ≤ _ := hE
    _ ≤ (Real.sqrt (energySK k (S p.1 p.2).β (S p.1 p.2).γ (w p.1 p.2) 0) +
          ∫ s in (0)..T, σ p.1 p.2 s) * B :=
        mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by linarith)
    _ ≤ ε / B * B := mul_le_mul_of_nonneg_right hp.le hB.le
    _ = ε := by field_simp

end RenewalGeometry.SlabWaveShift
