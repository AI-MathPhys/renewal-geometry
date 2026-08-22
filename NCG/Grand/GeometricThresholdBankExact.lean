/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Geometric threshold bank

Exact encoding of `thm:GT-geometric-threshold-bank` (RI.10–RI.13) via the
spectral theorem for Hermitian matrices.

* `layerSum τ q K λ` is the scalar geometric layer sum
  `τ·1[λ ≥ τ] + ∑_{k=1}^{K} (q-1) q^{k-1} τ · 1[λ ≥ q^k τ]`; it equals `q^m τ`
  on `[q^m τ, q^{m+1} τ)` (`layerSum_eq_pow`) and satisfies the scalar
  enclosure `D(λ) ≤ λ ≤ q D(λ) + τ` on `[0, q^{K+1} τ)` (`layerSum_enclosure`);
* `thresholdProjection S hS t = 1_{[t,∞)}(S)` and `layerBank` is the matrix
  layer sum (RI.10), expressed through the spectral theorem;
  `layerBank_eq_sum` is the boxed expansion (RI.10);
* `layerBank_enclosure` (RI.11): `𝔇 ⪯ S ⪯ q 𝔇 + τ I` in Loewner order when the
  bank covers the spectrum (`q^{K+1} τ > λ_max`);
* `bank_sum_enclosure` (RI.12, operator form): summing over source components,
  `𝔇 ⪯ B ⪯ q 𝔇 + ρ I`, and `min_eigen_enclosure`: `κ ≤ β ≤ q κ + ρ` for the
  minimum Rayleigh values;
* `influence_window` (RI.13): with `m I ⪯ C ⪯ M I`,
  `m/(qκ+ρ) ≤ Λ(B,C) ≤ M/κ` for the Loewner influence
  `Λ(B,C) = inf{λ ≥ 0 : C ⪯ λ B}`.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace GeometricThresholdBank

/-! ### The scalar layer sum -/

/-- Layer weights: `w₀ = τ`, `w_{k+1} = (q-1) q^k τ`. -/
def layerWeight (τ q : ℝ) : ℕ → ℝ
  | 0 => τ
  | k + 1 => (q - 1) * q ^ k * τ

/-- The scalar geometric layer sum with `K + 1` layers. -/
noncomputable def layerSum (τ q : ℝ) (K : ℕ) (l : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), if q ^ k * τ ≤ l then layerWeight τ q k else 0

theorem layerWeight_nonneg {τ q : ℝ} (hτ : 0 ≤ τ) (hq : 1 ≤ q) (k : ℕ) :
    0 ≤ layerWeight τ q k := by
  cases k with
  | zero => exact hτ
  | succ k =>
    simp only [layerWeight]
    have : 0 ≤ q - 1 := by linarith
    positivity

theorem layerSum_nonneg {τ q : ℝ} (hτ : 0 ≤ τ) (hq : 1 ≤ q) (K : ℕ) (l : ℝ) :
    0 ≤ layerSum τ q K l :=
  Finset.sum_nonneg fun k _ => by
    split_ifs
    · exact layerWeight_nonneg hτ hq k
    · exact le_rfl

/-- Partial sums of the layer weights telescope to `q^m τ`. -/
theorem sum_layerWeight (τ q : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), layerWeight τ q k = q ^ m * τ := by
  rw [Finset.sum_range_succ']
  simp only [layerWeight]
  have : ∑ k ∈ Finset.range m, (q - 1) * q ^ k * τ
      = ((∑ k ∈ Finset.range m, q ^ k) * (q - 1)) * τ := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [this, geom_sum_mul]
  ring

/-- Below the first threshold the layer sum vanishes. -/
theorem layerSum_eq_zero {τ q : ℝ} (hτ : 0 < τ) (hq : 1 ≤ q) (K : ℕ) {l : ℝ} (hl : l < τ) :
    layerSum τ q K l = 0 := by
  unfold layerSum
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [if_neg]
  have : τ ≤ q ^ k * τ := by
    have : 1 ≤ q ^ k := one_le_pow₀ hq
    nlinarith
  linarith

/-- On `[q^m τ, q^{m+1} τ)` with `m ≤ K` the layer sum is `q^m τ`. -/
theorem layerSum_eq_pow {τ q : ℝ} (hτ : 0 < τ) (hq : 1 < q) (K : ℕ) {l : ℝ} {m : ℕ}
    (hm : m ≤ K) (hlow : q ^ m * τ ≤ l) (hhigh : l < q ^ (m + 1) * τ) :
    layerSum τ q K l = q ^ m * τ := by
  unfold layerSum
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range (K + 1)).filter (fun k => q ^ k * τ ≤ l) = Finset.range (m + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hk⟩
      by_contra hcon
      push Not at hcon
      have : q ^ (m + 1) ≤ q ^ k := pow_le_pow_right₀ hq.le (by omega)
      have : q ^ (m + 1) * τ ≤ q ^ k * τ := mul_le_mul_of_nonneg_right this hτ.le
      linarith
    · intro hk
      refine ⟨by omega, ?_⟩
      have : q ^ k ≤ q ^ m := pow_le_pow_right₀ hq.le (by omega)
      have : q ^ k * τ ≤ q ^ m * τ := mul_le_mul_of_nonneg_right this hτ.le
      linarith
  rw [hfilter, sum_layerWeight]

/-- **Scalar enclosure** `D(λ) ≤ λ ≤ q D(λ) + τ` when the bank covers `λ`. -/
theorem layerSum_enclosure {τ q : ℝ} (hτ : 0 < τ) (hq : 1 < q) (K : ℕ) {l : ℝ} (hl0 : 0 ≤ l)
    (hcover : l < q ^ (K + 1) * τ) :
    layerSum τ q K l ≤ l ∧ l ≤ q * layerSum τ q K l + τ := by
  rcases lt_or_ge l τ with hlt | hge
  · rw [layerSum_eq_zero hτ hq.le K hlt]
    constructor
    · exact hl0
    · linarith
  · -- the least `m` with `l < q^(m+1) τ`
    have hex : ∃ m, l < q ^ (m + 1) * τ := ⟨K, hcover⟩
    classical
    set m := Nat.find hex with hm
    have hmspec : l < q ^ (m + 1) * τ := Nat.find_spec hex
    have hmK : m ≤ K := Nat.find_min' hex hcover
    have hlow : q ^ m * τ ≤ l := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0]; simpa using hge
      · have := Nat.find_min hex (show m - 1 < m by omega)
        push Not at this
        have hm1 : m - 1 + 1 = m := by omega
        rwa [hm1] at this
    rw [layerSum_eq_pow hτ hq K hmK hlow hmspec]
    constructor
    · exact hlow
    · rw [pow_succ] at hmspec
      nlinarith

/-! ### The matrix layer bank via the spectral theorem -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugation by the eigenvector unitary: `U · diag(f ∘ λ) · U^*`. -/
noncomputable def spectralFunction {S : Matrix n n ℂ} (hS : S.IsHermitian) (f : ℝ → ℝ) :
    Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ hS.eigenvectorUnitary
    (diagonal (RCLike.ofReal ∘ fun i => f (hS.eigenvalues i)))

/-- The spectral threshold projection `Q_S(t) = 1_{[t,∞)}(S)`. -/
noncomputable def thresholdProjection {S : Matrix n n ℂ} (hS : S.IsHermitian) (t : ℝ) :
    Matrix n n ℂ :=
  spectralFunction hS (fun l => if t ≤ l then 1 else 0)

/-- The geometric layer bank `𝔇_{τ,q}(S)` with `K + 1` layers. -/
noncomputable def layerBank {S : Matrix n n ℂ} (hS : S.IsHermitian) (τ q : ℝ) (K : ℕ) :
    Matrix n n ℂ :=
  spectralFunction hS (layerSum τ q K)

theorem spectralFunction_id {S : Matrix n n ℂ} (hS : S.IsHermitian) :
    spectralFunction hS id = S := by
  unfold spectralFunction
  exact hS.spectral_theorem.symm

theorem spectralFunction_add {S : Matrix n n ℂ} (hS : S.IsHermitian) (f g : ℝ → ℝ) :
    spectralFunction hS (fun l => f l + g l) = spectralFunction hS f + spectralFunction hS g := by
  unfold spectralFunction
  rw [← map_add, diagonal_add]
  congr 2
  funext i
  simp

theorem spectralFunction_sub {S : Matrix n n ℂ} (hS : S.IsHermitian) (f g : ℝ → ℝ) :
    spectralFunction hS (fun l => f l - g l) = spectralFunction hS f - spectralFunction hS g := by
  unfold spectralFunction
  rw [← map_sub, diagonal_sub]
  congr 2
  funext i
  simp

theorem spectralFunction_smul {S : Matrix n n ℂ} (hS : S.IsHermitian) (c : ℝ) (f : ℝ → ℝ) :
    spectralFunction hS (fun l => c * f l) = (c : ℂ) • spectralFunction hS f := by
  unfold spectralFunction
  rw [← map_smul]
  congr 1
  rw [← diagonal_smul]
  congr 1
  funext i
  simp

theorem spectralFunction_const {S : Matrix n n ℂ} (hS : S.IsHermitian) (c : ℝ) :
    spectralFunction hS (fun _ => c) = (c : ℂ) • (1 : Matrix n n ℂ) := by
  unfold spectralFunction
  have : diagonal (RCLike.ofReal ∘ fun i => (fun _ : ℝ => c) (hS.eigenvalues i))
      = (c : ℂ) • (1 : Matrix n n ℂ) := by
    rw [← diagonal_one, ← diagonal_smul]
    congr 1
    funext i
    simp
  rw [this, map_smul, map_one]

theorem spectralFunction_sum {S : Matrix n n ℂ} (hS : S.IsHermitian) {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) :
    spectralFunction hS (fun l => ∑ k ∈ s, f k l) = ∑ k ∈ s, spectralFunction hS (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [spectralFunction_const]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have : (fun l => ∑ k ∈ insert a s, f k l) = fun l => f a l + ∑ k ∈ s, f k l := by
      funext l; rw [Finset.sum_insert ha]
    rw [this, spectralFunction_add, ih]

/-- A spectral function with nonnegative values on the spectrum is PSD. -/
theorem spectralFunction_posSemidef {S : Matrix n n ℂ} (hS : S.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, 0 ≤ f (hS.eigenvalues i)) : (spectralFunction hS f).PosSemidef := by
  unfold spectralFunction
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  refine PosSemidef.mul_mul_conjTranspose_same ?_ _
  rw [posSemidef_diagonal_iff]
  intro i
  simpa [Complex.zero_le_real] using hf i

/-- **(RI.10)**: the layer bank is the displayed weighted sum of threshold
projections. -/
theorem layerBank_eq_sum {S : Matrix n n ℂ} (hS : S.IsHermitian) (τ q : ℝ) (K : ℕ) :
    layerBank hS τ q K
      = ∑ k ∈ Finset.range (K + 1),
          (layerWeight τ q k : ℂ) • thresholdProjection hS (q ^ k * τ) := by
  unfold layerBank thresholdProjection
  have : layerSum τ q K
      = fun l => ∑ k ∈ Finset.range (K + 1),
          layerWeight τ q k * (if q ^ k * τ ≤ l then 1 else 0) := by
    funext l
    unfold layerSum
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [this, spectralFunction_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact spectralFunction_smul hS _ _

/-- **(RI.11)**: `𝔇 ⪯ S ⪯ q 𝔇 + τ I` when the bank covers the spectrum. -/
theorem layerBank_enclosure {S : Matrix n n ℂ} (hS : S.PosSemidef) (τ q : ℝ) (hτ : 0 < τ)
    (hq : 1 < q) (K : ℕ) (hcover : ∀ i, hS.1.eigenvalues i < q ^ (K + 1) * τ) :
    (S - layerBank hS.1 τ q K).PosSemidef ∧
      ((q : ℂ) • layerBank hS.1 τ q K + (τ : ℂ) • (1 : Matrix n n ℂ) - S).PosSemidef := by
  have h1 : S - layerBank hS.1 τ q K
      = spectralFunction hS.1 (fun l => id l - layerSum τ q K l) := by
    rw [spectralFunction_sub, spectralFunction_id]
    rfl
  have h2 : (q : ℂ) • layerBank hS.1 τ q K + (τ : ℂ) • (1 : Matrix n n ℂ) - S
      = spectralFunction hS.1 (fun l => (q * layerSum τ q K l + τ) - id l) := by
    rw [spectralFunction_sub, spectralFunction_add, spectralFunction_smul, spectralFunction_const,
      spectralFunction_id]
    rfl
  constructor
  · rw [h1]
    refine spectralFunction_posSemidef hS.1 _ fun i => ?_
    have := (layerSum_enclosure hτ hq K (hS.eigenvalues_nonneg i) (hcover i)).1
    simp only [id]
    linarith
  · rw [h2]
    refine spectralFunction_posSemidef hS.1 _ fun i => ?_
    have := (layerSum_enclosure hτ hq K (hS.eigenvalues_nonneg i) (hcover i)).2
    simp only [id]
    linarith

/-! ### Source sums, minimum Rayleigh values, and the influence window -/

/-- The real quadratic form `Re ⟪x, M x⟫`. -/
noncomputable def rayleigh (M : Matrix n n ℂ) (x : n → ℂ) : ℝ := (star x ⬝ᵥ (M *ᵥ x)).re

omit [DecidableEq n] in
theorem rayleigh_nonneg {M : Matrix n n ℂ} (hM : M.PosSemidef) (x : n → ℂ) : 0 ≤ rayleigh M x :=
  (Complex.le_def.mp (hM.dotProduct_mulVec_nonneg x)).1

omit [DecidableEq n] in
theorem rayleigh_sub {A B : Matrix n n ℂ} (x : n → ℂ) :
    rayleigh (A - B) x = rayleigh A x - rayleigh B x := by
  unfold rayleigh
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re]

omit [DecidableEq n] in
theorem rayleigh_add {A B : Matrix n n ℂ} (x : n → ℂ) :
    rayleigh (A + B) x = rayleigh A x + rayleigh B x := by
  unfold rayleigh
  rw [add_mulVec, dotProduct_add, Complex.add_re]

omit [DecidableEq n] in
theorem rayleigh_smul (c : ℝ) (A : Matrix n n ℂ) (x : n → ℂ) :
    rayleigh ((c : ℂ) • A) x = c * rayleigh A x := by
  unfold rayleigh
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

theorem rayleigh_one (x : n → ℂ) : rayleigh 1 x = ∑ i, ‖x i‖ ^ 2 := by
  unfold rayleigh
  rw [one_mulVec, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.ofReal_re]

omit [DecidableEq n] in
/-- Loewner order in Rayleigh form. -/
theorem rayleigh_le_of_posSemidef {A B : Matrix n n ℂ} (h : (B - A).PosSemidef) (x : n → ℂ) :
    rayleigh A x ≤ rayleigh B x := by
  have := rayleigh_nonneg h x
  rw [rayleigh_sub] at this
  linarith

/-- **(RI.12, operator form)**: for `B = ∑ S_i` and `𝔇 = ∑ 𝔇_i`,
`𝔇 ⪯ B ⪯ q 𝔇 + ρ I` with `ρ = ∑ τ_i`. -/
theorem bank_sum_enclosure {ι : Type*} (s : Finset ι) (S : ι → Matrix n n ℂ)
    (hS : ∀ i, (S i).PosSemidef) (τ : ι → ℝ) (q : ℝ) (hτ : ∀ i, 0 < τ i) (hq : 1 < q)
    (K : ι → ℕ) (hcover : ∀ i j, (hS i).1.eigenvalues j < q ^ (K i + 1) * τ i) (x : n → ℂ) :
    rayleigh (∑ i ∈ s, layerBank (hS i).1 (τ i) q (K i)) x ≤ rayleigh (∑ i ∈ s, S i) x ∧
      rayleigh (∑ i ∈ s, S i) x
        ≤ q * rayleigh (∑ i ∈ s, layerBank (hS i).1 (τ i) q (K i)) x
          + (∑ i ∈ s, τ i) * ∑ j, ‖x j‖ ^ 2 := by
  classical
  have hray : ∀ (F : ι → Matrix n n ℂ), rayleigh (∑ i ∈ s, F i) x = ∑ i ∈ s, rayleigh (F i) x := by
    intro F
    induction s using Finset.induction_on with
    | empty => simp [rayleigh]
    | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rayleigh_add, ih]
  rw [hray, hray]
  constructor
  · refine Finset.sum_le_sum fun i _ => ?_
    exact rayleigh_le_of_posSemidef (layerBank_enclosure (hS i) (τ i) q (hτ i) hq (K i)
      (hcover i)).1 x
  · rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := rayleigh_le_of_posSemidef (layerBank_enclosure (hS i) (τ i) q (hτ i) hq (K i)
      (hcover i)).2 x
    rw [rayleigh_add, rayleigh_smul, rayleigh_smul, rayleigh_one] at this
    exact this

/-- `κ` is the minimum Rayleigh value of `M`: a lower bound attained at a
nonzero vector (finite-dimensional `λ_min`). -/
def IsMinRayleigh (M : Matrix n n ℂ) (κ : ℝ) : Prop :=
  (∀ x, κ * ∑ j, ‖x j‖ ^ 2 ≤ rayleigh M x) ∧
    ∃ x : n → ℂ, (∑ j, ‖x j‖ ^ 2) ≠ 0 ∧ rayleigh M x = κ * ∑ j, ‖x j‖ ^ 2

omit [DecidableEq n] in
/-- **(RI.12)**: `κ ≤ β ≤ q κ + ρ` for the minimum Rayleigh values of `𝔇` and `B`. -/
theorem min_eigen_enclosure (D B : Matrix n n ℂ) (q ρ κ β : ℝ)
    (hlow : ∀ x, rayleigh D x ≤ rayleigh B x)
    (hhigh : ∀ x, rayleigh B x ≤ q * rayleigh D x + ρ * ∑ j, ‖x j‖ ^ 2)
    (hκ : IsMinRayleigh D κ) (hβ : IsMinRayleigh B β) :
    κ ≤ β ∧ β ≤ q * κ + ρ := by
  obtain ⟨hκle, xD, hxD, hxDeq⟩ := hκ
  obtain ⟨hβle, xB, hxB, hxBeq⟩ := hβ
  have hnD : 0 < ∑ j, ‖xD j‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hxD)
  have hnB : 0 < ∑ j, ‖xB j‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hxB)
  constructor
  · -- evaluate at the minimizer of `B`
    have h1 := hκle xB
    have h2 := hlow xB
    rw [hxBeq] at h2
    by_contra hcon
    push Not at hcon
    nlinarith
  · -- evaluate at the minimizer of `D`
    have h1 := hβle xD
    have h2 := hhigh xD
    rw [hxDeq] at h2
    by_contra hcon
    push Not at hcon
    nlinarith

/-- The Loewner influence `Λ(B,C) = inf{λ ≥ 0 : C ⪯ λ B}` in Rayleigh form. -/
noncomputable def influence (B C : Matrix n n ℂ) : ℝ :=
  sInf {l : ℝ | 0 ≤ l ∧ ∀ x, rayleigh C x ≤ l * rayleigh B x}

omit [DecidableEq n] in
/-- **(RI.13)**: with `m I ⪯ C ⪯ M I` and the bank enclosure,
`m/(qκ+ρ) ≤ Λ(B,C) ≤ M/κ` (for `κ > 0`). -/
theorem influence_window (D B C : Matrix n n ℂ) (q ρ κ β m M : ℝ) (hq : 0 < q) (hρ : 0 ≤ ρ)
    (hκpos : 0 < κ) (hm : 0 ≤ m) (hmM : m ≤ M)
    (hlow : ∀ x, rayleigh D x ≤ rayleigh B x)
    (hhigh : ∀ x, rayleigh B x ≤ q * rayleigh D x + ρ * ∑ j, ‖x j‖ ^ 2)
    (hκ : IsMinRayleigh D κ) (hβ : IsMinRayleigh B β)
    (hCm : ∀ x, m * ∑ j, ‖x j‖ ^ 2 ≤ rayleigh C x)
    (hCM : ∀ x, rayleigh C x ≤ M * ∑ j, ‖x j‖ ^ 2) :
    m / (q * κ + ρ) ≤ influence B C ∧ influence B C ≤ M / κ := by
  obtain ⟨hκβ, hβle⟩ := min_eigen_enclosure D B q ρ κ β hlow hhigh hκ hβ
  have hMκ : 0 ≤ M / κ := div_nonneg (le_trans hm hmM) hκpos.le
  -- `M/κ` is admissible
  have hmem : M / κ ∈ {l : ℝ | 0 ≤ l ∧ ∀ x, rayleigh C x ≤ l * rayleigh B x} := by
    refine ⟨hMκ, fun x => ?_⟩
    have h1 := hCM x
    have h2 := hκ.1 x
    have h3 := hlow x
    have hnorm : 0 ≤ ∑ j, ‖x j‖ ^ 2 := by positivity
    calc rayleigh C x ≤ M * ∑ j, ‖x j‖ ^ 2 := h1
      _ = (M / κ) * (κ * ∑ j, ‖x j‖ ^ 2) := by field_simp
      _ ≤ (M / κ) * rayleigh D x := mul_le_mul_of_nonneg_left h2 hMκ
      _ ≤ (M / κ) * rayleigh B x := mul_le_mul_of_nonneg_left h3 hMκ
  have hbdd : BddBelow {l : ℝ | 0 ≤ l ∧ ∀ x, rayleigh C x ≤ l * rayleigh B x} :=
    ⟨0, fun l hl => hl.1⟩
  constructor
  · -- every admissible `λ` satisfies `λ ≥ m/(qκ+ρ)` (evaluate at the minimizer of `B`)
    refine le_csInf ⟨_, hmem⟩ fun l hl => ?_
    obtain ⟨_, xB, hxB, hxBeq⟩ := hβ
    have hnB : 0 < ∑ j, ‖xB j‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hxB)
    have h1 := hCm xB
    have h2 := hl.2 xB
    rw [hxBeq] at h2
    have hden : 0 < q * κ + ρ := by positivity
    rw [div_le_iff₀ hden]
    have hl0 := hl.1
    -- `m ‖x‖² ≤ λ β ‖x‖² ≤ λ (qκ+ρ) ‖x‖²`
    have : m * ∑ j, ‖xB j‖ ^ 2 ≤ l * (q * κ + ρ) * ∑ j, ‖xB j‖ ^ 2 := by
      calc m * ∑ j, ‖xB j‖ ^ 2 ≤ l * (β * ∑ j, ‖xB j‖ ^ 2) := le_trans h1 h2
        _ = l * β * ∑ j, ‖xB j‖ ^ 2 := by ring
        _ ≤ l * (q * κ + ρ) * ∑ j, ‖xB j‖ ^ 2 := by
            gcongr
    exact le_of_mul_le_mul_right this hnB
  · exact csInf_le hbdd hmem

end GeometricThresholdBank
end NCG
