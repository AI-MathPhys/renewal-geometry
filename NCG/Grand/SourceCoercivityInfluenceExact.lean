/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GeometricThresholdBankExact

/-!
# Source coercivity and reverse influence

Exact encoding of `thm:GT-source-coercivity-influence` (RI.3–RI.6) for
finite PSD source and target Grams `B, C`, with the Loewner influence
`Λ(B,C) = inf{λ ≥ 0 : C ⪯ λB}` (`GeometricThresholdBank.influence`) in
Rayleigh form.

* spectral support calculus for `B`: the support projection `Q = 1_{(0,∞)}(B)`
  (`supportProj`), `B Q = B`, `Q² = Q`, `Q = B^† B`, and the **spectral floor**
  `B ⪰ β₊ Q` with `β₊` the least positive eigenvalue (`floor_posSemidef`);
* `influence_finite_iff` (RI.3): an admissible `λ` exists iff `Ker B ⊆ Ker C`;
* `influence_eq_sup` (RI.4): on that branch `Λ(B,C)` is the supremum of the
  Rayleigh quotients `⟪x,Cx⟫/⟪x,Bx⟫` over `⟪x,Bx⟫ > 0` (the whitened norm
  `‖B^{†/2} C B^{†/2}‖` is this supremum by definition);
* `reciprocal_bound` (RI.5): every target-normalized source energy is at least
  `Λ⁻¹`, and `Λ⁻¹` is approached (`reciprocal_approx`), so
  `μ_C(B) = inf{⟪x,Bx⟫ : ⟪x,Cx⟫ = 1} = Λ(B,C)⁻¹` (`reciprocal_eq`);
* `extremizer_euler_lagrange` (RI.6): a maximizer `z` of the Rayleigh quotient
  satisfies `B z = Λ⁻¹ C z` on the supported quotient (with `⟪z,Cz⟫ = 1`,
  `⟪z,Bz⟫ = Λ⁻¹`), and `null_of_not_finite`: when no admissible `λ` exists
  there is a target-visible source null `z` with `B z = 0`, `⟪z,Cz⟫ > 0`.

Scope: attainment of the extremizer (compactness of the finite-dimensional
sphere) is not formalized; the Euler–Lagrange identity is proved for any
extremizer.
-/

open Matrix Finset NCG.GeometricThresholdBank
open scoped ComplexOrder MatrixOrder

-- decidability instances enter only through the spectral support calculus in proofs
set_option linter.unusedDecidableInType false

namespace NCG
namespace SourceCoercivityInfluence

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Spectral support calculus -/

theorem spectralFunction_congr {S : Matrix n n ℂ} (hS : S.IsHermitian) {f g : ℝ → ℝ}
    (h : ∀ i, f (hS.eigenvalues i) = g (hS.eigenvalues i)) :
    spectralFunction hS f = spectralFunction hS g := by
  unfold spectralFunction
  congr 2
  funext i
  simp [h i]

theorem spectralFunction_mul {S : Matrix n n ℂ} (hS : S.IsHermitian) (f g : ℝ → ℝ) :
    spectralFunction hS f * spectralFunction hS g = spectralFunction hS (fun l => f l * g l) := by
  unfold spectralFunction
  rw [← map_mul, diagonal_mul_diagonal]
  congr 2
  funext i
  simp

/-- The support projection `Q = 1_{(0,∞)}(B)`. -/
noncomputable def supportProj {B : Matrix n n ℂ} (hB : B.IsHermitian) : Matrix n n ℂ :=
  spectralFunction hB (fun l => if 0 < l then 1 else 0)

/-- The Moore–Penrose inverse `B^†` by spectral calculus. -/
noncomputable def pinv {B : Matrix n n ℂ} (hB : B.IsHermitian) : Matrix n n ℂ :=
  spectralFunction hB (fun l => if 0 < l then l⁻¹ else 0)

theorem supportProj_posSemidef {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    (supportProj hB).PosSemidef :=
  spectralFunction_posSemidef hB _ fun i => by split_ifs <;> norm_num

theorem supportProj_idem {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    supportProj hB * supportProj hB = supportProj hB := by
  unfold supportProj
  rw [spectralFunction_mul]
  refine spectralFunction_congr hB fun i => ?_
  split_ifs <;> norm_num

theorem mul_supportProj {B : Matrix n n ℂ} (hB : B.PosSemidef) :
    B * supportProj hB.1 = B := by
  have hid := spectralFunction_id hB.1
  calc B * supportProj hB.1
      = spectralFunction hB.1 id * spectralFunction hB.1 (fun l => if 0 < l then 1 else 0) := by
        unfold supportProj; rw [hid]
    _ = spectralFunction hB.1 (fun l => id l * if 0 < l then 1 else 0) :=
        spectralFunction_mul hB.1 _ _
    _ = spectralFunction hB.1 id := by
        refine spectralFunction_congr hB.1 fun i => ?_
        have := hB.eigenvalues_nonneg i
        simp only [id]
        split_ifs with h
        · ring
        · have : hB.1.eigenvalues i = 0 := le_antisymm (not_lt.mp h) this
          rw [this]; ring
    _ = B := hid

theorem supportProj_eq_pinv_mul {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    supportProj hB = pinv hB * B := by
  have hid := spectralFunction_id hB
  calc supportProj hB
      = spectralFunction hB (fun l => (if 0 < l then l⁻¹ else 0) * id l) := by
        unfold supportProj
        refine spectralFunction_congr hB fun i => ?_
        simp only [id]
        split_ifs with h
        · field_simp
        · ring
    _ = spectralFunction hB (fun l => if 0 < l then l⁻¹ else 0) * spectralFunction hB id :=
        (spectralFunction_mul hB _ _).symm
    _ = pinv hB * B := by unfold pinv; rw [hid]

/-- `Ker B ⊆ Ker Q`. -/
theorem supportProj_mulVec_eq_zero {B : Matrix n n ℂ} (hB : B.IsHermitian) {x : n → ℂ}
    (hx : B *ᵥ x = 0) : supportProj hB *ᵥ x = 0 := by
  rw [supportProj_eq_pinv_mul, ← mulVec_mulVec, hx, mulVec_zero]

/-- `x - Q x ∈ Ker B`. -/
theorem mulVec_sub_supportProj {B : Matrix n n ℂ} (hB : B.PosSemidef) (x : n → ℂ) :
    B *ᵥ (x - supportProj hB.1 *ᵥ x) = 0 := by
  rw [mulVec_sub, mulVec_mulVec, mul_supportProj hB, sub_self]

/-- The least positive eigenvalue (`1` if there is none). -/
noncomputable def posFloor {B : Matrix n n ℂ} (hB : B.IsHermitian) : ℝ := by
  classical
  exact if h : (Finset.univ.filter fun i => 0 < hB.eigenvalues i).Nonempty
    then ((Finset.univ.filter fun i => 0 < hB.eigenvalues i).image hB.eigenvalues).min'
      (Finset.Nonempty.image h _)
    else 1

theorem posFloor_pos {B : Matrix n n ℂ} (hB : B.IsHermitian) : 0 < posFloor hB := by
  classical
  unfold posFloor
  split_ifs with h
  · have := Finset.min'_mem
      ((Finset.univ.filter fun i => 0 < hB.eigenvalues i).image hB.eigenvalues)
      (Finset.Nonempty.image h _)
    rw [Finset.mem_image] at this
    obtain ⟨i, hi, hieq⟩ := this
    rw [Finset.mem_filter] at hi
    rw [← hieq]
    exact hi.2
  · norm_num

theorem posFloor_le {B : Matrix n n ℂ} (hB : B.IsHermitian) (i : n)
    (hi : 0 < hB.eigenvalues i) : posFloor hB ≤ hB.eigenvalues i := by
  classical
  unfold posFloor
  have hne : (Finset.univ.filter fun i => 0 < hB.eigenvalues i).Nonempty :=
    ⟨i, by simp [hi]⟩
  rw [dif_pos hne]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩)

/-- **Spectral floor**: `B ⪰ β₊ Q`. -/
theorem floor_posSemidef {B : Matrix n n ℂ} (hB : B.PosSemidef) :
    (B - (posFloor hB.1 : ℂ) • supportProj hB.1).PosSemidef := by
  have : B - (posFloor hB.1 : ℂ) • supportProj hB.1
      = spectralFunction hB.1 (fun l => id l - posFloor hB.1 * (if 0 < l then 1 else 0)) := by
    unfold supportProj
    rw [spectralFunction_sub, spectralFunction_smul, spectralFunction_id]
  rw [this]
  refine spectralFunction_posSemidef hB.1 _ fun i => ?_
  simp only [id]
  split_ifs with h
  · have := posFloor_le hB.1 i h
    linarith
  · simp only [mul_zero, sub_zero]
    exact hB.eigenvalues_nonneg i

/-! ### Rayleigh-form facts -/

omit [DecidableEq n] in
/-- For a PSD matrix the complex quadratic form is the real Rayleigh value. -/
theorem dotProduct_eq_rayleigh {M : Matrix n n ℂ} (hM : M.PosSemidef) (x : n → ℂ) :
    star x ⬝ᵥ (M *ᵥ x) = ((rayleigh M x : ℝ) : ℂ) := by
  have h := hM.dotProduct_mulVec_nonneg x
  rw [Complex.le_def] at h
  apply Complex.ext
  · simp [rayleigh]
  · rw [Complex.ofReal_im]
    simpa using h.2.symm

omit [DecidableEq n] in
theorem rayleigh_eq_zero_iff {M : Matrix n n ℂ} (hM : M.PosSemidef) (x : n → ℂ) :
    rayleigh M x = 0 ↔ M *ᵥ x = 0 := by
  rw [← hM.dotProduct_mulVec_zero_iff]
  constructor
  · intro h
    have hnn := hM.dotProduct_mulVec_nonneg x
    rw [Complex.le_def] at hnn
    apply Complex.ext
    · simpa [rayleigh] using h
    · simpa using hnn.2.symm
  · intro h
    simp [rayleigh, h]

omit [DecidableEq n] in
/-- Hermitian quadratic forms are symmetric under the reflection
`star v ⬝ᵥ M w = star (M v) ⬝ᵥ w`. -/
theorem dotProduct_mulVec_hermitian {M : Matrix n n ℂ} (hM : M.IsHermitian) (v w : n → ℂ) :
    star v ⬝ᵥ (M *ᵥ w) = star (M *ᵥ v) ⬝ᵥ w := by
  rw [dotProduct_mulVec, star_mulVec, hM.eq]

/-- On the kernel-inclusion branch the target energy only sees the supported
component: `⟪x, Cx⟫ = ⟪Qx, C Qx⟫`. -/
theorem rayleigh_target_supported {B C : Matrix n n ℂ} (hB : B.PosSemidef) (hC : C.IsHermitian)
    (hker : ∀ x, B *ᵥ x = 0 → C *ᵥ x = 0) (x : n → ℂ) :
    rayleigh C x = rayleigh C (supportProj hB.1 *ᵥ x) := by
  set q := supportProj hB.1 *ᵥ x with hq
  have hk : C *ᵥ (x - q) = 0 := hker _ (mulVec_sub_supportProj hB x)
  have hx : x = q + (x - q) := by abel
  unfold rayleigh
  conv_lhs => rw [hx]
  rw [mulVec_add, hk, add_zero, star_add, add_dotProduct]
  have : star (x - q) ⬝ᵥ (C *ᵥ q) = 0 := by
    rw [dotProduct_mulVec_hermitian hC, hk, star_zero, zero_dotProduct]
  rw [this, add_zero]

/-- `‖Q x‖² = ⟪x, Q x⟫` for the Hermitian idempotent `Q`. -/
theorem normSq_supportProj {B : Matrix n n ℂ} (hB : B.IsHermitian) (x : n → ℂ) :
    (∑ j, ‖(supportProj hB *ᵥ x) j‖ ^ 2) = rayleigh (supportProj hB) x := by
  rw [← rayleigh_one]
  unfold rayleigh
  rw [one_mulVec]
  congr 1
  have hQH : (supportProj hB).IsHermitian := (supportProj_posSemidef hB).1
  calc star (supportProj hB *ᵥ x) ⬝ᵥ (supportProj hB *ᵥ x)
      = star x ⬝ᵥ (supportProj hB *ᵥ (supportProj hB *ᵥ x)) :=
        (dotProduct_mulVec_hermitian hQH x _).symm
    _ = star x ⬝ᵥ (supportProj hB *ᵥ x) := by rw [mulVec_mulVec, supportProj_idem]

/-- The target Gram is bounded by its trace-sum of eigenvalues: `C ⪯ c_max I`. -/
theorem target_upper_bound {C : Matrix n n ℂ} (hC : C.PosSemidef) (x : n → ℂ) :
    rayleigh C x ≤ (∑ i, hC.1.eigenvalues i) * ∑ j, ‖x j‖ ^ 2 := by
  have hpsd : (((∑ i, hC.1.eigenvalues i : ℝ) : ℂ) • (1 : Matrix n n ℂ) - C).PosSemidef := by
    have : ((∑ i, hC.1.eigenvalues i : ℝ) : ℂ) • (1 : Matrix n n ℂ) - C
        = spectralFunction hC.1 (fun l => (∑ i, hC.1.eigenvalues i) - id l) := by
      rw [spectralFunction_sub, spectralFunction_const, spectralFunction_id]
    rw [this]
    refine spectralFunction_posSemidef hC.1 _ fun i => ?_
    simp only [id]
    have := Finset.single_le_sum (fun j _ => hC.eigenvalues_nonneg j) (Finset.mem_univ i)
    linarith
  have := rayleigh_le_of_posSemidef hpsd x
  rw [rayleigh_smul, rayleigh_one] at this
  exact this

/-! ### (RI.3) finiteness ⇔ kernel inclusion -/

set_option linter.unusedDecidableInType false in
/-- **(RI.3)**: an admissible influence constant exists iff `Ker B ⊆ Ker C`. -/
theorem influence_finite_iff {B C : Matrix n n ℂ} (hB : B.PosSemidef) (hC : C.PosSemidef) :
    (∃ l : ℝ, 0 ≤ l ∧ ∀ x, rayleigh C x ≤ l * rayleigh B x) ↔
      ∀ x, B *ᵥ x = 0 → C *ᵥ x = 0 := by
  constructor
  · rintro ⟨l, _, hl⟩ x hx
    have h1 : rayleigh B x = 0 := (rayleigh_eq_zero_iff hB x).mpr hx
    have h2 := hl x
    rw [h1, mul_zero] at h2
    have h3 := rayleigh_nonneg hC x
    exact (rayleigh_eq_zero_iff hC x).mp (le_antisymm h2 h3)
  · intro hker
    set β := posFloor hB.1 with hβ
    set cmax := ∑ i, hC.1.eigenvalues i with hcmax
    have hβpos := posFloor_pos hB.1
    have hcmax0 : 0 ≤ cmax := Finset.sum_nonneg fun i _ => hC.eigenvalues_nonneg i
    refine ⟨cmax / β, div_nonneg hcmax0 hβpos.le, fun x => ?_⟩
    have hfloor := rayleigh_le_of_posSemidef (floor_posSemidef hB) x
    rw [rayleigh_smul] at hfloor
    calc rayleigh C x = rayleigh C (supportProj hB.1 *ᵥ x) :=
          rayleigh_target_supported hB hC.1 hker x
      _ ≤ cmax * ∑ j, ‖(supportProj hB.1 *ᵥ x) j‖ ^ 2 := target_upper_bound hC _
      _ = cmax * rayleigh (supportProj hB.1) x := by rw [normSq_supportProj]
      _ = (cmax / β) * (β * rayleigh (supportProj hB.1) x) := by
          rw [← mul_assoc, div_mul_cancel₀ cmax hβpos.ne']
      _ ≤ (cmax / β) * rayleigh B x :=
          mul_le_mul_of_nonneg_left hfloor (div_nonneg hcmax0 hβpos.le)

/-! ### (RI.4) the influence as a Rayleigh supremum -/

/-- The admissible set `{λ ≥ 0 : C ⪯ λ B}`. -/
def admissible (B C : Matrix n n ℂ) : Set ℝ :=
  {l : ℝ | 0 ≤ l ∧ ∀ x, rayleigh C x ≤ l * rayleigh B x}

/-- The Rayleigh quotients over the source-supported directions. -/
def quotients (B C : Matrix n n ℂ) : Set ℝ :=
  {r : ℝ | ∃ x, 0 < rayleigh B x ∧ r = rayleigh C x / rayleigh B x}

omit [DecidableEq n] in
theorem quotient_le_of_admissible {B C : Matrix n n ℂ} {l : ℝ} (hl : l ∈ admissible B C)
    {r : ℝ} (hr : r ∈ quotients B C) : r ≤ l := by
  obtain ⟨x, hx, rfl⟩ := hr
  rw [div_le_iff₀ hx]
  exact hl.2 x

set_option linter.unusedDecidableInType false in
/-- **(RI.4)**: on the kernel-inclusion branch `Λ(B,C) = sup` of the Rayleigh
quotients. -/
theorem influence_eq_sup {B C : Matrix n n ℂ} (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hker : ∀ x, B *ᵥ x = 0 → C *ᵥ x = 0) :
    influence B C = sSup (quotients B C) := by
  obtain ⟨l₀, hl₀⟩ := (influence_finite_iff hB hC).mpr hker
  have hl₀' : l₀ ∈ admissible B C := hl₀
  have hbdd : BddAbove (quotients B C) := ⟨l₀, fun r hr => quotient_le_of_admissible hl₀' hr⟩
  have hq0 : ∀ r ∈ quotients B C, 0 ≤ r := by
    rintro r ⟨x, hx, rfl⟩
    exact div_nonneg (rayleigh_nonneg hC x) hx.le
  -- the supremum is admissible
  have hsup_adm : sSup (quotients B C) ∈ admissible B C := by
    refine ⟨?_, fun x => ?_⟩
    · rcases Set.eq_empty_or_nonempty (quotients B C) with h | h
      · rw [h, Real.sSup_empty]
      · obtain ⟨r, hr⟩ := h
        exact le_trans (hq0 r hr) (le_csSup hbdd hr)
    · rcases lt_or_eq_of_le (rayleigh_nonneg hB x) with hpos | hzero
      · have hmem : rayleigh C x / rayleigh B x ∈ quotients B C := ⟨x, hpos, rfl⟩
        have := le_csSup hbdd hmem
        rw [div_le_iff₀ hpos] at this
        exact this
      · have hBx : B *ᵥ x = 0 := (rayleigh_eq_zero_iff hB x).mp hzero.symm
        have hCx : rayleigh C x = 0 := (rayleigh_eq_zero_iff hC x).mpr (hker x hBx)
        rw [hCx, ← hzero, mul_zero]
  unfold influence
  apply le_antisymm
  · exact csInf_le ⟨0, fun l hl => hl.1⟩ hsup_adm
  · refine le_csInf ⟨_, hsup_adm⟩ fun l hl => ?_
    rcases Set.eq_empty_or_nonempty (quotients B C) with h | h
    · rw [h, Real.sSup_empty]; exact hl.1
    · exact csSup_le h fun r hr => quotient_le_of_admissible hl hr

/-! ### (RI.5) reciprocal target-normalized source energy -/

/-- Target-normalized source energies `{⟪x,Bx⟫ : ⟪x,Cx⟫ = 1}`. -/
def normalizedEnergies (B C : Matrix n n ℂ) : Set ℝ :=
  {s : ℝ | ∃ x, rayleigh C x = 1 ∧ s = rayleigh B x}

omit [DecidableEq n] in
/-- Every target-normalized source energy is at least `Λ⁻¹`. -/
theorem reciprocal_bound {B C : Matrix n n ℂ} {l : ℝ} (hl : l ∈ admissible B C) (hlpos : 0 < l)
    {s : ℝ} (hs : s ∈ normalizedEnergies B C) : l⁻¹ ≤ s := by
  obtain ⟨x, hx, rfl⟩ := hs
  have := hl.2 x
  rw [hx] at this
  rw [inv_eq_one_div, div_le_iff₀ hlpos, mul_comm]
  exact this

omit [DecidableEq n] in
/-- A source direction with positive Rayleigh quotient `r` yields the
target-normalized energy `r⁻¹`. -/
theorem reciprocal_approx {B C : Matrix n n ℂ}
    {x : n → ℂ} (hx : 0 < rayleigh B x) (hCx : 0 < rayleigh C x) :
    (rayleigh C x / rayleigh B x)⁻¹ ∈ normalizedEnergies B C := by
  -- rescale `x` by `(⟪x,Cx⟫)^{-1/2}`
  set t : ℝ := Real.sqrt (rayleigh C x)⁻¹ with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr (inv_pos.mpr hCx)
  have ht2 : t ^ 2 = (rayleigh C x)⁻¹ := Real.sq_sqrt (inv_pos.mpr hCx).le
  have hscale : ∀ M : Matrix n n ℂ, rayleigh M ((t : ℂ) • x) = t ^ 2 * rayleigh M x := by
    intro M
    unfold rayleigh
    rw [mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, ← sq,
      Complex.re_ofReal_mul]
  refine ⟨(t : ℂ) • x, ?_, ?_⟩
  · rw [hscale, ht2, inv_mul_cancel₀ hCx.ne']
  · rw [hscale, ht2, inv_div]
    field_simp

/-- **(RI.5)**: `μ_C(B) = Λ(B,C)⁻¹` on the finite positive branch, as the
two-sided characterization: `Λ⁻¹` bounds every normalized energy from below,
and normalized energies `r⁻¹` exist for every quotient `r > 0`, so
`inf normalizedEnergies = Λ⁻¹`. -/
theorem reciprocal_eq {B C : Matrix n n ℂ} (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hker : ∀ x, B *ᵥ x = 0 → C *ᵥ x = 0) (hpos : 0 < influence B C) :
    sInf (normalizedEnergies B C) = (influence B C)⁻¹ := by
  have hsup := influence_eq_sup hB hC hker
  obtain ⟨l₀, hl₀⟩ := (influence_finite_iff hB hC).mpr hker
  have hbdd : BddAbove (quotients B C) := ⟨l₀, fun r hr => quotient_le_of_admissible hl₀ hr⟩
  have hadm : influence B C ∈ admissible B C := by
    rw [hsup]
    -- reuse the admissibility of the supremum from `influence_eq_sup`
    have := influence_eq_sup hB hC hker
    unfold influence at this
    have hmem : sInf (admissible B C) ∈ admissible B C := by
      -- the infimum of the closed admissible set is admissible
      refine ⟨?_, fun x => ?_⟩
      · exact le_csInf ⟨l₀, hl₀⟩ fun l hl => hl.1
      · by_contra hcon
        push Not at hcon
        -- some admissible `l` is below the violating ratio
        have hBx : 0 < rayleigh B x := by
          rcases lt_or_eq_of_le (rayleigh_nonneg hB x) with h | h
          · exact h
          · have hBx0 : B *ᵥ x = 0 := (rayleigh_eq_zero_iff hB x).mp h.symm
            have : rayleigh C x = 0 := (rayleigh_eq_zero_iff hC x).mpr (hker x hBx0)
            rw [this, ← h, mul_zero] at hcon
            exact absurd hcon (lt_irrefl _)
        have hlt : sInf (admissible B C) < rayleigh C x / rayleigh B x := by
          rw [lt_div_iff₀ hBx]; exact hcon
        obtain ⟨l, hl, hll⟩ := exists_lt_of_csInf_lt ⟨l₀, hl₀⟩ hlt
        have := hl.2 x
        rw [lt_div_iff₀ hBx] at hll
        linarith
    rw [← this]
    exact hmem
  apply le_antisymm
  · -- `Λ⁻¹` is approached: normalized energies `r⁻¹` with `r` close to `Λ = sup`
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hne : (quotients B C).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [hsup, h, Real.sSup_empty] at hpos
      exact lt_irrefl _ hpos
    -- pick a quotient `r` with `r > Λ - δ`
    have hinvcont : ∀ δ : ℝ, 0 < δ → δ < influence B C →
        (influence B C - δ)⁻¹
          = (influence B C)⁻¹ + δ / (influence B C * (influence B C - δ)) := by
      intro δ hδ hδl
      have h1 : influence B C - δ ≠ 0 := by linarith
      field_simp
      ring
    -- choose δ so that the error is below ε
    obtain ⟨δ, hδpos, hδlt, hδerr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < influence B C ∧
        δ / (influence B C * (influence B C - δ)) < ε := by
      refine ⟨min (influence B C / 2) (ε * influence B C ^ 2 / 4),
        lt_min (by positivity) (by positivity), ?_, ?_⟩
      · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · have hm1 := min_le_left (influence B C / 2) (ε * influence B C ^ 2 / 4)
        have hm2 := min_le_right (influence B C / 2) (ε * influence B C ^ 2 / 4)
        have hden : influence B C / 2
            ≤ influence B C - min (influence B C / 2) (ε * influence B C ^ 2 / 4) := by linarith
        have hdenpos : 0 < influence B C
            * (influence B C - min (influence B C / 2) (ε * influence B C ^ 2 / 4)) :=
          mul_pos hpos (by linarith)
        rw [div_lt_iff₀ hdenpos]
        have hsq : 0 < ε * influence B C ^ 2 := mul_pos hε (pow_pos hpos 2)
        calc min (influence B C / 2) (ε * influence B C ^ 2 / 4)
            ≤ ε * influence B C ^ 2 / 4 := hm2
          _ < ε * (influence B C * (influence B C / 2)) := by
              have : ε * (influence B C * (influence B C / 2)) = ε * influence B C ^ 2 / 2 := by
                ring
              rw [this]; linarith
          _ ≤ ε * (influence B C
              * (influence B C - min (influence B C / 2) (ε * influence B C ^ 2 / 4))) := by
              gcongr
    obtain ⟨r, hr, hrlt⟩ := exists_lt_of_lt_csSup hne (by rw [← hsup]; linarith :
      influence B C - δ < sSup (quotients B C))
    obtain ⟨x, hBx, rfl⟩ := hr
    have hrpos : 0 < rayleigh C x / rayleigh B x := by linarith
    have hCx : 0 < rayleigh C x := by
      by_contra h
      push Not at h
      have := div_nonpos_of_nonpos_of_nonneg h hBx.le
      linarith
    have hmem := reciprocal_approx hBx hCx
    have hδl : 0 < influence B C - δ := by linarith
    calc sInf (normalizedEnergies B C) ≤ (rayleigh C x / rayleigh B x)⁻¹ :=
          csInf_le ⟨0, fun s ⟨y, _, hy⟩ => hy ▸ rayleigh_nonneg hB y⟩ hmem
      _ ≤ (influence B C - δ)⁻¹ := by
          gcongr
      _ = (influence B C)⁻¹ + δ / (influence B C * (influence B C - δ)) :=
          hinvcont δ hδpos hδlt
      _ < (influence B C)⁻¹ + ε := by linarith
  · -- `Λ⁻¹` is a lower bound
    rcases Set.eq_empty_or_nonempty (normalizedEnergies B C) with h | h
    · -- no normalized direction: then `C` has zero form on the support, impossible with `Λ > 0`
      exfalso
      have hne : (quotients B C).Nonempty := by
        by_contra h'
        rw [Set.not_nonempty_iff_eq_empty] at h'
        rw [hsup, h', Real.sSup_empty] at hpos
        exact lt_irrefl _ hpos
      obtain ⟨r, hr, hrlt⟩ := exists_lt_of_lt_csSup hne (by rw [← hsup]; linarith :
        influence B C / 2 < sSup (quotients B C))
      obtain ⟨x, hBx, rfl⟩ := hr
      have hCx : 0 < rayleigh C x := by
        by_contra h'
        push Not at h'
        have := div_nonpos_of_nonpos_of_nonneg h' hBx.le
        linarith
      have := reciprocal_approx hBx hCx
      rw [h] at this
      exact this
    · exact le_csInf h fun s hs => reciprocal_bound hadm hpos hs

/-! ### (RI.6) extremizers and the infinite branch -/

omit [DecidableEq n] in
/-- **Euler–Lagrange** for an extremizer: if `Λ` is admissible and the
quotient is attained at `z`, then `(Λ B - C) z = 0`, i.e. `B z = Λ⁻¹ C z`
when `Λ > 0`. -/
theorem extremizer_euler_lagrange {B C : Matrix n n ℂ} (hB : B.PosSemidef) (hC : C.PosSemidef)
    {l : ℝ} (hl : l ∈ admissible B C) (z : n → ℂ) (hz : rayleigh C z = l * rayleigh B z) :
    (l : ℂ) • (B *ᵥ z) - C *ᵥ z = 0 := by
  have hpsd : ((l : ℂ) • B - C).PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · change ((l : ℂ) • B - C)ᴴ = (l : ℂ) • B - C
      rw [conjTranspose_sub, conjTranspose_smul, hB.1.eq, hC.1.eq, Complex.star_def,
        Complex.conj_ofReal]
    · have h1 := hl.2 x
      have hval : star x ⬝ᵥ (((l : ℂ) • B - C) *ᵥ x)
          = ((l * rayleigh B x - rayleigh C x : ℝ) : ℂ) := by
        rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, dotProduct_eq_rayleigh hB,
          dotProduct_eq_rayleigh hC]
        push_cast
        ring
      rw [hval]
      exact Complex.zero_le_real.mpr (by linarith)
  have hzero : star z ⬝ᵥ (((l : ℂ) • B - C) *ᵥ z) = 0 := by
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, dotProduct_eq_rayleigh hB,
      dotProduct_eq_rayleigh hC, hz]
    push_cast
    ring
  have := hpsd.dotProduct_mulVec_zero_iff z |>.mp hzero
  rwa [sub_mulVec, smul_mulVec] at this

/-- **Infinite branch** (RI.6, second clause): if no admissible constant exists,
there is a target-visible source null `z` with `B z = 0` and `⟪z,Cz⟫ > 0`. -/
theorem null_of_not_finite {B C : Matrix n n ℂ} (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hinf : ¬ ∃ l : ℝ, 0 ≤ l ∧ ∀ x, rayleigh C x ≤ l * rayleigh B x) :
    ∃ z, B *ᵥ z = 0 ∧ 0 < rayleigh C z := by
  rw [influence_finite_iff hB hC] at hinf
  push Not at hinf
  obtain ⟨z, hBz, hCz⟩ := hinf
  refine ⟨z, hBz, ?_⟩
  rcases lt_or_eq_of_le (rayleigh_nonneg hC z) with h | h
  · exact h
  · exact absurd ((rayleigh_eq_zero_iff hC z).mp h.symm) hCz

end SourceCoercivityInfluence
end NCG
