/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Numerics.IntervalKit

/-!
# Modular scalar certificates (SM_emergence, CKM boundary data)

The exact scalar layer of the canonical modular CKM boundary:

* `phiMap`, `phiMap_fixed_exists_unique` — the modular weight
  `φ_* ∈ [0,1]` solving `φ = s_*((2+φ)/3)³` at `s_* = 229/256`
  exists and is unique (the map is a `229/256`-contraction);
* `xstar_bounds` — the certified enclosure
  `x_* = φ_*/2 = 0.274087996992…` (width `5·10⁻¹³`);
* `lFR_value` — `ℓ_FR(x_*) = 0.2356337644…` (the mirror light-plane
  rotation, the exact sine of the `V_FR` factor of the CKM assembly);
* `rFR_value` — `r_FR(x_*) = 0.0043438419…` (the rank-one residue);
* `qe_value`, `epspair_value` — the leakage ratio
  `q_e(x_*) = 0.0395934944998…` and the pair suppression
  `ε_pair(x_*) = 0.1444554119…`.

All enclosures are exact rational arithmetic (`norm_num`) plus the
square-root bracket for `√3`.
-/

namespace NCG

open Real

/-- The modular weight map `φ ↦ s_*((2+φ)/3)³`, `s_* = 229/256`. -/
noncomputable def phiMap (t : ℝ) : ℝ := (229 / 256) * ((2 + t) / 3) ^ 3

/-- `phiMap` is a `229/256`-contraction on `[0,1]`. -/
theorem phiMap_contract {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 1)
    (hst : s ≤ t) :
    phiMap t - phiMap s ≤ (229 / 256) * (t - s) := by
  unfold phiMap
  nlinarith [mul_nonneg (sub_nonneg.mpr hst)
    (by nlinarith : (0 : ℝ) ≤ 27 - ((2 + t) ^ 2 + (2 + t) * (2 + s)
      + (2 + s) ^ 2))]

/-- The modular fixed point exists and is unique in `[0,1]`. -/
theorem phiMap_fixed_exists_unique :
    ∃! φ, φ ∈ Set.Icc (0 : ℝ) 1 ∧ phiMap φ = φ := by
  obtain ⟨φ, hmem, hfix⟩ : ∃ φ ∈ Set.Icc (0 : ℝ) 1,
      (fun t => phiMap t - t) φ = 0 := by
    have hcont : ContinuousOn (fun t => phiMap t - t)
        (Set.Icc (0 : ℝ) 1) := by
      apply Continuous.continuousOn
      unfold phiMap
      fun_prop
    have h0 : (fun t => phiMap t - t) 1 ≤ 0 := by
      simp only [phiMap]
      norm_num
    have h1 : (0 : ℝ) ≤ (fun t => phiMap t - t) 0 := by
      simp only [phiMap]
      norm_num
    obtain ⟨φ, hφmem, hφ⟩ :=
      intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont
        (Set.mem_Icc.mpr ⟨h0, h1⟩)
    exact ⟨φ, hφmem, hφ⟩
  have hφfix : phiMap φ = φ := by
    have h := hfix
    simp only [sub_eq_zero] at h
    exact h
  refine ⟨φ, ⟨hmem, hφfix⟩, ?_⟩
  rintro ψ ⟨hψmem, hψfix⟩
  rcases le_total ψ φ with h | h
  · have hc := phiMap_contract hψmem.1 hmem.2 h
    rw [hφfix, hψfix] at hc
    nlinarith
  · have hc := phiMap_contract hmem.1 hψmem.2 h
    rw [hφfix, hψfix] at hc
    nlinarith

/-- Certified enclosure of the modular fixed point:
`φ_* = 0.548175993984…`, hence `x_* = φ_*/2 = 0.274087996992…`. -/
theorem xstar_bounds {φ : ℝ} (hmem : φ ∈ Set.Icc (0 : ℝ) 1)
    (hfix : phiMap φ = φ) :
    0.548175993983 ≤ φ ∧ φ ≤ 0.548175993985 := by
  constructor
  · by_contra h
    rw [not_le] at h
    have hc := phiMap_contract hmem.1
      (by norm_num : (0.548175993983 : ℝ) ≤ 1) h.le
    rw [hfix] at hc
    have hup : (0.548175993983 : ℝ) < phiMap 0.548175993983 := by
      unfold phiMap
      norm_num
    nlinarith
  · by_contra h
    rw [not_le] at h
    have hc := phiMap_contract
      (by norm_num : (0 : ℝ) ≤ 0.548175993985) hmem.2 h.le
    rw [hfix] at hc
    have hdown : phiMap 0.548175993985 < 0.548175993985 := by
      unfold phiMap
      norm_num
    nlinarith

/-- `√3` to thirteen digits. -/
theorem sqrt_three_bounds :
    (1.7320508075688 : ℝ) ≤ Real.sqrt 3 ∧
      Real.sqrt 3 ≤ 1.7320508075689 :=
  sqrt_mem_Icc (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `cert:canonical-ckm-main` (scalar layer): the mirror light-plane
rotation at the modular point, `ℓ_FR(x_*) = 0.2356337644…` — the
exact sine of the `V_FR` factor of the CKM assembly. -/
theorem lFR_value {φ : ℝ} (hmem : φ ∈ Set.Icc (0 : ℝ) 1)
    (hfix : phiMap φ = φ) :
    |4 * Real.sqrt 3 * (φ / 2) ^ 2 * (1 - φ / 2) /
        (4 * (φ / 2) ^ 4 + 3 * (1 - φ / 2) ^ 2)
      - 0.2356337644| ≤ 5e-11 := by
  obtain ⟨hφl, hφr⟩ := xstar_bounds hmem hfix
  obtain ⟨hs3l, hs3r⟩ := sqrt_three_bounds
  set x : ℝ := φ / 2 with hx
  have hxl : (0.2740879969915 : ℝ) ≤ x := by rw [hx]; linarith
  have hxr : x ≤ (0.2740879969925 : ℝ) := by rw [hx]; linarith
  have hbox : (0 : ℝ) ≤ (x - 0.2740879969915) * (0.2740879969925 - x) :=
    mul_nonneg (by linarith) (by linarith)
  have hAl : (0.0545335803425 : ℝ) ≤ x ^ 2 * (1 - x) := by nlinarith
  have hAr : x ^ 2 * (1 - x) ≤ (0.0545335803430 : ℝ) := by nlinarith
  have hNl : (0.3778197274875 : ℝ) ≤
      4 * Real.sqrt 3 * x ^ 2 * (1 - x) := by
    nlinarith [mul_le_mul hs3l hAl (by norm_num) (Real.sqrt_nonneg 3)]
  have hNr : 4 * Real.sqrt 3 * x ^ 2 * (1 - x) ≤
      (0.3778197274909 : ℝ) := by
    nlinarith [mul_le_mul hs3r hAr (by nlinarith) (by norm_num)]
  have hDl : (1.6034193081204 : ℝ) ≤
      4 * x ^ 4 + 3 * (1 - x) ^ 2 := by nlinarith
  have hDr : 4 * x ^ 4 + 3 * (1 - x) ^ 2 ≤
      (1.6034193081252 : ℝ) := by nlinarith
  have hDpos : (0 : ℝ) < 4 * x ^ 4 + 3 * (1 - x) ^ 2 := by linarith
  have hlo : (0.23563376435 : ℝ) ≤
      4 * Real.sqrt 3 * x ^ 2 * (1 - x) /
        (4 * x ^ 4 + 3 * (1 - x) ^ 2) := by
    rw [le_div_iff₀ hDpos]
    nlinarith
  have hhi : 4 * Real.sqrt 3 * x ^ 2 * (1 - x) /
      (4 * x ^ 4 + 3 * (1 - x) ^ 2) ≤ (0.23563376445 : ℝ) := by
    rw [div_le_iff₀ hDpos]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- `cert:canonical-ckm-main` (scalar layer): the common rank-one
residue at the modular point, `r_FR(x_*) = 0.0043438419…`. -/
theorem rFR_value {φ : ℝ} (hmem : φ ∈ Set.Icc (0 : ℝ) 1)
    (hfix : phiMap φ = φ) :
    |(φ / 2) ^ 4 * (4 * (φ / 2) ^ 4 + 3 * (φ / 2) ^ 2 - 6 * (φ / 2) + 3) /
        (2 * (1 + φ / 2) ^ 2 * (1 - φ / 2 + (φ / 2) ^ 2) ^ 2)
      - 0.0043438419| ≤ 5e-11 := by
  obtain ⟨hφl, hφr⟩ := xstar_bounds hmem hfix
  set x : ℝ := φ / 2 with hx
  have hxl : (0.2740879969915 : ℝ) ≤ x := by rw [hx]; linarith
  have hxr : x ≤ (0.2740879969925 : ℝ) := by rw [hx]; linarith
  have hbox : (0 : ℝ) ≤ (x - 0.2740879969915) * (0.2740879969925 - x) :=
    mul_nonneg (by linarith) (by linarith)
  have hx2l : (0.0751242300948 : ℝ) ≤ x ^ 2 := by nlinarith
  have hx2r : x ^ 2 ≤ (0.0751242300954 : ℝ) := by nlinarith
  have hx4l : (0.0056436499473 : ℝ) ≤ x ^ 4 := by nlinarith
  have hx4r : x ^ 4 ≤ (0.0056436499475 : ℝ) := by nlinarith
  have hBl : (1.6034193081186 : ℝ) ≤
      4 * x ^ 4 + 3 * x ^ 2 - 6 * x + 3 := by linarith
  have hBr : 4 * x ^ 4 + 3 * x ^ 2 - 6 * x + 3 ≤
      (1.6034193081272 : ℝ) := by linarith
  have hNl : (0.0090491372937 : ℝ) ≤
      x ^ 4 * (4 * x ^ 4 + 3 * x ^ 2 - 6 * x + 3) := by
    nlinarith [mul_le_mul hx4l hBl (by norm_num) (by positivity)]
  have hNr : x ^ 4 * (4 * x ^ 4 + 3 * x ^ 2 - 6 * x + 3) ≤
      (0.0090491372942 : ℝ) := by
    nlinarith [mul_le_mul hx4r hBr (by linarith) (by norm_num)]
  have hpl : (1.6233002240778 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith
  have hpr : (1 + x) ^ 2 ≤ (1.6233002240804 : ℝ) := by nlinarith
  have hql : (0.8010362331023 : ℝ) ≤ 1 - x + x ^ 2 := by linarith
  have hqr : 1 - x + x ^ 2 ≤ (0.8010362331039 : ℝ) := by linarith
  have hq2l : (0.6416590467427 : ℝ) ≤ (1 - x + x ^ 2) ^ 2 := by
    nlinarith [mul_le_mul hql hql (by norm_num) (by linarith)]
  have hq2r : (1 - x + x ^ 2) ^ 2 ≤ (0.6416590467453 : ℝ) := by
    nlinarith [mul_le_mul hqr hqr (by linarith) (by norm_num)]
  have hDl : (2.0832105487 : ℝ) ≤
      2 * (1 + x) ^ 2 * (1 - x + x ^ 2) ^ 2 := by
    nlinarith [mul_le_mul hpl hq2l (by norm_num) (by positivity)]
  have hDr : 2 * (1 + x) ^ 2 * (1 - x + x ^ 2) ^ 2 ≤
      (2.0832105488 : ℝ) := by
    nlinarith [mul_le_mul hpr hq2r (by linarith) (by norm_num)]
  have hDpos : (0 : ℝ) <
      2 * (1 + x) ^ 2 * (1 - x + x ^ 2) ^ 2 := by linarith
  have hlo : (0.00434384185 : ℝ) ≤
      x ^ 4 * (4 * x ^ 4 + 3 * x ^ 2 - 6 * x + 3) /
        (2 * (1 + x) ^ 2 * (1 - x + x ^ 2) ^ 2) := by
    rw [le_div_iff₀ hDpos]
    nlinarith
  have hhi : x ^ 4 * (4 * x ^ 4 + 3 * x ^ 2 - 6 * x + 3) /
      (2 * (1 + x) ^ 2 * (1 - x + x ^ 2) ^ 2) ≤
      (0.00434384195 : ℝ) := by
    rw [div_le_iff₀ hDpos]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- The odd-pair leakage ratio `q_e(x_*) = 0.0395934944998…`. -/
theorem qe_value {φ : ℝ} (hmem : φ ∈ Set.Icc (0 : ℝ) 1)
    (hfix : phiMap φ = φ) :
    |(φ / 2) ^ 2 / (1 + 3 * (φ / 2) + (φ / 2) ^ 2)
      - 0.0395934944998| ≤ 5e-13 := by
  obtain ⟨hφl, hφr⟩ := xstar_bounds hmem hfix
  set x : ℝ := φ / 2 with hx
  have hxl : (0.2740879969915 : ℝ) ≤ x := by rw [hx]; linarith
  have hxr : x ≤ (0.2740879969925 : ℝ) := by rw [hx]; linarith
  have hbox : (0 : ℝ) ≤ (x - 0.2740879969915) * (0.2740879969925 - x) :=
    mul_nonneg (by linarith) (by linarith)
  have hDpos : (0 : ℝ) < 1 + 3 * x + x ^ 2 := by nlinarith
  have hlo : (0.0395934944993 : ℝ) ≤
      x ^ 2 / (1 + 3 * x + x ^ 2) := by
    rw [le_div_iff₀ hDpos]
    nlinarith
  have hhi : x ^ 2 / (1 + 3 * x + x ^ 2) ≤
      (0.0395934945003 : ℝ) := by
    rw [div_le_iff₀ hDpos]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- The pair-orbit suppression `ε_pair(x_*) = 0.1444554119…`. -/
theorem epspair_value {φ : ℝ} (hmem : φ ∈ Set.Icc (0 : ℝ) 1)
    (hfix : phiMap φ = φ) :
    |(φ / 2) / (1 + 3 * (φ / 2) + (φ / 2) ^ 2)
      - 0.1444554119| ≤ 5e-11 := by
  obtain ⟨hφl, hφr⟩ := xstar_bounds hmem hfix
  set x : ℝ := φ / 2 with hx
  have hxl : (0.2740879969915 : ℝ) ≤ x := by rw [hx]; linarith
  have hxr : x ≤ (0.2740879969925 : ℝ) := by rw [hx]; linarith
  have hbox : (0 : ℝ) ≤ (x - 0.2740879969915) * (0.2740879969925 - x) :=
    mul_nonneg (by linarith) (by linarith)
  have hDpos : (0 : ℝ) < 1 + 3 * x + x ^ 2 := by nlinarith
  have hlo : (0.14445541185 : ℝ) ≤
      x / (1 + 3 * x + x ^ 2) := by
    rw [le_div_iff₀ hDpos]
    nlinarith
  have hhi : x / (1 + 3 * x + x ^ 2) ≤ (0.14445541195 : ℝ) := by
    rw [div_le_iff₀ hDpos]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

end NCG
