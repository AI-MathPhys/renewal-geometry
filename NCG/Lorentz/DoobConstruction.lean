/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.PerronExistence
import NCG.Lorentz.PerronPressure

/-!
# The Doob-normalized pressure law

`constr:pressure-law` (`manuscripts/renewal_emergence/renewal_emergence.tex`) for positive
transfer kernels: from the Perron data of
`NCG/Lorentz/PerronExistence.lean`,

* `doobP` — the Doob transform `P_{xy} = B_{xy} h_y / (r h_x)` of
  the kernel at its Perron root;
* `doobP_stochastic`, `doobP_pos` — `P` is a strictly positive
  stochastic edge law;
* `doobPi_stationary` (inside `pressure_law`) — the normalized
  product `π = ν h / ⟨ν, h⟩` of the left and right Perron vectors is
  a strictly positive stationary probability law for `P`;
* `perron_root_eq_pRad` — the Perron root **is** the Gelfand–Fekete
  growth rate of the eigenvector-free pressure development:
  `r = pRad B`, so `P(β) = log r` identifies the pressure with the
  Perron root;
* `pressure_law` — the assembled existence package.

The stationary-mean-depth derivative identity `μ_ℓ = −P'(β)` is not
formalized (it needs differentiability of the pressure in `β`), and
the construction is scoped to entrywise **positive** kernels (the
primitive-nonnegative case reduces by taking powers, which is not
formalized).  Downstream, this data discharges the `DoobData`
hypotheses of the entropy–affinity–depth chain.
-/

namespace NCG

open Matrix Filter

variable {n : ℕ} [NeZero n]

/-- The Doob transform of a kernel at a root `r` and gauge `h`. -/
noncomputable def doobP (B : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (h : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun x y => B x y * h y / (r * h x)

theorem doobP_pos {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, 0 < B i j) {r : ℝ} (hr : 0 < r)
    {h : Fin n → ℝ} (hh : ∀ i, 0 < h i) (x y : Fin n) :
    0 < doobP B r h x y := by
  rw [doobP, Matrix.of_apply]
  exact div_pos (mul_pos (hB x y) (hh y)) (mul_pos hr (hh x))

/-- **The Doob law is stochastic** at a right Perron pair. -/
theorem doobP_stochastic {B : Matrix (Fin n) (Fin n) ℝ} {r : ℝ}
    (hr : 0 < r) {h : Fin n → ℝ} (hh : ∀ i, 0 < h i)
    (heig : B.mulVec h = r • h) (x : Fin n) :
    ∑ y, doobP B r h x y = 1 := by
  have h1 : ∑ y, doobP B r h x y
      = (∑ y, B x y * h y) / (r * h x) := by
    rw [Finset.sum_div]
    rfl
  have h2 : ∑ y, B x y * h y = r * h x := by
    have h3 := congrFun heig x
    rw [Matrix.mulVec, dotProduct] at h3
    rw [h3, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  exact div_self (mul_pos hr (hh x)).ne'

/-- **The Perron root is the Gelfand–Fekete growth rate**: the
eigenvector sandwich identifies `r` with `pRad B`, so the pressure
of the eigenvector-free development is `log r`. -/
theorem perron_root_eq_pRad {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, 0 < B i j) {r : ℝ} (hr : 0 < r)
    {h : Fin n → ℝ} (hh : ∀ i, 0 < h i)
    (heig : B.mulVec h = r • h) :
    r = pRad B := by
  classical
  have hBnn : EntryNonneg B := fun i j => (hB i j).le
  have hw : HasDiagWitness B :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, 1, le_refl 1, by
      rw [pow_one]
      exact hB _ _⟩
  -- B^k h = r^k h
  have hpow : ∀ k : ℕ, (B ^ k).mulVec h = (r ^ k) • h := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
    | succ k ih =>
      rw [pow_succ', pow_succ']
      rw [← Matrix.mulVec_mulVec, ih]
      rw [Matrix.mulVec_smul, heig, smul_smul, mul_comm]
  -- entrywise sandwich for the entry sum
  set hmin := Finset.univ.inf' Finset.univ_nonempty h with hhmin
  set hmax := Finset.univ.sup' Finset.univ_nonempty h with hhmax
  have hminpos : 0 < hmin := by
    rw [hhmin, Finset.lt_inf'_iff]
    intro i _
    exact hh i
  have hmaxpos : 0 < hmax :=
    lt_of_lt_of_le (hh ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)
      (Finset.le_sup' _ (Finset.mem_univ _))
  have hminle : ∀ i, hmin ≤ h i := by
    intro i
    rw [hhmin]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  have hlemax : ∀ i, h i ≤ hmax := by
    intro i
    rw [hhmax]
    exact Finset.le_sup' _ (Finset.mem_univ i)
  -- hmin * entrySum(B^k) ≤ Σ_x r^k h x ≤ hmax * entrySum(B^k)
  have hsand : ∀ k : ℕ,
      hmin * entrySum (B ^ k) ≤ (∑ x, r ^ k * h x)
      ∧ (∑ x, r ^ k * h x) ≤ hmax * entrySum (B ^ k) := by
    intro k
    have hBk : ∀ x y, 0 ≤ (B ^ k) x y := entryNonneg_pow hBnn k
    have h4 : ∀ x, r ^ k * h x = ∑ y, (B ^ k) x y * h y := by
      intro x
      have h5 := congrFun (hpow k) x
      rw [Matrix.mulVec, dotProduct] at h5
      rw [Pi.smul_apply, smul_eq_mul] at h5
      exact h5.symm
    constructor
    · rw [entrySum, Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [h4 x, Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      rw [mul_comm hmin ((B ^ k) x y)]
      exact mul_le_mul_of_nonneg_left (hminle y) (hBk x y)
    · rw [entrySum, Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [h4 x, Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      rw [mul_comm hmax ((B ^ k) x y)]
      exact mul_le_mul_of_nonneg_left (hlemax y) (hBk x y)
  set H := ∑ x, h x with hH
  have hHpos : 0 < H := by
    rw [hH]
    exact Finset.sum_pos (fun i _ => hh i) Finset.univ_nonempty
  have hsum : ∀ k : ℕ, ∑ x, r ^ k * h x = r ^ k * H := by
    intro k
    rw [hH, Finset.mul_sum]
  -- squeeze the growth sequence
  have hgrow : Tendsto (fun k : ℕ => growthSeq B k / k) atTop
      (nhds (Real.log r)) := by
    have hES : ∀ k : ℕ, 0 < entrySum (B ^ k) :=
      fun k => entrySum_pow_pos hBnn hw k
    have hlow : ∀ k : ℕ,
        Real.log (r ^ k * H) - Real.log hmax
          ≤ growthSeq B k := by
      intro k
      have h6 := (hsand k).2
      rw [hsum k] at h6
      have h7 : Real.log (r ^ k * H)
          ≤ Real.log (hmax * entrySum (B ^ k)) :=
        Real.log_le_log (by positivity) h6
      rw [Real.log_mul hmaxpos.ne' (hES k).ne'] at h7
      rw [growthSeq]
      linarith
    have hup : ∀ k : ℕ,
        growthSeq B k ≤ Real.log (r ^ k * H)
          - Real.log hmin := by
      intro k
      have h6 := (hsand k).1
      rw [hsum k] at h6
      have h7 : Real.log (hmin * entrySum (B ^ k))
          ≤ Real.log (r ^ k * H) :=
        Real.log_le_log (mul_pos hminpos (hES k)) h6
      rw [Real.log_mul hminpos.ne' (hES k).ne'] at h7
      rw [growthSeq]
      linarith
    have hloglin : ∀ k : ℕ, Real.log (r ^ k * H)
        = k * Real.log r + Real.log H := by
      intro k
      rw [Real.log_mul (by positivity) hHpos.ne',
        Real.log_pow]
    -- (k log r + log H − log hmax)/k → log r, similarly above
    have hsq : Tendsto (fun k : ℕ =>
        (k * Real.log r + Real.log H - Real.log hmax) / k)
        atTop (nhds (Real.log r)) := by
      have h8 : Tendsto (fun k : ℕ => Real.log r
          + (Real.log H - Real.log hmax) / k) atTop
          (nhds (Real.log r + 0)) :=
        tendsto_const_nhds.add
          (tendsto_const_div_atTop_nhds_zero_nat _)
      rw [add_zero] at h8
      refine Tendsto.congr' ?_ h8
      filter_upwards [eventually_ne_atTop 0] with k hk
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      field_simp
      ring
    have hsq2 : Tendsto (fun k : ℕ =>
        (k * Real.log r + Real.log H - Real.log hmin) / k)
        atTop (nhds (Real.log r)) := by
      have h8 : Tendsto (fun k : ℕ => Real.log r
          + (Real.log H - Real.log hmin) / k) atTop
          (nhds (Real.log r + 0)) :=
        tendsto_const_nhds.add
          (tendsto_const_div_atTop_nhds_zero_nat _)
      rw [add_zero] at h8
      refine Tendsto.congr' ?_ h8
      filter_upwards [eventually_ne_atTop 0] with k hk
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      field_simp
      ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hsq hsq2
      ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have h10 := hlow k
      rw [hloglin k] at h10
      rw [div_le_div_iff₀ hkR hkR]
      exact mul_le_mul_of_nonneg_right h10 hkR.le
    · filter_upwards [eventually_gt_atTop 0] with k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have h10 := hup k
      rw [hloglin k] at h10
      rw [div_le_div_iff₀ hkR hkR]
      exact mul_le_mul_of_nonneg_right h10 hkR.le
  have h11 := tendsto_growthSeq hBnn hw
  have h12 : Real.log r = Real.log (pRad B) :=
    tendsto_nhds_unique hgrow h11
  have h13 : r = Real.exp (Real.log r) :=
    (Real.exp_log hr).symm
  rw [h13, h12, Real.exp_log (pRad_pos B)]

/-- **Construction `constr:pressure-law`** for positive transfer
kernels: the full Doob package — Perron root and gauges, strictly
positive stochastic edge law, and strictly positive stationary
probability weight. -/
theorem pressure_law {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, 0 < B i j) :
    ∃ (r : ℝ) (h ν : Fin n → ℝ) (π : Fin n → ℝ),
      0 < r ∧ (∀ i, 0 < h i) ∧ (∀ i, 0 < ν i)
        ∧ B.mulVec h = r • h ∧ B.vecMul ν = r • ν
        ∧ (∀ x y, 0 < doobP B r h x y)
        ∧ (∀ x, ∑ y, doobP B r h x y = 1)
        ∧ (∀ i, 0 < π i) ∧ (∑ i, π i = 1)
        ∧ (∀ y, ∑ x, π x * doobP B r h x y = π y)
        ∧ r = pRad B := by
  classical
  obtain ⟨r, h, hr, hh, heig⟩ := perron_exists hB
  obtain ⟨s, ν, hs, hν, heig'⟩ := perron_exists_left hB
  have hrs : r = s := perron_left_right_eq hh hν heig heig'
  subst hrs
  set Z := ∑ i, ν i * h i with hZ
  have hZpos : 0 < Z := by
    rw [hZ]
    exact Finset.sum_pos (fun i _ => mul_pos (hν i) (hh i))
      Finset.univ_nonempty
  refine ⟨r, h, ν, fun i => ν i * h i / Z, hr, hh, hν, heig,
    heig', fun x y => doobP_pos hB hr hh x y,
    fun x => doobP_stochastic hr hh heig x,
    fun i => div_pos (mul_pos (hν i) (hh i)) hZpos, ?_, ?_,
    perron_root_eq_pRad hB hr hh heig⟩
  · rw [← Finset.sum_div, ← hZ]
    exact div_self hZpos.ne'
  · intro y
    have h1 : ∀ x, ν x * h x / Z * doobP B r h x y
        = ν x * B x y * h y / (r * Z) := by
      intro x
      rw [doobP, Matrix.of_apply]
      field_simp [(hh x).ne']
    rw [Finset.sum_congr rfl fun x _ => h1 x]
    have h2 : ∑ x, ν x * B x y * h y / (r * Z)
        = (∑ x, ν x * B x y) * h y / (r * Z) := by
      rw [Finset.sum_mul, Finset.sum_div]
    rw [h2]
    have h3 : ∑ x, ν x * B x y = r * ν y := by
      have h4 := congrFun heig' y
      rw [Matrix.vecMul, dotProduct] at h4
      rw [h4, Pi.smul_apply, smul_eq_mul]
    rw [h3]
    field_simp [(hh y).ne']

end NCG
