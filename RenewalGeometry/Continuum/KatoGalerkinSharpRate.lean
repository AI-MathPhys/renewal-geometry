/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoGalerkinCFL
import RenewalGeometry.Continuum.KatoPhysicalIdentification

/-!
# Sharp high-norm rates of the spectral Galerkin approximation on `𝕋^d`

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` of the
Einstein–Standard-Model action-closure manuscript, `eq:generated-Galerkin-rate`:
`max_{a ≤ 2} ‖∂_t^a(U_N - U)‖_{C_tH^{s+4-a}} ≤ C N^{-p}` for `q = s + p + 8`.  Setting of
`KatoGalerkinODE` / `KatoLocalExistence`: `∂_tU + Σ_i A^i(U)∂_iU = F(U)` on `𝕋^d` (`ℤ^d`-periodic
fields), smooth real symmetric `A^i`, smooth `F`, Galerkin space `GS d n N`.

* `coef_const_of_ne` and **`tail_coef_genG_le`** — the generator `G(U)` is bounded in `H^{q-1}`
  on the `H^q` ball, hence its high Fourier modes are small:
  `Σ_{k ∉ box K} ⟨G(U), cas_k⟩² ≤ C (2π(K+1))^{-2(q-1)}`.
* **`galerkin_L2_cauchy_sharp`** — the improved `C_tL²` Cauchy estimate
  `‖U_N(t) - U_M(t)‖²_{L²} ≤ C (2π(N+1))^{-(2q-1)}` (`N ≤ M`): the cross term of the energy
  identity is now estimated by the `L²`-tail of `U_M` (`H^q`) **times** the `L²`-tail of `G(U_N)`
  (`H^{q-1}`), instead of the bounded `L²` norm of `G(U_N)` (`KatoGalerkin.galerkin_L2_cauchy`
  only gives `(2π(N+1))^{-q}`).
* **`kato_sharp_rates`** — Kato's local existence theorem with the sharp coefficient rates: for the
  limit `U` and every finite mode set `S`,
  `Σ_{k ∈ S} (c_k(U_N(t)) - c_k(U(t)))² ≤ C (2π(N+1))^{-(2q-1)}` (`L²`), and for every
  `r ≤ q`, **the `H^r` rate** `Σ_{k ∈ S} wq_r(k) (c_k(U_N(t)) - c_k(U(t)))² ≤ C_r (N+1)^{-(2(q-r)-1)}`
  (frequency splitting: inverse inequality on the box, `H^q` tail outside it), i.e.
  `‖U_N - U‖_{C_tH^r} ≤ C N^{-(q-r)+1/2}`.  For `q = s + p + 8`, `r = s + 4` this is
  `N^{-(p+7/2)} ≤ N^{-p}`: the `a = 0` clause of `eq:generated-Galerkin-rate` (with room).
* **`kato_sharp_rates_dt`** — the same together with the **time-derivative rate** (`a = 1`): the
  coefficients of the limit satisfy `d/dt c_k(U) = c_k(G(U))`, those of `U_N` satisfy
  `d/dt c_k(U_N) = c_k(G(U_N))` on `box N`, and for `2m_s ≤ ρ + 1 ≤ q - 1`
  `Σ_{k ∈ S} wq_ρ(k) (d/dt c_k(U_N) - d/dt c_k(U))² ≤ C'_ρ (N+1)^{-(2(q-ρ-2)+1)}`, i.e.
  `‖∂_t(U_N - U)‖_{C_tH^ρ} ≤ C N^{-(q-ρ-1)+1/2}`; for `ρ = s + 3` this is `N^{-(p+7/2)}`
  (low modes: `H^{ρ+1} → H^ρ` Lipschitz bound of `G` and the `H^{ρ+1}` rate; high modes: the
  `H^{q-1}` bound of `G(U)`).  The `a = 2` clause is not formalised.

Disclosed rendering: `Σ = 𝕋^d`, smooth data with an `H^q` bound, coefficients smooth on all of
`ℝ^n`; Sobolev norms on the Fourier (Hartley) side with the weights `wq r k` of
`KatoHartleyBasis` (the classical `H^r` norm of trigonometric fields).
-/

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.KatoRates

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### Coefficients of constants and the high modes of the generator -/

theorem casS_zero (x : ST d) : casS (0 : Fin d → ℤ) x = 1 := by
  simp [casS, cas, phL_apply]

/-- A constant has no Fourier (Hartley) coefficient at a nonzero mode. -/
theorem coef_const_of_ne (c t : ℝ) {k : Fin d → ℤ} (hk : k ≠ 0) :
    coef (fun _ : ST d => c) t k = 0 := by
  have e : (fun _ : ST d => c) = tfs {0} (fun _ => c) := by
    funext x; simp [tfs, casS_zero]
  rw [e, coef_tfs]
  simp [hk]

theorem zero_mem_box (K : ℕ) : (0 : Fin d → ℤ) ∈ KatoGalerkin.box K := by
  rw [mem_box]; intro i; simp

theorem ne_zero_of_not_mem_box {K : ℕ} {k : Fin d → ℤ} (hk : k ∉ KatoGalerkin.box K) :
    k ≠ 0 := by
  rintro rfl; exact hk (zero_mem_box K)

theorem genG_zero_fun {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (b : Fin n) (x : ST d) :
    genG A F (fun _ _ => (0 : ℝ)) b x = F b 0 := by
  simp only [genG, compF]
  have h0 : (fun _ : Fin n => (0 : ℝ)) = 0 := rfl
  have hpd : ∀ i : Fin d, pd (fun _ : ST d => (0 : ℝ)) i.succ x = 0 := fun i => by
    simp [SobolevOpen.pd]
  simp [hpd, h0]

/-- **High Fourier modes of the generator**: for `m > d/2`, `2m ≤ r + 1` and every radius `ρ`
there is `C_G` such that for every Galerkin state with `‖a‖_{H^{r+1}} ≤ ρ`, every finite mode set
`S` and every cutoff `K`, `Σ_{k ∈ S, k ∉ box K} ⟨G(U)_b, cas_k⟩² ≤ C_G (2π(K+1))^{-2r}`
(`G` is bounded `H^{r+1} → H^r`, `KatoCFL.Q_genG_sub_le`). -/
theorem tail_coef_genG_le {m r : ℕ} (hm : (d : ℝ) / 2 < m) (hr : 2 * m ≤ r + 1)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ∃ CG : ℝ, 0 ≤ CG ∧ ∀ (N : ℕ) (a : GS d n N), ‖a‖ ≤ ρ → ∀ (S : Finset (Fin d → ℤ))
      (b : Fin n) (K : ℕ),
      ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box K),
          coef (genG A F (fld (r + 1) a) b) 0 k ^ 2 ≤
        CG / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ r := by
  obtain ⟨C, hC0, hC⟩ := KatoCFL.Q_genG_sub_le (d := d) (n := n) hm hr hA hF hρ
  refine ⟨C * ρ ^ 2, by positivity, fun N a ha S b K => ?_⟩
  set u := fld (r + 1) a with hu
  set g : ST d → ℝ := fun x => genG A F u b x - genG A F (fun _ _ => (0 : ℝ)) b x with hg
  have hgs : ContDiff ℝ ∞ g :=
    (contDiff_genG hA hF (fun b => contDiff_fld _ a b) b).sub
      (contDiff_genG hA hF (fun _ => contDiff_const) b)
  have hgp : IsSPeriodic g := fun k x => by
    simp only [hg, genG_zero_fun]
    rw [hu, isSPeriodic_genG (fun b => isSPeriodic_fld _ a b) b k x]
  have hcoef : ∀ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box K),
      coef (genG A F u b) 0 k = coef g 0 k := by
    intro k hk
    have hk0 := ne_zero_of_not_mem_box (Finset.mem_filter.1 hk).2
    have e : g = fun x => genG A F u b x - F b 0 := by
      funext x; simp only [hg, genG_zero_fun]
    rw [e, coef_sub (contDiff_genG hA hF (fun b => contDiff_fld _ a b) b).continuous
      continuous_const, coef_const_of_ne _ _ hk0, sub_zero]
  rw [Finset.sum_congr rfl fun k hk => by rw [hcoef k hk]]
  refine (sum_tail_sq_le r K S (coef g 0)).trans ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine (bessel_Hq r S hgs hgp 0).trans ?_
  have hE : energyQ (r + 1) u 0 ≤ ρ ^ 2 := by
    rw [hu, energyQ_fld]; exact pow_le_pow_left₀ (norm_nonneg _) ha 2
  have h := hC u (fun _ _ => 0) (fun b => contDiff_fld _ a b) (fun _ => contDiff_const)
    (fun b => isSPeriodic_fld _ a b) (fun _ _ _ => rfl) 0 hE
    (by rw [energyQ_zero]; positivity) b
  refine h.trans ?_
  have e : (fun b x => u b x - (fun _ _ => (0 : ℝ)) b x) = u := by
    funext b x; simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hE hC0

/-! ### The sharp `L²` Cauchy estimate -/

/-- **The sharp `C_tL²` Cauchy estimate of the spectral Galerkin solutions**: for `m > d/2`,
`2m ≤ q`, `m + 1 ≤ q` (`q = r + 1`) and `N ≤ M`,
`sup_{t ∈ [0,T]} ‖U_N(t) - U_M(t)‖²_{L²} ≤ C (2π(N+1))^{-q} (2π(N+1))^{-(q-1)}`, with `C`
depending only on the data radius `R₀`, the uniform bound `R` and `T`.  Same energy argument as
`KatoGalerkin.galerkin_L2_cauchy`, but the cross term `Σ_{k ∈ KatoGalerkin.box M \ KatoGalerkin.box N} c_k(U_M) ĝ_k(U_N)` is
bounded by the `H^q` tail of `U_M` times the `H^{q-1}` tail of `G(U_N)` (`tail_coef_genG_le`). -/
theorem galerkin_L2_cauchy_sharp {m r : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ r + 1)
    (hmq : m + 1 ≤ r + 1) {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ R T : ℝ} (hR₀ : 0 ≤ R₀) (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U₀ : Fin n → ST d → ℝ), (∀ b, ContDiff ℝ ∞ (U₀ b)) →
      (∀ b, IsSPeriodic (U₀ b)) → energyQ (r + 1) U₀ 0 ≤ R₀ ^ 2 →
      ∀ (γ : (N : ℕ) → ℝ → GS d n N), (∀ N, γ N 0 = P0 (r + 1) N U₀) →
      (∀ N, ∀ t ∈ Set.Icc 0 T,
        HasDerivWithinAt (γ N) (GN A F (r + 1) (γ N t)) (Set.Icc 0 T) t) →
      (∀ N, ∀ t ∈ Set.Icc 0 T, ‖γ N t‖ ≤ R) →
      ∀ N M, N ≤ M → ∀ t ∈ Set.Icc 0 T,
        ∑ b, ∑ k ∈ KatoGalerkin.box M, (cf (r + 1) (γ N t) b k - cf (r + 1) (γ M t) b k) ^ 2 ≤
          C / ((2 * π * ((N : ℝ) + 1)) ^ (r + 1) * (2 * π * ((N : ℝ) + 1)) ^ r) := by
  set q := r + 1 with hqdef
  obtain ⟨CG, hCG0, hCG⟩ := tail_coef_genG_le (d := d) (n := n) hm hq hA hF hR
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  set B := Real.sqrt CS * R with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨K₁, hK₁0, hK₁⟩ := sym_L2_diff hA hsym hF hB0
  set Φ : (Fin n ⊕ (Fin d × Fin n × Fin n)) → (Fin n → ℝ) → ℝ :=
    fun k => Sum.elim (fun a => F a) (fun p => A p.1 p.2.1 p.2.2) k with hΦ
  have hΦs : ∀ k, ContDiff ℝ ∞ (Φ k) := by
    intro k; cases k with
    | inl a => exact hF a
    | inr p => exact hA p.1 p.2.1 p.2.2
  obtain ⟨Mc, hMc0, hMc⟩ := exists_coeff_bounds hΦs B
  set Gm := Mc + d * n * Mc * B with hGm
  have hGm0 : 0 ≤ Gm := by positivity
  refine ⟨(R₀ ^ 2 + 2 * n * R * Real.sqrt CG * T) * Real.exp (2 * K₁ * T), by positivity,
    fun U₀ hU hUp hE γ hγ0 hγ hγR N M hNM t ht => ?_⟩
  -- uniform pointwise bounds
  have hbd : ∀ L, ∀ s ∈ Set.Icc 0 T, (∀ b x, |fld q (γ L s) b x| ≤ B) ∧
      (∀ b (i : Fin d) x, |pd (fld q (γ L s) b) i.succ x| ≤ B) := by
    intro L s hs
    have hn := hγR L s hs
    refine ⟨fun b x => ?_, fun b i x => ?_⟩
    · exact (abs_fld_le hmq hCS hsup (γ L s) b x).1.trans
        (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))
    · exact ((abs_fld_le hmq hCS hsup (γ L s) b x).2 i).trans
        (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))
  have hGb : ∀ L, ∀ s ∈ Set.Icc 0 T, ∀ b x, |genG A F (fld q (γ L s)) b x| ≤ Gm := by
    intro L s hs b x
    exact abs_genG_le hB0 hMc0 (hbd L s hs).1 (hbd L s hs).2
      (fun a v hv => (hMc (Sum.inl a) v v hv hv).1)
      (fun i a b v hv => (hMc (Sum.inr (i, a, b)) v v hv hv).1) b x
  -- the difference functional and its derivative
  set s := (2 * π * ((N : ℝ) + 1)) ^ q with hs
  have hs1 : 1 ≤ s := one_le_pow₀ (one_le_two_pi_succ N)
  have hs0 : 0 < s := by linarith
  set s' := (2 * π * ((N : ℝ) + 1)) ^ r with hs'
  have hs'1 : 1 ≤ s' := one_le_pow₀ (one_le_two_pi_succ N)
  have hs'0 : 0 < s' := by linarith
  have hs's : s' ≤ s := by
    rw [hs, hs', hqdef, pow_succ]
    exact le_mul_of_one_le_right (by positivity) (one_le_two_pi_succ N)
  set ĝ : (L : ℕ) → ℝ → Fin n → (Fin d → ℤ) → ℝ := fun L s b k =>
    coef (genG A F (fld q (γ L s)) b) 0 k with hĝ
  set D : ℝ → ℝ := fun t => ∑ b, ∑ k ∈ KatoGalerkin.box M, (cf q (γ N t) b k - cf q (γ M t) b k) ^ 2
    with hD
  set D' : ℝ → ℝ := fun t => ∑ b, ∑ k ∈ KatoGalerkin.box M, 2 * (cf q (γ N t) b k - cf q (γ M t) b k) *
    ((if k ∈ KatoGalerkin.box N then ĝ N t b k else 0) - ĝ M t b k) with hD'
  have hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt D (D' t) (Set.Icc 0 T) t := by
    intro t ht
    refine HasDerivWithinAt.fun_sum fun b _ => HasDerivWithinAt.fun_sum fun k hk => ?_
    refine hasDerivWithinAt_sq' (HasDerivWithinAt.sub ?_ ?_)
    · by_cases hkN : k ∈ KatoGalerkin.box N
      · rw [if_pos hkN]; exact hasDerivWithinAt_cf (hγ N t ht) b hkN
      · rw [if_neg hkN]
        have : (fun t => cf q (γ N t) b k) = fun _ => 0 :=
          funext fun t => cf_eq_zero _ b hkN
        rw [this]; exact hasDerivWithinAt_const _ _ _
    · exact hasDerivWithinAt_cf (hγ M t ht) b hk
  -- the derivative bound
  have hD'b : ∀ t ∈ Set.Icc 0 T,
      D' t ≤ 2 * K₁ * D t + 2 * n * R * Real.sqrt CG / (s * s') := by
    intro t ht
    have hsplit : ∀ b, ∑ k ∈ KatoGalerkin.box M, 2 * (cf q (γ N t) b k - cf q (γ M t) b k) *
        ((if k ∈ KatoGalerkin.box N then ĝ N t b k else 0) - ĝ M t b k) =
        2 * sint (fun x => (fld q (γ N t) b x - fld q (γ M t) b x) *
          (genG A F (fld q (γ N t)) b x - genG A F (fld q (γ M t)) b x)) 0 +
        2 * ∑ k ∈ (KatoGalerkin.box M).filter (fun k => k ∉ KatoGalerkin.box N), cf q (γ M t) b k * ĝ N t b k := by
      intro b
      have h1 : sint (fun x => (fld q (γ N t) b x - fld q (γ M t) b x) *
          (genG A F (fld q (γ N t)) b x - genG A F (fld q (γ M t)) b x)) 0 =
          ∑ k ∈ KatoGalerkin.box M, (cf q (γ N t) b k - cf q (γ M t) b k) * (ĝ N t b k - ĝ M t b k) := by
        have e : (fun x => (fld q (γ N t) b x - fld q (γ M t) b x) *
            (genG A F (fld q (γ N t)) b x - genG A F (fld q (γ M t)) b x)) =
            fun x => tfs (KatoGalerkin.box M) (fun k => cf q (γ N t) b k - cf q (γ M t) b k) x *
              (fun x => genG A F (fld q (γ N t)) b x - genG A F (fld q (γ M t)) b x) x := by
          funext x; rw [fld_eq_tfs hNM (γ N t) b, fld, tfs_sub]
        rw [e, sint_tfs_mul (g := fun x => genG A F (fld q (γ N t)) b x -
            genG A F (fld q (γ M t)) b x) _ _
          ((contDiff_genG hA hF (fun b => contDiff_fld q _ b) b).continuous.sub
          (contDiff_genG hA hF (fun b => contDiff_fld q _ b) b).continuous)]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [coef_sub (contDiff_genG hA hF (fun b => contDiff_fld q _ b) b).continuous
          (contDiff_genG hA hF (fun b => contDiff_fld q _ b) b).continuous]
      rw [h1, Finset.mul_sum, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hkN : k ∈ KatoGalerkin.box N
      · rw [if_pos hkN, if_neg (not_not.2 hkN)]; ring
      · rw [if_neg hkN, if_pos hkN, cf_eq_zero _ b hkN]; ring
    have hP1 : ∑ b, sint (fun x => (fld q (γ N t) b x - fld q (γ M t) b x) *
        (genG A F (fld q (γ N t)) b x - genG A F (fld q (γ M t)) b x)) 0 ≤ K₁ * D t := by
      have := hK₁ (fld q (γ N t)) (fld q (γ M t)) (fun b => contDiff_fld q _ b)
        (fun b => contDiff_fld q _ b) (fun b => isSPeriodic_fld q _ b)
        (fun b => isSPeriodic_fld q _ b) (hbd N t ht).1 (hbd M t ht).1 (hbd N t ht).2
        (hbd M t ht).2 0
      refine this.trans (le_of_eq ?_)
      congr 1
      exact Finset.sum_congr rfl fun b _ => sint_fld_sub_sq hNM _ _ b 0
    have hP2 : ∀ b, |∑ k ∈ (KatoGalerkin.box M).filter (fun k => k ∉ KatoGalerkin.box N), cf q (γ M t) b k * ĝ N t b k| ≤
        R * Real.sqrt CG / (s * s') := by
      intro b
      set T' := (KatoGalerkin.box M).filter (fun k => k ∉ KatoGalerkin.box N)
      have hc1 : ∑ k ∈ T', cf q (γ M t) b k ^ 2 ≤ R ^ 2 / s ^ 2 := by
        refine (sum_tail_sq_le q N (KatoGalerkin.box M) (cf q (γ M t) b)).trans ?_
        have h2 : ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ q = s ^ 2 := by rw [hs, ← pow_mul, ← pow_mul, Nat.mul_comm]
        rw [h2]
        refine div_le_div_of_nonneg_right ((sum_wq_cf_sq_le (γ M t) b).trans ?_) (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) (hγR M t ht) 2
      have hc2 : ∑ k ∈ T', ĝ N t b k ^ 2 ≤ CG / s' ^ 2 := by
        have h2 : ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ r = s' ^ 2 := by
          rw [hs', ← pow_mul, ← pow_mul, Nat.mul_comm]
        have := hCG N (γ N t) (hγR N t ht) (KatoGalerkin.box M) b N
        rw [h2] at this
        exact this
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq T' (fun k => cf q (γ M t) b k)
        (fun k => ĝ N t b k)
      refine abs_le_of_sq_le_sq (hcs.trans ?_) (by positivity)
      calc (∑ k ∈ T', cf q (γ M t) b k ^ 2) * ∑ k ∈ T', ĝ N t b k ^ 2
          ≤ R ^ 2 / s ^ 2 * (CG / s' ^ 2) := mul_le_mul hc1 hc2
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = (R * Real.sqrt CG / (s * s')) ^ 2 := by
            rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hCG0]; field_simp
    have hsum : D' t = 2 * ∑ b, sint (fun x => (fld q (γ N t) b x - fld q (γ M t) b x) *
        (genG A F (fld q (γ N t)) b x - genG A F (fld q (γ M t)) b x)) 0 +
        2 * ∑ b, ∑ k ∈ (KatoGalerkin.box M).filter (fun k => k ∉ KatoGalerkin.box N), cf q (γ M t) b k * ĝ N t b k := by
      simp only [hD']
      rw [Finset.sum_congr rfl fun b _ => hsplit b, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.mul_sum]
    have hP2' : ∑ b, ∑ k ∈ (KatoGalerkin.box M).filter (fun k => k ∉ KatoGalerkin.box N),
        cf q (γ M t) b k * ĝ N t b k ≤ n * (R * Real.sqrt CG / (s * s')) := by
      calc ∑ b, ∑ k ∈ (KatoGalerkin.box M).filter (fun k => k ∉ KatoGalerkin.box N),
            cf q (γ M t) b k * ĝ N t b k
          ≤ ∑ _b : Fin n, R * Real.sqrt CG / (s * s') :=
            Finset.sum_le_sum fun b _ => (le_abs_self _).trans (hP2 b)
        _ = n * (R * Real.sqrt CG / (s * s')) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum]
    have : 2 * (n * (R * Real.sqrt CG / (s * s'))) = 2 * n * R * Real.sqrt CG / (s * s') := by
      ring
    linarith
  -- Grönwall
  have hcont : ContinuousOn D (Set.Icc 0 T) := fun t ht => (hderiv t ht).continuousWithinAt
  have hgr := SpectralGalerkin.le_gronwall_scalar (f := D) (f' := D') (K := 2 * K₁)
    (ε := 2 * n * R * Real.sqrt CG / (s * s')) hcont
    (fun t ht => (hderiv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) (fun t ht => hD'b t (Ico_subset_Icc_self ht)) t ht
  have hD0 : D 0 ≤ R₀ ^ 2 / (s * s') := by
    have e0 : D 0 = ∑ b, ∑ k ∈ (KatoGalerkin.box M).filter (fun k => k ∉ KatoGalerkin.box N), coef (U₀ b) 0 k ^ 2 := by
      simp only [hD, hγ0, cf_P0]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k hk => ?_
      by_cases hkN : k ∈ KatoGalerkin.box N
      · rw [if_pos hkN, if_pos (box_mono hNM hkN), if_neg (not_not.2 hkN)]; ring
      · rw [if_neg hkN, if_pos hk, if_pos hkN]; ring
    rw [e0]
    have h1 : ∀ b, ∑ k ∈ (KatoGalerkin.box M).filter (fun k => k ∉ KatoGalerkin.box N), coef (U₀ b) 0 k ^ 2 ≤
        Q q (U₀ b) 0 / s ^ 2 := by
      intro b
      refine (sum_tail_sq_le q N (KatoGalerkin.box M) (coef (U₀ b) 0)).trans ?_
      have h2 : ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ q = s ^ 2 := by rw [hs, ← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [h2]
      exact div_le_div_of_nonneg_right (bessel_Hq q (KatoGalerkin.box M) (hU b) (hUp b) 0) (by positivity)
    calc ∑ b, ∑ k ∈ (KatoGalerkin.box M).filter (fun k => k ∉ KatoGalerkin.box N), coef (U₀ b) 0 k ^ 2
        ≤ ∑ b, Q q (U₀ b) 0 / s ^ 2 := Finset.sum_le_sum fun b _ => h1 b
      _ = energyQ q U₀ 0 / s ^ 2 := by rw [energyQ, Finset.sum_div]
      _ ≤ R₀ ^ 2 / s ^ 2 := div_le_div_of_nonneg_right hE (by positivity)
      _ ≤ R₀ ^ 2 / (s * s') := by
          refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
          rw [sq]; exact mul_le_mul_of_nonneg_left hs's hs0.le
  have hK2 : 0 ≤ 2 * K₁ := by positivity
  have hε : 0 ≤ 2 * n * R * Real.sqrt CG / (s * s') := by positivity
  refine hgr.trans ((gronwallBound_le_mul_exp hK2 hε ht.1).trans ?_)
  have hexp : Real.exp (2 * K₁ * t) ≤ Real.exp (2 * K₁ * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK2)
  have hD0' : 0 ≤ D 0 := Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  calc (D 0 + 2 * n * R * Real.sqrt CG / (s * s') * t) * Real.exp (2 * K₁ * t)
      ≤ (R₀ ^ 2 / (s * s') + 2 * n * R * Real.sqrt CG / (s * s') * T) *
          Real.exp (2 * K₁ * T) := by
        refine mul_le_mul (add_le_add hD0 (mul_le_mul_of_nonneg_left ht.2 hε)) hexp
          (Real.exp_pos _).le (by positivity)
    _ = (R₀ ^ 2 + 2 * n * R * Real.sqrt CG * T) * Real.exp (2 * K₁ * T) / (s * s') := by
        field_simp

/-! ### Coefficient convergence and the sharp rates of the Kato limit -/

/-- The coefficients of a Galerkin field are its Galerkin coordinates (at every time slice). -/
theorem coef_fld (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) (t : ℝ) (k : Fin d → ℤ) :
    coef (fld q a b) t k = cf q a b k := by
  rw [fld, coef_tfs]
  split_ifs with hk
  · rfl
  · exact (cf_eq_zero a b hk).symm

/-- A slice-wise uniform bound controls the difference of coefficients on that slice. -/
theorem abs_coef_sub_le_slice {f g : ST d → ℝ} (hf : Continuous f) (hg : Continuous g)
    {t η : ℝ} (h : ∀ y, |f (Fin.cons t y) - g (Fin.cons t y)| ≤ η) (k : Fin d → ℤ) :
    |coef f t k - coef g t k| ≤ 2 * η := by
  rw [← coef_sub hf hg]
  unfold coef
  set φ : ST d → ℝ := fun x => casS k x * (f x - g x) with hφ
  have e : sint φ t = sint (fun x => φ (Fin.cons t (Fin.tail x))) t := by
    unfold sint; simp [Fin.tail_cons]
  rw [e]
  refine abs_sint_le (fun x => ?_) t
  simp only [hφ, abs_mul]
  have h0 : 0 ≤ η := (abs_nonneg _).trans (h 0)
  exact mul_le_mul (abs_casS_le k _) (h _) (abs_nonneg _) (by norm_num)

/-- The low-mode weight bound (iterated inverse inequality on the box):
`wq_ρ(k) ≤ (1 + 4π²d)^ρ (N + 1)^{2ρ}` for `|k_i| ≤ N`. -/
theorem wq_le_box {N : ℕ} {k : Fin d → ℤ} (hk : k ∈ KatoGalerkin.box N) :
    ∀ ρ : ℕ, wq ρ k ≤ (1 + 4 * π ^ 2 * d) ^ ρ * (((N : ℝ) + 1) ^ 2) ^ ρ
  | 0 => by simp [wq, wordsLE, muL_nil]
  | ρ + 1 => by
    have h1 := KatoCFL.wq_succ_le_box hk ρ
    have h2 := KatoCFL.one_add_le_succ_sq d N
    have h3 := wq_le_box hk ρ
    have h4 : 0 ≤ 1 + (d : ℝ) * (2 * π * N) ^ 2 := by positivity
    calc wq (ρ + 1) k ≤ (1 + d * (2 * π * N) ^ 2) * wq ρ k := h1
      _ ≤ ((1 + 4 * π ^ 2 * d) * ((N : ℝ) + 1) ^ 2) *
            ((1 + 4 * π ^ 2 * d) ^ ρ * (((N : ℝ) + 1) ^ 2) ^ ρ) :=
          mul_le_mul h2 h3 (wq_nonneg _ _) (by positivity)
      _ = (1 + 4 * π ^ 2 * d) ^ (ρ + 1) * (((N : ℝ) + 1) ^ 2) ^ (ρ + 1) := by ring

theorem succ_pow_le_two_pi (N j : ℕ) : ((N : ℝ) + 1) ^ j ≤ (2 * π * ((N : ℝ) + 1)) ^ j := by
  refine pow_le_pow_left₀ (by positivity) ?_ j
  have : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- **Kato's local existence theorem with the sharp Galerkin rates** (`thm:generated-dynamics`,
`eq:generated-Galerkin-rate`, clause `a = 0`).  Let `m > d/2`, `q = r + 1 ≥ 2m`, `q ≥ m + 2`,
`A^i` smooth real symmetric, `F` smooth.  For every data radius `R₀` there are `T > 0`, `R ≥ 0`,
`C ≥ 0` (depending only on `R₀` and `A, F, q, m, d, n`) such that every smooth periodic datum with
`‖U₀‖_{H^q} ≤ R₀` has a classical solution `U` on `[0, T] × 𝕋^d` (`U(0) = U₀`,
`∂_tU = F(U) - Σ_i A^i(U)∂_iU`, `U ∈ L^∞_tH^q` with bound `R`), which is the limit of spectral
Galerkin solutions `U_N` (`GalerkinHyp`) with, for every `t ∈ [0, T]` and every finite mode set
`S`:
* the `L²` rate `Σ_b Σ_{k ∈ S} (c_k(U_N(t)) - c_k(U(t)))² ≤ C (2π(N+1))^{-(2q-1)}`;
* the `H^ρ` rate for every `ρ ≤ q - 1`:
  `Σ_b Σ_{k ∈ S} wq_ρ(k) (c_k(U_N(t)) - c_k(U(t)))² ≤ ((1 + 4π²d)^ρ C + R²) (N+1)^{-(2(q-1-ρ)+1)}`,
  i.e. `‖U_N - U‖_{C_tH^ρ} ≤ C' N^{-(q-ρ)+1/2}`. -/
theorem kato_sharp_rates {m r : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ r + 1)
    (hq2 : m + 2 ≤ r + 1) {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∃ R ≥ 0, ∃ C ≥ 0, ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) →
      (∀ b, IsSPeriodic (U₀ b)) → energyQ (r + 1) U₀ 0 ≤ R₀ ^ 2 →
      ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ),
        (∀ b, Continuous (U b)) ∧ (∀ b, IsSPeriodic (U b)) ∧
        (∀ b y, U b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
        (∀ b (i : Fin d) x, HasDerivAt (fun s : ℝ => U b (x + s • ev i.succ)) (P b i x) 0) ∧
        (∀ b, ∀ t ∈ Set.Icc 0 T, ∀ y, HasDerivWithinAt (fun s => U b (Fin.cons s y))
          (F b (fun c => U c (Fin.cons t y)) -
            ∑ i, ∑ b', A i b b' (fun c => U c (Fin.cons t y)) * P b' i (Fin.cons t y))
          (Set.Icc 0 T) t) ∧
        (∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin d → ℤ),
          ∑ b, ∑ k ∈ S, wq (r + 1) k * coef (U b) t k ^ 2 ≤ R ^ 2) ∧
        ∃ γ : (N : ℕ) → ℝ → GS d n N, GalerkinHyp A F (r + 1) U₀ T R γ ∧
          (∀ N, ∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin d → ℤ),
            ∑ b, ∑ k ∈ S, (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2 ≤
              C / (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1)) ∧
          (∀ ρ ≤ r, ∀ N, ∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin d → ℤ),
            ∑ b, ∑ k ∈ S, wq ρ k * (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2 ≤
              ((1 + 4 * π ^ 2 * d) ^ ρ * C + R ^ 2) / ((N : ℝ) + 1) ^ (2 * (r - ρ) + 1)) := by
  obtain ⟨T, hT, R, hR, C₀, hC₀, hK⟩ := kato_local_existence (d := d) (n := n) hm hq hq2 hA
    hsym hF hR₀
  obtain ⟨C, hC0, hC⟩ := galerkin_L2_cauchy_sharp (d := d) (n := n) hm hq (by omega) hA hsym hF
    hR₀ hR hT.le
  refine ⟨T, hT, R, hR, C, hC0, fun U₀ hU hUp hE => ?_⟩
  obtain ⟨U, P, hUc, -, hUp', -, hU0, hUP, hUt, -, hUq, γ, hG, hconv, -⟩ := hK U₀ hU hUp hE
  have hcauchy := hC U₀ hU hUp hE γ hG.init hG.deriv hG.bound
  have hpow : ∀ N : ℕ, (2 * π * ((N : ℝ) + 1)) ^ (r + 1) * (2 * π * ((N : ℝ) + 1)) ^ r =
      (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1) := fun N => by
    rw [← pow_add]; congr 1; omega
  -- coefficient convergence along the Galerkin family
  have hlim : ∀ t ∈ Set.Icc 0 T, ∀ b k, Tendsto (fun M => cf (r + 1) (γ M t) b k) atTop
      (𝓝 (coef (U b) t k)) := by
    intro t ht b k
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (hconv b (ε / 4) (by positivity))
    refine ⟨M₀, fun M hM => ?_⟩
    rw [Real.dist_eq, ← coef_fld (r + 1) (γ M t) b t k]
    refine (abs_coef_sub_le_slice (contDiff_fld _ _ b).continuous (hUc b)
      (fun y => (hM₀ M hM t ht y).1) k).trans_lt (by linarith)
  -- the coefficient `L²` rate
  have hL2 : ∀ N, ∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin d → ℤ),
      ∑ b, ∑ k ∈ S, (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2 ≤
        C / (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1) := by
    intro N t ht S
    have ht' : Tendsto (fun M => ∑ b, ∑ k ∈ S, (cf (r + 1) (γ N t) b k -
        cf (r + 1) (γ M t) b k) ^ 2) atTop
        (𝓝 (∑ b, ∑ k ∈ S, (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2)) :=
      tendsto_finset_sum _ fun b _ => tendsto_finset_sum _ fun k _ =>
        (tendsto_const_nhds.sub (hlim t ht b k)).pow 2
    refine le_of_tendsto ht' ?_
    have hev : ∀ᶠ M in atTop, N ≤ M ∧ ∀ k ∈ S, k ∈ KatoGalerkin.box M := by
      refine (eventually_ge_atTop N).and ((Filter.eventually_all_finset S).2 fun k _ => ?_)
      obtain ⟨M₀, hM₀⟩ := exists_mem_box k
      exact eventually_atTop.2 ⟨M₀, fun M hM => box_mono hM hM₀⟩
    filter_upwards [hev] with M hM
    rw [← hpow N]
    refine le_trans ?_ (hcauchy N M hM.1 t ht)
    refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => hM.2 k hk) fun k _ _ => sq_nonneg _
  refine ⟨U, P, hUc, hUp', hU0, hUP, hUt, hUq, γ, hG, hL2, fun ρ hρ N t ht S => ?_⟩
  -- frequency splitting
  set D : (Fin d → ℤ) → Fin n → ℝ := fun k b => cf (r + 1) (γ N t) b k - coef (U b) t k
    with hD
  set L : ℝ := (1 + 4 * π ^ 2 * d) ^ ρ * (((N : ℝ) + 1) ^ 2) ^ ρ with hL
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hsplit : ∀ b, ∑ k ∈ S, wq ρ k * D k b ^ 2 =
      ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), wq ρ k * D k b ^ 2 +
      ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N), wq ρ k * coef (U b) t k ^ 2 := by
    intro b
    rw [← Finset.sum_filter_add_sum_filter_not S (fun k => k ∈ KatoGalerkin.box N)]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [hD, cf_eq_zero _ b (Finset.mem_filter.1 hk).2, zero_sub, neg_sq]
  -- low modes
  have hlow : ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), wq ρ k * D k b ^ 2 ≤
      L * (C / (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1)) := by
    calc ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), wq ρ k * D k b ^ 2
        ≤ ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), L * D k b ^ 2 :=
          Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_right (wq_le_box (Finset.mem_filter.1 hk).2 ρ) (sq_nonneg _)
      _ = L * ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), D k b ^ 2 := by
          rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
      _ ≤ L * (C / (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1)) :=
          mul_le_mul_of_nonneg_left (hL2 N t ht _) (by positivity)
  -- high modes
  have hhigh : ∑ b, ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N),
      wq ρ k * coef (U b) t k ^ 2 ≤ R ^ 2 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r + 1 - ρ) := by
    have hs : 0 < ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r + 1 - ρ) := by positivity
    rw [le_div_iff₀ hs, Finset.sum_mul]
    calc ∑ b, (∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N),
          wq ρ k * coef (U b) t k ^ 2) * ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r + 1 - ρ)
        ≤ ∑ b, ∑ k ∈ S, wq (r + 1) k * coef (U b) t k ^ 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [Finset.sum_mul]
          refine le_trans (Finset.sum_le_sum fun k hk => ?_)
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S)
              fun k _ _ => mul_nonneg (wq_nonneg _ k) (sq_nonneg _))
          have h := wq_tail (Finset.mem_filter.1 hk).2 ρ (r + 1 - ρ)
          rw [show ρ + (r + 1 - ρ) = r + 1 by omega] at h
          nlinarith [sq_nonneg (coef (U b) t k)]
      _ ≤ R ^ 2 := hUq t ht S
  -- combine
  have e1 : ∑ b, ∑ k ∈ S, wq ρ k * (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2 =
      ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), wq ρ k * D k b ^ 2 +
      ∑ b, ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N), wq ρ k * coef (U b) t k ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => hsplit b
  rw [e1]
  set e := 2 * (r - ρ) + 1 with he
  have hNe : 0 < ((N : ℝ) + 1) ^ e := by positivity
  -- the low part
  have hlow' : L * (C / (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1)) ≤
      (1 + 4 * π ^ 2 * d) ^ ρ * C / ((N : ℝ) + 1) ^ e := by
    have h1 : ((N : ℝ) + 1) ^ (2 * r + 1) ≤ (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1) :=
      succ_pow_le_two_pi N _
    have h2 : (((N : ℝ) + 1) ^ 2) ^ ρ * ((N : ℝ) + 1) ^ e = ((N : ℝ) + 1) ^ (2 * r + 1) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [hL, mul_div_assoc', div_le_div_iff₀ (by positivity) hNe]
    calc (1 + 4 * π ^ 2 * d) ^ ρ * (((N : ℝ) + 1) ^ 2) ^ ρ * C * ((N : ℝ) + 1) ^ e
        = (1 + 4 * π ^ 2 * d) ^ ρ * C * ((N : ℝ) + 1) ^ (2 * r + 1) := by rw [← h2]; ring
      _ ≤ (1 + 4 * π ^ 2 * d) ^ ρ * C * (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  -- the high part
  have hhigh' : R ^ 2 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r + 1 - ρ) ≤ R ^ 2 / ((N : ℝ) + 1) ^ e := by
    refine div_le_div_of_nonneg_left (sq_nonneg _) hNe ?_
    rw [← pow_mul]
    calc ((N : ℝ) + 1) ^ e ≤ ((N : ℝ) + 1) ^ (2 * (r + 1 - ρ)) :=
          pow_le_pow_right₀ hN1 (by omega)
      _ ≤ (2 * π * ((N : ℝ) + 1)) ^ (2 * (r + 1 - ρ)) := succ_pow_le_two_pi N _
  calc _ ≤ (1 + 4 * π ^ 2 * d) ^ ρ * C / ((N : ℝ) + 1) ^ e + R ^ 2 / ((N : ℝ) + 1) ^ e :=
        add_le_add (hlow.trans hlow') (hhigh.trans hhigh')
    _ = ((1 + 4 * π ^ 2 * d) ^ ρ * C + R ^ 2) / ((N : ℝ) + 1) ^ e := by rw [add_div]


/-! ### The time-derivative rate (`eq:generated-Galerkin-rate`, `a = 1`) -/

section TimeRate

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- Coefficients of a time-independent field do not depend on the slice. -/
theorem coef_slice_eq {g : ST d → ℝ} (hg : ∀ s s' y, g (Fin.cons s y) = g (Fin.cons s' y))
    (t t' : ℝ) (k : Fin d → ℤ) : coef g t k = coef g t' k := by
  unfold coef sint
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [casS_cons, hg t t' y]

/-- The `H^r` energy of a difference of Galerkin fields in coefficients. -/
theorem energyQ_fld_sub {q N M : ℕ} (hNM : N ≤ M) (a : GS d n N) (a' : GS d n M) (r : ℕ)
    (t : ℝ) : energyQ r (fun b x => fld q a b x - fld q a' b x) t =
      ∑ b, ∑ k ∈ KatoGalerkin.box M, wq r k * (cf q a b k - cf q a' b k) ^ 2 := by
  unfold energyQ
  refine Finset.sum_congr rfl fun b _ => ?_
  have e : (fun x => fld q a b x - fld q a' b x) =
      tfs (KatoGalerkin.box M) (fun k => cf q a b k - cf q a' b k) := by
    funext x; rw [fld_eq_tfs hNM a b, fld, tfs_sub]
  show Q r (fun x => fld q a b x - fld q a' b x) t = _
  rw [e, Q_tfs]

/-- **Kato's theorem with the sharp rates of the solution and of its time derivative**
(`thm:generated-dynamics`, `eq:generated-Galerkin-rate`, clauses `a = 0` and `a = 1`).  Let
`m_s > d/2`, `q = r + 1 ≥ 2m_s`, `q ≥ m_s + 2`, `A^i` smooth real symmetric, `F` smooth.  For every
data radius `R₀` there are `T > 0`, `R`, `C` and constants `C'_ρ` such that every smooth periodic
datum with `‖U₀‖_{H^q} ≤ R₀` has a classical solution `U` (with spatial derivatives `P`) on
`[0, T] × 𝕋^d`, the limit of spectral Galerkin solutions `U_N` (`GalerkinHyp`), whose Fourier
coefficients satisfy, for every `t ∈ [0, T]` and every finite mode set `S`:
* `d/dt c_k(U(t)) = c_k(G(U)(t))` (`G(U) = F(U) - Σ_i A^i(U)P_i`), while
  `d/dt c_k(U_N(t)) = c_k(G(U_N(t)))` for `k ∈ box N` (and `0` otherwise);
* (`a = 0`) `Σ_{k ∈ S} wq_ρ(k) (c_k(U_N) - c_k(U))² ≤ ((1 + 4π²d)^ρ C + R²) (N+1)^{-(2(r-ρ)+1)}`,
  `ρ ≤ r`;
* (`a = 1`) for `2m_s ≤ ρ + 1 ≤ r`:
  `Σ_{k ∈ S} wq_ρ(k) (d/dt c_k(U_N) - d/dt c_k(U))² ≤ C'_ρ (N+1)^{-(2(r-ρ-1)+1)}`,
  i.e. `‖∂_t(U_N - U)‖_{C_tH^ρ} ≤ C N^{-(q-ρ-1)+1/2}`. -/
theorem kato_sharp_rates_dt {ms r : ℕ} (hms : (d : ℝ) / 2 < ms) (hq : 2 * ms ≤ r + 1)
    (hq2 : ms + 2 ≤ r + 1) (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∃ R ≥ 0, ∃ C ≥ 0, ∃ Cdt : ℕ → ℝ, (∀ ρ, 0 ≤ Cdt ρ) ∧
      ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
      energyQ (r + 1) U₀ 0 ≤ R₀ ^ 2 →
      ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ) (γ : (N : ℕ) → ℝ → GS d n N),
        GalerkinHyp A F (r + 1) U₀ T R γ ∧
        (∀ b, Continuous (U b)) ∧ (∀ b, IsSPeriodic (U b)) ∧
        (∀ b y, U b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
        (∀ b (i : Fin d) x, HasDerivAt (fun s : ℝ => U b (x + s • ev i.succ)) (P b i x) 0) ∧
        (∀ b, ∀ t ∈ Set.Icc 0 T, ∀ y, HasDerivWithinAt (fun s => U b (Fin.cons s y))
          (genP A F U P b (Fin.cons t y)) (Set.Icc 0 T) t) ∧
        (∀ b k, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun s => coef (U b) s k)
          (coef (genP A F U P b) t k) (Set.Icc 0 T) t) ∧
        (∀ N b k, ∀ t ∈ Set.Icc 0 T, k ∈ KatoGalerkin.box N →
          HasDerivWithinAt (fun s => cf (r + 1) (γ N s) b k)
            (coef (genG A F (fld (r + 1) (γ N t)) b) 0 k) (Set.Icc 0 T) t) ∧
        (∀ ρ ≤ r, ∀ N, ∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin d → ℤ),
          ∑ b, ∑ k ∈ S, wq ρ k * (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2 ≤
            ((1 + 4 * π ^ 2 * d) ^ ρ * C + R ^ 2) / ((N : ℝ) + 1) ^ (2 * (r - ρ) + 1)) ∧
        (∀ ρ, 2 * ms ≤ ρ + 1 → ρ + 1 ≤ r → ∀ N, ∀ t ∈ Set.Icc 0 T,
          ∀ S : Finset (Fin d → ℤ),
          ∑ b, ∑ k ∈ S, wq ρ k * ((if k ∈ KatoGalerkin.box N then
            coef (genG A F (fld (r + 1) (γ N t)) b) 0 k else 0) - coef (genP A F U P b) t k) ^ 2 ≤
            Cdt ρ / ((N : ℝ) + 1) ^ (2 * (r - (ρ + 1)) + 1)) := by
  obtain ⟨T, hT, K, hK, hgal⟩ := galerkin_uniform (d := d) (n := n) hms hq hA hsym hF hR₀
  set R := 2 * R₀ + 1 with hRdef
  have hR : 0 ≤ R := by linarith
  obtain ⟨C, hC0, hC⟩ := galerkin_L2_cauchy_sharp (d := d) (n := n) hms hq (by omega) hA hsym hF
    hR₀ hR hT.le
  -- Lipschitz constants of the generator, order by order
  have hCL : ∀ ρ : ℕ, ∃ CL : ℝ, 0 ≤ CL ∧ (2 * ms ≤ ρ + 1 → ∀ u v : Fin n → ST d → ℝ,
      (∀ b, ContDiff ℝ ∞ (u b)) → (∀ b, ContDiff ℝ ∞ (v b)) → (∀ b, IsSPeriodic (u b)) →
      (∀ b, IsSPeriodic (v b)) → ∀ t, energyQ (ρ + 1) u t ≤ R ^ 2 →
      energyQ (ρ + 1) v t ≤ R ^ 2 → ∀ a,
      Q ρ (fun x => genG A F u a x - genG A F v a x) t ≤
        CL * energyQ (ρ + 1) (fun b x => u b x - v b x) t) := by
    intro ρ
    by_cases h : 2 * ms ≤ ρ + 1
    · obtain ⟨CL, hCL0, hCL⟩ := KatoCFL.Q_genG_sub_le (d := d) (n := n) hms h hA hF hR
      exact ⟨CL, hCL0, fun _ => hCL⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' h⟩
  choose CL hCL0 hCLs using hCL
  obtain ⟨CG, hCG0, hCGs⟩ := KatoCFL.Q_genG_sub_le (d := d) (n := n) hms hq hA hF hR
  set Cdt : ℕ → ℝ := fun ρ =>
    4 * n * CL ρ * ((1 + 4 * π ^ 2 * d) ^ (ρ + 1) * C + R ^ 2) + n * (CG * R ^ 2) with hCdt
  have hCdt0 : ∀ ρ, 0 ≤ Cdt ρ := fun ρ => by
    simp only [hCdt]; have := hCL0 ρ; positivity
  refine ⟨T, hT, R, hR, C, hC0, Cdt, hCdt0, fun U₀ hU hUp hE => ?_⟩
  have hex := fun N => hgal N U₀ hU hUp hE
  choose γ hγ0 hγ using hex
  have hG : GalerkinHyp A F (r + 1) U₀ T R γ :=
    ⟨hγ0, fun N t ht => (hγ N t ht).1, fun N t ht => (hγ N t ht).2.1⟩
  have hT0 := hT.le
  set U := limField (r + 1) hT0 γ with hUdef
  set P := limDeriv (r + 1) hT0 γ with hPdef
  have hcU := fun b => continuous_limField (hT := hT0) hms (by omega : ms + 2 ≤ r + 1) hA hsym
    hF hR₀ hR hU hUp hE hG b
  have hU1 := tendstoUniformly_galerkinField (hT := hT0) hms (by omega : ms + 2 ≤ r + 1) hA
    hsym hF hR₀ hR hU hUp hE hG
  have hG1 := tendstoUniformly_galGen (hT := hT0) hms (by omega : ms + 2 ≤ r + 1) hA hsym hF
    hR₀ hR hU hUp hE hG
  have hcG := fun b => continuous_limGen (hT := hT0) hms (by omega : ms + 2 ≤ r + 1) hA hsym hF
    hR₀ hR hU hUp hE hG b
  have hgenP : ∀ b x, genP A F U P b x = limGen (A := A) (F := F) (r + 1) hT0 γ b x :=
    fun b x => rfl
  have hcauchy := hC U₀ hU hUp hE γ hG.init hG.deriv hG.bound
  have hpow : ∀ N : ℕ, (2 * π * ((N : ℝ) + 1)) ^ (r + 1) * (2 * π * ((N : ℝ) + 1)) ^ r =
      (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1) := fun N => by
    rw [← pow_add]; congr 1; omega
  -- coefficient convergence of the fields
  have hlim : ∀ t ∈ Set.Icc 0 T, ∀ b k, Tendsto (fun M => cf (r + 1) (γ M t) b k) atTop
      (𝓝 (coef (U b) t k)) := by
    intro t ht b k
    have h := tendsto_coef_unif (fun M => continuous_galerkinField hG.continuousOn M b) (hcU b)
      (hU1 b) k
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (h (ε / 2) (by positivity))
    refine ⟨M₀, fun M hM => ?_⟩
    have e : coef (galerkinField (r + 1) hT0 γ M b) t k = cf (r + 1) (γ M t) b k := by
      rw [← KatoRates.coef_fld (r + 1) (γ M t) b t k]
      unfold coef sint
      exact integral_congr_ae (Eventually.of_forall fun y => by
        simp only [galerkinField_cons ht])
    have := hM₀ M hM t
    rw [e] at this
    rw [Real.dist_eq]
    linarith
  -- the coefficient `L²` and `H^ρ` rates (as in `kato_sharp_rates`)
  have hL2 : ∀ N, ∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin d → ℤ),
      ∑ b, ∑ k ∈ S, (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2 ≤
        C / (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1) := by
    intro N t ht S
    have ht' : Tendsto (fun M => ∑ b, ∑ k ∈ S, (cf (r + 1) (γ N t) b k -
        cf (r + 1) (γ M t) b k) ^ 2) atTop
        (𝓝 (∑ b, ∑ k ∈ S, (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2)) :=
      tendsto_finset_sum _ fun b _ => tendsto_finset_sum _ fun k _ =>
        (tendsto_const_nhds.sub (hlim t ht b k)).pow 2
    refine le_of_tendsto ht' ?_
    have hev : ∀ᶠ M in atTop, N ≤ M ∧ ∀ k ∈ S, k ∈ KatoGalerkin.box M := by
      refine (eventually_ge_atTop N).and ((Filter.eventually_all_finset S).2 fun k _ => ?_)
      obtain ⟨M₀, hM₀⟩ := exists_mem_box k
      exact eventually_atTop.2 ⟨M₀, fun M hM => box_mono hM hM₀⟩
    filter_upwards [hev] with M hM
    rw [← hpow N]
    refine le_trans ?_ (hcauchy N M hM.1 t ht)
    refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => hM.2 k hk) fun k _ _ => sq_nonneg _
  have hUq : ∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin d → ℤ),
      ∑ b, ∑ k ∈ S, wq (r + 1) k * coef (U b) t k ^ 2 ≤ R ^ 2 := fun t ht S =>
    limField_Hq_bound (hT := hT0) hms (by omega : ms + 2 ≤ r + 1) hA hsym hF hR₀ hR hU hUp hE
      hG ht S
  have hHρ : ∀ ρ ≤ r, ∀ N, ∀ t ∈ Set.Icc 0 T, ∀ S : Finset (Fin d → ℤ),
      ∑ b, ∑ k ∈ S, wq ρ k * (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2 ≤
        ((1 + 4 * π ^ 2 * d) ^ ρ * C + R ^ 2) / ((N : ℝ) + 1) ^ (2 * (r - ρ) + 1) := by
    intro ρ hρ N t ht S
    set D : (Fin d → ℤ) → Fin n → ℝ := fun k b => cf (r + 1) (γ N t) b k - coef (U b) t k
      with hD
    set L : ℝ := (1 + 4 * π ^ 2 * d) ^ ρ * (((N : ℝ) + 1) ^ 2) ^ ρ with hL
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hsplit : ∀ b, ∑ k ∈ S, wq ρ k * D k b ^ 2 =
        ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), wq ρ k * D k b ^ 2 +
        ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N), wq ρ k * coef (U b) t k ^ 2 := by
      intro b
      rw [← Finset.sum_filter_add_sum_filter_not S (fun k => k ∈ KatoGalerkin.box N)]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [hD, cf_eq_zero _ b (Finset.mem_filter.1 hk).2, zero_sub, neg_sq]
    have hlow : ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), wq ρ k * D k b ^ 2 ≤
        L * (C / (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1)) := by
      calc ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), wq ρ k * D k b ^ 2
          ≤ ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), L * D k b ^ 2 :=
            Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun k hk =>
              mul_le_mul_of_nonneg_right (KatoRates.wq_le_box (Finset.mem_filter.1 hk).2 ρ)
                (sq_nonneg _)
        _ = L * ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), D k b ^ 2 := by
            rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
        _ ≤ L * (C / (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1)) :=
            mul_le_mul_of_nonneg_left (hL2 N t ht _) (by positivity)
    have hhigh : ∑ b, ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N),
        wq ρ k * coef (U b) t k ^ 2 ≤ R ^ 2 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r + 1 - ρ) := by
      have hs : 0 < ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r + 1 - ρ) := by positivity
      rw [le_div_iff₀ hs, Finset.sum_mul]
      calc ∑ b, (∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N),
            wq ρ k * coef (U b) t k ^ 2) * ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r + 1 - ρ)
          ≤ ∑ b, ∑ k ∈ S, wq (r + 1) k * coef (U b) t k ^ 2 := by
            refine Finset.sum_le_sum fun b _ => ?_
            rw [Finset.sum_mul]
            refine le_trans (Finset.sum_le_sum fun k hk => ?_)
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S)
                fun k _ _ => mul_nonneg (wq_nonneg _ k) (sq_nonneg _))
            have h := wq_tail (Finset.mem_filter.1 hk).2 ρ (r + 1 - ρ)
            rw [show ρ + (r + 1 - ρ) = r + 1 by omega] at h
            nlinarith [sq_nonneg (coef (U b) t k)]
        _ ≤ R ^ 2 := hUq t ht S
    have e1 : ∑ b, ∑ k ∈ S, wq ρ k * (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2 =
        ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), wq ρ k * D k b ^ 2 +
        ∑ b, ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N), wq ρ k * coef (U b) t k ^ 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => hsplit b
    rw [e1]
    set e := 2 * (r - ρ) + 1 with he
    have hNe : 0 < ((N : ℝ) + 1) ^ e := by positivity
    have hlow' : L * (C / (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1)) ≤
        (1 + 4 * π ^ 2 * d) ^ ρ * C / ((N : ℝ) + 1) ^ e := by
      have h1 : ((N : ℝ) + 1) ^ (2 * r + 1) ≤ (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1) :=
        KatoRates.succ_pow_le_two_pi N _
      have h2 : (((N : ℝ) + 1) ^ 2) ^ ρ * ((N : ℝ) + 1) ^ e = ((N : ℝ) + 1) ^ (2 * r + 1) := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      rw [hL, mul_div_assoc', div_le_div_iff₀ (by positivity) hNe]
      calc (1 + 4 * π ^ 2 * d) ^ ρ * (((N : ℝ) + 1) ^ 2) ^ ρ * C * ((N : ℝ) + 1) ^ e
          = (1 + 4 * π ^ 2 * d) ^ ρ * C * ((N : ℝ) + 1) ^ (2 * r + 1) := by rw [← h2]; ring
        _ ≤ (1 + 4 * π ^ 2 * d) ^ ρ * C * (2 * π * ((N : ℝ) + 1)) ^ (2 * r + 1) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    have hhigh' : R ^ 2 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r + 1 - ρ) ≤
        R ^ 2 / ((N : ℝ) + 1) ^ e := by
      refine div_le_div_of_nonneg_left (sq_nonneg _) hNe ?_
      rw [← pow_mul]
      calc ((N : ℝ) + 1) ^ e ≤ ((N : ℝ) + 1) ^ (2 * (r + 1 - ρ)) :=
            pow_le_pow_right₀ hN1 (by omega)
        _ ≤ (2 * π * ((N : ℝ) + 1)) ^ (2 * (r + 1 - ρ)) := KatoRates.succ_pow_le_two_pi N _
    calc _ ≤ (1 + 4 * π ^ 2 * d) ^ ρ * C / ((N : ℝ) + 1) ^ e + R ^ 2 / ((N : ℝ) + 1) ^ e :=
          add_le_add (hlow.trans hlow') (hhigh.trans hhigh')
      _ = ((1 + 4 * π ^ 2 * d) ^ ρ * C + R ^ 2) / ((N : ℝ) + 1) ^ e := by rw [add_div]
  -- the time derivative of the limit coefficients
  have hdt : ∀ b k, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun s => coef (U b) s k)
      (coef (genP A F U P b) t k) (Set.Icc 0 T) t := by
    intro b k t ht
    have hcont : Continuous fun s => coef (limGen (A := A) (F := F) (r + 1) hT0 γ b) s k :=
      continuous_coef (hcG b) k
    have hd := ((hcont.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add
      (coef (U₀ b) 0 k)).hasDerivWithinAt (s := Set.Icc 0 T)
    refine hd.congr (fun s hs => ?_) ?_
    · exact coef_limField_eq (hT := hT0) hms (by omega : ms + 2 ≤ r + 1) hA hsym hF hR₀ hR hU
        hUp hE hG hs b k
    · exact coef_limField_eq (hT := hT0) hms (by omega : ms + 2 ≤ r + 1) hA hsym hF hR₀ hR hU
        hUp hE hG ht b k
  refine ⟨U, P, γ, hG, hcU, fun b => isSPeriodic_limField b,
    fun b y => limField_zero (hT := hT0) hms (by omega : ms + 2 ≤ r + 1) hA hsym hF hR₀ hR hU
      hUp hE hG b y,
    fun b i x => hasDerivAt_limField (hT := hT0) hms (by omega : ms + 2 ≤ r + 1) hA hsym hF hR₀
      hR hU hUp hE hG b i x,
    fun b t ht y => hasDerivWithinAt_limField (hT := hT0) hms (by omega : ms + 2 ≤ r + 1) hA
      hsym hF hR₀ hR hU hUp hE hG ht b y,
    hdt, fun N b k t ht hk => hasDerivWithinAt_cf (hG.deriv N t ht) b hk, hHρ,
    fun ρ hρ1 hρr N t ht S => ?_⟩
  -- the `a = 1` rate
  set GN' : (M : ℕ) → Fin n → ST d → ℝ := fun M b => genG A F (fld (r + 1) (γ M t)) b with hGN'
  set Ĝ : Fin n → ST d → ℝ := fun b => genP A F U P b with hĜ
  have hGNs : ∀ M b, ContDiff ℝ ∞ (GN' M b) := fun M b =>
    contDiff_genG hA hF (fun c => contDiff_fld _ _ c) b
  have hGNp : ∀ M b, IsSPeriodic (GN' M b) := fun M b =>
    isSPeriodic_genG (fun c => isSPeriodic_fld _ _ c) b
  have hGNt : ∀ M b k, coef (GN' M b) t k = coef (GN' M b) 0 k := fun M b k =>
    coef_slice_eq (fun s s' y => genG_fld_cons_eq _ _ b s s' y) t 0 k
  -- coefficient convergence of the generator
  have hlimG : ∀ b k, Tendsto (fun M => coef (GN' M b) 0 k) atTop (𝓝 (coef (Ĝ b) t k)) := by
    intro b k
    have h := tendsto_coef_unif (fun M => continuous_galGen (hT := hT0) hms
      (by omega : ms + 2 ≤ r + 1) hA hsym hF hR₀ hR hU hUp hE hG M b) (hcG b) (hG1 b) k
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (h (ε / 2) (by positivity))
    refine ⟨M₀, fun M hM => ?_⟩
    have e : coef (galGen (A := A) (F := F) (r + 1) hT0 γ M b) t k = coef (GN' M b) 0 k := by
      rw [← hGNt]
      unfold coef sint
      exact integral_congr_ae (Eventually.of_forall fun y => by
        simp only [galGen_cons ht, hGN'])
    have := hM₀ M hM t
    rw [e] at this
    rw [Real.dist_eq]
    have e2 : coef (Ĝ b) t k = coef (limGen (A := A) (F := F) (r + 1) hT0 γ b) t k := rfl
    rw [e2]
    linarith
  have hEn : ∀ M, energyQ (ρ + 1) (fld (r + 1) (γ M t)) 0 ≤ R ^ 2 := fun M => by
    refine le_trans ?_ ((energyQ_fld (r + 1) (γ M t) 0).le.trans
      (pow_le_pow_left₀ (norm_nonneg _) (hG.bound M t ht) 2))
    exact Finset.sum_le_sum fun b _ => Q_mono (by omega) _ _
  -- low modes: comparison with `G(U_M)` and passage to the limit
  set rate : ℝ := ((1 + 4 * π ^ 2 * d) ^ (ρ + 1) * C + R ^ 2) /
    ((N : ℝ) + 1) ^ (2 * (r - (ρ + 1)) + 1) with hrate
  have hlowM : ∀ M, N ≤ M → ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N),
      wq ρ k * (coef (GN' N b) 0 k - coef (GN' M b) 0 k) ^ 2 ≤ 4 * n * CL ρ * rate := by
    intro M hNM
    have hrM : ((1 + 4 * π ^ 2 * d) ^ (ρ + 1) * C + R ^ 2) /
        ((M : ℝ) + 1) ^ (2 * (r - (ρ + 1)) + 1) ≤ rate := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hNM) _
    have hdiff : energyQ (ρ + 1) (fun b x => fld (r + 1) (γ N t) b x -
        fld (r + 1) (γ M t) b x) 0 ≤ 4 * rate := by
      rw [energyQ_fld_sub hNM]
      have h1 := hHρ (ρ + 1) hρr N t ht (KatoGalerkin.box M)
      have h2 := hHρ (ρ + 1) hρr M t ht (KatoGalerkin.box M)
      calc ∑ b, ∑ k ∈ KatoGalerkin.box M, wq (ρ + 1) k *
            (cf (r + 1) (γ N t) b k - cf (r + 1) (γ M t) b k) ^ 2
          ≤ ∑ b, ∑ k ∈ KatoGalerkin.box M, (2 * (wq (ρ + 1) k *
              (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2) + 2 * (wq (ρ + 1) k *
              (cf (r + 1) (γ M t) b k - coef (U b) t k) ^ 2)) :=
            Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun k _ => by
              have hw := wq_nonneg (ρ + 1) k
              nlinarith [mul_nonneg hw (sq_nonneg (cf (r + 1) (γ N t) b k +
                cf (r + 1) (γ M t) b k - 2 * coef (U b) t k))]
        _ = 2 * ∑ b, ∑ k ∈ KatoGalerkin.box M, wq (ρ + 1) k *
              (cf (r + 1) (γ N t) b k - coef (U b) t k) ^ 2 +
            2 * ∑ b, ∑ k ∈ KatoGalerkin.box M, wq (ρ + 1) k *
              (cf (r + 1) (γ M t) b k - coef (U b) t k) ^ 2 := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ 2 * rate + 2 * rate := add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left (h2.trans hrM) (by norm_num))
        _ = 4 * rate := by ring
    calc ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N),
          wq ρ k * (coef (GN' N b) 0 k - coef (GN' M b) 0 k) ^ 2
        ≤ ∑ b, Q ρ (fun x => GN' N b x - GN' M b x) 0 := by
          refine Finset.sum_le_sum fun b _ => ?_
          refine le_trans ?_ (bessel_Hq ρ (S.filter (fun k => k ∈ KatoGalerkin.box N))
            ((hGNs N b).sub (hGNs M b)) (fun k x => by simp only [hGNp N b k x, hGNp M b k x]) 0)
          refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
          rw [coef_sub (hGNs N b).continuous (hGNs M b).continuous]
      _ ≤ ∑ _b : Fin n, CL ρ * (4 * rate) := by
          refine Finset.sum_le_sum fun b _ => ?_
          refine (hCLs ρ hρ1 _ _ (fun c => contDiff_fld _ _ c) (fun c => contDiff_fld _ _ c)
            (fun c => isSPeriodic_fld _ _ c) (fun c => isSPeriodic_fld _ _ c) 0 (hEn N) (hEn M)
            b).trans ?_
          exact mul_le_mul_of_nonneg_left hdiff (hCL0 ρ)
      _ = 4 * n * CL ρ * rate := by simp; ring
  have hlow : ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N),
      wq ρ k * (coef (GN' N b) 0 k - coef (Ĝ b) t k) ^ 2 ≤ 4 * n * CL ρ * rate := by
    have ht' : Tendsto (fun M => ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N),
        wq ρ k * (coef (GN' N b) 0 k - coef (GN' M b) 0 k) ^ 2) atTop
        (𝓝 (∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N),
          wq ρ k * (coef (GN' N b) 0 k - coef (Ĝ b) t k) ^ 2)) :=
      tendsto_finset_sum _ fun b _ => tendsto_finset_sum _ fun k _ =>
        ((tendsto_const_nhds.sub (hlimG b k)).pow 2).const_mul _
    exact le_of_tendsto ht' (eventually_atTop.2 ⟨N, fun M hM => hlowM M hM⟩)
  -- high modes: the `H^{q-1}` bound of the generator
  have hhighM : ∀ M b, ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N),
      wq r k * coef (GN' M b) 0 k ^ 2 ≤ CG * R ^ 2 := by
    intro M b
    have hEq : energyQ (r + 1) (fld (r + 1) (γ M t)) 0 ≤ R ^ 2 := by
      rw [energyQ_fld]; exact pow_le_pow_left₀ (norm_nonneg _) (hG.bound M t ht) 2
    have hz : energyQ (r + 1) (fun (_ : Fin n) (_ : ST d) => (0 : ℝ)) 0 ≤ R ^ 2 := by
      rw [energyQ_zero]; positivity
    have h := hCGs (fld (r + 1) (γ M t)) (fun _ _ => 0) (fun c => contDiff_fld _ _ c)
      (fun _ => contDiff_const) (fun c => isSPeriodic_fld _ _ c) (fun _ _ _ => rfl) 0 hEq hz b
    have e0 : (fun b x => fld (r + 1) (γ M t) b x - (fun _ _ => (0 : ℝ)) b x) =
        fld (r + 1) (γ M t) := by funext b x; simp
    rw [e0] at h
    set g : ST d → ℝ := fun x => GN' M b x - genG A F (fun _ _ => (0 : ℝ)) b x with hg
    have hgs : ContDiff ℝ ∞ g := (hGNs M b).sub (contDiff_genG hA hF (fun _ => contDiff_const) b)
    have hgp : IsSPeriodic g := fun k x => by
      simp only [hg, KatoRates.genG_zero_fun, hGNp M b k x]
    have hcoef : ∀ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N),
        coef (GN' M b) 0 k = coef g 0 k := by
      intro k hk
      have hk0 := KatoRates.ne_zero_of_not_mem_box (Finset.mem_filter.1 hk).2
      have e : g = fun x => GN' M b x - F b 0 := by
        funext x; simp only [hg, KatoRates.genG_zero_fun]
      rw [e, coef_sub (hGNs M b).continuous continuous_const,
        KatoRates.coef_const_of_ne _ _ hk0, sub_zero]
    rw [Finset.sum_congr rfl fun k hk => by rw [hcoef k hk]]
    exact (bessel_Hq r (S.filter (fun k => k ∉ KatoGalerkin.box N)) hgs hgp 0).trans
      (h.trans (mul_le_mul_of_nonneg_left hEq hCG0))
  have hhigh : ∑ b, ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N),
      wq ρ k * coef (Ĝ b) t k ^ 2 ≤
        n * (CG * R ^ 2) / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r - ρ) := by
    have hs : 0 < ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r - ρ) := by positivity
    rw [le_div_iff₀ hs, Finset.sum_mul]
    calc ∑ b, (∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N), wq ρ k * coef (Ĝ b) t k ^ 2) *
          ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r - ρ)
        ≤ ∑ b, ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N), wq r k * coef (Ĝ b) t k ^ 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun k hk => ?_
          have h := wq_tail (Finset.mem_filter.1 hk).2 ρ (r - ρ)
          rw [show ρ + (r - ρ) = r by omega] at h
          nlinarith [sq_nonneg (coef (Ĝ b) t k)]
      _ ≤ ∑ _b : Fin n, CG * R ^ 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          have ht' : Tendsto (fun M => ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N),
              wq r k * coef (GN' M b) 0 k ^ 2) atTop
              (𝓝 (∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N),
                wq r k * coef (Ĝ b) t k ^ 2)) :=
            tendsto_finset_sum _ fun k _ => ((hlimG b k).pow 2).const_mul _
          exact le_of_tendsto ht' (Eventually.of_forall fun M => hhighM M b)
      _ = n * (CG * R ^ 2) := by simp
  -- combine
  have hsplit : ∀ b, ∑ k ∈ S, wq ρ k * ((if k ∈ KatoGalerkin.box N then coef (GN' N b) 0 k
      else 0) - coef (Ĝ b) t k) ^ 2 =
      ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N),
        wq ρ k * (coef (GN' N b) 0 k - coef (Ĝ b) t k) ^ 2 +
      ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N), wq ρ k * coef (Ĝ b) t k ^ 2 := by
    intro b
    rw [← Finset.sum_filter_add_sum_filter_not S (fun k => k ∈ KatoGalerkin.box N)]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_pos (Finset.mem_filter.1 hk).2]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_neg (Finset.mem_filter.1 hk).2, zero_sub, neg_sq]
  have e1 : ∑ b, ∑ k ∈ S, wq ρ k * ((if k ∈ KatoGalerkin.box N then
      coef (genG A F (fld (r + 1) (γ N t)) b) 0 k else 0) - coef (genP A F U P b) t k) ^ 2 =
      ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N),
        wq ρ k * (coef (GN' N b) 0 k - coef (Ĝ b) t k) ^ 2 +
      ∑ b, ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N), wq ρ k * coef (Ĝ b) t k ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => hsplit b
  rw [e1]
  set e := 2 * (r - (ρ + 1)) + 1 with he
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hNe : 0 < ((N : ℝ) + 1) ^ e := by positivity
  have hhigh' : n * (CG * R ^ 2) / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (r - ρ) ≤
      n * (CG * R ^ 2) / ((N : ℝ) + 1) ^ e := by
    refine div_le_div_of_nonneg_left (by positivity) hNe ?_
    rw [← pow_mul]
    calc ((N : ℝ) + 1) ^ e ≤ ((N : ℝ) + 1) ^ (2 * (r - ρ)) := pow_le_pow_right₀ hN1 (by omega)
      _ ≤ (2 * π * ((N : ℝ) + 1)) ^ (2 * (r - ρ)) := KatoRates.succ_pow_le_two_pi N _
  calc _ ≤ 4 * n * CL ρ * rate + n * (CG * R ^ 2) / ((N : ℝ) + 1) ^ e :=
        add_le_add hlow (hhigh.trans hhigh')
    _ = Cdt ρ / ((N : ℝ) + 1) ^ e := by
        simp only [hCdt, hrate]; rw [add_div]; ring

end TimeRate
end RenewalGeometry.KatoRates
