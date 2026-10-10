/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoGalerkinSharpRate

/-!
# Persistence of regularity for quasilinear symmetric hyperbolic systems on `𝕋^d`

Generic infrastructure (no renewal notions) for `lem:generated-physical-identification`
(Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics`): the Kato solution of
smooth data is bounded in **every** `H^{q'}` on the Kato interval of the base order `q`.

Setting: `∂_tU + Σ_i A^i(U)∂_iU = F(U)` on `𝕋^d`, smooth real symmetric `A^i`, smooth `F`,
`m > d/2`.

* **`pairQ_genG_le_low`** — the `H^{q'}` energy inequality of `QLEnergy.pairQ_genG_le` with the
  constant depending only on pointwise bounds of the derivatives of order `≤ r` (`q' ≤ 2r`), not
  on the `H^{q'}` norm itself (the tame structure of the commutator estimate);
* `low_bound_of_energy` — such pointwise bounds from an `H^{r+m}` bound (Sobolev embedding);
* **`galerkin_higher_bound`** — along a spectral Galerkin trajectory of order `q ≥ 2m + 1` with a
  uniform `H^q` bound on `[0, T]`, every `H^{q'}` norm (`q' ≥ q`) stays bounded on `[0, T]`,
  uniformly in the cutoff (energy identity at order `q'` + Gronwall, induction on `q'`);
* **`kato_local_existence_allOrders`** — Kato's local existence theorem with the solution bounded
  in every `H^{q'}` on the Kato interval `[0, T]` of the base order (Fourier side);
* **`kato_two_sided_allOrders`** — the same on the symmetric interval `(-T, T)`.

Disclosed: `Σ = 𝕋^d`; smooth data; base order `q ≥ 2m + 1` (one order above the threshold of
`kato_local_existence`, so that the tame induction starts).
-/

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.KatoPersist

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### The tame energy inequality -/

section Tame

/-- **The `H^q` energy inequality with a constant depending only on low-order pointwise bounds**:
for smooth real symmetric `A^i`, smooth `F`, `1 ≤ r`, `1 ≤ q ≤ 2r` and `B₀ ≥ 0` there is `K` such
that every smooth spatially periodic field whose derivatives of order `≤ r` are bounded by `B₀` on
the slice `t` satisfies `⟨U, G(U)⟩_{H^q}(t) ≤ K (1 + ‖U(t)‖²_{H^q})`. -/
theorem pairQ_genG_le_low {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {r q : ℕ}
    (hqr : q ≤ 2 * r) (hr1 : 1 ≤ r) (hq1 : 1 ≤ q) {B0 : ℝ} (hB00 : 0 ≤ B0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, IsSPeriodic (u b)) → ∀ t,
        (∀ y b (L : List (Fin d)), L.length ≤ r → |sd L (u b) (Fin.cons t y)| ≤ B0) →
        pairQ q u (genG A F u) t ≤ K * (1 + energyQ q u t) := by
  set Φ : (Fin n ⊕ (Fin d × Fin n × Fin n)) → (Fin n → ℝ) → ℝ :=
    fun k => Sum.elim (fun a => F a) (fun p => A p.1 p.2.1 p.2.2) k with hΦ
  have hΦs : ∀ k, ContDiff ℝ ∞ (Φ k) := by
    intro k; cases k with
    | inl a => exact hF a
    | inr p => exact hA p.1 p.2.1 p.2.2
  obtain ⟨M, hM0, hM⟩ := exists_bound_family hΦs B0 q
  set P := cq q * M * Bc d n r B0 ^ q with hP
  have hBc := one_le_Bc d n r hB00
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg (cq_nonneg q) hM0) (pow_nonneg (by linarith) _)
  set E := Ecst d n q B0 P with hE
  have hE0 : 0 ≤ E := by unfold Ecst at hE; rw [hE]; positivity
  set cσ := Nsig d n q * ∑ p ∈ Finset.range (q + 1), (d : ℝ) ^ p with hcσ
  have hcσ0 : 0 ≤ cσ := mul_nonneg (Nsig_nonneg d n q) (by positivity)
  set W := ((wordsLE d q).card : ℝ) with hW
  set K := (1 / 2 + 1 / 2 * d * n * P) + W * n * E ^ 2 * (1 + (q + 1) ^ 2 * cσ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun u hu hup t hB => ?_⟩
  have hEn := energyQ_nonneg q u t
  have hval : ∀ y, ‖vslice u t y‖ ≤ B0 := by
    intro y
    refine (pi_norm_le_iff_of_nonneg hB00).2 fun b => ?_
    have := hB y b [] (Nat.zero_le _)
    simpa [Real.norm_eq_abs] using this
  have hMF : ∀ y a, ∀ k ≤ q, ‖iteratedFDeriv ℝ k (F a) (vslice u t y)‖ ≤ M := fun y a k hk =>
    hM (Sum.inl a) _ (hval y) k hk
  have hMA : ∀ y i a b, ∀ k ≤ q, ‖iteratedFDeriv ℝ k (A i a b) (vslice u t y)‖ ≤ M :=
    fun y i a b k hk => hM (Sum.inr (i, a, b)) _ (hval y) k hk
  have hword : ∀ L ∈ wordsLE d q, ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (u a) (Fin.cons t y) *
      sd L (genG A F u a) (Fin.cons t y) ≤
        (1 / 2 + 1 / 2 * d * n * P) *
          (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (u a) (Fin.cons t y) ^ 2) +
        (1 / 2) * n * ∫ y in Icc (0 : Fin d → ℝ) 1, (E * (1 + (q + 1) * sig q u t y)) ^ 2 :=
    fun L hL => word_energy_le hA hsym hF hu hup hB00 hM0 hr1 hq1 hB hMF hMA hqr L
      (mem_wordsLE.mp hL)
  have hσint : ∫ y in Icc (0 : Fin d → ℝ) 1, (E * (1 + (q + 1) * sig q u t y)) ^ 2 ≤
      E ^ 2 * (2 + 2 * (q + 1) ^ 2 * (cσ * energyQ q u t)) := by
    have hs := integral_sig_sq_le hu q t
    have hterm : ∑ b, ∑ p ∈ Finset.range (q + 1), ∑ w : Fin p → Fin d,
        ∫ y in Icc (0 : Fin d → ℝ) 1, sd (List.ofFn w).reverse (u b) (Fin.cons t y) ^ 2 ≤
          (∑ p ∈ Finset.range (q + 1), (d : ℝ) ^ p) * energyQ q u t := by
      unfold energyQ
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun p hp => ?_
      have hpq : p ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
      calc ∑ w : Fin p → Fin d, ∫ y in Icc (0 : Fin d → ℝ) 1,
            sd (List.ofFn w).reverse (u b) (Fin.cons t y) ^ 2
          ≤ ∑ _w : Fin p → Fin d, Q q (u b) t :=
            Finset.sum_le_sum fun w _ => term_le_Q (by simp; exact hpq) (u b) t
        _ = (d : ℝ) ^ p * Q q (u b) t := by simp
    have hσ2 : ∫ y in Icc (0 : Fin d → ℝ) 1, sig q u t y ^ 2 ≤ cσ * energyQ q u t := by
      refine hs.trans ?_
      rw [hcσ, mul_assoc]
      exact mul_le_mul_of_nonneg_left hterm (Nsig_nonneg d n q)
    have hc : Continuous fun y => sig q u t y := continuous_sig hu q t
    calc ∫ y in Icc (0 : Fin d → ℝ) 1, (E * (1 + (q + 1) * sig q u t y)) ^ 2
        ≤ ∫ y in Icc (0 : Fin d → ℝ) 1, E ^ 2 * (2 + 2 * (q + 1) ^ 2 * sig q u t y ^ 2) := by
          refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun y _ => ?_
          · exact ((continuous_const.mul (continuous_const.add (continuous_const.mul hc))).pow
              2).integrableOn_Icc
          · exact (continuous_const.mul (continuous_const.add (continuous_const.mul
              (hc.pow 2)))).integrableOn_Icc
          · rw [mul_pow]
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg E)
            have := one_add_sq_le ((q + 1) * sig q u t y)
            rw [mul_pow] at this
            linarith
      _ = E ^ 2 * (2 + 2 * (q + 1) ^ 2 * ∫ y in Icc (0 : Fin d → ℝ) 1, sig q u t y ^ 2) := by
          have hc2 : Continuous fun y => sig q u t y ^ 2 := hc.pow 2
          rw [integral_const_mul]
          congr 1
          rw [integral_add (continuous_const.integrableOn_Icc)
            ((hc2.integrableOn_Icc).const_mul _), integral_const_mul, setIntegral_const]
          have hv : (volume (Icc (0 : Fin d → ℝ) 1)).toReal = 1 := by
            rw [PeriodicCube.volume_cube]; simp
          rw [measureReal_def, hv, one_smul]
      _ ≤ E ^ 2 * (2 + 2 * (q + 1) ^ 2 * (cσ * energyQ q u t)) := by
          gcongr
  have hsumV : ∑ L ∈ wordsLE d q, ∫ y in Icc (0 : Fin d → ℝ) 1,
      ∑ a, sd L (u a) (Fin.cons t y) ^ 2 = energyQ q u t := by
    unfold energyQ Q
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [integral_finsetSum _ fun a _ => integrableOn_sq (contDiff_sd L (hu a)).continuous t]
  have hpair : pairQ q u (genG A F u) t = ∑ L ∈ wordsLE d q, ∫ y in Icc (0 : Fin d → ℝ) 1,
      ∑ a, sd L (u a) (Fin.cons t y) * sd L (genG A F u a) (Fin.cons t y) := by
    unfold pairQ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [integral_finsetSum _ fun a _ => integrableOn_slice (show Continuous fun x =>
      sd L (u a) x * sd L (genG A F u a) x from (contDiff_sd L (hu a)).continuous.mul
      (contDiff_sd L (contDiff_genG hA hF hu a)).continuous) t]
  rw [hpair]
  calc ∑ L ∈ wordsLE d q, ∫ y in Icc (0 : Fin d → ℝ) 1,
        ∑ a, sd L (u a) (Fin.cons t y) * sd L (genG A F u a) (Fin.cons t y)
      ≤ ∑ L ∈ wordsLE d q, ((1 / 2 + 1 / 2 * d * n * P) *
          (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (u a) (Fin.cons t y) ^ 2) +
        (1 / 2) * n * (E ^ 2 * (2 + 2 * (q + 1) ^ 2 * (cσ * energyQ q u t)))) := by
        refine Finset.sum_le_sum fun L hL => (hword L hL).trans ?_
        gcongr
    _ = (1 / 2 + 1 / 2 * d * n * P) * energyQ q u t +
          W * ((1 / 2) * n * (E ^ 2 * (2 + 2 * (q + 1) ^ 2 * (cσ * energyQ q u t)))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumV, Finset.sum_const, nsmul_eq_mul]
    _ ≤ K * (1 + energyQ q u t) := by
        rw [hK]
        have h1 : 0 ≤ W * n * E ^ 2 := by positivity
        have h2 : 0 ≤ (1 / 2 + 1 / 2 * d * n * P) := by positivity
        nlinarith [mul_nonneg h1 hcσ0, mul_nonneg (mul_nonneg h1 hcσ0) hEn, mul_nonneg h2 hEn,
          mul_nonneg h1 hEn, sq_nonneg ((q : ℝ) + 1)]

/-- **Low-order pointwise bounds from a Sobolev bound**: for `m > d/2` there is `C_S` such that an
`H^{r+m}` bound `‖U(t)‖²_{H^{r+m}} ≤ R²` gives `|∂^LU_b(t, y)| ≤ √C_S R` for `|L| ≤ r`. -/
theorem low_bound_of_energy {m : ℕ} (hm : (d : ℝ) / 2 < m) :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ (r : ℕ) (u : Fin n → ST d → ℝ), (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, IsSPeriodic (u b)) → ∀ t (R : ℝ), 0 ≤ R → energyQ (r + m) u t ≤ R ^ 2 →
        ∀ y b (L : List (Fin d)), L.length ≤ r →
          |sd L (u b) (Fin.cons t y)| ≤ Real.sqrt CS * R := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  refine ⟨CS, hCS, fun r u hu hup t R hR hE y b L hL => ?_⟩
  have h1 := hsup _ (contDiff_sd L (hu b)) (isSPeriodic_sd L (hup b)) t y
  have h2 : Q m (sd L (u b)) t ≤ R ^ 2 := by
    refine (Q_sd_le (a := L) (m := m) (k := r + m) (by omega) (u b) t).trans ?_
    refine le_trans ?_ hE
    exact Finset.single_le_sum (f := fun a => Q (r + m) (u a) t) (fun a _ => Q_nonneg _ (u a) t)
      (Finset.mem_univ b)
  have h3 : sd L (u b) (Fin.cons t y) ^ 2 ≤ (Real.sqrt CS * R) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hCS]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hCS)
  exact abs_le_of_sq_le_sq' h3 (by positivity) |> fun h => abs_le.2 h

end Tame

/-! ### Higher energies along the Galerkin trajectories -/

section Galerkin

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- The `H^{q'}` energy of the field of a Galerkin state of order `q`, in coefficients. -/
def hE (q q' : ℕ) {N : ℕ} (a : GS d n N) : ℝ := ∑ b, ∑ k ∈ KatoGalerkin.box N, wq q' k * cf q a b k ^ 2

theorem energyQ_fld_eq_hE (q q' : ℕ) {N : ℕ} (a : GS d n N) (t : ℝ) :
    energyQ q' (fld q a) t = hE q q' a := by
  unfold energyQ hE
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [fld, Q_tfs]

theorem hE_nonneg (q q' : ℕ) {N : ℕ} (a : GS d n N) : 0 ≤ hE q q' a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (wq_nonneg q' k) (sq_nonneg _)

/-- The `H^{q'}` pairing of a Galerkin field with the generator, in coefficients. -/
theorem pairQ_fld_eq (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (q q' : ℕ) {N : ℕ} (a : GS d n N) :
    pairQ q' (fld q a) (genG A F (fld q a)) 0 =
      ∑ b, ∑ k ∈ KatoGalerkin.box N, wq q' k * cf q a b k * coef (genG A F (fld q a) b) 0 k := by
  unfold pairQ
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := pairWords_tfs q' (KatoGalerkin.box N) (cf q a b)
    (contDiff_genG hA hF (fun b => contDiff_fld q a b) b)
    (isSPeriodic_genG (fun b => isSPeriodic_fld q a b) b) 0
  refine (Eq.trans ?_ h).trans (Finset.sum_congr rfl fun k _ => by ring)
  rfl

/-- **The energy identity at order `q'` along a Galerkin trajectory of order `q`**:
`d/dt ‖U_N‖²_{H^{q'}} = 2 ⟨U_N, G(U_N)⟩_{H^{q'}}` (the projection disappears). -/
theorem hasDerivWithinAt_hE (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {q q' N : ℕ} {γ : ℝ → GS d n N} {s : Set ℝ} {t : ℝ}
    (hγ : HasDerivWithinAt γ (GN A F q (γ t)) s t) :
    HasDerivWithinAt (fun τ => hE q q' (γ τ))
      (2 * pairQ q' (fld q (γ t)) (genG A F (fld q (γ t))) 0) s t := by
  rw [pairQ_fld_eq hA hF, Finset.mul_sum]
  unfold hE
  refine HasDerivWithinAt.fun_sum fun b _ => ?_
  rw [Finset.mul_sum]
  refine HasDerivWithinAt.fun_sum fun k hk => ?_
  have h := (KatoGalerkin.hasDerivWithinAt_sq' (hasDerivWithinAt_cf hγ b hk)).const_mul (wq q' k)
  exact h.congr_deriv (by ring)

/-- **Gronwall on an interval**: if `f' ≤ C f` on `[0, T]` (`C ≥ 0`, one-sided derivatives within
`[0, T]`), then `f(t) ≤ e^{Ct} f(0)`. -/
theorem le_exp_mul_of_deriv_le {f f' : ℝ → ℝ} {T C : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t)
    (hle : ∀ t ∈ Icc 0 T, f' t ≤ C * f t) : ∀ t ∈ Icc 0 T, f t ≤ Real.exp (C * t) * f 0 := by
  set g : ℝ → ℝ := fun t => Real.exp (-(C * t)) * f t with hg
  have hgd : ∀ t ∈ Icc 0 T, HasDerivWithinAt g
      (Real.exp (-(C * t)) * (f' t - C * f t)) (Icc 0 T) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => Real.exp (-(C * t))) (Real.exp (-(C * t)) * (-C)) t := by
      have := ((hasDerivAt_id t).const_mul C).neg.exp
      simpa using this
    have := h1.hasDerivWithinAt.mul (hf t ht)
    exact this.congr_deriv (by ring)
  have hanti : AntitoneOn g (Icc 0 T) := by
    have hcont : ContinuousOn g (Icc 0 T) := fun t ht => (hgd t ht).continuousWithinAt
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hcont ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hgd t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [((hgd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (by linarith [hle t (Ioo_subset_Icc_self ht)])
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have := hanti h0 ht ht.1
  simp only [hg, mul_zero, neg_zero, Real.exp_zero, one_mul] at this
  have hpos := Real.exp_pos (C * t)
  calc f t = Real.exp (C * t) * (Real.exp (-(C * t)) * f t) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (C * t) * f 0 := mul_le_mul_of_nonneg_left this hpos.le

/-- The truncated data have `H^{q'}` energy at most that of the data (Bessel). -/
theorem hE_P0_le (q q' N : ℕ) {U₀ : Fin n → ST d → ℝ} (hU : ∀ b, ContDiff ℝ ∞ (U₀ b))
    (hUp : ∀ b, IsSPeriodic (U₀ b)) : hE q q' (P0 (d := d) q N U₀) ≤ energyQ q' U₀ 0 := by
  unfold hE energyQ
  refine Finset.sum_le_sum fun b _ => ?_
  have h := bessel_Hq q' (KatoGalerkin.box N) (hU b) (hUp b) 0
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) h
  rw [cf_P0, ite_eq_left hk]

/-- **Persistence of regularity for the spectral Galerkin scheme**: let `m > d/2`, `q ≥ 2m + 1`,
and let `γ_N` be Galerkin trajectories of order `q` on `[0, T]` from the truncations of a smooth
periodic datum `U₀`, with the uniform bound `‖U_N(t)‖_{H^q} ≤ R`.  Then for every `j` there is
`R_j` with `‖U_N(t)‖_{H^{q+j}} ≤ R_j` for all cutoffs `N` and `t ∈ [0, T]`. -/
theorem galerkin_higher_bound {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m + 1 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {T R : ℝ} (hR : 0 ≤ R) {U₀ : Fin n → ST d → ℝ}
    (hU : ∀ b, ContDiff ℝ ∞ (U₀ b)) (hUp : ∀ b, IsSPeriodic (U₀ b))
    {γ : (N : ℕ) → ℝ → GS d n N} (hG : GalerkinHyp A F q U₀ T R γ) :
    ∀ j : ℕ, ∃ Rj : ℝ, 0 ≤ Rj ∧ ∀ N, ∀ t ∈ Icc 0 T, hE q (q + j) (γ N t) ≤ Rj ^ 2 := by
  obtain ⟨CS, hCS, hlow⟩ := low_bound_of_energy (d := d) (n := n) hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    exact_mod_cast this
  intro j
  induction j with
  | zero =>
    refine ⟨R, hR, fun N t ht => ?_⟩
    rw [Nat.add_zero, ← energyQ_fld_eq_hE q q _ 0, energyQ_fld]
    exact pow_le_pow_left₀ (norm_nonneg _) (hG.bound N t ht) 2
  | succ j ih =>
    obtain ⟨Rj, hRj, hbd⟩ := ih
    set r := q + j - m with hr
    have hrm : r + m = q + j := by omega
    obtain ⟨K, hK0, hK⟩ := pairQ_genG_le_low (d := d) (n := n) hA hsym hF
      (r := r) (q := q + (j + 1)) (by omega) (by omega) (by omega)
      (B0 := Real.sqrt CS * Rj) (by positivity)
    refine ⟨Real.sqrt (Real.exp (2 * K * T) * (1 + energyQ (q + (j + 1)) U₀ 0)),
      Real.sqrt_nonneg _, fun N t ht => ?_⟩
    set f : ℝ → ℝ := fun τ => 1 + hE q (q + (j + 1)) (γ N τ) with hf
    have hfd : ∀ τ ∈ Icc 0 T, HasDerivWithinAt f
        (2 * pairQ (q + (j + 1)) (fld q (γ N τ)) (genG A F (fld q (γ N τ))) 0) (Icc 0 T) τ :=
      fun τ hτ => (hasDerivWithinAt_hE hA hF (hG.deriv N τ hτ)).const_add 1
    have hle : ∀ τ ∈ Icc 0 T,
        2 * pairQ (q + (j + 1)) (fld q (γ N τ)) (genG A F (fld q (γ N τ))) 0 ≤ (2 * K) * f τ := by
      intro τ hτ
      have hlowτ : ∀ y b (L : List (Fin d)), L.length ≤ r →
          |sd L (fld q (γ N τ) b) (Fin.cons 0 y)| ≤ Real.sqrt CS * Rj := by
        have hE' : energyQ (r + m) (fld q (γ N τ)) 0 ≤ Rj ^ 2 := by
          rw [hrm, energyQ_fld_eq_hE]; exact hbd N τ hτ
        exact hlow r _ (fun b => contDiff_fld q _ b) (fun b => isSPeriodic_fld q _ b) 0 Rj hRj hE'
      have h := hK (fld q (γ N τ)) (fun b => contDiff_fld q _ b) (fun b => isSPeriodic_fld q _ b)
        0 hlowτ
      rw [energyQ_fld_eq_hE] at h
      simp only [hf]
      linarith
    have hgr := le_exp_mul_of_deriv_le hfd hle t ht
    have h0 : f 0 ≤ 1 + energyQ (q + (j + 1)) U₀ 0 := by
      simp only [hf]
      rw [hG.init N]
      linarith [hE_P0_le q (q + (j + 1)) N hU hUp]
    rw [Real.sq_sqrt (by have := energyQ_nonneg (q + (j + 1)) U₀ 0; positivity)]
    have hexp : Real.exp (2 * K * t) ≤ Real.exp (2 * K * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))
    have hf0 : 0 ≤ f 0 := by simp only [hf]; linarith [hE_nonneg q (q + (j + 1)) (γ N 0)]
    calc hE q (q + (j + 1)) (γ N t) ≤ f t := by simp only [hf]; linarith
      _ ≤ Real.exp (2 * K * t) * f 0 := hgr
      _ ≤ Real.exp (2 * K * T) * (1 + energyQ (q + (j + 1)) U₀ 0) :=
          mul_le_mul hexp h0 hf0 (Real.exp_pos _).le

end Galerkin

/-! ### The Kato solution in every `H^{q'}` -/

section Limit

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- Every finite mode set lies in all sufficiently large boxes. -/
theorem exists_box_superset (S : Finset (Fin d → ℤ)) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → S ⊆ KatoGalerkin.box N := by
  refine ⟨S.sup fun k => Finset.univ.sup fun i => (k i).natAbs, fun N hN k hk => ?_⟩
  rw [KatoGalerkin.mem_box]
  intro i
  have h1 : (k i).natAbs ≤ Finset.univ.sup fun i => (k i).natAbs :=
    Finset.le_sup (f := fun i => (k i).natAbs) (Finset.mem_univ i)
  have h2 : (Finset.univ.sup fun i => (k i).natAbs) ≤
      S.sup fun k => Finset.univ.sup fun i => (k i).natAbs :=
    Finset.le_sup (f := fun k => Finset.univ.sup fun i => (k i).natAbs) hk
  have h3 : (k i).natAbs ≤ N := h1.trans (h2.trans hN)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h3

/-- The coefficients of a slice depend only on the slice values. -/
theorem coef_congr_slice {f g : ST d → ℝ} {t t' : ℝ}
    (h : ∀ y, f (Fin.cons t y) = g (Fin.cons t' y)) (k : Fin d → ℤ) :
    coef f t k = coef g t' k := by
  unfold coef sint
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [casS_cons, h y]

/-- **Kato's local existence theorem with persistence of regularity** (`Σ = 𝕋^d`): for
`m > d/2`, `q ≥ 2m + 1`, smooth real symmetric `A^i` and smooth `F`, and every radius `R₀`, there
is `T > 0` such that every smooth periodic datum with `‖U₀‖_{H^q} ≤ R₀` has a classical solution
on `[0, T] × 𝕋^d` (`ForwardSol`) which is bounded in **every** `H^{q+j}` on `[0, T]`
(Fourier side: `Σ_{k ∈ S} wq_{q+j}(k) c_k(U(t))² ≤ R_j²` for every finite mode set `S`). -/
theorem kato_local_existence_allOrders {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m + 1 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
      energyQ q U₀ 0 ≤ R₀ ^ 2 →
      ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ), ForwardSol A F U₀ T U P ∧
        ∀ j : ℕ, ∃ Rj : ℝ, 0 ≤ Rj ∧ ∀ t ∈ Icc 0 T, ∀ S : Finset (Fin d → ℤ),
          ∑ b, ∑ k ∈ S, wq (q + j) k * coef (U b) t k ^ 2 ≤ Rj ^ 2 := by
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    exact_mod_cast this
  obtain ⟨T, hT, R, hR, C, -, hK⟩ := kato_local_existence (A := A) (F := F) hm
    (by omega : 2 * m ≤ q) (by omega : m + 2 ≤ q) hA hsym hF hR₀
  refine ⟨T, hT, fun U₀ hU hUp hE0 => ?_⟩
  obtain ⟨U, P, c1, c2, c3, c4, c5, c6, c7, -, -, γ, hG, hconv, -⟩ := hK U₀ hU hUp hE0
  refine ⟨U, P, ⟨c1, c2, c3, c4, c5, c6, c7⟩, fun j => ?_⟩
  obtain ⟨Rj, hRj, hbd⟩ := galerkin_higher_bound hm hq hA hsym hF hR hU hUp hG j
  refine ⟨Rj, hRj, fun t ht S => ?_⟩
  -- coefficient convergence on the slice `t`
  have hcoef : ∀ b k, Tendsto (fun N => coef (fld q (γ N t) b) t k) atTop
      (𝓝 (coef (U b) t k)) := by
    intro b k
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hconv b (ε / 4) (by positivity))
    refine ⟨N₁, fun N hN => ?_⟩
    rw [Real.dist_eq]
    have h1 := KatoRates.abs_coef_sub_le_slice (contDiff_fld q (γ N t) b).continuous (c1 b)
      (t := t) (η := ε / 4) (fun y => (hN₁ N hN t ht y).1) k
    linarith
  have hlim : Tendsto (fun N => ∑ b, ∑ k ∈ S, wq (q + j) k * coef (fld q (γ N t) b) t k ^ 2)
      atTop (𝓝 (∑ b, ∑ k ∈ S, wq (q + j) k * coef (U b) t k ^ 2)) :=
    tendsto_finsetSum _ fun b _ => tendsto_finsetSum _ fun k _ =>
      ((hcoef b k).pow 2).const_mul _
  obtain ⟨N₀, hN₀⟩ := exists_box_superset S
  refine le_of_tendsto hlim (eventually_atTop.2 ⟨N₀, fun N hN => ?_⟩)
  have hS := hN₀ N hN
  calc ∑ b, ∑ k ∈ S, wq (q + j) k * coef (fld q (γ N t) b) t k ^ 2
      = ∑ b, ∑ k ∈ S, wq (q + j) k * cf q (γ N t) b k ^ 2 := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k hk => ?_
        rw [fld, coef_tfs_of_mem _ t (hS hk)]
    _ ≤ hE q (q + j) (γ N t) := by
        unfold KatoPersist.hE
        refine Finset.sum_le_sum fun b _ => ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg hS fun k _ _ =>
          mul_nonneg (wq_nonneg _ k) (sq_nonneg _)
    _ ≤ Rj ^ 2 := hbd N t ht

/-- **Kato's theorem on `(-T, T)` with persistence of regularity**: the two-sided solution of
`KatoGalerkin.kato_two_sided` (base order `q ≥ 2m + 1`) is bounded in every `H^{q+j}` on
`(-T, T)`. -/
theorem kato_two_sided_allOrders {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m + 1 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
      energyQ q U₀ 0 ≤ R₀ ^ 2 →
      ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ), TwoSidedSol A F U₀ T U P ∧
        ∀ j : ℕ, ∃ Rj : ℝ, 0 ≤ Rj ∧ ∀ t ∈ Ioo (-T) T, ∀ S : Finset (Fin d → ℤ),
          ∑ b, ∑ k ∈ S, wq (q + j) k * coef (U b) t k ^ 2 ≤ Rj ^ 2 := by
  obtain ⟨T₁, hT₁, h₁⟩ := kato_local_existence_allOrders (A := A) (F := F) hm hq hA hsym hF hR₀
  obtain ⟨T₂, hT₂, h₂⟩ := kato_local_existence_allOrders (A := fun i a b v => -A i a b v)
    (F := fun a v => -F a v) hm hq (fun i a b => (hA i a b).neg)
    (fun i a b v => by rw [hsym]) (fun a => (hF a).neg) hR₀
  refine ⟨min T₁ T₂, lt_min hT₁ hT₂, fun U₀ hU hUp hE => ?_⟩
  obtain ⟨Up, Pp, hp, hbp⟩ := h₁ U₀ hU hUp hE
  obtain ⟨Um, Pm, hm', hbm⟩ := h₂ U₀ hU hUp hE
  refine ⟨_, _, twoSided_of_forward (lt_min hT₁ hT₂) (hp.mono (min_le_left _ _))
    (hm'.mono (min_le_right _ _)), fun j => ?_⟩
  obtain ⟨R1, hR1, hb1⟩ := hbp j
  obtain ⟨R2, hR2, hb2⟩ := hbm j
  refine ⟨max R1 R2, le_max_of_le_left hR1, fun t ht S => ?_⟩
  rcases le_or_gt 0 t with h | h
  · have e : ∀ b k, coef (glue Up Um b) t k = coef (Up b) t k := fun b k =>
      coef_congr_slice (fun y => by simp [glue, h]) k
    simp only [e]
    refine (hb1 t ⟨h, ht.2.le.trans (min_le_left _ _)⟩ S).trans ?_
    exact pow_le_pow_left₀ hR1 (le_max_left _ _) 2
  · have e : ∀ b k, coef (glue Up Um b) t k = coef (Um b) (-t) k := fun b k =>
      coef_congr_slice (fun y => by simp [glue, not_le.2 h, refl_cons]) k
    simp only [e]
    refine (hb2 (-t) ⟨by linarith, by linarith [ht.1, min_le_right T₁ T₂]⟩ S).trans ?_
    exact pow_le_pow_left₀ hR2 (le_max_right _ _) 2

end Limit

end RenewalGeometry.KatoPersist
