/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.QuasilinearSymmetricEnergy
import RenewalGeometry.Continuum.ActualJetForcingBound

/-!
# Moser composition on the slices of `[0, T] × 𝕋^d` and smooth-coefficient forcing bounds

Generic infrastructure (no renewal notions) for `lem:actual-jet-complete-forcing` of the
Einstein–Standard-Model action-closure manuscript ("Smooth composition and the `H^k` algebra
estimate on the three-dimensional closed slices control products with the undifferentiated
residuals").

Setting of `SlabSobolevAlgebra` / `QuasilinearSymmetricEnergy`: smooth, spatially periodic fields
on `ℝ^{1+d}`, classical squared `H^q` slice norms `Q_q`.

* **`Q_compF_le`** — the **Moser composition estimate**: for `m > d/2`, `2m ≤ q + 1` and a smooth
  `Φ : ℝ^n → ℝ`, every `R ≥ 0` has a `K` with `Q_q(Φ ∘ U)(t) ≤ K` whenever
  `‖U(t)‖²_{H^q} ≤ R²` (tame Faà di Bruno bound + Sobolev embedding of the low-order derivatives).
* **`exists_contDiff_eqOn`** — a function smooth on an open set agrees on a compact subset with a
  globally smooth function (smooth cutoff).
* **`Q_compOn_le`** — the Moser estimate for maps smooth only on an open chart `O`, for fields
  taking values in a compact `K ⊂ O` on the slab (the "chart margins").
* **`forcing_bound_chart`** — `ActualJetForcing.forcing_bound` with coefficient fields given by
  maps smooth on a chart composed with the state: the derivative-counted forcing bound with a
  constant depending only on the `H^k` radius and the compact chart margin.
-/

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff Manifold

noncomputable section

namespace RenewalGeometry.SlabMoser

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-- **Moser composition estimate on the slices**: for `m > d/2`, `2m ≤ q + 1` and a smooth
`Φ : ℝ^n → ℝ`, for every radius `R ≥ 0` there is `K ≥ 0` such that every smooth periodic field
`U` with `‖U(t)‖²_{H^q} ≤ R²` has `Q_q(Φ ∘ U)(t) ≤ K`. -/
theorem Q_compF_le {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q + 1)
    {Φ : (Fin n → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, IsSPeriodic (u b)) → ∀ t, energyQ q u t ≤ R ^ 2 → Q q (compF Φ u) t ≤ K := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  obtain ⟨r, hr⟩ : ∃ r, r = q - m := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    exact_mod_cast this
  have hqr : q ≤ 2 * r + 1 := by omega
  set B0 := Real.sqrt CS * R with hB0
  have hB00 : 0 ≤ B0 := by positivity
  obtain ⟨M, hM0, hM⟩ := exists_bound_family (κ := Unit) (fun _ => hΦ) B0 q
  set P := cq q * M * Bc d n r B0 ^ q with hP
  have hBc := one_le_Bc d n r hB00
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg (cq_nonneg q) hM0) (pow_nonneg (by linarith) _)
  set cσ := Nsig d n q * ∑ p ∈ Finset.range (q + 1), (d : ℝ) ^ p with hcσ
  have hcσ0 : 0 ≤ cσ := mul_nonneg (Nsig_nonneg d n q) (by positivity)
  set W := ((wordsLE d q).card : ℝ) with hW
  set K := W * (P ^ 2 * (2 + 2 * (q + 1) ^ 2 * (cσ * R ^ 2))) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun u hu hup t hEt => ?_⟩
  -- low-order bounds from the Sobolev embedding
  have hB : ∀ y b (L : List (Fin d)), L.length ≤ r → |sd L (u b) (Fin.cons t y)| ≤ B0 := by
    intro y b L hL
    have h1 := hsup _ (contDiff_sd L (hu b)) (isSPeriodic_sd L (hup b)) t y
    have h2 : Q m (sd L (u b)) t ≤ R ^ 2 := by
      refine (Q_sd_le (a := L) (m := m) (k := q) (by omega) (u b) t).trans ?_
      refine le_trans ?_ hEt
      exact Finset.single_le_sum (f := fun a => Q q (u a) t) (fun a _ => Q_nonneg q (u a) t)
        (Finset.mem_univ b)
    have h3 : sd L (u b) (Fin.cons t y) ^ 2 ≤ (Real.sqrt CS * R) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hCS]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hCS)
    exact abs_le_of_sq_le_sq' h3 hB00 |> fun h => abs_le.2 h
  have hval : ∀ y, ‖vslice u t y‖ ≤ B0 := by
    intro y
    refine (pi_norm_le_iff_of_nonneg hB00).2 fun b => ?_
    have := hB y b [] (Nat.zero_le _)
    simpa [Real.norm_eq_abs] using this
  have hMΦ : ∀ y, ∀ k ≤ q, ‖iteratedFDeriv ℝ k Φ (vslice u t y)‖ ≤ M := fun y k hk =>
    hM () _ (hval y) k hk
  -- pointwise bound on every word
  have hpt : ∀ L ∈ wordsLE d q, ∀ y, sd L (compF Φ u) (Fin.cons t y) ^ 2 ≤
      P ^ 2 * (2 + 2 * (q + 1) ^ 2 * sig q u t y ^ 2) := by
    intro L hL y
    have hLq := mem_wordsLE.mp hL
    have h := abs_sd_compF_le hΦ hu hB00 (hB y) (hMΦ y) L hLq (hLq.trans hqr)
    have hσ := sig_nonneg q u t y
    have h2 : sd L (compF Φ u) (Fin.cons t y) ^ 2 ≤ (P * (1 + (q + 1) * sig q u t y)) ^ 2 := by
      have := abs_nonneg (sd L (compF Φ u) (Fin.cons t y))
      rw [← sq_abs]
      exact pow_le_pow_left₀ this h 2
    refine h2.trans ?_
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg P)
    have := one_add_sq_le ((q + 1) * sig q u t y)
    rw [mul_pow] at this
    linarith
  -- the σ integral
  have hσ2 : ∫ y in Icc (0 : Fin d → ℝ) 1, sig q u t y ^ 2 ≤ cσ * R ^ 2 := by
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
    have hpow : 0 ≤ ∑ p ∈ Finset.range (q + 1), (d : ℝ) ^ p := by positivity
    calc ∫ y in Icc (0 : Fin d → ℝ) 1, sig q u t y ^ 2
        ≤ Nsig d n q * ((∑ p ∈ Finset.range (q + 1), (d : ℝ) ^ p) * energyQ q u t) :=
          hs.trans (mul_le_mul_of_nonneg_left hterm (Nsig_nonneg d n q))
      _ ≤ Nsig d n q * ((∑ p ∈ Finset.range (q + 1), (d : ℝ) ^ p) * R ^ 2) := by
          gcongr
          exact Nsig_nonneg d n q
      _ = cσ * R ^ 2 := by rw [hcσ]; ring
  -- integrate and sum over the words
  have hc : Continuous fun y => sig q u t y := continuous_sig hu q t
  have hword : ∀ L ∈ wordsLE d q, ∫ y in Icc (0 : Fin d → ℝ) 1,
      sd L (compF Φ u) (Fin.cons t y) ^ 2 ≤ P ^ 2 * (2 + 2 * (q + 1) ^ 2 * (cσ * R ^ 2)) := by
    intro L hL
    have hcomp := contDiff_compF hΦ hu
    calc ∫ y in Icc (0 : Fin d → ℝ) 1, sd L (compF Φ u) (Fin.cons t y) ^ 2
        ≤ ∫ y in Icc (0 : Fin d → ℝ) 1, P ^ 2 * (2 + 2 * (q + 1) ^ 2 * sig q u t y ^ 2) := by
          refine setIntegral_mono_on (integrableOn_sq (contDiff_sd L hcomp).continuous t) ?_
            measurableSet_Icc fun y _ => hpt L hL y
          exact (continuous_const.mul (continuous_const.add (continuous_const.mul
            (hc.pow 2)))).integrableOn_Icc
      _ = P ^ 2 * (2 + 2 * (q + 1) ^ 2 * ∫ y in Icc (0 : Fin d → ℝ) 1, sig q u t y ^ 2) := by
          have hc2 : Continuous fun y => sig q u t y ^ 2 := hc.pow 2
          rw [integral_const_mul]
          congr 1
          rw [integral_add (continuous_const.integrableOn_Icc)
            ((hc2.integrableOn_Icc).const_mul _), integral_const_mul, setIntegral_const]
          have hv : (volume (Icc (0 : Fin d → ℝ) 1)).toReal = 1 := by
            rw [PeriodicCube.volume_cube]; simp
          rw [measureReal_def, hv, one_smul]
      _ ≤ P ^ 2 * (2 + 2 * (q + 1) ^ 2 * (cσ * R ^ 2)) := by gcongr
  calc Q q (compF Φ u) t = ∑ L ∈ wordsLE d q, ∫ y in Icc (0 : Fin d → ℝ) 1,
        sd L (compF Φ u) (Fin.cons t y) ^ 2 := rfl
    _ ≤ ∑ _L ∈ wordsLE d q, P ^ 2 * (2 + 2 * (q + 1) ^ 2 * (cσ * R ^ 2)) :=
        Finset.sum_le_sum hword
    _ = K := by rw [Finset.sum_const, nsmul_eq_mul, hK, hW]

/-! ### Smooth cutoff extension from a chart -/

/-- **Smooth extension from a chart**: a function smooth on an open set `O` of a
finite-dimensional space agrees on a compact `K ⊂ O` with a globally smooth function. -/
theorem exists_contDiff_eqOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {O K : Set E} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {Φ : E → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ O) :
    ∃ Φ' : E → ℝ, ContDiff ℝ ∞ Φ' ∧ ∀ v ∈ K, Φ' v = Φ v := by
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
    hO.isClosed_compl hK.isClosed (n := ⊤) (disjoint_compl_left.mono_right hKO)
  have hfs : ContDiff ℝ ∞ (f : E → ℝ) := contMDiff_iff_contDiff.mp f.contMDiff
  refine ⟨fun v => f v * Φ v, ?_, fun v hv => ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hx : x ∈ O
    · exact hfs.contDiffAt.mul (hΦ.contDiffAt (hO.mem_nhds hx))
    · have hev : ∀ᶠ y in 𝓝 x, f y = 0 :=
        hf0.filter_mono (nhds_le_nhdsSet (show x ∈ Oᶜ from hx))
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      rw [hy, zero_mul]
  · have : f v = 1 := hf1.self_of_nhdsSet v hv
    simp [this]

/-! ### Forcing bounds with smooth coefficient maps -/

/-- **The derivative-counted forcing bound with smooth coefficient maps of the state**
(`eq:actual-jet-complete-forcing`): for globally smooth coefficient maps of the state values and an
`H^k` radius `R`, there is `C_M` with
`Q_k(𝓕_err)(t) ≤ C_M (Σ Q_k(R_B) + Σ Q_{k+1}(R_D) + Σ Q_{k+1}(C) + Σ Q_k(∂_tC))` for every smooth
periodic state `U` with `‖U(t)‖²_{H^k} ≤ R²` (coefficients `Φ(U)` by the Moser estimate
`Q_compF_le`, products by the `H^k` algebra, derivative counting by `ActualJetForcing.forcing_bound`). -/
theorem forcing_bound_comp {k m : ℕ} (hm : (d : ℝ) / 2 < m) (hk : 2 * m ≤ k + 1)
    {ι κ θ : Type*} [Fintype ι] [Fintype κ] [Fintype θ]
    {Φb : ι → (Fin n → ℝ) → ℝ} {Φq : κ → Fin d → (Fin n → ℝ) → ℝ}
    {Φc Φc0 : θ → (Fin n → ℝ) → ℝ} {Φcj : θ → Fin d → (Fin n → ℝ) → ℝ}
    (hb : ∀ i, ContDiff ℝ ∞ (Φb i)) (hq : ∀ p j, ContDiff ℝ ∞ (Φq p j))
    (hc : ∀ l, ContDiff ℝ ∞ (Φc l)) (hc0 : ∀ l, ContDiff ℝ ∞ (Φc0 l))
    (hcj : ∀ l j, ContDiff ℝ ∞ (Φcj l j)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ u : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, IsSPeriodic (u b)) → ∀ {RB : ι → ST d → ℝ} {RD : κ → ST d → ℝ}
      {C dtC : θ → ST d → ℝ}, (∀ i, ContDiff ℝ ∞ (RB i)) → (∀ p, ContDiff ℝ ∞ (RD p)) →
      (∀ l, ContDiff ℝ ∞ (C l)) → (∀ l, ContDiff ℝ ∞ (dtC l)) →
      (∀ i, IsSPeriodic (RB i)) → (∀ p, IsSPeriodic (RD p)) → (∀ l, IsSPeriodic (C l)) →
      (∀ l, IsSPeriodic (dtC l)) → ∀ t, energyQ k u t ≤ R ^ 2 →
      Q k (ActualJetForcing.forcingErr (fun i => compF (Φb i) u) RB
          (fun p j => compF (Φq p j) u) RD (fun l => compF (Φc l) u) (fun l => compF (Φc0 l) u)
          (fun l j => compF (Φcj l j) u) C dtC) t ≤
        CM * (∑ i, Q k (RB i) t + ∑ p, Q (k + 1) (RD p) t + ∑ l, Q (k + 1) (C l) t +
          ∑ l, Q k (dtC l) t) := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  -- one Moser constant for the whole (finite) family of coefficient maps
  set Fam := ι ⊕ (κ × Fin d) ⊕ θ ⊕ θ ⊕ (θ × Fin d) with hFam
  let Φ : Fam → (Fin n → ℝ) → ℝ := fun z => match z with
    | Sum.inl i => Φb i
    | Sum.inr (Sum.inl p) => Φq p.1 p.2
    | Sum.inr (Sum.inr (Sum.inl l)) => Φc l
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl l))) => Φc0 l
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr p))) => Φcj p.1 p.2
  have hΦ : ∀ z, ContDiff ℝ ∞ (Φ z) := by
    intro z
    rcases z with i | p | l | l | p
    · exact hb i
    · exact hq p.1 p.2
    · exact hc l
    · exact hc0 l
    · exact hcj p.1 p.2
  have hK := fun z => Q_compF_le (n := n) (d := d) hm hk (hΦ z) hR
  choose K hK0 hKb using hK
  set M := ∑ z, K z with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun z _ => hK0 z
  have hKM : ∀ z, K z ≤ M := fun z =>
    Finset.single_le_sum (f := K) (fun z _ => hK0 z) (Finset.mem_univ z)
  have hA := SlabSobAlg.algC_nonneg (d := d) k hCS
  refine ⟨8 * SlabSobAlg.algC d k CS * M * ((Fintype.card ι + Fintype.card κ * d ^ 2 +
    Fintype.card θ * (2 + d ^ 2)) : ℝ), by positivity, ?_⟩
  intro u hu hup RB RD C dtC hRB hRD hC hdtC pRB pRD pC pdtC t hEt
  have hbd : ∀ z, Q k (compF (Φ z) u) t ≤ M := fun z => (hKb z u hu hup t hEt).trans (hKM z)
  exact ActualJetForcing.forcing_bound hk hCS hsup
    (fun i => contDiff_compF (hb i) hu) hRB (fun p j => contDiff_compF (hq p j) hu) hRD
    (fun l => contDiff_compF (hc l) hu) (fun l => contDiff_compF (hc0 l) hu)
    (fun l j => contDiff_compF (hcj l j) hu) hC hdtC
    (fun i => isSPeriodic_compF _ hup) pRB (fun p j => isSPeriodic_compF _ hup) pRD
    (fun l => isSPeriodic_compF _ hup) (fun l => isSPeriodic_compF _ hup)
    (fun l j => isSPeriodic_compF _ hup) pC pdtC hM0 (fun i => hbd (Sum.inl i))
    (fun p j => hbd (Sum.inr (Sum.inl (p, j)))) (fun l => hbd (Sum.inr (Sum.inr (Sum.inl l))))
    (fun l => hbd (Sum.inr (Sum.inr (Sum.inr (Sum.inl l)))))
    (fun l j => hbd (Sum.inr (Sum.inr (Sum.inr (Sum.inr (l, j))))))

/-! ### Forcings of the actual-jet form with coefficient maps smooth on a chart -/

/-- Coordinates of a linear image: `L(e(r)) = Σ_a r_a L(e(δ_a))`. -/
theorem linear_coord {Y Z : Type*} [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
    {a : ℕ} (eY : (Fin a → ℝ) →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] Z) (p : Z →ₗ[ℝ] ℝ) (r : Fin a → ℝ) :
    p (B (eY r)) = ∑ i, p (B (eY (Pi.single i 1))) * r i := by
  have hr : r = ∑ i, r i • (Pi.single i 1 : Fin a → ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hr]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The derivative-counted forcing bound for forcings of the actual-jet form**
(`eq:actual-jet-complete-forcing`), in coordinates.  Let the state space `X` have coordinates
`eX : ℝ^n ≃L X`, let `O ⊆ X` be an open chart and `K ⊂ O` compact (the chart margin), and let the
forcing be
`𝓕_err = 𝓑(U)R_B + 𝓓(U)R_D + Σ_j 𝒬_j(U)∂_jR_D + 𝒥_C(U)C + 𝒥_C^0(U)∂_tC + Σ_j 𝒥_C^j(U)∂_jC`
with coefficient maps linear in the residuals / defect and smooth in `U` on `O` (the residuals and
the defect enter through arbitrary linear coordinate maps `eY`, `eYD`; any linear functional `pZ`
of the forcing is estimated).  Then for every radius `R` there is `C_M` such that for every smooth
periodic state (coordinates `u`) with values in `K` on the slab `[0, T] × ℝ^d` and
`‖u(t)‖²_{H^k} ≤ R²`, any smooth field agreeing with `pZ(𝓕_err)` on the slab satisfies
`Q_k ≤ C_M (Σ Q_k(R_B) + Σ Q_{k+1}(R_D) + Σ Q_{k+1}(C) + Σ Q_k(∂_tC))`. -/
theorem writer_forcing_bound {k m : ℕ} (hm : (d : ℝ) / 2 < m) (hk : 2 * m ≤ k + 1)
    {X Y YD Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [AddCommGroup Y] [Module ℝ Y]
    [AddCommGroup YD] [Module ℝ YD] [AddCommGroup Z] [Module ℝ Z] {a b : ℕ}
    (eX : (Fin n → ℝ) ≃L[ℝ] X) (eY : (Fin a → ℝ) →ₗ[ℝ] Y) (eYD : (Fin b → ℝ) →ₗ[ℝ] YD)
    (pZ : Z →ₗ[ℝ] ℝ) {O K : Set X} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (Bm : X → Y →ₗ[ℝ] Z) (Dm : X → YD →ₗ[ℝ] Z) (Qm : Fin d → X → YD →ₗ[ℝ] Z)
    (Gc G0 : X → (Fin 4 → ℝ) →ₗ[ℝ] Z) (Gj : Fin d → X → (Fin 4 → ℝ) →ₗ[ℝ] Z)
    (hB : ∀ y, ContDiffOn ℝ ∞ (fun x => pZ (Bm x y)) O)
    (hD : ∀ y, ContDiffOn ℝ ∞ (fun x => pZ (Dm x y)) O)
    (hQ : ∀ j y, ContDiffOn ℝ ∞ (fun x => pZ (Qm j x y)) O)
    (hGc : ∀ y, ContDiffOn ℝ ∞ (fun x => pZ (Gc x y)) O)
    (hG0 : ∀ y, ContDiffOn ℝ ∞ (fun x => pZ (G0 x y)) O)
    (hGj : ∀ j y, ContDiffOn ℝ ∞ (fun x => pZ (Gj j x y)) O) {R T : ℝ} (hR : 0 ≤ R) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ u : Fin n → ST d → ℝ, (∀ i, ContDiff ℝ ∞ (u i)) →
      (∀ i, IsSPeriodic (u i)) → ∀ {RB : Fin a → ST d → ℝ} {RD : Fin b → ST d → ℝ}
      {C dtC : Fin 4 → ST d → ℝ}, (∀ i, ContDiff ℝ ∞ (RB i)) → (∀ i, ContDiff ℝ ∞ (RD i)) →
      (∀ l, ContDiff ℝ ∞ (C l)) → (∀ l, ContDiff ℝ ∞ (dtC l)) →
      (∀ i, IsSPeriodic (RB i)) → (∀ i, IsSPeriodic (RD i)) → (∀ l, IsSPeriodic (C l)) →
      (∀ l, IsSPeriodic (dtC l)) →
      (∀ x : ST d, x 0 ∈ Icc 0 T → eX (fun i => u i x) ∈ K) → ∀ t ∈ Icc 0 T,
      energyQ k u t ≤ R ^ 2 → ∀ F : ST d → ℝ, ContDiff ℝ ∞ F →
      (∀ x : ST d, x 0 ∈ Icc 0 T → F x =
        pZ (Bm (eX fun i => u i x) (eY fun i => RB i x)) +
        pZ (Dm (eX fun i => u i x) (eYD fun i => RD i x)) +
        ∑ j, pZ (Qm j (eX fun i => u i x) (eYD fun i => pd (RD i) j.succ x)) +
        pZ (Gc (eX fun i => u i x) fun l => C l x) +
        pZ (G0 (eX fun i => u i x) fun l => dtC l x) +
        ∑ j, pZ (Gj j (eX fun i => u i x) fun l => pd (C l) j.succ x)) →
      Q k F t ≤ CM * (∑ i, Q k (RB i) t + ∑ i, Q (k + 1) (RD i) t + ∑ l, Q (k + 1) (C l) t +
        ∑ l, Q k (dtC l) t) := by
  -- coefficient maps in coordinates, smooth on the open chart preimage
  set O' := eX ⁻¹' O with hO'
  set K' := eX ⁻¹' K with hK'
  have hO'o : IsOpen O' := hO.preimage eX.continuous
  have hK'c : IsCompact K' := by
    have := hK.image eX.symm.continuous
    rwa [hK', ← ContinuousLinearEquiv.image_symm_eq_preimage]
  have hK'O' : K' ⊆ O' := fun v hv => hKO hv
  have hsm : ∀ {f : X → ℝ}, ContDiffOn ℝ ∞ f O → ContDiffOn ℝ ∞ (fun v => f (eX v)) O' :=
    fun hf => hf.comp eX.contDiff.contDiffOn fun v hv => hv
  have hext : ∀ {f : X → ℝ}, ContDiffOn ℝ ∞ f O →
      ∃ f' : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ f' ∧ ∀ v ∈ K', f' v = f (eX v) :=
    fun hf => exists_contDiff_eqOn hO'o hK'c hK'O' (hsm hf)
  choose Φb hΦb hΦbK using fun i : Fin a => hext (hB (eY (Pi.single i 1)))
  choose Φd hΦd hΦdK using fun i : Fin b => hext (hD (eYD (Pi.single i 1)))
  choose Φq hΦq hΦqK using fun (p : Fin b) (j : Fin d) => hext (hQ j (eYD (Pi.single p 1)))
  choose Φc hΦc hΦcK using fun l : Fin 4 => hext (hGc (Pi.single l 1))
  choose Φc0 hΦc0 hΦc0K using fun l : Fin 4 => hext (hG0 (Pi.single l 1))
  choose Φcj hΦcj hΦcjK using fun (l : Fin 4) (j : Fin d) => hext (hGj j (Pi.single l 1))
  set Φbd : Fin a ⊕ Fin b → (Fin n → ℝ) → ℝ := Sum.elim Φb Φd with hΦbd
  have hΦbd' : ∀ i, ContDiff ℝ ∞ (Φbd i) := by
    intro i; rcases i with i | i
    · exact hΦb i
    · exact hΦd i
  obtain ⟨CM, hCM0, hCM⟩ := forcing_bound_comp (n := n) hm hk hΦbd' hΦq hΦc hΦc0 hΦcj hR
  refine ⟨2 * CM, by positivity, ?_⟩
  intro u hu hup RB RD C dtC hRB hRD hC hdtC pRB pRD pC pdtC hK t ht hEt F hF hFeq
  set RBD : Fin a ⊕ Fin b → ST d → ℝ := Sum.elim RB RD with hRBD
  have hRBD' : ∀ i, ContDiff ℝ ∞ (RBD i) := by
    intro i; rcases i with i | i
    · exact hRB i
    · exact hRD i
  have pRBD : ∀ i, IsSPeriodic (RBD i) := by
    intro i; rcases i with i | i
    · exact pRB i
    · exact pRD i
  have hbound := hCM u hu hup hRBD' hRD hC hdtC pRBD pRD pC pdtC t hEt
  have hFE : ContDiff ℝ ∞ (ActualJetForcing.forcingErr (fun i => compF (Φbd i) u) RBD
      (fun p j => compF (Φq p j) u) RD (fun l => compF (Φc l) u) (fun l => compF (Φc0 l) u)
      (fun l j => compF (Φcj l j) u) C dtC) := by
    unfold ActualJetForcing.forcingErr
    refine ContDiff.add (ContDiff.add (ContDiff.sum fun i _ => (contDiff_compF (hΦbd' i) hu).mul
      (hRBD' i)) (ContDiff.sum fun p _ => (contDiff_compF (hΦq p.1 p.2) hu).mul
      (contDiff_pd_top (hRD p.1) _))) (ContDiff.add (ContDiff.add (ContDiff.sum fun l _ =>
      (contDiff_compF (hΦc l) hu).mul (hC l)) (ContDiff.sum fun l _ =>
      (contDiff_compF (hΦc0 l) hu).mul (hdtC l))) (ContDiff.sum fun p _ =>
      (contDiff_compF (hΦcj p.1 p.2) hu).mul (contDiff_pd_top (hC p.1) _)))
  have hQeq : Q k F t = Q k (ActualJetForcing.forcingErr (fun i => compF (Φbd i) u) RBD
      (fun p j => compF (Φq p j) u) RD (fun l => compF (Φc l) u) (fun l => compF (Φc0 l) u)
      (fun l j => compF (Φcj l j) u) C dtC) t := by
    refine Q_congr_slab hF hFE (fun x hx => ?_) k ht
    have hv : (fun i => u i x) ∈ K' := hK x hx
    rw [hFeq x hx]
    unfold ActualJetForcing.forcingErr
    simp only [compF]
    have e3 : pZ (Gc (eX fun i => u i x) fun l => C l x) =
        ∑ l, pZ (Gc (eX fun i => u i x) (Pi.single l 1)) * C l x :=
      linear_coord LinearMap.id (Gc _) pZ _
    have e4 : pZ (G0 (eX fun i => u i x) fun l => dtC l x) =
        ∑ l, pZ (G0 (eX fun i => u i x) (Pi.single l 1)) * dtC l x :=
      linear_coord LinearMap.id (G0 _) pZ _
    rw [linear_coord eY (Bm _) pZ, linear_coord eYD (Dm _) pZ, e3, e4]
    have e1 : ∀ j, pZ (Qm j (eX fun i => u i x) (eYD fun i => pd (RD i) j.succ x)) =
        ∑ p, pZ (Qm j (eX fun i => u i x) (eYD (Pi.single p 1))) * pd (RD p) j.succ x :=
      fun j => linear_coord eYD (Qm j _) pZ _
    have e2 : ∀ j, pZ (Gj j (eX fun i => u i x) fun l => pd (C l) j.succ x) =
        ∑ l, pZ (Gj j (eX fun i => u i x) (Pi.single l 1)) * pd (C l) j.succ x :=
      fun j => linear_coord LinearMap.id (Gj j _) pZ _
    simp only [e1, e2]
    rw [Fintype.sum_sum_type]
    simp only [hRBD, hΦbd, Sum.elim_inl, Sum.elim_inr]
    simp only [hΦbK _ _ hv, hΦdK _ _ hv, hΦqK _ _ _ hv, hΦcK _ _ hv, hΦc0K _ _ hv,
      hΦcjK _ _ _ hv]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
      Finset.sum_comm (s := Finset.univ (α := Fin d)),
      Finset.sum_comm (s := Finset.univ (α := Fin d))]
    ring
  rw [hQeq]
  refine hbound.trans ?_
  rw [Fintype.sum_sum_type]
  simp only [hRBD, Sum.elim_inl, Sum.elim_inr]
  have hDk : ∑ i, Q k (RD i) t ≤ ∑ i, Q (k + 1) (RD i) t :=
    Finset.sum_le_sum fun i _ => Q_mono (Nat.le_succ k) (RD i) t
  have h1 : 0 ≤ ∑ i, Q k (RB i) t := Finset.sum_nonneg fun i _ => Q_nonneg k _ t
  have h2 : 0 ≤ ∑ i, Q k (RD i) t := Finset.sum_nonneg fun i _ => Q_nonneg k _ t
  have h3 : 0 ≤ ∑ l, Q (k + 1) (C l) t := Finset.sum_nonneg fun i _ => Q_nonneg _ _ t
  have h4 : 0 ≤ ∑ l, Q k (dtC l) t := Finset.sum_nonneg fun i _ => Q_nonneg k _ t
  nlinarith

end RenewalGeometry.SlabMoser
