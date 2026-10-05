/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.QuasilinearDifferenceStability
import RenewalGeometry.Continuum.SliceForcingBound

/-!
# Difference calculus on the slices: products, generators, time derivatives

Generic infrastructure (no renewal notions) for the curvature and stress recovery of
`prop:coupled-bootstrap` (`eq:bootstrap-curvature`) of the Einstein–Standard-Model action-closure
manuscript ("The equation bounds `∂_tW` in `L²_tH^{k-1}_x` by the same state and forcing
quantities. … All second metric derivatives then differ by `O(d)` in `L²_tH^{k-1}`").

* `Q_mul_sub_le` — `Q_j(f̂ĝ - fg) ≤ 2C_alg(Q_j(f̂)Q_j(ĝ - g) + Q_j(f̂ - f)Q_j(g))`;
* **`Q_genG_sub_le`** — the generator is Lipschitz from `H^k` to `H^{k-1}`:
  `Q_{k-1}(G(V)_a - G(U)_a) ≤ C ‖V - U‖²_{H^k}` on `H^k` balls with `U ∈ H^{k+1}`;
* `Q_genG_le` — `Q_{k-1}(G(U)_a) ≤ C(R)` on `H^k` balls.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.QLRecovery

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy QLDiff

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-- **Differences of products**: `Q_j(f̂ĝ - fg) ≤ 2C_alg(Q_j(f̂)Q_j(ĝ - g) + Q_j(f̂ - f)Q_j(g))`. -/
theorem Q_mul_sub_le {j m : ℕ} (hj : 2 * m ≤ j + 1) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    {f f' g g' : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hf' : ContDiff ℝ ∞ f') (hg : ContDiff ℝ ∞ g)
    (hg' : ContDiff ℝ ∞ g') (hpf : IsSPeriodic f) (hpf' : IsSPeriodic f') (hpg : IsSPeriodic g)
    (hpg' : IsSPeriodic g') (t : ℝ) :
    Q j (fun x => f' x * g' x - f x * g x) t ≤
      2 * algC d j CS * (Q j f' t * Q j (fun x => g' x - g x) t +
        Q j (fun x => f' x - f x) t * Q j g t) := by
  have e : (fun x => f' x * g' x - f x * g x) =
      fun x => f' x * (g' x - g x) + (f' x - f x) * g x := by
    funext x; ring
  rw [e]
  have h1 : ContDiff ℝ ∞ (fun x => f' x * (g' x - g x)) := hf'.mul (hg'.sub hg)
  have h2 : ContDiff ℝ ∞ (fun x => (f' x - f x) * g x) := (hf'.sub hf).mul hg
  have hdg : IsSPeriodic (fun x => g' x - g x) := fun k x => by simp only [hpg' k x, hpg k x]
  have hdf : IsSPeriodic (fun x => f' x - f x) := fun k x => by simp only [hpf' k x, hpf k x]
  refine (Q_add_le j h1 h2 t).trans ?_
  have a1 := Q_mul_le hj hCS hsup hf' (hg'.sub hg) hpf' hdg t
  have a2 := Q_mul_le hj hCS hsup (hf'.sub hf) hg hdf hpg t
  nlinarith [a1, a2]

/-- `Q_j` of a finite sum of `N` terms, crude form. -/
theorem Q_sum_le' (j : ℕ) {κ : Type*} [Fintype κ] {f : κ → ST d → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (t : ℝ) :
    Q j (fun x => ∑ i, f i x) t ≤ Fintype.card κ * ∑ i, Q j (f i) t := by
  have := Q_sum_le j (Finset.univ : Finset κ) hf t
  simpa [Finset.card_univ] using this

set_option maxHeartbeats 1000000 in
/-- **The generator is Lipschitz from `H^k` into `H^{k-1}`**: on `H^k` balls (and an `H^{k+1}`
bound for the reference), `Q_{k-1}(G(V)_a - G(U)_a) ≤ C ‖V - U‖²_{H^k}`. -/
theorem Q_genG_sub_le {m k : ℕ} (hm : (d : ℝ) / 2 < m) (hk : 2 * m ≤ k)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, ContDiff ℝ ∞ (v b)) → (∀ b, IsSPeriodic (u b)) → (∀ b, IsSPeriodic (v b)) → ∀ t,
      energyQ k u t + energyQ k v t ≤ R ^ 2 → energyQ (k + 1) u t ≤ R ^ 2 → ∀ a,
      Q (k - 1) (fun x => genG A F v a x - genG A F u a x) t ≤ C * energyQ k (subF v u) t := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    exact_mod_cast this
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk1 : 2 * m ≤ k' + 1 + 1 := by omega
  have hk'1 : 2 * m ≤ k' + 1 := by omega
  simp only [Nat.add_sub_cancel]
  have hCF := fun a => Q_compF_sub_le hm hk1 (hF a) hR
  choose CF hCF0 hCF using hCF
  have hCA := fun (p : Fin d × Fin n × Fin n) => Q_compF_sub_le hm hk1 (hA p.1 p.2.1 p.2.2) hR
  choose CA hCA0 hCA using hCA
  have hKA := fun (p : Fin d × Fin n × Fin n) =>
    SlabMoser.Q_compF_le hm hk1 (hA p.1 p.2.1 p.2.2) hR
  choose KA hKA0 hKA using hKA
  set CFs := ∑ a, CF a
  set CAs := ∑ p, CA p
  set KAs := ∑ p, KA p
  have hCFs0 : 0 ≤ CFs := Finset.sum_nonneg fun a _ => hCF0 a
  have hCAs0 : 0 ≤ CAs := Finset.sum_nonneg fun p _ => hCA0 p
  have hKAs0 : 0 ≤ KAs := Finset.sum_nonneg fun p _ => hKA0 p
  have hal := algC_nonneg (d := d) k' hCS
  have hal1 := algC_nonneg (d := d) (k' + 1) hCS
  set N : ℝ := 1 + d * n
  refine ⟨2 * (CFs + 2 * N * (d * n) * (algC d k' CS * KAs + algC d (k' + 1) CS * CAs * R ^ 2)),
    by positivity, ?_⟩
  intro u v hu hv hpu hpv t hE hE1 a
  set E := energyQ (k' + 1) (subF v u) t
  have hE0 : 0 ≤ E := energyQ_nonneg _ _ _
  have hEv : energyQ (k' + 1) v t ≤ R ^ 2 := by linarith [energyQ_nonneg (k' + 1) u t]
  have hw := contDiff_subF hu hv
  have hwp := isSPeriodic_subF hpu hpv
  have hQw : ∀ b, Q (k' + 1) (subF v u b) t ≤ E := fun b =>
    Finset.single_le_sum (f := fun b => Q (k' + 1) (subF v u b) t) (fun b _ => Q_nonneg _ _ t)
      (Finset.mem_univ b)
  have hAv : ∀ i a b, ContDiff ℝ ∞ (compF (A i a b) v) := fun i a b => contDiff_compF (hA i a b) hv
  have hAu : ∀ i a b, ContDiff ℝ ∞ (compF (A i a b) u) := fun i a b => contDiff_compF (hA i a b) hu
  have hAvp : ∀ i a b, IsSPeriodic (compF (A i a b) v) := fun i a b => isSPeriodic_compF _ hpv
  have hAup : ∀ i a b, IsSPeriodic (compF (A i a b) u) := fun i a b => isSPeriodic_compF _ hpu
  -- the decomposition of the generator difference
  rw [genG_sub_eq hu hv a]
  have hX : ContDiff ℝ ∞ (Xt F u v a) := (contDiff_compF (hF a) hv).sub (contDiff_compF (hF a) hu)
  have hP : ∀ i b, ContDiff ℝ ∞ (fun x => compF (A i a b) v x * pd (subF v u b) i.succ x) :=
    fun i b => (hAv i a b).mul (contDiff_pd_top (hw b) _)
  have hY : ∀ i b, ContDiff ℝ ∞ (Yt A u v i a b) := fun i b =>
    ((hAv i a b).sub (hAu i a b)).mul (contDiff_pd_top (hu b) _)
  have hS : ContDiff ℝ ∞ (fun x => ∑ i, ∑ b, (compF (A i a b) v x * pd (subF v u b) i.succ x +
      Yt A u v i a b x)) := ContDiff.sum fun i _ => ContDiff.sum fun b _ => (hP i b).add (hY i b)
  refine (Q_sub_le k' hX hS t).trans ?_
  have hXb : Q k' (Xt F u v a) t ≤ CFs * E :=
    (Q_mono (Nat.le_succ k') _ t).trans ((hCF a u v hu hv hpu hpv t hE).trans
      (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := CF) (fun a _ => hCF0 a)
        (Finset.mem_univ a)) hE0))
  have hPb : ∀ i b, Q k' (fun x => compF (A i a b) v x * pd (subF v u b) i.succ x) t ≤
      algC d k' CS * KAs * E := by
    intro i b
    refine (Q_mul_le hk'1 hCS hsup (hAv i a b) (contDiff_pd_top (hw b) _) (hAvp i a b)
      (isSPeriodic_pd (hwp b) _) t).trans ?_
    have h1 : Q k' (compF (A i a b) v) t ≤ KAs :=
      (Q_mono (Nat.le_succ k') _ t).trans ((hKA (i, a, b) v hv hpv t hEv).trans
        (Finset.single_le_sum (f := KA) (fun p _ => hKA0 p) (Finset.mem_univ (i, a, b))))
    have h2 : Q k' (pd (subF v u b) i.succ) t ≤ E := (Q_pd_le i _ t).trans (hQw b)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hal) h2 (Q_nonneg _ _ _)
      (mul_nonneg hal hKAs0)
  have hYb : ∀ i b, Q k' (Yt A u v i a b) t ≤ algC d (k' + 1) CS * CAs * R ^ 2 * E := by
    intro i b
    refine (Q_mono (Nat.le_succ k') _ t).trans ?_
    have hdiff : ContDiff ℝ ∞ (fun x => compF (A i a b) v x - compF (A i a b) u x) :=
      (hAv i a b).sub (hAu i a b)
    have hdp : IsSPeriodic (fun x => compF (A i a b) v x - compF (A i a b) u x) :=
      fun k x => by simp only [hAvp i a b k x, hAup i a b k x]
    have h1 := Q_mul_le hk1 hCS hsup hdiff (contDiff_pd_top (hu b) i.succ) hdp
      (isSPeriodic_pd (hpu b) _) t
    have h2 : Q (k' + 1) (fun x => compF (A i a b) v x - compF (A i a b) u x) t ≤ CAs * E :=
      (hCA (i, a, b) u v hu hv hpu hpv t hE).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := CA) (fun p _ => hCA0 p) (Finset.mem_univ _)) hE0)
    have h3 : Q (k' + 1) (pd (u b) i.succ) t ≤ R ^ 2 :=
      (Q_pd_le i _ t).trans ((Finset.single_le_sum (f := fun b => Q (k' + 1 + 1) (u b) t)
        (fun b _ => Q_nonneg _ _ t) (Finset.mem_univ b)).trans hE1)
    calc Q (k' + 1) (Yt A u v i a b) t ≤ algC d (k' + 1) CS *
          Q (k' + 1) (fun x => compF (A i a b) v x - compF (A i a b) u x) t *
          Q (k' + 1) (pd (u b) i.succ) t := h1
      _ ≤ algC d (k' + 1) CS * (CAs * E) * R ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 hal1) h3 (Q_nonneg _ _ _)
            (mul_nonneg hal1 (mul_nonneg hCAs0 hE0))
      _ = algC d (k' + 1) CS * CAs * R ^ 2 * E := by ring
  have hSb : Q k' (fun x => ∑ i, ∑ b, (compF (A i a b) v x * pd (subF v u b) i.succ x +
      Yt A u v i a b x)) t ≤ 2 * (d * n) * (d * n) * ((algC d k' CS * KAs +
        algC d (k' + 1) CS * CAs * R ^ 2) * E) := by
    set B := (algC d k' CS * KAs + algC d (k' + 1) CS * CAs * R ^ 2) * E with hBdef
    have hterm : ∀ i b, Q k' (fun x => compF (A i a b) v x * pd (subF v u b) i.succ x +
        Yt A u v i a b x) t ≤ 2 * B := by
      intro i b
      refine (Q_add_le k' (hP i b) (hY i b) t).trans ?_
      have := hPb i b
      have := hYb i b
      rw [hBdef]; nlinarith
    have hrow : ∀ i, ContDiff ℝ ∞ (fun x => ∑ b, (compF (A i a b) v x *
        pd (subF v u b) i.succ x + Yt A u v i a b x)) := fun i =>
      ContDiff.sum fun b _ => (hP i b).add (hY i b)
    have h1 := Q_sum_le' (f := fun i x => ∑ b, (compF (A i a b) v x *
        pd (subF v u b) i.succ x + Yt A u v i a b x)) k' hrow t
    have h2 : ∀ i, Q k' (fun x => ∑ b, (compF (A i a b) v x *
        pd (subF v u b) i.succ x + Yt A u v i a b x)) t ≤ n * (n * (2 * B)) := by
      intro i
      have := Q_sum_le' (f := fun b x => compF (A i a b) v x * pd (subF v u b) i.succ x +
        Yt A u v i a b x) k' (fun b => (hP i b).add (hY i b)) t
      simp only [Fintype.card_fin] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
      calc ∑ b, Q k' (fun x => compF (A i a b) v x * pd (subF v u b) i.succ x +
            Yt A u v i a b x) t ≤ ∑ _b : Fin n, 2 * B := Finset.sum_le_sum fun b _ => hterm i b
        _ = n * (2 * B) := by simp
    simp only [Fintype.card_fin] at h1
    have hB0 : 0 ≤ B := by rw [hBdef]; positivity
    calc _ ≤ (d : ℝ) * ∑ i, Q k' (fun x => ∑ b, (compF (A i a b) v x *
          pd (subF v u b) i.succ x + Yt A u v i a b x)) t := h1
      _ ≤ (d : ℝ) * ∑ _i : Fin d, (n * (n * (2 * B))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h2 i) (Nat.cast_nonneg _)
      _ = (d : ℝ) * (d * (n * (n * (2 * B)))) := by simp
      _ ≤ 2 * (d * n) * (d * n) * B := by nlinarith [sq_nonneg ((d : ℝ) * n)]
  have hN1 : (d : ℝ) * n ≤ N := by simp only [N]; linarith
  have hdn : (0 : ℝ) ≤ d * n := by positivity
  have hB0 : 0 ≤ (algC d k' CS * KAs + algC d (k' + 1) CS * CAs * R ^ 2) * E := by positivity
  calc 2 * Q k' (Xt F u v a) t + 2 * Q k' (fun x => ∑ i, ∑ b,
        (compF (A i a b) v x * pd (subF v u b) i.succ x + Yt A u v i a b x)) t
      ≤ 2 * (CFs * E) + 2 * (2 * (d * n) * (d * n) * ((algC d k' CS * KAs +
          algC d (k' + 1) CS * CAs * R ^ 2) * E)) := by linarith
    _ ≤ 2 * (CFs * E) + 2 * (2 * N * (d * n) * ((algC d k' CS * KAs +
          algC d (k' + 1) CS * CAs * R ^ 2) * E)) := by
        have : 2 * (d * n) * (d * n) * ((algC d k' CS * KAs + algC d (k' + 1) CS * CAs * R ^ 2) *
            E) ≤ 2 * N * (d * n) * ((algC d k' CS * KAs + algC d (k' + 1) CS * CAs * R ^ 2) * E) := by
          have h2 : 2 * ((d : ℝ) * n) ≤ 2 * N := by linarith
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hdn) hB0
          linarith
        linarith
    _ = 2 * (CFs + 2 * N * (d * n) * (algC d k' CS * KAs + algC d (k' + 1) CS * CAs * R ^ 2)) *
          E := by ring

set_option maxHeartbeats 1000000 in
/-- **The generator is bounded from `H^k` into `H^{k-1}`** on `H^k` balls. -/
theorem Q_genG_le {m k : ℕ} (hm : (d : ℝ) / 2 < m) (hk : 2 * m ≤ k)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, IsSPeriodic (u b)) → ∀ t, energyQ k u t ≤ R ^ 2 → ∀ a,
      Q (k - 1) (genG A F u a) t ≤ C := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    exact_mod_cast this
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk1 : 2 * m ≤ k' + 1 + 1 := by omega
  have hk'1 : 2 * m ≤ k' + 1 := by omega
  simp only [Nat.add_sub_cancel]
  have hKF := fun a => SlabMoser.Q_compF_le hm hk1 (hF a) hR
  choose KF hKF0 hKF using hKF
  have hKA := fun (p : Fin d × Fin n × Fin n) =>
    SlabMoser.Q_compF_le hm hk1 (hA p.1 p.2.1 p.2.2) hR
  choose KA hKA0 hKA using hKA
  set KFs := ∑ a, KF a
  set KAs := ∑ p, KA p
  have hKFs0 : 0 ≤ KFs := Finset.sum_nonneg fun a _ => hKF0 a
  have hKAs0 : 0 ≤ KAs := Finset.sum_nonneg fun p _ => hKA0 p
  have hal := algC_nonneg (d := d) k' hCS
  refine ⟨2 * KFs + 2 * ((d * n : ℕ) * ((d * n : ℕ) * (algC d k' CS * KAs * R ^ 2))),
    by positivity, ?_⟩
  intro u hu hup t hE a
  have hFc := contDiff_compF (hF a) hu
  have hP : ∀ i b, ContDiff ℝ ∞ (fun x => compF (A i a b) u x * pd (u b) i.succ x) := fun i b =>
    (contDiff_compF (hA i a b) hu).mul (contDiff_pd_top (hu b) _)
  have hrow : ∀ i, ContDiff ℝ ∞ (fun x => ∑ b, compF (A i a b) u x * pd (u b) i.succ x) :=
    fun i => ContDiff.sum fun b _ => hP i b
  unfold genG
  refine (Q_sub_le k' hFc (ContDiff.sum fun i _ => hrow i) t).trans ?_
  have h1 : Q k' (compF (F a) u) t ≤ KFs :=
    (Q_mono (Nat.le_succ k') _ t).trans ((hKF a u hu hup t hE).trans
      (Finset.single_le_sum (f := KF) (fun a _ => hKF0 a) (Finset.mem_univ a)))
  have hterm : ∀ i b, Q k' (fun x => compF (A i a b) u x * pd (u b) i.succ x) t ≤
      algC d k' CS * KAs * R ^ 2 := by
    intro i b
    refine (Q_mul_le hk'1 hCS hsup (contDiff_compF (hA i a b) hu)
      (contDiff_pd_top (hu b) _) (isSPeriodic_compF _ hup) (isSPeriodic_pd (hup b) _)
      t).trans ?_
    have hq1 : Q k' (compF (A i a b) u) t ≤ KAs :=
      (Q_mono (Nat.le_succ k') _ t).trans ((hKA (i, a, b) u hu hup t hE).trans
        (Finset.single_le_sum (f := KA) (fun p _ => hKA0 p) (Finset.mem_univ _)))
    have hq2 : Q k' (pd (u b) i.succ) t ≤ R ^ 2 :=
      (Q_pd_le i _ t).trans ((Finset.single_le_sum (f := fun b => Q (k' + 1) (u b) t)
        (fun b _ => Q_nonneg _ _ t) (Finset.mem_univ b)).trans hE)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hq1 hal) hq2 (Q_nonneg _ _ _)
      (mul_nonneg hal hKAs0)
  have hS1 := Q_sum_le' (f := fun i x => ∑ b, compF (A i a b) u x * pd (u b) i.succ x) k' hrow t
  have hS2 : ∀ i, Q k' (fun x => ∑ b, compF (A i a b) u x * pd (u b) i.succ x) t ≤
      n * (n * (algC d k' CS * KAs * R ^ 2)) := by
    intro i
    have := Q_sum_le' (f := fun b x => compF (A i a b) u x * pd (u b) i.succ x) k' (hP i) t
    simp only [Fintype.card_fin] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    calc ∑ b, Q k' (fun x => compF (A i a b) u x * pd (u b) i.succ x) t
        ≤ ∑ _b : Fin n, algC d k' CS * KAs * R ^ 2 := Finset.sum_le_sum fun b _ => hterm i b
      _ = n * (algC d k' CS * KAs * R ^ 2) := by simp
  simp only [Fintype.card_fin] at hS1
  have hX0 : 0 ≤ algC d k' CS * KAs * R ^ 2 := by positivity
  have h2 : Q k' (fun x => ∑ i, ∑ b, compF (A i a b) u x * pd (u b) i.succ x) t ≤
      (d * n : ℕ) * ((d * n : ℕ) * (algC d k' CS * KAs * R ^ 2)) := by
    calc _ ≤ (d : ℝ) * ∑ i, Q k' (fun x => ∑ b, compF (A i a b) u x * pd (u b) i.succ x) t := hS1
      _ ≤ (d : ℝ) * ∑ _i : Fin d, (n * (n * (algC d k' CS * KAs * R ^ 2))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hS2 i) (Nat.cast_nonneg _)
      _ = (d : ℝ) * (d * (n * (n * (algC d k' CS * KAs * R ^ 2)))) := by simp
      _ ≤ _ := by push_cast; nlinarith [sq_nonneg ((d : ℝ) * n), sq_nonneg (n : ℝ)]
  linarith


/-! ### Affine expressions in the first derivatives of the state -/

/-- The time and space derivatives of the difference on a slice where both fields solve the
system (the reference exactly, the approximate one with defect `e`):
`Q_{k-1}(∂_δ(v_b - u_b))(t) ≤ (2C_G + 1)‖v - u‖²_{H^k} + 2‖e‖²_{H^k}`. -/
theorem Q_pd_sub_slice {m k : ℕ} (hk1 : 1 ≤ k)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {u v e : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (hv : ∀ b, ContDiff ℝ ∞ (v b))
    (he : ∀ b, ContDiff ℝ ∞ (e b)) {t CG : ℝ}
    (hU : ∀ a, ∀ x : ST d, x 0 = t → pd (u a) 0 x = genG A F u a x)
    (hV : ∀ a, ∀ x : ST d, x 0 = t → pd (v a) 0 x = genG A F v a x + e a x)
    (hG : ∀ a, Q (k - 1) (fun x => genG A F v a x - genG A F u a x) t ≤
      CG * energyQ k (subF v u) t)
    (δ : Fin (d + 1)) (b : Fin n) :
    Q (k - 1) (pd (subF v u b) δ) t ≤
      (2 * CG + 1) * energyQ k (subF v u) t + 2 * energyQ k e t := by
  have hw := contDiff_subF hu hv
  have hE0 := energyQ_nonneg k (subF v u) t
  have hEe0 := energyQ_nonneg k e t
  have hQw : Q k (subF v u b) t ≤ energyQ k (subF v u) t :=
    Finset.single_le_sum (f := fun b => Q k (subF v u b) t) (fun b _ => Q_nonneg k _ t)
      (Finset.mem_univ b)
  have hQe : Q k (e b) t ≤ energyQ k e t :=
    Finset.single_le_sum (f := fun b => Q k (e b) t) (fun b _ => Q_nonneg k _ t)
      (Finset.mem_univ b)
  have hCG0 : 0 ≤ CG * energyQ k (subF v u) t := (Q_nonneg _ _ _).trans (hG b)
  induction δ using Fin.cases with
  | zero =>
    have hgs : ContDiff ℝ ∞ (fun x => genG A F v b x - genG A F u b x) :=
      (contDiff_genG hA hF hv b).sub (contDiff_genG hA hF hu b)
    have hcong := SliceForcing.Q_congr_slice (contDiff_pd_top (hw b) 0) (hgs.add (he b)) t
      (fun y => by
        rw [QLDiff.pd_sub_eq (hv b) (hu b), hV b _ rfl, hU b _ rfl]; ring) (k - 1)
    rw [hcong]
    refine (Q_add_le (k - 1) hgs (he b) t).trans ?_
    have h1 := hG b
    have h2 : Q (k - 1) (e b) t ≤ energyQ k e t := (Q_mono (Nat.sub_le k 1) _ t).trans hQe
    nlinarith
  | succ j =>
    have h1 : Q (k - 1) (pd (subF v u b) j.succ) t ≤ Q (k - 1 + 1) (subF v u b) t :=
      Q_pd_le j _ t
    rw [Nat.sub_add_cancel hk1] at h1
    nlinarith

/-- The derivatives of a solution on a slice: `Q_{k-1}(∂_δu_b)(t) ≤ R² + C_G0`. -/
theorem Q_pd_ref_slice {k : ℕ} (hk1 : 1 ≤ k)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) {t R CG0 : ℝ}
    (hU : ∀ a, ∀ x : ST d, x 0 = t → pd (u a) 0 x = genG A F u a x)
    (hEu : energyQ k u t ≤ R ^ 2) (hG0 : ∀ a, Q (k - 1) (genG A F u a) t ≤ CG0)
    (δ : Fin (d + 1)) (b : Fin n) : Q (k - 1) (pd (u b) δ) t ≤ R ^ 2 + CG0 := by
  have hQu : Q k (u b) t ≤ R ^ 2 :=
    (Finset.single_le_sum (f := fun b => Q k (u b) t) (fun b _ => Q_nonneg k _ t)
      (Finset.mem_univ b)).trans hEu
  have hR0 : 0 ≤ R ^ 2 := sq_nonneg R
  induction δ using Fin.cases with
  | zero =>
    have hcong := SliceForcing.Q_congr_slice (contDiff_pd_top (hu b) 0)
      (contDiff_genG hA hF hu b) t (fun y => hU b _ rfl) (k - 1)
    rw [hcong]
    linarith [hG0 b]
  | succ j =>
    have h1 : Q (k - 1) (pd (u b) j.succ) t ≤ Q (k - 1 + 1) (u b) t := Q_pd_le j _ t
    rw [Nat.sub_add_cancel hk1] at h1
    have := (Q_nonneg (k - 1) (genG A F u b) t).trans (hG0 b)
    linarith

set_option maxHeartbeats 2000000 in
/-- **Affine expressions in the first derivatives of the state** (curvature recovery): for smooth
coefficient maps `P₀`, `P₁` there is `C` such that on a slice where the reference solves the system
and the approximate field solves it with defect `e`,
`Q_{k-1}((P₀(V) + Σ_p P₁^p(V)∂_pV) - (P₀(U) + Σ_p P₁^p(U)∂_pU))(t) ≤ C(‖V - U‖²_{H^k} +
‖e‖²_{H^k})`. -/
theorem affine_slice_bound {m k : ℕ} (hm : (d : ℝ) / 2 < m) (hk : 2 * m ≤ k)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {P0 : (Fin n → ℝ) → ℝ} {P1 : Fin (d + 1) × Fin n → (Fin n → ℝ) → ℝ}
    (hP0 : ContDiff ℝ ∞ P0) (hP1 : ∀ p, ContDiff ℝ ∞ (P1 p)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v e : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, ContDiff ℝ ∞ (v b)) → (∀ b, ContDiff ℝ ∞ (e b)) → (∀ b, IsSPeriodic (u b)) →
      (∀ b, IsSPeriodic (v b)) → ∀ t, energyQ k u t + energyQ k v t ≤ R ^ 2 →
      energyQ (k + 1) u t ≤ R ^ 2 →
      (∀ a, ∀ x : ST d, x 0 = t → pd (u a) 0 x = genG A F u a x) →
      (∀ a, ∀ x : ST d, x 0 = t → pd (v a) 0 x = genG A F v a x + e a x) →
      Q (k - 1) (fun x => (P0 (fun b => v b x) +
          ∑ p : Fin (d + 1) × Fin n, P1 p (fun b => v b x) * pd (v p.2) p.1 x) -
        (P0 (fun b => u b x) + ∑ p : Fin (d + 1) × Fin n,
          P1 p (fun b => u b x) * pd (u p.2) p.1 x)) t ≤
        C * (energyQ k (subF v u) t + energyQ k e t) := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    exact_mod_cast this
  have hk1 : 2 * m ≤ k + 1 := by omega
  have hkm1 : 2 * m ≤ k - 1 + 1 := by omega
  have hkk : k - 1 ≤ k := Nat.sub_le k 1
  obtain ⟨C0, hC00, hC0⟩ := Q_compF_sub_le hm hk1 hP0 hR
  have hC1 := fun p => Q_compF_sub_le hm hk1 (hP1 p) hR
  choose C1 hC10 hC1 using hC1
  have hK1 := fun p => SlabMoser.Q_compF_le hm hk1 (hP1 p) hR
  choose K1 hK10 hK1 using hK1
  obtain ⟨CG, hCG0, hCG⟩ := Q_genG_sub_le hm hk hA hF hR
  obtain ⟨CG0, hCG00, hCG0'⟩ := Q_genG_le hm hk hA hF hR
  set C1s := ∑ p, C1 p
  set K1s := ∑ p, K1 p
  have hC1s : 0 ≤ C1s := Finset.sum_nonneg fun p _ => hC10 p
  have hK1s : 0 ≤ K1s := Finset.sum_nonneg fun p _ => hK10 p
  have hal := algC_nonneg (d := d) (k - 1) hCS
  set N : ℝ := (Fintype.card (Fin (d + 1) × Fin n) : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  set B := 2 * algC d (k - 1) CS * (K1s * (2 * CG + 1) + C1s * (R ^ 2 + CG0)) with hBdef
  set Be := 2 * algC d (k - 1) CS * (K1s * 2) with hBedef
  have hB0 : 0 ≤ B := by positivity
  have hBe0 : 0 ≤ Be := by positivity
  refine ⟨2 * C0 + 2 * N * (N * (B + Be)), by positivity, ?_⟩
  intro u v e hu hv he hpu hpv t hE hE1 hU hV
  set E := energyQ k (subF v u) t
  set Ee := energyQ k e t
  have hE0 : 0 ≤ E := energyQ_nonneg _ _ _
  have hEe0 : 0 ≤ Ee := energyQ_nonneg _ _ _
  have hEu : energyQ k u t ≤ R ^ 2 := by linarith [energyQ_nonneg k v t]
  have hEv : energyQ k v t ≤ R ^ 2 := by linarith [energyQ_nonneg k u t]
  have hGd : ∀ a, Q (k - 1) (fun x => genG A F v a x - genG A F u a x) t ≤ CG * E :=
    fun a => hCG u v hu hv hpu hpv t hE hE1 a
  have hG0 : ∀ a, Q (k - 1) (genG A F u a) t ≤ CG0 := fun a => hCG0' u hu hpu t hEu a
  have hw := contDiff_subF hu hv
  -- the pieces
  have hP0v := contDiff_compF hP0 hv
  have hP0u := contDiff_compF hP0 hu
  have hP1v : ∀ p, ContDiff ℝ ∞ (compF (P1 p) v) := fun p => contDiff_compF (hP1 p) hv
  have hP1u : ∀ p, ContDiff ℝ ∞ (compF (P1 p) u) := fun p => contDiff_compF (hP1 p) hu
  have hprod : ∀ p, ContDiff ℝ ∞ (fun x => compF (P1 p) v x * pd (v p.2) p.1 x -
      compF (P1 p) u x * pd (u p.2) p.1 x) := fun p =>
    ((hP1v p).mul (contDiff_pd_top (hv p.2) _)).sub ((hP1u p).mul (contDiff_pd_top (hu p.2) _))
  have heq : (fun x => (P0 (fun b => v b x) +
      ∑ p : Fin (d + 1) × Fin n, P1 p (fun b => v b x) * pd (v p.2) p.1 x) -
      (P0 (fun b => u b x) + ∑ p : Fin (d + 1) × Fin n,
        P1 p (fun b => u b x) * pd (u p.2) p.1 x)) =
      fun x => (compF P0 v x - compF P0 u x) + ∑ p : Fin (d + 1) × Fin n,
        (compF (P1 p) v x * pd (v p.2) p.1 x - compF (P1 p) u x * pd (u p.2) p.1 x) := by
    funext x
    simp only [compF, Finset.sum_sub_distrib]
    ring
  rw [heq]
  refine (Q_add_le (k - 1) (hP0v.sub hP0u) (ContDiff.sum fun p _ => hprod p) t).trans ?_
  have hA0 : Q (k - 1) (fun x => compF P0 v x - compF P0 u x) t ≤ C0 * E :=
    (Q_mono hkk _ t).trans (hC0 u v hu hv hpu hpv t hE)
  have hterm : ∀ p : Fin (d + 1) × Fin n, Q (k - 1) (fun x => compF (P1 p) v x *
      pd (v p.2) p.1 x - compF (P1 p) u x * pd (u p.2) p.1 x) t ≤ B * E + Be * Ee := by
    intro p
    refine (Q_mul_sub_le hkm1 hCS hsup (hP1u p) (hP1v p) (contDiff_pd_top (hu p.2) _)
      (contDiff_pd_top (hv p.2) _) (isSPeriodic_compF _ hpu) (isSPeriodic_compF _ hpv)
      (isSPeriodic_pd (hpu p.2) _) (isSPeriodic_pd (hpv p.2) _) t).trans ?_
    have h1 : Q (k - 1) (compF (P1 p) v) t ≤ K1s :=
      (Q_mono hkk _ t).trans ((hK1 p v hv hpv t hEv).trans
        (Finset.single_le_sum (f := K1) (fun p _ => hK10 p) (Finset.mem_univ p)))
    have hdd : (fun x => pd (v p.2) p.1 x - pd (u p.2) p.1 x) = pd (subF v u p.2) p.1 :=
      funext fun x => (QLDiff.pd_sub_eq (hv p.2) (hu p.2) p.1 x).symm
    have h2 : Q (k - 1) (fun x => pd (v p.2) p.1 x - pd (u p.2) p.1 x) t ≤
        (2 * CG + 1) * E + 2 * Ee := by
      rw [hdd]
      exact Q_pd_sub_slice (m := m) (by omega) hA hF hu hv he hU hV hGd p.1 p.2
    have h3 : Q (k - 1) (fun x => compF (P1 p) v x - compF (P1 p) u x) t ≤ C1s * E :=
      (Q_mono hkk _ t).trans ((hC1 p u v hu hv hpu hpv t hE).trans
        (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := C1) (fun p _ => hC10 p)
          (Finset.mem_univ p)) hE0))
    have h4 : Q (k - 1) (pd (u p.2) p.1) t ≤ R ^ 2 + CG0 :=
      Q_pd_ref_slice (by omega) hA hF hu hU hEu hG0 p.1 p.2
    have hq1 := Q_nonneg (k - 1) (compF (P1 p) v) t
    have hq2 := Q_nonneg (k - 1) (fun x => pd (v p.2) p.1 x - pd (u p.2) p.1 x) t
    have hq3 := Q_nonneg (k - 1) (fun x => compF (P1 p) v x - compF (P1 p) u x) t
    have hq4 := Q_nonneg (k - 1) (pd (u p.2) p.1) t
    have e1 : Q (k - 1) (compF (P1 p) v) t * Q (k - 1)
        (fun x => pd (v p.2) p.1 x - pd (u p.2) p.1 x) t ≤ K1s * ((2 * CG + 1) * E + 2 * Ee) :=
      mul_le_mul h1 h2 hq2 hK1s
    have e2 : Q (k - 1) (fun x => compF (P1 p) v x - compF (P1 p) u x) t *
        Q (k - 1) (pd (u p.2) p.1) t ≤ C1s * E * (R ^ 2 + CG0) :=
      mul_le_mul h3 h4 hq4 (mul_nonneg hC1s hE0)
    calc 2 * algC d (k - 1) CS * (Q (k - 1) (compF (P1 p) v) t *
          Q (k - 1) (fun x => pd (v p.2) p.1 x - pd (u p.2) p.1 x) t +
          Q (k - 1) (fun x => compF (P1 p) v x - compF (P1 p) u x) t *
            Q (k - 1) (pd (u p.2) p.1) t)
        ≤ 2 * algC d (k - 1) CS * (K1s * ((2 * CG + 1) * E + 2 * Ee) +
            C1s * E * (R ^ 2 + CG0)) := by gcongr
      _ = B * E + Be * Ee := by rw [hBdef, hBedef]; ring
  have hsum := Q_sum_le' (f := fun p x => compF (P1 p) v x * pd (v p.2) p.1 x -
    compF (P1 p) u x * pd (u p.2) p.1 x) (k - 1) hprod t
  have hsum2 : ∑ p : Fin (d + 1) × Fin n, Q (k - 1) (fun x => compF (P1 p) v x *
      pd (v p.2) p.1 x - compF (P1 p) u x * pd (u p.2) p.1 x) t ≤ N * (B * E + Be * Ee) := by
    calc _ ≤ ∑ _p : Fin (d + 1) × Fin n, (B * E + Be * Ee) := Finset.sum_le_sum fun p _ => hterm p
      _ = N * (B * E + Be * Ee) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hX : 0 ≤ B * E + Be * Ee := by positivity
  have hfin : Q (k - 1) (fun x => ∑ p : Fin (d + 1) × Fin n, (compF (P1 p) v x *
      pd (v p.2) p.1 x - compF (P1 p) u x * pd (u p.2) p.1 x)) t ≤ N * (N * (B * E + Be * Ee)) :=
    hsum.trans (mul_le_mul_of_nonneg_left hsum2 hN)
  have hBE : N * (N * (B * E + Be * Ee)) ≤ N * (N * (B + Be)) * (E + Ee) := by
    have : B * E + Be * Ee ≤ (B + Be) * (E + Ee) := by nlinarith
    have hNN : 0 ≤ N * N := mul_nonneg hN hN
    nlinarith
  nlinarith

/-- **Affine expressions in the residuals** (stress recovery): for smooth coefficient maps
`Q₀`, `Q₁^i`, `Q_k((Q₀(V) - Σ_i r_iQ₁^i(V)) - Q₀(U))(t) ≤ C(‖V - U‖²_{H^k} + Σ_i Q_k(r_i)(t))`. -/
theorem affineRes_slice_bound {m k : ℕ} (hm : (d : ℝ) / 2 < m) (hk : 2 * m ≤ k + 1)
    {ι : Type*} [Fintype ι] {Q0 : (Fin n → ℝ) → ℝ} {Q1 : ι → (Fin n → ℝ) → ℝ}
    (hQ0 : ContDiff ℝ ∞ Q0) (hQ1 : ∀ i, ContDiff ℝ ∞ (Q1 i)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Fin n → ST d → ℝ, ∀ r : ι → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, ContDiff ℝ ∞ (v b)) → (∀ i, ContDiff ℝ ∞ (r i)) → (∀ b, IsSPeriodic (u b)) →
      (∀ b, IsSPeriodic (v b)) → (∀ i, IsSPeriodic (r i)) → ∀ t,
      energyQ k u t + energyQ k v t ≤ R ^ 2 →
      Q k (fun x => (Q0 (fun b => v b x) - ∑ i, r i x * Q1 i (fun b => v b x)) -
        Q0 (fun b => u b x)) t ≤ C * (energyQ k (subF v u) t + ∑ i, Q k (r i) t) := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  obtain ⟨C0, hC00, hC0⟩ := Q_compF_sub_le hm hk hQ0 hR
  have hK1 := fun i => SlabMoser.Q_compF_le hm hk (hQ1 i) hR
  choose K1 hK10 hK1 using hK1
  set K1s := ∑ i, K1 i
  have hK1s : 0 ≤ K1s := Finset.sum_nonneg fun i _ => hK10 i
  have hal := algC_nonneg (d := d) k hCS
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨2 * C0 + 2 * N * (algC d k CS * K1s), by positivity, ?_⟩
  intro u v r hu hv hr hpu hpv hpr t hE
  have hEv : energyQ k v t ≤ R ^ 2 := by linarith [energyQ_nonneg k u t]
  have hQ0v := contDiff_compF hQ0 hv
  have hQ0u := contDiff_compF hQ0 hu
  have hP : ∀ i, ContDiff ℝ ∞ (fun x => r i x * compF (Q1 i) v x) := fun i =>
    (hr i).mul (contDiff_compF (hQ1 i) hv)
  have heq : (fun x => (Q0 (fun b => v b x) - ∑ i, r i x * Q1 i (fun b => v b x)) -
      Q0 (fun b => u b x)) = fun x => 1 * (compF Q0 v x - compF Q0 u x) +
        (-1) * ∑ i, r i x * compF (Q1 i) v x := by
    funext x; simp only [compF]; ring
  rw [heq]
  refine (Q_lincomb_le k (f := fun x => compF Q0 v x - compF Q0 u x)
    (g := fun x => ∑ i, r i x * compF (Q1 i) v x) (hQ0v.sub hQ0u)
    (ContDiff.sum fun i _ => hP i) 1 (-1) t).trans ?_
  have hA0 := hC0 u v hu hv hpu hpv t hE
  have hterm : ∀ i, Q k (fun x => r i x * compF (Q1 i) v x) t ≤ algC d k CS * K1s * Q k (r i) t := by
    intro i
    refine (Q_mul_le hk hCS hsup (hr i) (contDiff_compF (hQ1 i) hv) (hpr i)
      (isSPeriodic_compF _ hpv) t).trans ?_
    have h1 : Q k (compF (Q1 i) v) t ≤ K1s := (hK1 i v hv hpv t hEv).trans
      (Finset.single_le_sum (f := K1) (fun i _ => hK10 i) (Finset.mem_univ i))
    have := Q_nonneg k (r i) t
    calc algC d k CS * Q k (r i) t * Q k (compF (Q1 i) v) t ≤ algC d k CS * Q k (r i) t * K1s :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = algC d k CS * K1s * Q k (r i) t := by ring
  have hsum := Q_sum_le' (f := fun i x => r i x * compF (Q1 i) v x) k hP t
  have hsum2 : ∑ i, Q k (fun x => r i x * compF (Q1 i) v x) t ≤
      algC d k CS * K1s * ∑ i, Q k (r i) t := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hterm i
  have hE0 := energyQ_nonneg k (subF v u) t
  have hr0 : 0 ≤ ∑ i, Q k (r i) t := Finset.sum_nonneg fun i _ => Q_nonneg _ _ _
  have h3 : Q k (fun x => ∑ i, r i x * compF (Q1 i) v x) t ≤
      N * (algC d k CS * K1s * ∑ i, Q k (r i) t) := hsum.trans (mul_le_mul_of_nonneg_left hsum2 hN)
  have hX : 0 ≤ algC d k CS * K1s := by positivity
  norm_num
  nlinarith [mul_nonneg hN (mul_nonneg hX hr0), mul_nonneg hC00 hr0,
    mul_nonneg (mul_nonneg hN hX) hE0]
end RenewalGeometry.QLRecovery
