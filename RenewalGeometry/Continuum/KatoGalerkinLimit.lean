/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoGalerkinODE
import RenewalGeometry.Analysis.SobolevChainRule

/-!
# Kato's local existence theorem through the spectral Galerkin limit

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` and
`lem:generated-physical-identification` (Einstein–Standard-Model action-closure manuscript,
`app:generated-dynamics`): the cutoff-uniform Galerkin solutions of `KatoGalerkinODE` converge,
and the limit is a classical solution of the quasilinear symmetric hyperbolic system
`∂_tU + Σ_i A^i(U)∂_iU = F(U)` on `[0, T] × 𝕋^d`.

* `wq_tail`: high modes carry large weights, `k ∉ box K ⇒ wq r k (2π(K+1))^{2j} ≤ wq (r+j) k`;
  `Q_tfs_split` (frequency splitting): `Q_{m+1}` of a trigonometric field is bounded by its `L²`
  norm on low modes plus a small multiple of its `H^q` norm (`q ≥ m + 2`).
* `sym_L2_diff` — **the symmetric `L²` difference estimate**:
  `⟨U - V, G(U) - G(V)⟩_{L²} ≤ K₁ ‖U - V‖²_{L²}` for smooth periodic fields with `W^{1,∞}`
  bounds (symmetric integration by parts for the principal part).
* `galerkin_L2_cauchy` — **the Galerkin solutions are Cauchy in `C_tL²` with rate**
  `sup_t ‖U_N(t) - U_M(t)‖²_{L²} ≤ C (2π(N+1))^{-q}` (`N ≤ M`).
* `galerkin_unif_cauchy` — for `q ≥ m + 2`, the Galerkin fields **and their first spatial
  derivatives** are uniformly Cauchy on `[0, T] × ℝ^d` (frequency splitting + slice Sobolev).
-/

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.KatoGalerkin

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### Weights of high modes and frequency splitting -/

theorem muL_append (L₁ L₂ : List (Fin d)) (k : Fin d → ℤ) :
    muL (L₁ ++ L₂) k = muL L₁ k * muL L₂ k := by
  simp [muL, List.map_append, List.prod_append]

theorem muL_replicate (j : ℕ) (i : Fin d) (k : Fin d → ℤ) :
    muL (List.replicate j i) k = ((2 * π * (k i : ℝ)) ^ 2) ^ j := by
  simp [muL, List.map_replicate, List.prod_replicate]

theorem exists_large_of_not_mem_box {K : ℕ} {k : Fin d → ℤ} (hk : k ∉ box K) :
    ∃ i, ((K : ℝ) + 1) ≤ |(k i : ℝ)| := by
  rw [mem_box] at hk
  push_neg at hk
  obtain ⟨i, hi⟩ := hk
  refine ⟨i, ?_⟩
  have h1 : (K : ℤ) + 1 ≤ |k i| := hi
  have h2 : ((K : ℤ) + 1 : ℝ) ≤ ((|k i| : ℤ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  exact h2

/-- **High modes carry large weights**: if `k ∉ box K` then
`wq r k (2π(K+1))^{2j} ≤ wq (r + j) k`. -/
theorem wq_tail {K : ℕ} {k : Fin d → ℤ} (hk : k ∉ box K) (r j : ℕ) :
    wq r k * ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j ≤ wq (r + j) k := by
  obtain ⟨i, hi⟩ := exists_large_of_not_mem_box hk
  have hs : (2 * π * ((K : ℝ) + 1)) ^ 2 ≤ (2 * π * (k i : ℝ)) ^ 2 := by
    have h0 : 0 ≤ 2 * π * ((K : ℝ) + 1) := by positivity
    have : 2 * π * ((K : ℝ) + 1) ≤ |2 * π * (k i : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    calc (2 * π * ((K : ℝ) + 1)) ^ 2 ≤ |2 * π * (k i : ℝ)| ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = _ := sq_abs _
  set app : List (Fin d) → List (Fin d) := fun L => L ++ List.replicate j i with happ
  have hinj : Set.InjOn app (wordsLE d r) := fun L₁ _ L₂ _ h =>
    List.append_cancel_right h
  have hsub : (wordsLE d r).image app ⊆ wordsLE d (r + j) := by
    intro L hL
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 hL
    rw [mem_wordsLE] at hL' ⊢
    simp only [happ, List.length_append, List.length_replicate]
    omega
  calc wq r k * ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j
      = ∑ L ∈ wordsLE d r, muL L k * ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j := by
        rw [wq, Finset.sum_mul]
    _ ≤ ∑ L ∈ wordsLE d r, muL (app L) k := by
        refine Finset.sum_le_sum fun L _ => ?_
        rw [happ, muL_append, muL_replicate]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hs j)
          (muL_nonneg L k)
    _ = ∑ L ∈ (wordsLE d r).image app, muL L k := (Finset.sum_image (f := fun L => muL L k) hinj).symm
    _ ≤ wq (r + j) k := Finset.sum_le_sum_of_subset_of_nonneg hsub
        fun L _ _ => muL_nonneg L k

theorem one_le_two_pi_succ (K : ℕ) : 1 ≤ 2 * π * ((K : ℝ) + 1) := by
  have : (1 : ℝ) ≤ (K : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) K]
  nlinarith [Real.pi_gt_three]

/-- A high mode has weight at least `(2π(K+1))^{2q}`. -/
theorem wq_ge_of_not_mem_box {K : ℕ} {k : Fin d → ℤ} (hk : k ∉ box K) (q : ℕ) :
    ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ q ≤ wq q k := by
  have h := wq_tail hk 0 q
  have h1 : wq 0 k = 1 := by simp [wq, wordsLE, muL_nil]
  rw [h1, one_mul, zero_add] at h
  exact h

/-- **Frequency splitting**: for a trigonometric field and every cut `K`,
`Q_r(tfs S c) ≤ W_K Σ_S c² + (2π(K+1))^{-2j} Q_{r+j}(tfs S c)`,
`W_K = Σ_{k ∈ box K} wq r k`. -/
theorem Q_tfs_split (r j K : ℕ) (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) (t : ℝ) :
    Q r (tfs S c) t ≤ (∑ k ∈ box (d := d) K, wq r k) * ∑ k ∈ S, c k ^ 2 +
      Q (r + j) (tfs S c) t / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j := by
  rw [Q_tfs, Q_tfs]
  set s := ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j with hs
  have hspos : 0 < s := by positivity
  have hW : 0 ≤ ∑ k ∈ box (d := d) K, wq r k := Finset.sum_nonneg fun k _ => wq_nonneg r k
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k ∈ box K
  · have h1 : wq r k ≤ ∑ k ∈ box K, wq r k :=
      Finset.single_le_sum (f := fun k => wq r k) (fun k _ => wq_nonneg r k) hk
    have h2 : 0 ≤ wq (r + j) k * c k ^ 2 / s := by
      have := wq_nonneg (r + j) k; positivity
    nlinarith [sq_nonneg (c k)]
  · have h1 := wq_tail hk r j
    rw [← hs] at h1
    have h2 : wq r k * c k ^ 2 ≤ wq (r + j) k * c k ^ 2 / s := by
      rw [le_div_iff₀ hspos]
      nlinarith [sq_nonneg (c k)]
    have h3 : 0 ≤ (∑ k ∈ box (d := d) K, wq r k) * c k ^ 2 := mul_nonneg hW (sq_nonneg _)
    linarith

/-! ### Trigonometric fields: monotonicity and differences -/

theorem tfs_mono {S S' : Finset (Fin d → ℤ)} (h : S ⊆ S') {c : (Fin d → ℤ) → ℝ}
    (hc : ∀ k ∈ S', k ∉ S → c k = 0) : tfs S c = tfs S' c := by
  funext x
  unfold tfs
  refine Finset.sum_subset h fun k hk hkS => ?_
  rw [hc k hk hkS, zero_mul]

theorem tfs_sub (S : Finset (Fin d → ℤ)) (c c' : (Fin d → ℤ) → ℝ) (x : ST d) :
    tfs S c x - tfs S c' x = tfs S (fun k => c k - c' k) x := by
  unfold tfs
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem coef_sub {f g : ST d → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ)
    (k : Fin d → ℤ) : coef (fun x => f x - g x) t k = coef f t k - coef g t k := by
  unfold coef
  have e : (fun x => casS k x * (f x - g x)) = fun x => casS k x * f x - casS k x * g x := by
    funext x; ring
  rw [e]
  exact sint_sub ((contDiff_casS k).continuous.mul hf) ((contDiff_casS k).continuous.mul hg) t

/-! ### A Grönwall bound -/

theorem gronwallBound_le_mul_exp {δ K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rcases eq_or_lt_of_le hK with h | h
  · subst h
    rw [gronwallBound_K0]; simp
  · rw [gronwallBound_of_K_ne_0 h.ne']
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have := Real.add_one_le_exp (-(K * x))
      have h2 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by
        rw [← Real.exp_add]; simp
      have h3 := Real.exp_pos (K * x)
      nlinarith
    have h4 : ε * ((Real.exp (K * x) - 1) / K) ≤ ε * (x * Real.exp (K * x)) := by
      refine mul_le_mul_of_nonneg_left ?_ hε
      rw [div_le_iff₀ h]; nlinarith
    have e5 : ε / K * (Real.exp (K * x) - 1) = ε * ((Real.exp (K * x) - 1) / K) := by ring
    show δ * Real.exp (K * x) + ε / K * (Real.exp (K * x) - 1) ≤ _
    rw [e5]
    nlinarith

/-! ### The symmetric `L²` difference estimate -/

/-- Size, derivative and Lipschitz bounds of finitely many smooth functions on the sup-ball
`‖v‖ ≤ B` of `ℝ^n`. -/
theorem exists_coeff_bounds {κ : Type*} [Fintype κ] {Φ : κ → (Fin n → ℝ) → ℝ}
    (hΦ : ∀ k, ContDiff ℝ ∞ (Φ k)) (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k, ∀ v w : Fin n → ℝ, ‖v‖ ≤ B → ‖w‖ ≤ B →
      |Φ k v| ≤ M ∧ ‖fderiv ℝ (Φ k) v‖ ≤ M ∧ |Φ k v - Φ k w| ≤ M * ‖v - w‖ := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_family hΦ B 1
  refine ⟨M, hM0, fun k v w hv hw => ⟨?_, ?_, ?_⟩⟩
  · have := hM k v hv 0 (Nat.zero_le _)
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · have := hM k v hv 1 le_rfl
    rwa [norm_iteratedFDeriv_one] at this
  · have h := (convex_closedBall (0 : Fin n → ℝ) B).norm_image_sub_le_of_norm_fderiv_le
      (f := Φ k) (C := M) (fun x _ => (hΦ k).differentiable (by simp) x)
      (fun x hx => by
        have := hM k x (by simpa using hx) 1 le_rfl
        rwa [norm_iteratedFDeriv_one] at this)
      (x := w) (y := v) (by simpa using hw) (by simpa using hv)
    rwa [Real.norm_eq_abs] at h

theorem norm_sq_le_sum_sq (w : Fin n → ℝ) : ‖w‖ ^ 2 ≤ ∑ b, w b ^ 2 := by
  have h : ‖w‖ ≤ Real.sqrt (∑ b, w b ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun b => w b ^ 2)
      (fun b _ => sq_nonneg _) (Finset.mem_univ b))
  calc ‖w‖ ^ 2 ≤ Real.sqrt (∑ b, w b ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun b _ => sq_nonneg _)

theorem sum_abs_sq_le (w : Fin n → ℝ) : (∑ b, |w b|) ^ 2 ≤ n * ∑ b, w b ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun b => |w b|)
  simpa [sq_abs] using this

theorem norm_le_of_abs_le {w : Fin n → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ b, |w b| ≤ B) :
    ‖w‖ ≤ B :=
  (pi_norm_le_iff_of_nonneg hB).2 fun b => by rw [Real.norm_eq_abs]; exact h b

theorem pd_sub_real {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (μ : Fin (d + 1)) (x : ST d) : pd (fun x => f x - g x) μ x = pd f μ x - pd g μ x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- The pointwise decomposition of `Σ_b e_b (G(u) - G(v))_b`, `e = u - v`. -/
theorem genG_diff_decomp {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    (hv : ∀ b, ContDiff ℝ ∞ (v b)) (x : ST d) :
    ∑ b, (u b x - v b x) * (genG A F u b x - genG A F v b x) =
      (∑ b, (u b x - v b x) * (F b (fun c => u c x) - F b (fun c => v c x)) -
        ∑ i, ∑ b, ∑ b', (u b x - v b x) *
          ((A i b b' (fun c => u c x) - A i b b' (fun c => v c x)) * pd (v b') i.succ x)) -
      ∑ i, ∑ b, ∑ b', (u b x - v b x) * compF (A i b b') u x *
        pd (fun x => u b' x - v b' x) i.succ x := by
  have hb : ∀ b, (u b x - v b x) * (genG A F u b x - genG A F v b x) =
      (u b x - v b x) * (F b (fun c => u c x) - F b (fun c => v c x)) -
      ∑ i, ∑ b', (u b x - v b x) *
          ((A i b b' (fun c => u c x) - A i b b' (fun c => v c x)) * pd (v b') i.succ x) -
      ∑ i, ∑ b', (u b x - v b x) * compF (A i b b') u x *
        pd (fun x => u b' x - v b' x) i.succ x := by
    intro b
    simp only [genG, compF, pd_sub_real (hu _) (hv _)]
    have hs : ∑ i, ∑ b', A i b b' (fun c => u c x) * pd (u b') i.succ x -
        ∑ i, ∑ b', A i b b' (fun c => v c x) * pd (v b') i.succ x =
        ∑ i, ∑ b', (A i b b' (fun c => u c x) - A i b b' (fun c => v c x)) *
          pd (v b') i.succ x +
        ∑ i, ∑ b', A i b b' (fun c => u c x) * (pd (u b') i.succ x - pd (v b') i.succ x) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b' _ => by ring
    have e1 : (u b x - v b x) * (F b (fun c => u c x) -
        ∑ i, ∑ b', A i b b' (fun c => u c x) * pd (u b') i.succ x -
        (F b (fun c => v c x) - ∑ i, ∑ b', A i b b' (fun c => v c x) * pd (v b') i.succ x)) =
        (u b x - v b x) * (F b (fun c => u c x) - F b (fun c => v c x)) -
        (u b x - v b x) * (∑ i, ∑ b', A i b b' (fun c => u c x) * pd (u b') i.succ x -
          ∑ i, ∑ b', A i b b' (fun c => v c x) * pd (v b') i.succ x) := by ring
    rw [e1, hs, mul_add, Finset.mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum]
    have e2 : ∀ i b', (u b x - v b x) * (A i b b' (fun c => u c x) *
        (pd (u b') i.succ x - pd (v b') i.succ x)) = (u b x - v b x) *
        A i b b' (fun c => u c x) * (pd (u b') i.succ x - pd (v b') i.succ x) :=
      fun i b' => by ring
    simp only [e2]
    ring
  rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_comm (f := fun b i => ∑ b' : Fin n,
      (u b x - v b x) * ((A i b b' (fun c => u c x) - A i b b' (fun c => v c x)) *
        pd (v b') i.succ x)),
    Finset.sum_comm (f := fun b i => ∑ b' : Fin n,
      (u b x - v b x) * compF (A i b b') u x * pd (fun x => u b' x - v b' x) i.succ x)]

/-- The chain-rule bound `|∂_i Φ(u)| ≤ n M B`. -/
theorem abs_pd_compF_le {Φ : (Fin n → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {u : Fin n → ST d → ℝ}
    (hu : ∀ b, ContDiff ℝ ∞ (u b)) {M B : ℝ} (hM0 : 0 ≤ M) (hB : 0 ≤ B) (x : ST d)
    {i : Fin (d + 1)} (hfd : ‖fderiv ℝ Φ (fun c => u c x)‖ ≤ M)
    (hdu : ∀ c, |pd (u c) i x| ≤ B) :
    |pd (compF Φ u) i x| ≤ n * M * B := by
  have h := SobolevOpen.pd_comp (Φ := Φ) (V := u) (x := x) (hΦ.differentiable (by simp) _)
    (fun c => (hu c).differentiable (by simp) x) i
  rw [show compF Φ u = fun y => Φ (fun c => u c y) from rfl, h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ c, |fderiv ℝ Φ (fun c => u c x) (Pi.single c 1) * pd (u c) i x|
      ≤ ∑ _c : Fin n, M * B := Finset.sum_le_sum fun c _ => by
        rw [abs_mul]
        refine mul_le_mul ?_ (hdu c) (abs_nonneg _) hM0
        have := (fderiv ℝ Φ (fun c => u c x)).le_opNorm (Pi.single c 1)
        rw [Real.norm_eq_abs] at this
        refine this.trans ?_
        have h1 : ‖(Pi.single c (1 : ℝ) : Fin n → ℝ)‖ ≤ 1 := by
          refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun c' => ?_
          by_cases hc : c' = c
          · subst hc; simp
          · simp [Pi.single_apply, hc]
        calc ‖fderiv ℝ Φ (fun c => u c x)‖ * ‖(Pi.single c (1 : ℝ) : Fin n → ℝ)‖ ≤ M * 1 :=
              mul_le_mul hfd h1 (norm_nonneg _) hM0
          _ = M := mul_one M
    _ = n * M * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **The symmetric `L²` difference estimate**: for smooth periodic fields `u, v` with
`|u|, |v|, |∂_iu|, |∂_iv| ≤ B`,
`Σ_b ∫ (u_b - v_b)(G(u) - G(v))_b ≤ K₁ Σ_b ∫ (u_b - v_b)²` on every slice, with `K₁` depending
only on `B` (and `A, F, d, n`).  The principal part is handled by symmetric integration by parts
(`QLEnergy.integral_sym_eq`), which is where the symmetry of `A^i` enters. -/
theorem sym_L2_diff (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {B : ℝ}
    (hB : 0 ≤ B) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ u v : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, ContDiff ℝ ∞ (v b)) → (∀ b, IsSPeriodic (u b)) → (∀ b, IsSPeriodic (v b)) →
      (∀ b x, |u b x| ≤ B) → (∀ b x, |v b x| ≤ B) →
      (∀ b (i : Fin d) x, |pd (u b) i.succ x| ≤ B) →
      (∀ b (i : Fin d) x, |pd (v b) i.succ x| ≤ B) → ∀ t,
      ∑ b, sint (fun x => (u b x - v b x) * (genG A F u b x - genG A F v b x)) t ≤
        K₁ * ∑ b, sint (fun x => (u b x - v b x) ^ 2) t := by
  set Φ : (Fin n ⊕ (Fin d × Fin n × Fin n)) → (Fin n → ℝ) → ℝ :=
    fun k => Sum.elim (fun a => F a) (fun p => A p.1 p.2.1 p.2.2) k with hΦ
  have hΦs : ∀ k, ContDiff ℝ ∞ (Φ k) := by
    intro k; cases k with
    | inl a => exact hF a
    | inr p => exact hA p.1 p.2.1 p.2.2
  obtain ⟨M, hM0, hM⟩ := exists_coeff_bounds hΦs B
  have hMF : ∀ a (v w : Fin n → ℝ), ‖v‖ ≤ B → ‖w‖ ≤ B → |F a v - F a w| ≤ M * ‖v - w‖ :=
    fun a v w hv hw => (hM (Sum.inl a) v w hv hw).2.2
  have hMA : ∀ i a b (v w : Fin n → ℝ), ‖v‖ ≤ B → ‖w‖ ≤ B →
      |A i a b v - A i a b w| ≤ M * ‖v - w‖ :=
    fun i a b v w hv hw => (hM (Sum.inr (i, a, b)) v w hv hw).2.2
  have hMA' : ∀ i a b (v : Fin n → ℝ), ‖v‖ ≤ B → ‖fderiv ℝ (A i a b) v‖ ≤ M :=
    fun i a b v hv => (hM (Sum.inr (i, a, b)) v v hv hv).2.1
  set c₁ : ℝ := M * (n + 1) / 2 + d * n * M * B * (n + 1) / 2 with hc₁
  set c₂ : ℝ := n * n * M * B with hc₂
  refine ⟨c₁ + d * c₂ / 2, by positivity, fun u v hu hv hup hvp hub hvb hdu hdv t => ?_⟩
  set e : Fin n → ST d → ℝ := fun b x => u b x - v b x with he
  have hes : ∀ b, ContDiff ℝ ∞ (e b) := fun b => (hu b).sub (hv b)
  have hep : ∀ b, IsSPeriodic (e b) := fun b k x => by simp [he, hup b k x, hvp b k x]
  set E2 : ST d → ℝ := fun x => ∑ b, e b x ^ 2 with hE2
  have hux : ∀ x, ‖(fun c => u c x)‖ ≤ B := fun x => norm_le_of_abs_le hB fun c => hub c x
  have hvx : ∀ x, ‖(fun c => v c x)‖ ≤ B := fun x => norm_le_of_abs_le hB fun c => hvb c x
  have hnorm : ∀ x, ‖(fun c => u c x) - (fun c => v c x)‖ ^ 2 ≤ E2 x := fun x =>
    norm_sq_le_sum_sq _
  have habs : ∀ x, (∑ b, |e b x|) ^ 2 ≤ n * E2 x := fun x => sum_abs_sq_le _
  -- the zero-order part
  set X : ST d → ℝ := fun x =>
    ∑ b, (u b x - v b x) * (F b (fun c => u c x) - F b (fun c => v c x)) -
      ∑ i, ∑ b, ∑ b', (u b x - v b x) *
        ((A i b b' (fun c => u c x) - A i b b' (fun c => v c x)) * pd (v b') i.succ x) with hX
  have hXb : ∀ x, X x ≤ c₁ * E2 x := by
    intro x
    set w := ‖(fun c => u c x) - (fun c => v c x)‖ with hw
    have hw0 : 0 ≤ w := norm_nonneg _
    set S := ∑ b, |e b x| with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => abs_nonneg _
    have hwS : w * S ≤ (n + 1) / 2 * E2 x := by
      nlinarith [hnorm x, habs x, sq_nonneg (w - S)]
    have h1 : |∑ b, (u b x - v b x) * (F b (fun c => u c x) - F b (fun c => v c x))| ≤
        M * (w * S) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ b, |(u b x - v b x) * (F b (fun c => u c x) - F b (fun c => v c x))|
          ≤ ∑ b, |e b x| * (M * w) := Finset.sum_le_sum fun b _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hMF b _ _ (hux x) (hvx x)) (abs_nonneg _)
        _ = M * (w * S) := by rw [← Finset.sum_mul, ← hS]; ring
    have h2 : |∑ i : Fin d, ∑ b, ∑ b', (u b x - v b x) *
        ((A i b b' (fun c => u c x) - A i b b' (fun c => v c x)) * pd (v b') i.succ x)| ≤
        d * n * M * B * (w * S) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i : Fin d, |∑ b, ∑ b', (u b x - v b x) *
            ((A i b b' (fun c => u c x) - A i b b' (fun c => v c x)) * pd (v b') i.succ x)|
          ≤ ∑ _i : Fin d, n * M * B * (w * S) := Finset.sum_le_sum fun i _ => by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc ∑ b, |∑ b', (u b x - v b x) *
                  ((A i b b' (fun c => u c x) - A i b b' (fun c => v c x)) * pd (v b') i.succ x)|
                ≤ ∑ b, |e b x| * (n * (M * w * B)) := Finset.sum_le_sum fun b _ => by
                  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                  calc ∑ b', |(u b x - v b x) * ((A i b b' (fun c => u c x) -
                        A i b b' (fun c => v c x)) * pd (v b') i.succ x)|
                      ≤ ∑ _b' : Fin n, |e b x| * (M * w * B) :=
                        Finset.sum_le_sum fun b' _ => by
                          rw [abs_mul, abs_mul]
                          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                          exact mul_le_mul (hMA i b b' _ _ (hux x) (hvx x)) (hdv b' i x)
                            (abs_nonneg _) (by positivity)
                    _ = |e b x| * (n * (M * w * B)) := by
                      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                      ring
              _ = n * M * B * (w * S) := by rw [← Finset.sum_mul, ← hS]; ring
        _ = d * n * M * B * (w * S) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hXx : X x ≤ M * (w * S) + d * n * M * B * (w * S) := by
      have h3 := neg_abs_le (∑ i : Fin d, ∑ b, ∑ b', (u b x - v b x) *
        ((A i b b' (fun c => u c x) - A i b b' (fun c => v c x)) * pd (v b') i.succ x))
      have h4 := le_abs_self (∑ b, (u b x - v b x) *
        (F b (fun c => u c x) - F b (fun c => v c x)))
      simp only [hX]
      linarith
    have hMB : 0 ≤ M + d * n * M * B := by positivity
    calc X x ≤ (M + d * n * M * B) * (w * S) := by linarith
      _ ≤ (M + d * n * M * B) * ((n + 1) / 2 * E2 x) := mul_le_mul_of_nonneg_left hwS hMB
      _ = c₁ * E2 x := by rw [hc₁]; ring
  -- the principal part after symmetric integration by parts
  set Z : Fin d → ST d → ℝ := fun i x =>
    ∑ b, ∑ b', e b x * pd (compF (A i b b') u) i.succ x * e b' x with hZ
  have hZb : ∀ i x, Z i x ≤ c₂ * E2 x := by
    intro i x
    have hpd : ∀ b b', |pd (compF (A i b b') u) i.succ x| ≤ n * M * B := fun b b' =>
      abs_pd_compF_le (hA i b b') hu hM0 hB x (hMA' i b b' _ (hux x)) fun c => hdu c i x
    calc Z i x ≤ ∑ b, ∑ b', |e b x| * (n * M * B) * |e b' x| :=
          Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => by
            refine (le_abs_self _).trans ?_
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpd b b')
              (abs_nonneg _)) (abs_nonneg _)
      _ = n * M * B * (∑ b, |e b x|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b' _ => by ring
      _ ≤ n * M * B * (n * E2 x) := mul_le_mul_of_nonneg_left (habs x) (by positivity)
      _ = c₂ * E2 x := by rw [hc₂]; ring
  have hcZ : ∀ i, Continuous (Z i) := fun i =>
    continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun b' _ =>
      ((hes b).continuous.mul (contDiff_pd_top (contDiff_compF (hA i b b') hu) _).continuous).mul
        (hes b').continuous
  have hcY : ∀ i : Fin d, Continuous fun x => ∑ b, ∑ b', e b x * compF (A i b b') u x *
      pd (e b') i.succ x := fun i =>
    continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun b' _ =>
      ((hes b).continuous.mul (contDiff_compF (hA i b b') hu).continuous).mul
        (contDiff_pd_top (hes b') _).continuous
  have hcX : Continuous X := by
    simp only [hX]
    refine (continuous_finsetSum _ fun b _ => ((hu b).continuous.sub (hv b).continuous).mul
      (((hF b).continuous.comp (continuous_pi fun c => (hu c).continuous)).sub
        ((hF b).continuous.comp (continuous_pi fun c => (hv c).continuous)))).sub
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun b _ =>
        continuous_finsetSum _ fun b' _ => ((hu b).continuous.sub (hv b).continuous).mul
          ((((hA i b b').continuous.comp (continuous_pi fun c => (hu c).continuous)).sub
            ((hA i b b').continuous.comp (continuous_pi fun c => (hv c).continuous))).mul
            (contDiff_pd_top (hv b') _).continuous))
  have hY : ∀ i, sint (fun x => ∑ b, ∑ b', e b x * compF (A i b b') u x *
      pd (e b') i.succ x) t = -(1 / 2) * sint (Z i) t := fun i =>
    integral_sym_eq hes hep (fun b b' => contDiff_compF (hA i b b') hu)
      (fun b b' => isSPeriodic_compF _ hup)
      (fun b b' x => by simp only [compF]; exact hsym i b b' _) t i
  have hcE2 : Continuous E2 := continuous_finsetSum _ fun b _ => (hes b).continuous.pow 2
  -- assemble
  have hdec : (fun x => ∑ b, (u b x - v b x) * (genG A F u b x - genG A F v b x)) =
      fun x => X x - ∑ i, ∑ b, ∑ b', e b x * compF (A i b b') u x * pd (e b') i.succ x := by
    funext x
    rw [genG_diff_decomp hu hv x]
  have hL : ∑ b, sint (fun x => (u b x - v b x) * (genG A F u b x - genG A F v b x)) t =
      sint X t + 1 / 2 * ∑ i, sint (Z i) t := by
    rw [← sint_sum (f := fun b x => (u b x - v b x) * (genG A F u b x - genG A F v b x))
      Finset.univ (fun b => ((hu b).continuous.sub (hv b).continuous).mul
        ((contDiff_genG hA hF hu b).continuous.sub (contDiff_genG hA hF hv b).continuous)) t,
      hdec]
    have hsY : Continuous fun x => ∑ i : Fin d, ∑ b, ∑ b', e b x * compF (A i b b') u x *
        pd (e b') i.succ x := continuous_finsetSum _ fun i _ => hcY i
    rw [sint_sub (f := X) (g := fun x => ∑ i : Fin d, ∑ b, ∑ b', e b x * compF (A i b b') u x *
        pd (e b') i.succ x) hcX hsY t,
      sint_sum (f := fun i x => ∑ b, ∑ b', e b x * compF (A i b b') u x * pd (e b') i.succ x)
        Finset.univ hcY t]
    simp only [hY, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hR : ∑ b, sint (fun x => (u b x - v b x) ^ 2) t = sint E2 t :=
    (sint_sum (f := fun b x => (u b x - v b x) ^ 2) Finset.univ
      (fun b => ((hu b).continuous.sub (hv b).continuous).pow 2) t).symm
  rw [hL, hR]
  have h1 : sint X t ≤ c₁ * sint E2 t := by
    rw [← sint_const_mul]
    exact sint_mono hcX (continuous_const.mul hcE2) hXb t
  have h2 : ∀ i, sint (Z i) t ≤ c₂ * sint E2 t := fun i => by
    rw [← sint_const_mul]
    exact sint_mono (hcZ i) (continuous_const.mul hcE2) (hZb i) t
  have h3 : ∑ i : Fin d, sint (Z i) t ≤ d * (c₂ * sint E2 t) := by
    calc ∑ i : Fin d, sint (Z i) t ≤ ∑ _i : Fin d, c₂ * sint E2 t :=
          Finset.sum_le_sum fun i _ => h2 i
      _ = d * (c₂ * sint E2 t) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith

/-! ### Pointwise bounds -/

theorem Q_le_energyQ (q : ℕ) (u : Fin n → ST d → ℝ) (t : ℝ) (b : Fin n) :
    Q q (u b) t ≤ energyQ q u t :=
  Finset.single_le_sum (f := fun b => Q q (u b) t) (fun b _ => Q_nonneg _ _ _)
    (Finset.mem_univ b)

/-- **Sup bounds for Galerkin fields** from the slice Sobolev embedding (`m > d/2`,
`q ≥ m + 1`): `|U_N|, |∂_iU_N| ≤ √C_S ‖a‖`. -/
theorem abs_fld_le {m q : ℕ} (hmq : m + 1 ≤ q) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    {N : ℕ} (a : GS d n N) (b : Fin n) (x : ST d) :
    |fld q a b x| ≤ Real.sqrt CS * ‖a‖ ∧
      ∀ i : Fin d, |pd (fld q a b) i.succ x| ≤ Real.sqrt CS * ‖a‖ := by
  have hQ : Q q (fld q a b) (x 0) ≤ ‖a‖ ^ 2 :=
    (Q_le_energyQ q (fld q a) (x 0) b).trans (energyQ_fld q a (x 0)).le
  have hsq : Real.sqrt (CS * ‖a‖ ^ 2) = Real.sqrt CS * ‖a‖ := by
    rw [Real.sqrt_mul hCS, Real.sqrt_sq (norm_nonneg _)]
  rw [← Fin.cons_self_tail x]
  refine ⟨?_, fun i => ?_⟩
  · rw [← hsq]
    refine Real.abs_le_sqrt ?_
    refine (hsup _ (contDiff_fld q a b) (isSPeriodic_fld q a b) _ _).trans ?_
    exact mul_le_mul_of_nonneg_left ((Q_mono (by omega) _ _).trans hQ) hCS
  · rw [← hsq]
    refine Real.abs_le_sqrt ?_
    refine (hsup _ (contDiff_pd_top (contDiff_fld q a b) _)
      (isSPeriodic_pd (isSPeriodic_fld q a b) _) _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCS
    exact (Q_pd_le i _ _).trans ((Q_mono hmq _ _).trans hQ)

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- A pointwise bound for the generator. -/
theorem abs_genG_le {B M : ℝ} (hB : 0 ≤ B) (hM0 : 0 ≤ M) {u : Fin n → ST d → ℝ}
    (hub : ∀ b x, |u b x| ≤ B) (hdu : ∀ b (i : Fin d) x, |pd (u b) i.succ x| ≤ B)
    (hMF : ∀ a (v : Fin n → ℝ), ‖v‖ ≤ B → |F a v| ≤ M)
    (hMA : ∀ i a b (v : Fin n → ℝ), ‖v‖ ≤ B → |A i a b v| ≤ M) (a : Fin n) (x : ST d) :
    |genG A F u a x| ≤ M + d * n * M * B := by
  have hux : ‖(fun c => u c x)‖ ≤ B := norm_le_of_abs_le hB fun c => hub c x
  unfold genG compF
  refine (abs_sub _ _).trans (add_le_add (hMF a _ hux) ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin d, |∑ b, A i a b (fun c => u c x) * pd (u b) i.succ x|
      ≤ ∑ _i : Fin d, n * (M * B) := Finset.sum_le_sum fun i _ => by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ b, |A i a b (fun c => u c x) * pd (u b) i.succ x| ≤ ∑ _b : Fin n, M * B :=
              Finset.sum_le_sum fun b _ => by
                rw [abs_mul]
                exact mul_le_mul (hMA i a b _ hux) (hdu b i x) (abs_nonneg _) hM0
          _ = n * (M * B) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = d * n * M * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### The Galerkin coefficients along a solution -/

/-- The coefficient ODE: `d/dt c_{b,k}(t) = ⟨G(U_N(t))_b, cas_k⟩` for `k ∈ box N`. -/
theorem hasDerivWithinAt_cf {q N : ℕ} {γ : ℝ → GS d n N} {s : Set ℝ} {t : ℝ}
    (hγ : HasDerivWithinAt γ (GN A F q (γ t)) s t) (b : Fin n) {k : Fin d → ℤ}
    (hk : k ∈ box N) :
    HasDerivWithinAt (fun t => cf q (γ t) b k) (coef (genG A F (fld q (γ t)) b) 0 k) s t := by
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) ((b, ⟨k, hk⟩) : Fin n × box (d := d) N)).hasFDerivAt
    |>.comp_hasDerivWithinAt t hγ
  have h2 := h1.div_const (Real.sqrt (wq q k))
  have e : (fun t => cf q (γ t) b k) =
      fun t => (EuclideanSpace.proj (𝕜 := ℝ) ((b, ⟨k, hk⟩) : Fin n × box (d := d) N))
        (γ t) / Real.sqrt (wq q k) := by
    funext t; rw [cf, dif_pos hk]; rfl
  have h3 : coef (genG A F (fld q (γ t)) b) 0 k =
      (EuclideanSpace.proj (𝕜 := ℝ) ((b, ⟨k, hk⟩) : Fin n × box (d := d) N))
        (GN A F q (γ t)) / Real.sqrt (wq q k) := by
    show _ = GN A F q (γ t) (b, ⟨k, hk⟩) / Real.sqrt (wq q k)
    rw [GN_apply]
    field_simp [sqrt_wq_ne q k]
  rw [e, h3]
  exact h2

theorem cf_eq_zero {q N : ℕ} (a : GS d n N) (b : Fin n) {k : Fin d → ℤ} (hk : k ∉ box N) :
    cf q a b k = 0 := by rw [cf, dif_neg hk]

/-- The field of a cutoff-`N` state, written on a larger box. -/
theorem fld_eq_tfs {q N M : ℕ} (hNM : N ≤ M) (a : GS d n N) (b : Fin n) :
    fld q a b = tfs (box M) (cf q a b) :=
  tfs_mono (box_mono hNM) fun k _ hk => cf_eq_zero a b hk

/-- The `L²` distance of two Galerkin fields in coefficients. -/
theorem sint_fld_sub_sq {q N M : ℕ} (hNM : N ≤ M) (a : GS d n N) (a' : GS d n M) (b : Fin n)
    (t : ℝ) : sint (fun x => (fld q a b x - fld q a' b x) ^ 2) t =
      ∑ k ∈ box M, (cf q a b k - cf q a' b k) ^ 2 := by
  have e : (fun x => (fld q a b x - fld q a' b x) ^ 2) =
      fun x => tfs (box M) (fun k => cf q a b k - cf q a' b k) x ^ 2 := by
    funext x; rw [fld_eq_tfs hNM a b, fld, tfs_sub]
  rw [e, sint_tfs_sq]

theorem hasDerivWithinAt_sq' {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ}
    (h : HasDerivWithinAt f f' s x) : HasDerivWithinAt (fun y => f y ^ 2) (2 * f x * f') s x := by
  have h2 := h.fun_pow 2
  exact h2.congr_deriv (by push_cast; ring)

/-- The per-component `H^q` norm of a Galerkin field is bounded by the state norm. -/
theorem sum_wq_cf_sq_le {q N : ℕ} (a : GS d n N) (b : Fin n) :
    ∑ k ∈ box N, wq q k * cf q a b k ^ 2 ≤ ‖a‖ ^ 2 := by
  have h := Q_le_energyQ q (fld q a) 0 b
  rw [energyQ_fld, fld, Q_tfs] at h
  exact h

/-- The high-mode part of a coefficient vector: `Σ_{k ∈ S, k ∉ box N} c_k² ≤
(2π(N+1))^{-2q} Σ_{k ∈ S} wq q k c_k²`. -/
theorem sum_tail_sq_le (q N : ℕ) (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) :
    ∑ k ∈ S.filter (fun k => k ∉ box N), c k ^ 2 ≤
      (∑ k ∈ S, wq q k * c k ^ 2) / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ q := by
  have hs : 0 < ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ q := by positivity
  rw [le_div_iff₀ hs, Finset.sum_mul]
  calc ∑ k ∈ S.filter (fun k => k ∉ box N), c k ^ 2 * ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ q
      ≤ ∑ k ∈ S.filter (fun k => k ∉ box N), wq q k * c k ^ 2 :=
        Finset.sum_le_sum fun k hk => by
          have := wq_ge_of_not_mem_box (Finset.mem_filter.1 hk).2 q
          nlinarith [sq_nonneg (c k)]
    _ ≤ ∑ k ∈ S, wq q k * c k ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) fun k _ _ => mul_nonneg (wq_nonneg q k) (sq_nonneg _)

theorem two_pi_succ_pow_le (q N : ℕ) :
    (2 * π * ((N : ℝ) + 1)) ^ q ≤ ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ q := by
  rw [← pow_mul]
  exact pow_le_pow_right₀ (one_le_two_pi_succ N) (by omega)

/-- **The spectral Galerkin solutions are Cauchy in `C_tL²`, with rate**: for `N ≤ M`,
`sup_{t ∈ [0,T]} ‖U_N(t) - U_M(t)‖²_{L²} ≤ C (2π(N+1))^{-q}`, where `C` depends only on the
data radius `R₀`, the uniform bound `R`, `T` (and `A, F, q, m, d, n`).  Proof: the coefficient
ODEs, the symmetric `L²` difference estimate `sym_L2_diff` for the common modes, the
`H^q`-tail of `U_M` against the `L²`-bounded `G(U_N)` for the modes `box M \ box N`, and
Grönwall. -/
theorem galerkin_L2_cauchy {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hmq : m + 1 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ R T : ℝ} (hR₀ : 0 ≤ R₀) (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U₀ : Fin n → ST d → ℝ), (∀ b, ContDiff ℝ ∞ (U₀ b)) →
      (∀ b, IsSPeriodic (U₀ b)) → energyQ q U₀ 0 ≤ R₀ ^ 2 →
      ∀ (γ : (N : ℕ) → ℝ → GS d n N), (∀ N, γ N 0 = P0 q N U₀) →
      (∀ N, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (γ N) (GN A F q (γ N t)) (Set.Icc 0 T) t) →
      (∀ N, ∀ t ∈ Set.Icc 0 T, ‖γ N t‖ ≤ R) →
      ∀ N M, N ≤ M → ∀ t ∈ Set.Icc 0 T,
        ∑ b, ∑ k ∈ box M, (cf q (γ N t) b k - cf q (γ M t) b k) ^ 2 ≤
          C / (2 * π * ((N : ℝ) + 1)) ^ q := by
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
  refine ⟨(R₀ ^ 2 + 2 * n * R * Gm * T) * Real.exp (2 * K₁ * T), by positivity,
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
  set ĝ : (L : ℕ) → ℝ → Fin n → (Fin d → ℤ) → ℝ := fun L s b k =>
    coef (genG A F (fld q (γ L s)) b) 0 k with hĝ
  set D : ℝ → ℝ := fun t => ∑ b, ∑ k ∈ box M, (cf q (γ N t) b k - cf q (γ M t) b k) ^ 2
    with hD
  set D' : ℝ → ℝ := fun t => ∑ b, ∑ k ∈ box M, 2 * (cf q (γ N t) b k - cf q (γ M t) b k) *
    ((if k ∈ box N then ĝ N t b k else 0) - ĝ M t b k) with hD'
  have hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt D (D' t) (Set.Icc 0 T) t := by
    intro t ht
    refine HasDerivWithinAt.fun_sum fun b _ => HasDerivWithinAt.fun_sum fun k hk => ?_
    refine hasDerivWithinAt_sq' (HasDerivWithinAt.sub ?_ ?_)
    · by_cases hkN : k ∈ box N
      · rw [if_pos hkN]; exact hasDerivWithinAt_cf (hγ N t ht) b hkN
      · rw [if_neg hkN]
        have : (fun t => cf q (γ N t) b k) = fun _ => 0 :=
          funext fun t => cf_eq_zero _ b hkN
        rw [this]; exact hasDerivWithinAt_const _ _ _
    · exact hasDerivWithinAt_cf (hγ M t ht) b hk
  -- the derivative bound
  have hD'b : ∀ t ∈ Set.Icc 0 T, D' t ≤ 2 * K₁ * D t + 2 * n * R * Gm / s := by
    intro t ht
    have hsplit : ∀ b, ∑ k ∈ box M, 2 * (cf q (γ N t) b k - cf q (γ M t) b k) *
        ((if k ∈ box N then ĝ N t b k else 0) - ĝ M t b k) =
        2 * sint (fun x => (fld q (γ N t) b x - fld q (γ M t) b x) *
          (genG A F (fld q (γ N t)) b x - genG A F (fld q (γ M t)) b x)) 0 +
        2 * ∑ k ∈ (box M).filter (fun k => k ∉ box N), cf q (γ M t) b k * ĝ N t b k := by
      intro b
      have h1 : sint (fun x => (fld q (γ N t) b x - fld q (γ M t) b x) *
          (genG A F (fld q (γ N t)) b x - genG A F (fld q (γ M t)) b x)) 0 =
          ∑ k ∈ box M, (cf q (γ N t) b k - cf q (γ M t) b k) * (ĝ N t b k - ĝ M t b k) := by
        have e : (fun x => (fld q (γ N t) b x - fld q (γ M t) b x) *
            (genG A F (fld q (γ N t)) b x - genG A F (fld q (γ M t)) b x)) =
            fun x => tfs (box M) (fun k => cf q (γ N t) b k - cf q (γ M t) b k) x *
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
      by_cases hkN : k ∈ box N
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
    have hP2 : ∀ b, |∑ k ∈ (box M).filter (fun k => k ∉ box N), cf q (γ M t) b k * ĝ N t b k| ≤
        R * Gm / s := by
      intro b
      set T' := (box M).filter (fun k => k ∉ box N)
      have hc1 : ∑ k ∈ T', cf q (γ M t) b k ^ 2 ≤ R ^ 2 / s ^ 2 := by
        refine (sum_tail_sq_le q N (box M) (cf q (γ M t) b)).trans ?_
        have h2 : ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ q = s ^ 2 := by rw [hs, ← pow_mul, ← pow_mul, Nat.mul_comm]
        rw [h2]
        refine div_le_div_of_nonneg_right ((sum_wq_cf_sq_le (γ M t) b).trans ?_) (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) (hγR M t ht) 2
      have hc2 : ∑ k ∈ T', ĝ N t b k ^ 2 ≤ Gm ^ 2 := by
        have hb := bessel_L2 T' (contDiff_genG hA hF (fun b => contDiff_fld q (γ N t) b)
          b).continuous 0
        refine hb.trans ?_
        have : sint (fun x => genG A F (fld q (γ N t)) b x ^ 2) 0 ≤ sint (fun _ => Gm ^ 2) 0 :=
          sint_mono (f := fun x => genG A F (fld q (γ N t)) b x ^ 2) (g := fun _ => Gm ^ 2)
            ((contDiff_genG hA hF (fun b => contDiff_fld q (γ N t) b) b).continuous.pow 2)
            continuous_const (fun x => by
              have := hGb N t ht b x
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2) 0
        rwa [sint_const] at this
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq T' (fun k => cf q (γ M t) b k)
        (fun k => ĝ N t b k)
      refine abs_le_of_sq_le_sq (hcs.trans ?_) (by positivity)
      calc (∑ k ∈ T', cf q (γ M t) b k ^ 2) * ∑ k ∈ T', ĝ N t b k ^ 2
          ≤ R ^ 2 / s ^ 2 * Gm ^ 2 := mul_le_mul hc1 hc2
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = (R * Gm / s) ^ 2 := by ring
    have hsum : D' t = 2 * ∑ b, sint (fun x => (fld q (γ N t) b x - fld q (γ M t) b x) *
        (genG A F (fld q (γ N t)) b x - genG A F (fld q (γ M t)) b x)) 0 +
        2 * ∑ b, ∑ k ∈ (box M).filter (fun k => k ∉ box N), cf q (γ M t) b k * ĝ N t b k := by
      simp only [hD']
      rw [Finset.sum_congr rfl fun b _ => hsplit b, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.mul_sum]
    have hP2' : ∑ b, ∑ k ∈ (box M).filter (fun k => k ∉ box N), cf q (γ M t) b k * ĝ N t b k ≤
        n * (R * Gm / s) := by
      calc ∑ b, ∑ k ∈ (box M).filter (fun k => k ∉ box N), cf q (γ M t) b k * ĝ N t b k
          ≤ ∑ _b : Fin n, R * Gm / s := Finset.sum_le_sum fun b _ => (le_abs_self _).trans (hP2 b)
        _ = n * (R * Gm / s) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum]
    have : 2 * (n * (R * Gm / s)) = 2 * n * R * Gm / s := by ring
    linarith
  -- Grönwall
  have hcont : ContinuousOn D (Set.Icc 0 T) := fun t ht => (hderiv t ht).continuousWithinAt
  have hgr := SpectralGalerkin.le_gronwall_scalar (f := D) (f' := D') (K := 2 * K₁)
    (ε := 2 * n * R * Gm / s) hcont
    (fun t ht => (hderiv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) (fun t ht => hD'b t (Ico_subset_Icc_self ht)) t ht
  have hD0 : D 0 ≤ R₀ ^ 2 / s := by
    have e0 : D 0 = ∑ b, ∑ k ∈ (box M).filter (fun k => k ∉ box N), coef (U₀ b) 0 k ^ 2 := by
      simp only [hD, hγ0, cf_P0]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k hk => ?_
      by_cases hkN : k ∈ box N
      · rw [if_pos hkN, if_pos (box_mono hNM hkN), if_neg (not_not.2 hkN)]; ring
      · rw [if_neg hkN, if_pos hk, if_pos hkN]; ring
    rw [e0]
    have h1 : ∀ b, ∑ k ∈ (box M).filter (fun k => k ∉ box N), coef (U₀ b) 0 k ^ 2 ≤
        Q q (U₀ b) 0 / s ^ 2 := by
      intro b
      refine (sum_tail_sq_le q N (box M) (coef (U₀ b) 0)).trans ?_
      have h2 : ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ q = s ^ 2 := by rw [hs, ← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [h2]
      exact div_le_div_of_nonneg_right (bessel_Hq q (box M) (hU b) (hUp b) 0) (by positivity)
    calc ∑ b, ∑ k ∈ (box M).filter (fun k => k ∉ box N), coef (U₀ b) 0 k ^ 2
        ≤ ∑ b, Q q (U₀ b) 0 / s ^ 2 := Finset.sum_le_sum fun b _ => h1 b
      _ = energyQ q U₀ 0 / s ^ 2 := by rw [energyQ, Finset.sum_div]
      _ ≤ R₀ ^ 2 / s ^ 2 := div_le_div_of_nonneg_right hE (by positivity)
      _ ≤ R₀ ^ 2 / s := by
          refine div_le_div_of_nonneg_left (sq_nonneg _) hs0 ?_
          nlinarith
  have hK2 : 0 ≤ 2 * K₁ := by positivity
  have hε : 0 ≤ 2 * n * R * Gm / s := by positivity
  refine hgr.trans ((gronwallBound_le_mul_exp hK2 hε ht.1).trans ?_)
  have hexp : Real.exp (2 * K₁ * t) ≤ Real.exp (2 * K₁ * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK2)
  have hD0' : 0 ≤ D 0 := Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  calc (D 0 + 2 * n * R * Gm / s * t) * Real.exp (2 * K₁ * t)
      ≤ (R₀ ^ 2 / s + 2 * n * R * Gm / s * T) * Real.exp (2 * K₁ * T) := by
        refine mul_le_mul (add_le_add hD0 (mul_le_mul_of_nonneg_left ht.2 hε)) hexp
          (Real.exp_pos _).le (by positivity)
    _ = (R₀ ^ 2 + 2 * n * R * Gm * T) * Real.exp (2 * K₁ * T) / s := by
        field_simp

/-! ### Uniform convergence of the fields and of their first derivatives -/

theorem le_two_pi_succ_pow {q : ℕ} (hq : 1 ≤ q) (N : ℕ) :
    (N : ℝ) + 1 ≤ (2 * π * ((N : ℝ) + 1)) ^ q := by
  have h1 : (N : ℝ) + 1 ≤ 2 * π * ((N : ℝ) + 1) := by
    have := Real.pi_gt_three; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; nlinarith
  calc (N : ℝ) + 1 ≤ 2 * π * ((N : ℝ) + 1) := h1
    _ = (2 * π * ((N : ℝ) + 1)) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (one_le_two_pi_succ N) hq

/-- **The Galerkin fields and their first spatial derivatives converge uniformly** on
`[0, T] × ℝ^d` (`m > d/2`, `q ≥ m + 2`): Cauchy in `C_tL²` (`galerkin_L2_cauchy`) plus the
uniform `H^q` bound give, by frequency splitting (`Q_tfs_split`) and the slice Sobolev embedding,
uniform Cauchy bounds for `U_N` and `∂_iU_N`. -/
theorem galerkin_unif_cauchy {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq2 : m + 2 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ R T : ℝ} (hR₀ : 0 ≤ R₀) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (U₀ : Fin n → ST d → ℝ) (hU : ∀ b, ContDiff ℝ ∞ (U₀ b)) (hUp : ∀ b, IsSPeriodic (U₀ b))
    (hE : energyQ q U₀ 0 ≤ R₀ ^ 2) (γ : (N : ℕ) → ℝ → GS d n N) (hγ0 : ∀ N, γ N 0 = P0 q N U₀)
    (hγ : ∀ N, ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (γ N) (GN A F q (γ N t)) (Set.Icc 0 T) t)
    (hγR : ∀ N, ∀ t ∈ Set.Icc 0 T, ‖γ N t‖ ≤ R) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N M, N₀ ≤ N → N ≤ M → ∀ t ∈ Set.Icc 0 T, ∀ b x,
      |fld q (γ N t) b x - fld q (γ M t) b x| ≤ ε ∧
      ∀ i : Fin d, |pd (fld q (γ N t) b) i.succ x - pd (fld q (γ M t) b) i.succ x| ≤ ε := by
  obtain ⟨C, hC0, hC⟩ := galerkin_L2_cauchy hm (by omega : m + 1 ≤ q) hA hsym hF hR₀ hR hT
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  intro ε hε
  set j := q - (m + 1) with hj
  have hj1 : 1 ≤ j := by omega
  have hqj : m + 1 + j = q := by omega
  obtain ⟨K, hK⟩ := exists_nat_gt (8 * CS * R ^ 2 / ε ^ 2)
  set W := ∑ k ∈ box (d := d) K, wq (m + 1) k with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun k _ => wq_nonneg _ k
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * CS * W * C / ε ^ 2)
  refine ⟨N₀, fun N M hN hNM t ht b x => ?_⟩
  have hε2 : 0 < ε ^ 2 := by positivity
  set δ : (Fin d → ℤ) → ℝ := fun k => cf q (γ N t) b k - cf q (γ M t) b k with hδ
  set e : ST d → ℝ := tfs (box M) δ with he
  have he_eq : ∀ x, e x = fld q (γ N t) b x - fld q (γ M t) b x := fun x => by
    rw [he, fld_eq_tfs hNM (γ N t) b, fld, tfs_sub]
  have hes : ContDiff ℝ ∞ e := contDiff_tfs _ _
  have hep : IsSPeriodic e := isSPeriodic_tfs _ _
  -- the key bound `Q_{m+1}(e) ≤ ε² / (2 CS)`-type estimate
  have hQq : ∀ t', Q q e t' ≤ 4 * R ^ 2 := by
    intro t'
    have h1 : Q q e t' = Q q (fun x => fld q (γ N t) b x - fld q (γ M t) b x) t' := by
      congr 1; funext x; exact he_eq x
    rw [h1]
    refine (Q_sub_le q (contDiff_fld q _ b) (contDiff_fld q _ b) t').trans ?_
    have h2 : ∀ L, ∀ s ∈ Set.Icc 0 T, Q q (fld q (γ L s) b) t' ≤ R ^ 2 := fun L s hs =>
      (Q_le_energyQ q (fld q (γ L s)) t' b).trans ((energyQ_fld q _ t').le.trans
        (pow_le_pow_left₀ (norm_nonneg _) (hγR L s hs) 2))
    linarith [h2 N t ht, h2 M t ht]
  have hL2 : ∑ k ∈ box M, δ k ^ 2 ≤ C / (2 * π * ((N : ℝ) + 1)) ^ q := by
    refine le_trans ?_ (hC U₀ hU hUp hE γ hγ0 hγ hγR N M hNM t ht)
    exact Finset.single_le_sum (f := fun b => ∑ k ∈ box M,
      (cf q (γ N t) b k - cf q (γ M t) b k) ^ 2)
      (fun b _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ b)
  have hQm : ∀ t', CS * Q (m + 1) e t' < ε ^ 2 := by
    intro t'
    have hsplit := Q_tfs_split (m + 1) j K (box M) δ t'
    rw [← he, hqj] at hsplit
    have hsK : (K : ℝ) + 1 ≤ ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j := by
      have h1 := le_two_pi_succ_pow (q := 2 * j) (by omega) K
      rwa [pow_mul] at h1
    have hsK0 : 0 < (K : ℝ) + 1 := by positivity
    have hsN := le_two_pi_succ_pow (q := q) (by omega) N
    have hsN0 : 0 < (N : ℝ) + 1 := by positivity
    have t1 : CS * (W * ∑ k ∈ box M, δ k ^ 2) ≤ CS * W * C / ((N : ℝ) + 1) := by
      calc CS * (W * ∑ k ∈ box M, δ k ^ 2) ≤ CS * (W * (C / (2 * π * ((N : ℝ) + 1)) ^ q)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL2 hW0) hCS
        _ ≤ CS * (W * (C / ((N : ℝ) + 1))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hW0) hCS
            exact div_le_div_of_nonneg_left hC0 hsN0 hsN
        _ = CS * W * C / ((N : ℝ) + 1) := by ring
    have t2 : CS * (Q q e t' / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j) ≤
        CS * (4 * R ^ 2) / ((K : ℝ) + 1) := by
      rw [← mul_div_assoc]
      calc CS * Q q e t' / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j
          ≤ CS * (4 * R ^ 2) / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hQq t') hCS) (by positivity)
        _ ≤ CS * (4 * R ^ 2) / ((K : ℝ) + 1) :=
            div_le_div_of_nonneg_left (by positivity) hsK0 hsK
    have t3 : CS * W * C / ((N : ℝ) + 1) < ε ^ 2 / 2 := by
      rw [div_lt_iff₀ hsN0]
      have h1 : 2 * CS * W * C / ε ^ 2 < N₀ := hN₀
      rw [div_lt_iff₀ hε2] at h1
      have h2 : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    have t4 : CS * (4 * R ^ 2) / ((K : ℝ) + 1) < ε ^ 2 / 2 := by
      rw [div_lt_iff₀ hsK0]
      have h1 : 8 * CS * R ^ 2 / ε ^ 2 < K := hK
      rw [div_lt_iff₀ hε2] at h1
      nlinarith
    calc CS * Q (m + 1) e t' ≤ CS * (W * ∑ k ∈ box M, δ k ^ 2 +
          Q q e t' / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j) :=
          mul_le_mul_of_nonneg_left hsplit hCS
      _ = CS * (W * ∑ k ∈ box M, δ k ^ 2) +
          CS * (Q q e t' / ((2 * π * ((K : ℝ) + 1)) ^ 2) ^ j) := by ring
      _ < ε ^ 2 := by linarith
  rw [← Fin.cons_self_tail x]
  refine ⟨?_, fun i => ?_⟩
  · rw [← he_eq]
    refine abs_le_of_sq_le_sq ?_ hε.le
    refine (hsup e hes hep _ _).trans ?_
    exact ((mul_le_mul_of_nonneg_left (Q_mono (Nat.le_succ m) e _) hCS)).trans (hQm _).le
  · have hpd : pd (fld q (γ N t) b) i.succ (Fin.cons (x 0) (Fin.tail x)) -
        pd (fld q (γ M t) b) i.succ (Fin.cons (x 0) (Fin.tail x)) =
        pd e i.succ (Fin.cons (x 0) (Fin.tail x)) := by
      have : e = fun x => fld q (γ N t) b x - fld q (γ M t) b x := funext he_eq
      rw [this, pd_sub_real (contDiff_fld q _ b) (contDiff_fld q _ b)]
    rw [hpd]
    refine abs_le_of_sq_le_sq ?_ hε.le
    refine (hsup _ (contDiff_pd_top hes _) (isSPeriodic_pd hep _) _ _).trans ?_
    exact (mul_le_mul_of_nonneg_left (Q_pd_le i e _) hCS).trans (hQm _).le

end RenewalGeometry.KatoGalerkin
