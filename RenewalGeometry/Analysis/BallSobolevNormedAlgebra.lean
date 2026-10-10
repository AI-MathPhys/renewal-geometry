/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevHilbert

/-!
# `H^s(B)`, `s ≥ 3`, as a commutative Banach algebra on balls of `ℝ⁴`
  (stage D1b of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `jet_eq_of_nil` — an `H^s(B)` jet is determined by its function component (uniqueness of weak
  derivatives);
* `exists_tendsto_smoothJet` — **density of smooth jets** in the Hilbert space `HsB c r s`;
* `norm_smoothJet_mul_le` — the algebra estimate `‖uv‖ ≤ K ‖u‖ ‖v‖` for smooth functions in the
  Hilbert (jet) norm (from `nW_mul_le`);
* `mulJ` — the product of two `H^s(B)` jets (`s ≥ 3`), whose function component is the pointwise
  product (`nilF_mulJ`), and `tendsto_smoothJet_mul`: the jets of products of smooth approximants
  converge to it; hence **`‖mulJ F G‖ ≤ K ‖F‖ ‖G‖`** (`norm_mulJ_le`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg

set_option linter.unusedSectionVars false

/-- In `ℓ²` products the norm is at most the sum of the component norms. -/
theorem norm_le_sum_norm_piLp {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, NormedAddCommGroup (β i)] (x : PiLp 2 β) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  rw [PiLp.norm_eq_of_L2]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun i _ => norm_nonneg _, ?_⟩
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => ‖x i‖ * ‖x j‖)
    (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)

section Jets

variable {n : ℕ} [NeZero n] (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- **An `H^s(B)` jet is determined by its function component.** -/
theorem jet_eq_of_nil {s : ℕ} {F G : JetAmb c r s} (hF : F ∈ HsB c r s) (hG : G ∈ HsB c r s)
    (h : F (nilW s) = G (nilW s)) : F = G := by
  have key : ∀ (L : List (Fin n)) (hL : L ∈ wordsUpTo n s), F ⟨L, hL⟩ = G ⟨L, hL⟩ := by
    intro L
    induction L with
    | nil => intro hL; exact h
    | cons i L ih =>
      intro hL
      have hL' : L ∈ wordsUpTo n s := mem_wordsUpTo.mpr (by
        have := mem_wordsUpTo.mp hL; simp at this; omega)
      have h1 := hF ⟨L, hL'⟩ i hL
      have h2 := hG ⟨L, hL'⟩ i hL
      rw [ih hL'] at h1
      exact weakR_unique c r i h1 h2
  exact PiLp.ext fun w => key w.1 w.2

/-- Components of smooth jets. -/
theorem smoothJet_apply {s : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (w : ↥(wordsUpTo n s)) :
    smoothJet c r s hu w = (memLp_euclBall_of_continuous c hr.out.le
      (contDiff_pdw hu w.1).continuous 2).toLp (pdw u w.1) := rfl

/-- Convergence of smooth jets from the convergence of every component. -/
theorem tendsto_smoothJet_of_components {s : ℕ} {φ : ℕ → (Fin n → ℝ) → ℝ}
    (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) {F : JetAmb c r s}
    (h : ∀ w : ↥(wordsUpTo n s), Tendsto (fun m => eLpNorm (pdw (φ m) w.1 -
      ((F w : L2B c r) : (Fin n → ℝ) → ℝ)) 2 (volume.restrict (euclBall c r))) atTop (𝓝 0)) :
    Tendsto (fun m => smoothJet c r s (hφ m)) atTop (𝓝 F) := by
  have hc : ∀ w : ↥(wordsUpTo n s), Tendsto (fun m => smoothJet c r s (hφ m) w) atTop
      (𝓝 (F w)) := by
    intro w
    simp only [smoothJet_apply]
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine (h w).congr fun m => eLpNorm_congr_ae ?_
    filter_upwards [(memLp_euclBall_of_continuous c hr.out.le
      (contDiff_pdw (hφ m) w.1).continuous 2).coeFn_toLp] with x hx
    simp [hx]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun m => norm_nonneg _) (fun m => norm_le_sum_norm_piLp _) ?_
  have : Tendsto (fun m => ∑ w : ↥(wordsUpTo n s), ‖smoothJet c r s (hφ m) w - F w‖) atTop
      (𝓝 (∑ _w : ↥(wordsUpTo n s), (0 : ℝ))) :=
    tendsto_finsetSum _ fun w _ => (tendsto_iff_norm_sub_tendsto_zero.mp (hc w))
  simpa using this

/-- **Density of smooth jets in `H^s(B)`**: every element of `HsB c r s` is the limit of the jets
of smooth functions. -/
theorem exists_tendsto_smoothJet {s : ℕ} {F : JetAmb c r s} (hF : F ∈ HsB c r s) :
    ∃ (φ : ℕ → (Fin n → ℝ) → ℝ) (hφ : ∀ m, ContDiff ℝ ∞ (φ m)),
      Tendsto (fun m => smoothJet c r s (hφ m)) atTop (𝓝 F) := by
  set u : (Fin n → ℝ) → ℝ := ((F (nilW s) : L2B c r) : (Fin n → ℝ) → ℝ)
  have hu : MemHk (euclBall c r) s u := memHk_of_mem_HsB c r hF s (nilW s) (by simp [nilW])
  obtain ⟨φ, hφ, hcv⟩ := (memHk_iff_exists_convHk c r s).mp hu
  have hex : ∀ w : ↥(wordsUpTo n s), ∃ g : (Fin n → ℝ) → ℝ,
      MemLp g 2 (volume.restrict (euclBall c r)) ∧
      Tendsto (fun m => eLpNorm (pdw (φ m) w.1 - g) 2 (volume.restrict (euclBall c r)))
        atTop (𝓝 0) := fun w => hcv.exists_word_limit w.1 (mem_wordsUpTo.mp w.2)
  choose g hgm hg using hex
  set J : JetAmb c r s := WithLp.toLp 2 fun w => (hgm w).toLp (g w)
  have hJc : ∀ w, (J w : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)] g w :=
    fun w => (hgm w).coeFn_toLp
  have hconv : Tendsto (fun m => smoothJet c r s (hφ m)) atTop (𝓝 J) := by
    refine tendsto_smoothJet_of_components c r hφ fun w => (hg w).congr fun m => ?_
    exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (hJc w).symm)
  have hJmem : J ∈ HsB c r s :=
    (isClosed_HsB c r s).mem_of_tendsto hconv (Eventually.of_forall fun m => smoothJet_mem c r s _)
  refine ⟨φ, hφ, ?_⟩
  convert hconv using 2
  refine (jet_eq_of_nil c r hJmem hF ?_).symm
  -- both function components are `L²` limits of `φ m`
  have h1 : Tendsto (fun m => (memLp_euclBall_of_continuous c hr.out.le (hφ m).continuous 2).toLp
      (φ m)) atTop (𝓝 (J (nilW s))) := by
    have := (continuous_apply (nilW s)).continuousAt.tendsto.comp
      ((PiLp.continuous_ofLp 2 _).continuousAt.tendsto.comp hconv)
    exact this
  have h2 : Tendsto (fun m => (memLp_euclBall_of_continuous c hr.out.le (hφ m).continuous 2).toLp
      (φ m)) atTop (𝓝 (F (nilW s))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hcv.base.2.congr fun m => eLpNorm_congr_ae ?_
    filter_upwards [(memLp_euclBall_of_continuous c hr.out.le (hφ m).continuous 2).coeFn_toLp]
      with x hx
    simp [hx, u]
  exact tendsto_nhds_unique h1 h2

end Jets

/-! ### The algebra estimate in the jet norm -/

section Product

variable (c : Fin 4 → ℝ) (r : ℝ) [hr : Fact (0 < r)]

theorem norm_smoothJet_apply {s : ℕ} {u : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (w : ↥(wordsUpTo 4 s)) :
    ‖smoothJet c r s hu w‖ = (eLpNorm (pdw u w.1) 2 (volume.restrict (euclBall c r))).toReal := by
  rw [smoothJet_apply, Lp.norm_toLp]

/-- The jet norm of a smooth function is at most the classical norm `nW`. -/
theorem norm_smoothJet_le_nW {s : ℕ} {u : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) :
    ‖smoothJet c r s hu‖ ≤ (nW c r s u).toReal := by
  refine (norm_le_sum_norm_piLp _).trans ?_
  simp only [norm_smoothJet_apply]
  unfold nW
  rw [ENNReal.toReal_sum fun w _ => (memLp_ball_of_contDiff c r hr.out (contDiff_pdw hu w)
    2).eLpNorm_lt_top.ne]
  rw [← Finset.sum_coe_sort (wordsUpTo 4 s)]

/-- The classical norm `nW` is at most `#words` times the jet norm. -/
theorem nW_le_card_mul_norm {s : ℕ} {u : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) :
    (nW c r s u).toReal ≤ (wordsUpTo 4 s).card * ‖smoothJet c r s hu‖ := by
  unfold nW
  rw [ENNReal.toReal_sum fun w _ => (memLp_ball_of_contDiff c r hr.out (contDiff_pdw hu w)
    2).eLpNorm_lt_top.ne, ← Finset.sum_coe_sort (wordsUpTo 4 s)]
  calc ∑ w : ↥(wordsUpTo 4 s), (eLpNorm (pdw u w.1) 2 (volume.restrict (euclBall c r))).toReal
      = ∑ w : ↥(wordsUpTo 4 s), ‖smoothJet c r s hu w‖ := by simp only [norm_smoothJet_apply]
    _ ≤ ∑ _w : ↥(wordsUpTo 4 s), ‖smoothJet c r s hu‖ :=
        Finset.sum_le_sum fun w _ => PiLp.norm_apply_le _ w
    _ = (wordsUpTo 4 s).card * ‖smoothJet c r s hu‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

/-- **The algebra estimate in the jet (Hilbert) norm**, smooth functions, `s ≥ 3`. -/
theorem exists_norm_smoothJet_mul_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ {s : ℕ}, 3 ≤ s →
    ∀ {u v : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v),
      ‖smoothJet c r s (hu.mul hv)‖ ≤
        ((wordsUpTo 4 s).card * 2 ^ s * K * (wordsUpTo 4 s).card ^ 2) *
          ‖smoothJet c r s hu‖ * ‖smoothJet c r s hv‖ := by
  obtain ⟨K, hK, hmul⟩ := nW_mul_le c r hr.out
  refine ⟨K.toReal, ENNReal.toReal_nonneg, fun {s} hs {u v} hu hv => ?_⟩
  have h1 := hmul hs hu hv
  have hfin : ∀ {w : (Fin 4 → ℝ) → ℝ}, ContDiff ℝ ∞ w → nW c r s w ≠ ⊤ :=
    fun hw => (nW_lt_top c r hr.out hw s).ne
  have h2 : (nW c r s (fun x => u x * v x)).toReal ≤
      ((wordsUpTo 4 s).card * 2 ^ s * K.toReal) * (nW c r s u).toReal * (nW c r s v).toReal := by
    have := ENNReal.toReal_mono (by
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) hK)
        (hfin hu)) (hfin hv)) h1
    simpa [ENNReal.toReal_mul] using this
  have e : smoothJet c r s (hu.mul hv) = smoothJet c r s (u := fun x => u x * v x) (hu.mul hv) := rfl
  calc ‖smoothJet c r s (hu.mul hv)‖ ≤ (nW c r s (fun x => u x * v x)).toReal :=
        norm_smoothJet_le_nW c r (hu.mul hv)
    _ ≤ ((wordsUpTo 4 s).card * 2 ^ s * K.toReal) * (nW c r s u).toReal * (nW c r s v).toReal := h2
    _ ≤ ((wordsUpTo 4 s).card * 2 ^ s * K.toReal) * ((wordsUpTo 4 s).card * ‖smoothJet c r s hu‖) *
          ((wordsUpTo 4 s).card * ‖smoothJet c r s hv‖) := by
        gcongr
        · exact nW_le_card_mul_norm c r hu
        · exact nW_le_card_mul_norm c r hv
    _ = _ := by ring

end Product

/-! ### The product of two `H^s(B)` jets -/

section Mul

variable (c : Fin 4 → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- The function component of a jet. -/
def nilF {s : ℕ} (F : JetAmb c r s) : (Fin 4 → ℝ) → ℝ :=
  ((F (nilW s) : L2B c r) : (Fin 4 → ℝ) → ℝ)

theorem memHk_nilF {s : ℕ} {F : JetAmb c r s} (hF : F ∈ HsB c r s) :
    MemHk (euclBall c r) s (nilF c r F) :=
  memHk_of_mem_HsB c r hF s (nilW s) (by simp [nilW])

theorem exists_mulJ {s : ℕ} (hs : 3 ≤ s) (F G : HsB c r s) :
    ∃ J ∈ HsB c r s, nilF c r J =ᵐ[volume.restrict (euclBall c r)]
      fun x => nilF c r (F : JetAmb c r s) x * nilF c r (G : JetAmb c r s) x :=
  exists_mem_HsB_of_memHk c r (memHk_mul c r hr.out hs (memHk_nilF c r F.2) (memHk_nilF c r G.2))

/-- **The product of two `H^s(B)` jets** (`s ≥ 3`): the jet of the pointwise product. -/
def mulJ {s : ℕ} (hs : 3 ≤ s) (F G : HsB c r s) : HsB c r s :=
  ⟨(exists_mulJ c r hs F G).choose, (exists_mulJ c r hs F G).choose_spec.1⟩

theorem nilF_mulJ {s : ℕ} (hs : 3 ≤ s) (F G : HsB c r s) :
    nilF c r (mulJ c r hs F G : JetAmb c r s) =ᵐ[volume.restrict (euclBall c r)]
      fun x => nilF c r (F : JetAmb c r s) x * nilF c r (G : JetAmb c r s) x :=
  (exists_mulJ c r hs F G).choose_spec.2

/-- `H^s(B)` elements with a.e. equal function components are equal. -/
theorem HsB_ext {s : ℕ} {F G : HsB c r s}
    (h : nilF c r (F : JetAmb c r s) =ᵐ[volume.restrict (euclBall c r)]
      nilF c r (G : JetAmb c r s)) : F = G :=
  Subtype.ext (jet_eq_of_nil c r F.2 G.2 (Lp.ext h))

/-- Jets of smooth functions are linear in the function. -/
theorem smoothJet_sub {s : ℕ} {u v : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) :
    smoothJet c r s (u := fun x => u x - v x) (hu.sub hv) =
      smoothJet c r s hu - smoothJet c r s hv := by
  refine PiLp.ext fun w => ?_
  simp only [smoothJet_apply, PiLp.sub_apply]
  rw [← MemLp.toLp_sub]
  congr 1
  rw [pdw_sub hu hv w.1]
  rfl

theorem nilF_smoothJet {s : ℕ} {u : (Fin 4 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) :
    nilF c r (smoothJet c r s hu) =ᵐ[volume.restrict (euclBall c r)] u := by
  have := (memLp_euclBall_of_continuous c hr.out.le (contDiff_pdw hu (nilW s).1).continuous
    2).coeFn_toLp
  simpa [nilF, smoothJet_apply, nilW] using this

/-- The function components converge in `L²` along convergent jets. -/
theorem tendsto_nil_of_tendsto {s : ℕ} {Φ : ℕ → JetAmb c r s} {J : JetAmb c r s}
    (h : Tendsto Φ atTop (𝓝 J)) : Tendsto (fun m => Φ m (nilW s)) atTop (𝓝 (J (nilW s))) :=
  (continuous_apply (nilW s)).continuousAt.tendsto.comp
    ((PiLp.continuous_ofLp 2 _).continuousAt.tendsto.comp h)

/-- **Products of smooth approximants converge to the product jet.** -/
theorem tendsto_smoothJet_mul {s : ℕ} (hs : 3 ≤ s) {F G : HsB c r s}
    {φ ψ : ℕ → (Fin 4 → ℝ) → ℝ} (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) (hψ : ∀ m, ContDiff ℝ ∞ (ψ m))
    (hF : Tendsto (fun m => smoothJet c r s (hφ m)) atTop (𝓝 (F : JetAmb c r s)))
    (hG : Tendsto (fun m => smoothJet c r s (hψ m)) atTop (𝓝 (G : JetAmb c r s))) :
    Tendsto (fun m => smoothJet c r s ((hφ m).mul (hψ m))) atTop
      (𝓝 (mulJ c r hs F G : JetAmb c r s)) := by
  obtain ⟨K0, hK0, hK⟩ := exists_norm_smoothJet_mul_le c r
  set K := (wordsUpTo 4 s).card * 2 ^ s * K0 * (wordsUpTo 4 s).card ^ 2 with hKdef
  have hK0' : 0 ≤ K := by positivity
  set a : ℕ → JetAmb c r s := fun m => smoothJet c r s ((hφ m).mul (hψ m))
  -- the bilinear difference estimate
  have hdiff : ∀ m p, ‖a m - a p‖ ≤ K * ‖smoothJet c r s (hφ m) - smoothJet c r s (hφ p)‖ *
      ‖smoothJet c r s (hψ m)‖ + K * ‖smoothJet c r s (hφ p)‖ *
        ‖smoothJet c r s (hψ m) - smoothJet c r s (hψ p)‖ := by
    intro m p
    have e : a m - a p = smoothJet c r s (((hφ m).sub (hφ p)).mul (hψ m)) +
        smoothJet c r s ((hφ p).mul ((hψ m).sub (hψ p))) := by
      refine PiLp.ext fun w => ?_
      simp only [a, smoothJet_apply, PiLp.sub_apply, PiLp.add_apply]
      rw [← MemLp.toLp_sub, ← MemLp.toLp_add]
      congr 1
      have h1 := pdw_sub ((hφ m).mul (hψ m)) ((hφ p).mul (hψ p)) w.1
      have h2 := pdw_add (((hφ m).sub (hφ p)).mul (hψ m)) ((hφ p).mul ((hψ m).sub (hψ p))) w.1
      have e3 : (fun x => φ m x * ψ m x - φ p x * ψ p x) =
          fun x => (φ m x - φ p x) * ψ m x + φ p x * (ψ m x - ψ p x) := by funext x; ring
      rw [e3] at h1
      rw [h1] at h2
      funext x
      have := congrFun h2 x
      simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
      exact this
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have := hK hs ((hφ m).sub (hφ p)) (hψ m)
      rw [smoothJet_sub c r (hφ m) (hφ p)] at this
      exact this
    · have := hK hs (hφ p) ((hψ m).sub (hψ p))
      rw [smoothJet_sub c r (hψ m) (hψ p)] at this
      exact this
  -- the products form a Cauchy sequence
  have hcauchy : CauchySeq a := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have t1 : Tendsto (fun q : ℕ × ℕ => smoothJet c r s (hφ q.1) - smoothJet c r s (hφ q.2))
        atTop (𝓝 ((F : JetAmb c r s) - F)) :=
      (hF.comp tendsto_fst_nat).sub (hF.comp tendsto_snd_nat)
    have t2 : Tendsto (fun q : ℕ × ℕ => smoothJet c r s (hψ q.1) - smoothJet c r s (hψ q.2))
        atTop (𝓝 ((G : JetAmb c r s) - G)) :=
      (hG.comp tendsto_fst_nat).sub (hG.comp tendsto_snd_nat)
    have hR : Tendsto (fun q : ℕ × ℕ => K * ‖smoothJet c r s (hφ q.1) - smoothJet c r s (hφ q.2)‖ *
        ‖smoothJet c r s (hψ q.1)‖ + K * ‖smoothJet c r s (hφ q.2)‖ *
          ‖smoothJet c r s (hψ q.1) - smoothJet c r s (hψ q.2)‖) atTop
        (𝓝 (K * ‖(F : JetAmb c r s) - F‖ * ‖(G : JetAmb c r s)‖ +
          K * ‖(F : JetAmb c r s)‖ * ‖(G : JetAmb c r s) - G‖)) :=
      (((tendsto_const_nhds.mul t1.norm).mul (hG.comp tendsto_fst_nat).norm)).add
        ((tendsto_const_nhds.mul (hF.comp tendsto_snd_nat).norm).mul t2.norm)
    simp only [sub_self, norm_zero, mul_zero, zero_mul, add_zero] at hR
    refine squeeze_zero (fun q => dist_nonneg) (fun q => ?_) hR
    rw [dist_eq_norm]
    exact hdiff q.1 q.2
  obtain ⟨J, hJ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hJmem : J ∈ HsB c r s :=
    (isClosed_HsB c r s).mem_of_tendsto hJ (Eventually.of_forall fun m => smoothJet_mem c r s _)
  suffices hEq : ((mulJ c r hs F G : HsB c r s) : JetAmb c r s) = J by rw [hEq]; exact hJ
  -- identify the limit through its function component
  have hB := isFiniteMeasure_restrict_euclBall c hr.out.le
  set μB := volume.restrict (euclBall c r)
  set u := nilF c r (F : JetAmb c r s)
  set v := nilF c r (G : JetAmb c r s)
  have hum : MemLp u 2 μB := Lp.memLp _
  have hvm : MemLp v 2 μB := Lp.memLp _
  have hφu : Tendsto (fun m => eLpNorm (φ m - u) 2 μB) atTop (𝓝 0) := by
    have := tendsto_nil_of_tendsto c r hF
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at this
    refine this.congr fun m => eLpNorm_congr_ae ?_
    filter_upwards [nilF_smoothJet c r (s := s) (hφ m)] with x hx
    simp only [Pi.sub_apply, u, nilF] at hx ⊢
    rw [hx]
  have hψv : Tendsto (fun m => eLpNorm (ψ m - v) 2 μB) atTop (𝓝 0) := by
    have := tendsto_nil_of_tendsto c r hG
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at this
    refine this.congr fun m => eLpNorm_congr_ae ?_
    filter_upwards [nilF_smoothJet c r (s := s) (hψ m)] with x hx
    simp only [Pi.sub_apply, v, nilF] at hx ⊢
    rw [hx]
  have hJU : Tendsto (fun m => eLpNorm ((fun x => φ m x * ψ m x) - nilF c r J) 2 μB) atTop
      (𝓝 0) := by
    have := tendsto_nil_of_tendsto c r hJ
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at this
    refine this.congr fun m => eLpNorm_congr_ae ?_
    filter_upwards [nilF_smoothJet c r (s := s) ((hφ m).mul (hψ m))] with x hx
    simp only [Pi.sub_apply, nilF] at hx ⊢
    rw [hx]
  set U := nilF c r J
  have hUm : MemLp U 2 μB := Lp.memLp _
  obtain ⟨V, hV⟩ : ∃ V : ℝ≥0∞, V = μB Set.univ ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := ⟨_, rfl⟩
  have hVt : V ≠ ⊤ := by
    rw [hV]; exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have huv : AEStronglyMeasurable (fun x => u x * v x) μB :=
    hum.aestronglyMeasurable.mul hvm.aestronglyMeasurable
  have hbound : ∀ m, eLpNorm (U - fun x => u x * v x) 1 μB ≤
      eLpNorm ((fun x => φ m x * ψ m x) - U) 2 μB * V +
        (eLpNorm (φ m - u) 2 μB * (eLpNorm (ψ m - v) 2 μB + eLpNorm v 2 μB) +
          eLpNorm u 2 μB * eLpNorm (ψ m - v) 2 μB) := by
    intro m
    have hφm := (hφ m).continuous.aestronglyMeasurable (μ := μB)
    have hψm := (hψ m).continuous.aestronglyMeasurable (μ := μB)
    have hΦm := ((hφ m).mul (hψ m)).continuous.aestronglyMeasurable (μ := μB)
    have e1 : (U - fun x => u x * v x) =
        (U - fun x => φ m x * ψ m x) + ((fun x => φ m x * ψ m x) - fun x => u x * v x) := by
      funext x; simp
    have e2 : ((fun x => φ m x * ψ m x) - fun x => u x * v x) =
        (φ m - u) • ψ m + u • (ψ m - v) := by
      funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]; ring
    rw [e1]
    refine (eLpNorm_add_le (hUm.aestronglyMeasurable.sub hΦm) (hΦm.sub huv) le_rfl).trans ?_
    gcongr
    · rw [eLpNorm_sub_comm, hV]
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
        (hΦm.sub hUm.aestronglyMeasurable)
    · rw [e2]
      refine (eLpNorm_add_le ((hφm.sub hum.aestronglyMeasurable).smul hψm)
        (hum.aestronglyMeasurable.smul (hψm.sub hvm.aestronglyMeasurable)) le_rfl).trans ?_
      gcongr
      · refine (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hψm
          (hφm.sub hum.aestronglyMeasurable)).trans ?_
        gcongr
        exact eLpNorm_le_via hψm hvm.aestronglyMeasurable
      · exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
          (hψm.sub hvm.aestronglyMeasurable) hum.aestronglyMeasurable
  have hlim : Tendsto (fun m => eLpNorm ((fun x => φ m x * ψ m x) - U) 2 μB * V +
      (eLpNorm (φ m - u) 2 μB * (eLpNorm (ψ m - v) 2 μB + eLpNorm v 2 μB) +
        eLpNorm u 2 μB * eLpNorm (ψ m - v) 2 μB)) atTop (𝓝 0) := by
    have t1 := ENNReal.Tendsto.mul_const hJU (Or.inr hVt)
    have t2 : Tendsto (fun m => eLpNorm (ψ m - v) 2 μB + eLpNorm v 2 μB) atTop
        (𝓝 (eLpNorm v 2 μB)) := by
      simpa using hψv.add (tendsto_const_nhds (x := eLpNorm v 2 μB))
    have t3 := ENNReal.Tendsto.mul hφu (Or.inr hvm.eLpNorm_lt_top.ne) t2
      (Or.inr ENNReal.zero_ne_top)
    have t4 := ENNReal.Tendsto.const_mul hψv (Or.inr hum.eLpNorm_lt_top.ne)
    simpa using t1.add (t3.add t4)
  have h0 : eLpNorm (U - fun x => u x * v x) 1 μB = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) bot_le
  have hae := (eLpNorm_eq_zero_iff (hUm.aestronglyMeasurable.sub huv) one_ne_zero).mp h0
  have hUuv : U =ᵐ[μB] fun x => u x * v x := hae.mono fun x hx => sub_eq_zero.mp hx
  exact jet_eq_of_nil c r (mulJ c r hs F G).2 hJmem
    (Lp.ext ((nilF_mulJ c r hs F G).trans hUuv.symm))

/-- **The algebra estimate on `H^s(B)`, `s ≥ 3`**: there is `K` with
`‖F G‖ ≤ K ‖F‖ ‖G‖` in the Hilbert (jet) norm. -/
theorem exists_norm_mulJ_le {s : ℕ} (hs : 3 ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F G : HsB c r s, ‖mulJ c r hs F G‖ ≤ K * ‖F‖ * ‖G‖ := by
  obtain ⟨K0, hK0, hK⟩ := exists_norm_smoothJet_mul_le c r
  refine ⟨(wordsUpTo 4 s).card * 2 ^ s * K0 * (wordsUpTo 4 s).card ^ 2, by positivity,
    fun F G => ?_⟩
  obtain ⟨φ, hφ, hF⟩ := exists_tendsto_smoothJet c r F.2
  obtain ⟨ψ, hψ, hG⟩ := exists_tendsto_smoothJet c r G.2
  have hP := tendsto_smoothJet_mul c r hs hφ hψ hF hG
  have h1 : Tendsto (fun m => ‖smoothJet c r s ((hφ m).mul (hψ m))‖) atTop
      (𝓝 ‖(mulJ c r hs F G : JetAmb c r s)‖) := hP.norm
  have h2 : Tendsto (fun m => ((wordsUpTo 4 s).card * 2 ^ s * K0 * (wordsUpTo 4 s).card ^ 2) *
      ‖smoothJet c r s (hφ m)‖ * ‖smoothJet c r s (hψ m)‖) atTop
      (𝓝 (((wordsUpTo 4 s).card * 2 ^ s * K0 * (wordsUpTo 4 s).card ^ 2) *
        ‖(F : JetAmb c r s)‖ * ‖(G : JetAmb c r s)‖)) :=
    (tendsto_const_nhds.mul hF.norm).mul hG.norm
  exact le_of_tendsto_of_tendsto' h1 h2 fun m => hK hs (hφ m) (hψ m)

end Mul

/-! ### The commutative Banach algebra `SobAlg c r s` -/

section Alg

variable (c : Fin 4 → ℝ) (r : ℝ) [hr : Fact (0 < r)] (s : ℕ) [hs : Fact (3 ≤ s)]

/-- **The Banach algebra `H^s(B)`** (`B = B_r(c) ⊂ ℝ⁴`, `s ≥ 3`): the Hilbert space `HsB c r s`
with the pointwise product and the norm rescaled by a constant so that it is submultiplicative. -/
def SobAlg : Type := HsB c r s

namespace SobAlg

instance instAddCommGroup : AddCommGroup (SobAlg c r s) :=
  inferInstanceAs (AddCommGroup (HsB c r s))

instance instModule : Module ℝ (SobAlg c r s) := inferInstanceAs (Module ℝ (HsB c r s))

variable {c r s}

/-- The underlying jet. -/
def jet (F : SobAlg c r s) : HsB c r s := F

/-- An element from its jet. -/
def ofJet (F : HsB c r s) : SobAlg c r s := F

@[simp] theorem jet_ofJet (F : HsB c r s) : jet (ofJet F) = F := rfl
@[simp] theorem ofJet_jet (F : SobAlg c r s) : ofJet (jet F) = F := rfl
@[simp] theorem jet_add (F G : SobAlg c r s) : jet (F + G) = jet F + jet G := rfl
@[simp] theorem jet_sub (F G : SobAlg c r s) : jet (F - G) = jet F - jet G := rfl
@[simp] theorem jet_neg (F : SobAlg c r s) : jet (-F) = -jet F := rfl
@[simp] theorem jet_zero : jet (0 : SobAlg c r s) = 0 := rfl
@[simp] theorem jet_smul (a : ℝ) (F : SobAlg c r s) : jet (a • F) = a • jet F := rfl

/-- The function component (an `L²(B)` representative). -/
def fn (F : SobAlg c r s) : (Fin 4 → ℝ) → ℝ := nilF c r ((jet F : HsB c r s) : JetAmb c r s)

theorem memHk_fn (F : SobAlg c r s) : MemHk (euclBall c r) s (fn F) := memHk_nilF c r (jet F).2

theorem memLp_fn (F : SobAlg c r s) : MemLp (fn F) 2 (volume.restrict (euclBall c r)) :=
  Lp.memLp _

/-- Elements are determined by their function components. -/
theorem ext_fn {F G : SobAlg c r s}
    (h : fn F =ᵐ[volume.restrict (euclBall c r)] fn G) : F = G :=
  HsB_ext c r h

instance instMul : Mul (SobAlg c r s) := ⟨fun F G => ofJet (mulJ c r hs.out (jet F) (jet G))⟩

instance instOne : One (SobAlg c r s) :=
  ⟨ofJet ⟨smoothJet c r s (u := fun _ => (1 : ℝ)) contDiff_const, smoothJet_mem c r s _⟩⟩

theorem fn_mul (F G : SobAlg c r s) :
    fn (F * G) =ᵐ[volume.restrict (euclBall c r)] fun x => fn F x * fn G x :=
  nilF_mulJ c r hs.out (jet F) (jet G)

theorem fn_one : fn (1 : SobAlg c r s) =ᵐ[volume.restrict (euclBall c r)] fun _ => 1 :=
  nilF_smoothJet c r (s := s) (u := fun _ => (1 : ℝ)) contDiff_const

theorem fn_add (F G : SobAlg c r s) :
    fn (F + G) =ᵐ[volume.restrict (euclBall c r)] fun x => fn F x + fn G x :=
  Lp.coeFn_add ((jet F : JetAmb c r s) (nilW s)) ((jet G : JetAmb c r s) (nilW s))

theorem fn_sub (F G : SobAlg c r s) :
    fn (F - G) =ᵐ[volume.restrict (euclBall c r)] fun x => fn F x - fn G x :=
  Lp.coeFn_sub ((jet F : JetAmb c r s) (nilW s)) ((jet G : JetAmb c r s) (nilW s))

theorem fn_neg (F : SobAlg c r s) :
    fn (-F) =ᵐ[volume.restrict (euclBall c r)] fun x => -fn F x :=
  Lp.coeFn_neg ((jet F : JetAmb c r s) (nilW s))

theorem fn_zero : fn (0 : SobAlg c r s) =ᵐ[volume.restrict (euclBall c r)] fun _ => 0 :=
  Lp.coeFn_zero _ _ _

theorem fn_smul (a : ℝ) (F : SobAlg c r s) :
    fn (a • F) =ᵐ[volume.restrict (euclBall c r)] fun x => a * fn F x :=
  Lp.coeFn_smul a ((jet F : JetAmb c r s) (nilW s))

/-- `SobAlg c r s` is a commutative ring under the pointwise product. -/
instance instCommRing : CommRing (SobAlg c r s) :=
  { instAddCommGroup c r s with
    mul := (· * ·)
    one := 1
    mul_assoc := fun F G H => ext_fn (by
      filter_upwards [fn_mul (F * G) H, fn_mul F G, fn_mul F (G * H), fn_mul G H]
        with x h1 h2 h3 h4
      rw [h1, h2, h3, h4]; ring)
    one_mul := fun F => ext_fn (by
      filter_upwards [fn_mul 1 F, fn_one (c := c) (r := r) (s := s)] with x h1 h2
      rw [h1, h2]; ring)
    mul_one := fun F => ext_fn (by
      filter_upwards [fn_mul F 1, fn_one (c := c) (r := r) (s := s)] with x h1 h2
      rw [h1, h2]; ring)
    left_distrib := fun F G H => ext_fn (by
      filter_upwards [fn_mul F (G + H), fn_add G H, fn_add (F * G) (F * H), fn_mul F G,
        fn_mul F H] with x h1 h2 h3 h4 h5
      rw [h1, h2, h3, h4, h5]; ring)
    right_distrib := fun F G H => ext_fn (by
      filter_upwards [fn_mul (F + G) H, fn_add F G, fn_add (F * H) (G * H), fn_mul F H,
        fn_mul G H] with x h1 h2 h3 h4 h5
      rw [h1, h2, h3, h4, h5]; ring)
    zero_mul := fun F => ext_fn (by
      filter_upwards [fn_mul 0 F, fn_zero (c := c) (r := r) (s := s)] with x h1 h2
      rw [h1, h2]; ring)
    mul_zero := fun F => ext_fn (by
      filter_upwards [fn_mul F 0, fn_zero (c := c) (r := r) (s := s)] with x h1 h2
      rw [h1, h2]; ring)
    mul_comm := fun F G => ext_fn (by
      filter_upwards [fn_mul F G, fn_mul G F] with x h1 h2
      rw [h1, h2]; ring)
    natCast := fun n => ((n : ℝ) • (1 : SobAlg c r s))
    natCast_zero := by simp
    natCast_succ := fun n => by simp [add_smul]
    intCast := fun z => ((z : ℝ) • (1 : SobAlg c r s))
    intCast_ofNat := fun n => by simp only [Int.cast_natCast]; rfl
    intCast_negSucc := fun n => by
      simp only [Int.cast_negSucc, neg_smul]
      congr 1
    npow := npowRec
    npow_zero := fun _ => rfl
    npow_succ := fun _ _ => rfl }

theorem mul_def (F G : SobAlg c r s) : F * G = ofJet (mulJ c r hs.out (jet F) (jet G)) := rfl

/-- `SobAlg c r s` is an `ℝ`-algebra. -/
instance instAlgebra : Algebra ℝ (SobAlg c r s) :=
  Algebra.ofModule
    (fun a F G => ext_fn (by
      filter_upwards [fn_mul (a • F) G, fn_smul a F, fn_smul a (F * G), fn_mul F G]
        with x h1 h2 h3 h4
      rw [h1, h2, h3, h4]; ring))
    (fun a F G => ext_fn (by
      filter_upwards [fn_mul F (a • G), fn_smul a G, fn_smul a (F * G), fn_mul F G]
        with x h1 h2 h3 h4
      rw [h1, h2, h3, h4]; ring))

variable (c r s)

/-- The rescaling constant of the norm. -/
def Kal : ℝ := (exists_norm_mulJ_le c r hs.out).choose + 1

theorem Kal_pos : 0 < Kal c r s := by
  have := (exists_norm_mulJ_le c r hs.out).choose_spec.1
  unfold Kal; linarith

theorem norm_mulJ_le_Kal (F G : HsB c r s) :
    ‖mulJ c r hs.out F G‖ ≤ Kal c r s * ‖F‖ * ‖G‖ := by
  refine ((exists_norm_mulJ_le c r hs.out).choose_spec.2 F G).trans ?_
  gcongr
  unfold Kal; linarith

/-- The rescaling map into the Hilbert space `HsB c r s`. -/
def scaleL : SobAlg c r s →ₗ[ℝ] HsB c r s where
  toFun F := Kal c r s • jet F
  map_add' F G := by simp [smul_add]
  map_smul' a F := by simp [smul_comm a]

theorem scaleL_injective : Function.Injective (scaleL c r s) := by
  intro F G h
  have h' : Kal c r s • jet F = Kal c r s • jet G := h
  exact smul_right_injective _ (Kal_pos c r s).ne' h'

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (SobAlg c r s) :=
  NormedAddCommGroup.induced (SobAlg c r s) (HsB c r s) (scaleL c r s) (scaleL_injective c r s)

variable {c r s}

theorem norm_def (F : SobAlg c r s) : ‖F‖ = Kal c r s * ‖jet F‖ := by
  change ‖Kal c r s • jet F‖ = _
  rw [norm_smul, Real.norm_of_nonneg (Kal_pos c r s).le]

theorem norm_jet_le (F : SobAlg c r s) : ‖jet F‖ ≤ (Kal c r s)⁻¹ * ‖F‖ := by
  rw [norm_def, ← mul_assoc, inv_mul_cancel₀ (Kal_pos c r s).ne', one_mul]

noncomputable instance instNormedSpace : NormedSpace ℝ (SobAlg c r s) :=
  NormedSpace.induced ℝ (SobAlg c r s) (HsB c r s) (scaleL c r s)

/-- **`SobAlg c r s` is a normed commutative ring** (submultiplicative norm). -/
noncomputable instance instNormedCommRing : NormedCommRing (SobAlg c r s) :=
  { instNormedAddCommGroup c r s, instCommRing (c := c) (r := r) (s := s) with
    norm_mul_le := fun F G => by
      rw [norm_def, norm_def, norm_def]
      have h := norm_mulJ_le_Kal c r s (jet F) (jet G)
      have hK := (Kal_pos c r s).le
      calc Kal c r s * ‖jet (F * G)‖ = Kal c r s * ‖mulJ c r hs.out (jet F) (jet G)‖ := rfl
        _ ≤ Kal c r s * (Kal c r s * ‖jet F‖ * ‖jet G‖) := by gcongr
        _ = Kal c r s * ‖jet F‖ * (Kal c r s * ‖jet G‖) := by ring }

/-- **`SobAlg c r s` is a normed `ℝ`-algebra.** -/
noncomputable instance instNormedAlgebra : NormedAlgebra ℝ (SobAlg c r s) :=
  { instAlgebra (c := c) (r := r) (s := s) with
    norm_smul_le := fun a F => norm_smul_le a F }

theorem isometry_scaleL : Isometry (scaleL c r s) :=
  Isometry.of_dist_eq fun F G => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]; rfl

theorem scaleL_surjective : Function.Surjective (scaleL c r s) := by
  intro F
  refine ⟨ofJet ((Kal c r s)⁻¹ • F), ?_⟩
  change Kal c r s • ((Kal c r s)⁻¹ • F) = F
  rw [smul_smul, mul_inv_cancel₀ (Kal_pos c r s).ne', one_smul]

/-- **`SobAlg c r s` is complete** (a Banach algebra). -/
instance instCompleteSpace : CompleteSpace (SobAlg c r s) := by
  rw [completeSpace_iff_isComplete_univ]
  have hui := (isometry_scaleL (c := c) (r := r) (s := s)).isUniformInducing
  rw [← hui.isComplete_iff, image_univ, (scaleL_surjective (c := c) (r := r) (s := s)).range_eq]
  exact isComplete_univ

end SobAlg

end Alg

end RenewalGeometry.BallAnalysis.BallAlg
