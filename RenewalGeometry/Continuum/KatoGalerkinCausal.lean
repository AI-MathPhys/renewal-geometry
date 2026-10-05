/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoGalerkinCFL

/-!
# The `H^m` difference energy estimate and discrete causal stability of the midpoint scheme

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` of the
Einstein–Standard-Model action-closure manuscript, `eq:generated-causal`: "If two midpoint
trajectories have a normalized forcing difference `r_j`, the same energy calculation at any
`3 ≤ m ≤ q - 1` gives `max_{jτ ≤ T} ‖U^j - V^j‖_{H^m} ≤ C_T(‖U^0 - V^0‖_{H^m} + τ Σ_j ‖r_j‖_{H^m})`
with `C_T` independent of `N, τ`."  Setting of `KatoGalerkinODE`: `∂_tU + Σ_i A^i(U)∂_iU = F(U)` on
`𝕋^d`, smooth real symmetric `A^i`, smooth `F`, generator `G(U) = F(U) - Σ_i A^i(U)∂_iU`.

* `abs_sd_mul_le` — the pointwise Leibniz bound `|∂^L(fg)| ≤ 2^{|L|} M_f M_g`;
* **`pairQ_genG_sub_le`** — **the `H^m` difference energy estimate**: if the derivatives of `U`, `V`
  of order `≤ m + 1` are bounded by `B` on a slice, then
  `⟨U - V, G(U) - G(V)⟩_{H^m} ≤ K_B ‖U - V‖²_{H^m}` (Hadamard decomposition of the difference,
  commutator form of the Leibniz rule, symmetric integration by parts for the principal part
  `A^i(U)∂_i(U - V)`);
* `pairQ_genG_sub_le_Hq` — the same on the `H^q` ball, `q ≥ m + 1 + m_s`, `m_s > d/2`
  (Sobolev embedding);
* `hmInner`, `inner_GN_sub_le` — the `H^m` inner product on the Galerkin space and the
  cutoff-uniform difference energy inequality `⟪G_N a - G_N b, a - b⟫_{H^m} ≤ K ‖a - b‖²_{H^m}`
  (the projection disappears from the pairing);
* **`midpoint_causal_Hm`** (`eq:generated-causal`) — for two midpoint trajectories in the `H^q` ball
  of radius `R`, `U^{j+1} = U^j + τ G_N(m_U^j)`, `V^{j+1} = V^j + τ(G_N(m_V^j) + r_j)`:
  `‖U^n - V^n‖_{H^m} ≤ e^{2Knτ}(‖U^0 - V^0‖_{H^m} + 2τ Σ_{j<n} ‖r_j‖_{H^m})` with `K` depending only
  on `R` (`τK ≤ 1`), i.e. `C_T = 2e^{2KT}` independent of `N` and `τ`.

Disclosed: `Σ = 𝕋^d`; the range is `m + 1 + m_s ≤ q` with `m_s > d/2` (for `d = 3`: `m ≤ q - 3`),
narrower than the manuscript's `m ≤ q - 1` but containing the order `m = s + 4 = q - p - 4` at which
`eq:generated-time-rate` uses the estimate.
-/

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.KatoCausal

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoCFL

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### Pointwise bounds -/

/-- **Pointwise Leibniz bound**: `|∂^L(fg)(x)| ≤ 2^{|L|} M_f M_g` when all derivatives of `f`, `g`
of order `≤ |L|` at `x` are bounded by `M_f`, `M_g`. -/
theorem abs_sd_mul_le {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (L : List (Fin d)) (x : ST d) {Mf Mg : ℝ}
    (hMf : ∀ L' : List (Fin d), L'.length ≤ L.length → |sd L' f x| ≤ Mf)
    (hMg : ∀ L' : List (Fin d), L'.length ≤ L.length → |sd L' g x| ≤ Mg) :
    |sd L (fun x => f x * g x) x| ≤ 2 ^ L.length * (Mf * Mg) := by
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf [] (Nat.zero_le _))
  rw [sd_mul L hf hg x]
  refine (list_abs_sum_le _ _).trans ?_
  calc ((splits L).map fun p => |sd p.1 f x * sd p.2 g x|).sum
      ≤ ((splits L).map fun _ => Mf * Mg).sum := by
        refine List.sum_le_sum fun p hp => ?_
        have hlen := length_of_mem_splits hp
        rw [abs_mul]
        exact mul_le_mul (hMf _ (by omega)) (hMg _ (by omega)) (abs_nonneg _) hMf0
    _ = 2 ^ L.length * (Mf * Mg) := by
        rw [List.map_const', List.sum_replicate, nsmul_eq_mul, length_splits]; push_cast; ring

/-- Bounds for the pair field. -/
theorem abs_sd_pairF_le {u v : Fin n → ST d → ℝ} {x : ST d} {B : ℝ} {L : List (Fin d)}
    (hBu : ∀ b, |sd L (u b) x| ≤ B)
    (hBv : ∀ b, |sd L (v b) x| ≤ B) (c : Fin (n + n)) : |sd L (KatoCFL.pairF u v c) x| ≤ B := by
  refine Fin.addCases (fun c => ?_) (fun c => ?_) c
  · simpa only [KatoCFL.pairF, Fin.append_left] using hBu c
  · simpa only [KatoCFL.pairF, Fin.append_right] using hBv c


/-! ### The word derivative of the generator difference -/

section Diff

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- The difference field `e = U - V`. -/
abbrev dif (u v : Fin n → ST d → ℝ) : Fin n → ST d → ℝ := fun b x => u b x - v b x

/-- The Hadamard quotient fields `Ψ^F_{ac}(U, V)` and `Ψ^A_{iabc}(U, V)`. -/
abbrev psiF (F : Fin n → (Fin n → ℝ) → ℝ) (u v : Fin n → ST d → ℝ) (a c : Fin n) : ST d → ℝ :=
  compF (onPair (hadQ (F a) c)) (pairF u v)

abbrev psiA (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (u v : Fin n → ST d → ℝ) (i : Fin d)
    (a b c : Fin n) : ST d → ℝ :=
  compF (onPair (hadQ (A i a b) c)) (pairF u v)

theorem contDiff_dif {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    (hv : ∀ b, ContDiff ℝ ∞ (v b)) (b : Fin n) : ContDiff ℝ ∞ (dif u v b) :=
  (hu b).sub (hv b)

theorem isSPeriodic_dif {u v : Fin n → ST d → ℝ} (hu : ∀ b, IsSPeriodic (u b))
    (hv : ∀ b, IsSPeriodic (v b)) (b : Fin n) : IsSPeriodic (dif u v b) := fun k x => by
  simp only [dif, hu b k x, hv b k x]

theorem contDiff_psiF (hF : ∀ a, ContDiff ℝ ∞ (F a)) {u v : Fin n → ST d → ℝ}
    (hu : ∀ b, ContDiff ℝ ∞ (u b)) (hv : ∀ b, ContDiff ℝ ∞ (v b)) (a c : Fin n) :
    ContDiff ℝ ∞ (psiF F u v a c) :=
  contDiff_compF (contDiff_onPair (contDiff_hadQ (hF a) c)) (contDiff_pairF hu hv)

theorem contDiff_psiA (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) {u v : Fin n → ST d → ℝ}
    (hu : ∀ b, ContDiff ℝ ∞ (u b)) (hv : ∀ b, ContDiff ℝ ∞ (v b)) (i : Fin d) (a b c : Fin n) :
    ContDiff ℝ ∞ (psiA A u v i a b c) :=
  contDiff_compF (contDiff_onPair (contDiff_hadQ (hA i a b) c)) (contDiff_pairF hu hv)

/-- **The word derivative of the generator difference** in commutator form:
`∂^L(G(U) - G(V))_a = Σ_c ∂^L(e_cΨ^F_{ac}) - Σ_{i,b} (A^i_{ab}(U)∂_i∂^Le_b
  + Σ_{NE splits} ∂^{L₁}A^i_{ab}(U) ∂^{L₂}∂_ie_b + Σ_c ∂^L(e_c Ψ^A_{iabc} ∂_iv_b))`. -/
theorem sd_genG_sub (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (hv : ∀ b, ContDiff ℝ ∞ (v b))
    (a : Fin n) (L : List (Fin d)) (x : ST d) :
    sd L (fun x => genG A F u a x - genG A F v a x) x =
      ∑ c, sd L (fun x => dif u v c x * psiF F u v a c x) x -
        ∑ i, ∑ b, (compF (A i a b) u x * pd (sd L (dif u v b)) i.succ x +
          ((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
            sd p.2 (pd (dif u v b) i.succ) x).sum +
          ∑ c, sd L (fun x => dif u v c x * (psiA A u v i a b c x * pd (v b) i.succ x)) x) := by
  have he := contDiff_dif hu hv
  have hpF := contDiff_psiF hF hu hv
  have hpA := contDiff_psiA hA hu hv
  have hAu : ∀ i a b, ContDiff ℝ ∞ (compF (A i a b) u) := fun i a b => contDiff_compF (hA i a b) hu
  have hfun : (fun x => genG A F u a x - genG A F v a x) = fun x =>
      (∑ c, dif u v c x * psiF F u v a c x) -
        ∑ i, ∑ b, (compF (A i a b) u x * pd (dif u v b) i.succ x +
          ∑ c, dif u v c x * (psiA A u v i a b c x * pd (v b) i.succ x)) := by
    funext x
    exact genG_sub_eq hA hF hu hv a x
  have h1 : ∀ c, ContDiff ℝ ∞ (fun x => dif u v c x * psiF F u v a c x) := fun c =>
    (he c).mul (hpF a c)
  have h3 : ∀ i b c, ContDiff ℝ ∞
      (fun x => dif u v c x * (psiA A u v i a b c x * pd (v b) i.succ x)) := fun i b c =>
    (he c).mul ((hpA i a b c).mul (contDiff_pd_top (hv b) _))
  have h2 : ∀ i b, ContDiff ℝ ∞ (fun x => compF (A i a b) u x * pd (dif u v b) i.succ x) :=
    fun i b => (hAu i a b).mul (contDiff_pd_top (he b) _)
  have h23 : ∀ i b, ContDiff ℝ ∞ (fun x => compF (A i a b) u x * pd (dif u v b) i.succ x +
      ∑ c, dif u v c x * (psiA A u v i a b c x * pd (v b) i.succ x)) := fun i b =>
    (h2 i b).add (ContDiff.sum fun c _ => h3 i b c)
  rw [hfun, sd_sub L (ContDiff.sum fun c _ => h1 c)
    (ContDiff.sum fun i _ => ContDiff.sum fun b _ => h23 i b)]
  simp only
  rw [sd_sum L Finset.univ h1, sd_sum L Finset.univ (fun i => ContDiff.sum fun b _ => h23 i b)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sd_sum L Finset.univ (fun b => h23 i b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sd_add L (h2 i b) (ContDiff.sum fun c _ => h3 i b c), sd_sum L Finset.univ (h3 i b)]
  simp only
  rw [sd_mul_comm L (hAu i a b) (contDiff_pd_top (he b) _) x, sd_pd L (he b) i]

end Diff

/-! ### The pointwise difference estimate -/

section Pointwise

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- The constant of the pointwise difference bound. -/
def Dcst (d n m : ℕ) (P1 P2 B : ℝ) : ℝ :=
  n * (2 ^ m * P2) + d * n * (2 ^ m * P1 + n * (2 ^ m * (2 ^ m * P2 * B)))

theorem Dcst_nonneg (d n m : ℕ) {P1 P2 B : ℝ} (h1 : 0 ≤ P1) (h2 : 0 ≤ P2) (hB : 0 ≤ B) :
    0 ≤ Dcst d n m P1 P2 B := by unfold Dcst; positivity

/-- **Pointwise difference bound**: if the derivatives of `U`, `V` of order `≤ m + 1` are bounded
by `B` at `x = (t, y)` and the coefficient derivatives of order `≤ m` by `M`, then for every word
`|L| ≤ m`, with `e = U - V` and `σ = Σ_{c, |L'| ≤ m} |∂^{L'}e_c(x)|`:
`Σ_a ∂^Le_a ∂^L(G(U) - G(V))_a + Σ_{i,a,b} ∂^Le_a A^i_{ab}(U) ∂_i∂^Le_b
  ≤ ½ Σ_a (∂^Le_a)² + ½ n (D σ)²`. -/
theorem pointwise_diff_key (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (hv : ∀ b, ContDiff ℝ ∞ (v b))
    {t : ℝ} {y : Fin d → ℝ} {m : ℕ} {B M : ℝ} (hB0 : 0 ≤ B) (hM0 : 0 ≤ M)
    (hBu : ∀ b (L : List (Fin d)), L.length ≤ m + 1 → |sd L (u b) (Fin.cons t y)| ≤ B)
    (hBv : ∀ b (L : List (Fin d)), L.length ≤ m + 1 → |sd L (v b) (Fin.cons t y)| ≤ B)
    (hMA : ∀ i a b, ∀ k ≤ m, ‖iteratedFDeriv ℝ k (A i a b) (vslice u t y)‖ ≤ M)
    (hMF : ∀ a c, ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (onPair (hadQ (F a) c)) (vslice (pairF u v) t y)‖ ≤ M)
    (hMP : ∀ i a b c, ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (onPair (hadQ (A i a b) c)) (vslice (pairF u v) t y)‖ ≤ M)
    (L : List (Fin d)) (hL : L.length ≤ m) :
    ∑ a, sd L (dif u v a) (Fin.cons t y) *
        sd L (fun x => genG A F u a x - genG A F v a x) (Fin.cons t y) +
      ∑ i, ∑ a, ∑ b, sd L (dif u v a) (Fin.cons t y) * compF (A i a b) u (Fin.cons t y) *
        pd (sd L (dif u v b)) i.succ (Fin.cons t y) ≤
      (1 / 2) * ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2 +
        (1 / 2) * n * (Dcst d n m (cq m * M * Bc d n m B ^ m)
          (cq m * M * Bc d (n + n) m B ^ m) B * sig m (dif u v) t y) ^ 2 := by
  set x : ST d := Fin.cons t y with hx
  set P1 := cq m * M * Bc d n m B ^ m with hP1
  set P2 := cq m * M * Bc d (n + n) m B ^ m with hP2
  set σ := sig m (dif u v) t y with hσ
  have hσ0 : 0 ≤ σ := sig_nonneg _ _ _ _
  have hP10 : 0 ≤ P1 := by
    have := one_le_Bc d n m hB0; rw [hP1]; exact mul_nonneg (mul_nonneg (cq_nonneg m) hM0)
      (pow_nonneg (by linarith) _)
  have hP20 : 0 ≤ P2 := by
    have := one_le_Bc d (n + n) m hB0; rw [hP2]; exact mul_nonneg (mul_nonneg (cq_nonneg m) hM0)
      (pow_nonneg (by linarith) _)
  have he := contDiff_dif hu hv
  have hpF := contDiff_psiF hF hu hv
  have hpA := contDiff_psiA hA hu hv
  have h2m : ∀ k, k ≤ m → (2 : ℝ) ^ k ≤ 2 ^ m := fun k hk =>
    pow_le_pow_right₀ (by norm_num) hk
  -- bounds
  have hE : ∀ c (L' : List (Fin d)), L'.length ≤ m → |sd L' (dif u v c) x| ≤ σ :=
    fun c L' hL' => abs_sd_le_sig (dif u v) t y c hL'
  have hBu' : ∀ b (L' : List (Fin d)), L'.length ≤ m → |sd L' (u b) x| ≤ B :=
    fun b L' hL' => hBu b L' (by omega)
  have hBp : ∀ c (L' : List (Fin d)), L'.length ≤ m → |sd L' (pairF u v c) x| ≤ B :=
    fun c L' hL' => abs_sd_pairF_le (hBu' · L' hL') (fun b => hBv b L' (by omega)) c
  have hPA : ∀ i a b (L' : List (Fin d)), L'.length ≤ m →
      |sd L' (compF (A i a b) u) x| ≤ P1 := fun i a b L' hL' =>
    abs_sd_compF_le_small (hA i a b) hu hB0 hBu' (hMA i a b) L' hL' hL'
  have hPF : ∀ a c (L' : List (Fin d)), L'.length ≤ m → |sd L' (psiF F u v a c) x| ≤ P2 :=
    fun a c L' hL' => abs_sd_compF_le_small (contDiff_onPair (contDiff_hadQ (hF a) c))
      (contDiff_pairF hu hv) hB0 hBp (hMF a c) L' hL' hL'
  have hPP : ∀ i a b c (L' : List (Fin d)), L'.length ≤ m →
      |sd L' (psiA A u v i a b c) x| ≤ P2 :=
    fun i a b c L' hL' => abs_sd_compF_le_small (contDiff_onPair (contDiff_hadQ (hA i a b) c))
      (contDiff_pairF hu hv) hB0 hBp (hMP i a b c) L' hL' hL'
  have hPV : ∀ i a b c (L' : List (Fin d)), L'.length ≤ m →
      |sd L' (fun x => psiA A u v i a b c x * pd (v b) i.succ x) x| ≤ 2 ^ m * P2 * B := by
    intro i a b c L' hL'
    refine (abs_sd_mul_le (Mf := P2) (Mg := B) (hpA i a b c) (contDiff_pd_top (hv b) _) L' x
      (fun L'' hL'' => hPP i a b c L'' (by omega)) (fun L'' hL'' => ?_)).trans ?_
    · rw [← sd_cons]; exact hBv b _ (by simp; omega)
    · have := h2m _ hL'
      have : 0 ≤ P2 * B := mul_nonneg hP20 hB0
      nlinarith
  -- the three remainder families
  have hT1 : ∀ a c, |sd L (fun x => dif u v c x * psiF F u v a c x) x| ≤ 2 ^ m * P2 * σ := by
    intro a c
    refine (abs_sd_mul_le (Mf := σ) (Mg := P2) (he c) (hpF a c) L x (fun L' hL' => hE c L' (by omega))
      (fun L' hL' => hPF a c L' (by omega))).trans ?_
    have := h2m _ hL
    have : 0 ≤ σ * P2 := mul_nonneg hσ0 hP20
    nlinarith
  have hNE : ∀ i a b, |((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
      sd p.2 (pd (dif u v b) i.succ) x).sum| ≤ 2 ^ m * P1 * σ := by
    intro i a b
    refine (list_abs_sum_le _ _).trans ?_
    calc ((splitsNE L).map fun p => |sd p.1 (compF (A i a b) u) x *
          sd p.2 (pd (dif u v b) i.succ) x|).sum
        ≤ ((splitsNE L).map fun _ => P1 * σ).sum := by
          refine List.sum_le_sum fun p hp => ?_
          obtain ⟨hps, hp1⟩ := mem_splitsNE hp
          have hlen := length_of_mem_splits hps
          have hp1pos : 1 ≤ p.1.length := List.length_pos_iff.2 hp1
          rw [abs_mul]
          refine mul_le_mul (hPA i a b p.1 (by omega)) ?_ (abs_nonneg _) hP10
          rw [← sd_cons]
          exact hE b _ (by simp; omega)
      _ = (splitsNE L).length * (P1 * σ) := by
          rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ ≤ 2 ^ m * P1 * σ := by
          have h1 : ((splitsNE L).length : ℝ) ≤ 2 ^ m := by
            have := (length_splitsNE_le L).trans (Nat.pow_le_pow_right (by norm_num) hL)
            exact_mod_cast this
          have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hP10 hσ0)
          linarith
  have hT3 : ∀ i a b c, |sd L (fun x => dif u v c x * (psiA A u v i a b c x *
      pd (v b) i.succ x)) x| ≤ 2 ^ m * (2 ^ m * P2 * B) * σ := by
    intro i a b c
    refine (abs_sd_mul_le (Mf := σ) (Mg := 2 ^ m * P2 * B) (he c)
      ((hpA i a b c).mul (contDiff_pd_top (hv b) _)) L x
      (fun L' hL' => hE c L' (by omega)) (fun L' hL' => hPV i a b c L' (by omega))).trans ?_
    have := h2m _ hL
    have : 0 ≤ σ * (2 ^ m * P2 * B) := by positivity
    nlinarith
  -- the remainder
  set R : Fin n → ℝ := fun a => ∑ c, sd L (fun x => dif u v c x * psiF F u v a c x) x -
    ∑ i, ∑ b, (((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
        sd p.2 (pd (dif u v b) i.succ) x).sum +
      ∑ c, sd L (fun x => dif u v c x * (psiA A u v i a b c x * pd (v b) i.succ x)) x)
    with hR
  set D := Dcst d n m P1 P2 B with hD
  have hRb : ∀ a, |R a| ≤ D * σ := by
    intro a
    simp only [hR]
    refine (abs_sub _ _).trans ?_
    have h1 : |∑ c, sd L (fun x => dif u v c x * psiF F u v a c x) x| ≤ n * (2 ^ m * P2 * σ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ c, |sd L (fun x => dif u v c x * psiF F u v a c x) x|
          ≤ ∑ _c : Fin n, 2 ^ m * P2 * σ := Finset.sum_le_sum fun c _ => hT1 a c
        _ = n * (2 ^ m * P2 * σ) := by simp
    have h2 : |∑ i, ∑ b, (((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
        sd p.2 (pd (dif u v b) i.succ) x).sum +
      ∑ c, sd L (fun x => dif u v c x * (psiA A u v i a b c x * pd (v b) i.succ x)) x)| ≤
        d * n * (2 ^ m * P1 * σ + n * (2 ^ m * (2 ^ m * P2 * B) * σ)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |∑ b, (((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
            sd p.2 (pd (dif u v b) i.succ) x).sum + ∑ c, sd L (fun x => dif u v c x *
              (psiA A u v i a b c x * pd (v b) i.succ x)) x)|
          ≤ ∑ _i : Fin d, n * (2 ^ m * P1 * σ + n * (2 ^ m * (2 ^ m * P2 * B) * σ)) := by
            refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc ∑ b, |((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
                  sd p.2 (pd (dif u v b) i.succ) x).sum + ∑ c, sd L (fun x => dif u v c x *
                    (psiA A u v i a b c x * pd (v b) i.succ x)) x|
                ≤ ∑ _b : Fin n, (2 ^ m * P1 * σ + n * (2 ^ m * (2 ^ m * P2 * B) * σ)) := by
                  refine Finset.sum_le_sum fun b _ => (abs_add_le _ _).trans
                    (add_le_add (hNE i a b) ?_)
                  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                  calc ∑ c, |sd L (fun x => dif u v c x * (psiA A u v i a b c x *
                        pd (v b) i.succ x)) x| ≤ ∑ _c : Fin n, 2 ^ m * (2 ^ m * P2 * B) * σ :=
                        Finset.sum_le_sum fun c _ => hT3 i a b c
                    _ = n * (2 ^ m * (2 ^ m * P2 * B) * σ) := by simp
              _ = n * (2 ^ m * P1 * σ + n * (2 ^ m * (2 ^ m * P2 * B) * σ)) := by simp; ring
        _ = d * n * (2 ^ m * P1 * σ + n * (2 ^ m * (2 ^ m * P2 * B) * σ)) := by simp; ring
    calc _ ≤ n * (2 ^ m * P2 * σ) +
          d * n * (2 ^ m * P1 * σ + n * (2 ^ m * (2 ^ m * P2 * B) * σ)) := add_le_add h1 h2
      _ = D * σ := by rw [hD]; unfold Dcst; ring
  -- the identity
  have hident : ∑ a, sd L (dif u v a) x * sd L (fun x => genG A F u a x - genG A F v a x) x +
      ∑ i, ∑ a, ∑ b, sd L (dif u v a) x * compF (A i a b) u x * pd (sd L (dif u v b)) i.succ x =
      ∑ a, sd L (dif u v a) x * R a := by
    simp only [sd_genG_sub hA hF hu hv, hR, Finset.sum_add_distrib, mul_sub, mul_add,
      Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i a => ∑ b, sd L (dif u v a) x * compF (A i a b) u x *
      pd (sd L (dif u v b)) i.succ x)]
    simp only [mul_assoc]
    ring
  rw [hident]
  have hD0 : 0 ≤ D := Dcst_nonneg d n m hP10 hP20 hB0
  calc ∑ a, sd L (dif u v a) x * R a ≤ ∑ a, |sd L (dif u v a) x| * (D * σ) := by
        refine Finset.sum_le_sum fun a _ => (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hRb a) (abs_nonneg _)
    _ ≤ ∑ a, ((1 / 2) * sd L (dif u v a) x ^ 2 + (1 / 2) * (D * σ) ^ 2) := by
        refine Finset.sum_le_sum fun a _ => ?_
        have := two_mul_le_add_sq |sd L (dif u v a) x| (D * σ)
        rw [sq_abs] at this
        nlinarith
    _ = (1 / 2) * ∑ a, sd L (dif u v a) x ^ 2 + (1 / 2) * n * (D * σ) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp; ring

end Pointwise

/-! ### The integrated difference estimate -/

section Integrated

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- **The difference energy inequality on one word**. -/
theorem word_diff_energy_le (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (hv : ∀ b, ContDiff ℝ ∞ (v b))
    (hup : ∀ b, IsSPeriodic (u b)) (hvp : ∀ b, IsSPeriodic (v b))
    {t : ℝ} {m : ℕ} {B M : ℝ} (hB0 : 0 ≤ B) (hM0 : 0 ≤ M) (hm1 : 1 ≤ m)
    (hBu : ∀ y b (L : List (Fin d)), L.length ≤ m + 1 → |sd L (u b) (Fin.cons t y)| ≤ B)
    (hBv : ∀ y b (L : List (Fin d)), L.length ≤ m + 1 → |sd L (v b) (Fin.cons t y)| ≤ B)
    (hMA : ∀ y i a b, ∀ k ≤ m, ‖iteratedFDeriv ℝ k (A i a b) (vslice u t y)‖ ≤ M)
    (hMF : ∀ y a c, ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (onPair (hadQ (F a) c)) (vslice (pairF u v) t y)‖ ≤ M)
    (hMP : ∀ y i a b c, ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (onPair (hadQ (A i a b) c)) (vslice (pairF u v) t y)‖ ≤ M)
    (L : List (Fin d)) (hL : L.length ≤ m) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (dif u v a) (Fin.cons t y) *
        sd L (fun x => genG A F u a x - genG A F v a x) (Fin.cons t y) ≤
      (1 / 2 + 1 / 2 * d * n * (cq m * M * Bc d n m B ^ m)) *
          (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2) +
        (1 / 2) * n * (Dcst d n m (cq m * M * Bc d n m B ^ m)
          (cq m * M * Bc d (n + n) m B ^ m) B) ^ 2 *
          ∫ y in Icc (0 : Fin d → ℝ) 1, sig m (dif u v) t y ^ 2 := by
  set P := cq m * M * Bc d n m B ^ m with hP
  set D := Dcst d n m P (cq m * M * Bc d (n + n) m B ^ m) B with hD
  have hBc := one_le_Bc d n m hB0
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg (cq_nonneg m) hM0) (pow_nonneg (by linarith) _)
  have he := contDiff_dif hu hv
  have hep := isSPeriodic_dif hup hvp
  have hV : ∀ a, ContDiff ℝ ∞ (sd L (dif u v a)) := fun a => contDiff_sd L (he a)
  have hVp : ∀ a, IsSPeriodic (sd L (dif u v a)) := fun a => isSPeriodic_sd L (hep a)
  have hAc : ∀ i a b, ContDiff ℝ ∞ (compF (A i a b) u) := fun i a b => contDiff_compF (hA i a b) hu
  have hAp : ∀ i a b, IsSPeriodic (compF (A i a b) u) := fun i a b =>
    isSPeriodic_compF (A i a b) hup
  have hG : ∀ a, ContDiff ℝ ∞ (fun x => genG A F u a x - genG A F v a x) := fun a =>
    (contDiff_genG hA hF hu a).sub (contDiff_genG hA hF hv a)
  have c1 : Continuous fun x => ∑ a, sd L (dif u v a) x *
      sd L (fun x => genG A F u a x - genG A F v a x) x :=
    continuous_finsetSum _ fun a _ => (hV a).continuous.mul (contDiff_sd L (hG a)).continuous
  have c2 : ∀ i, Continuous fun x => ∑ a, ∑ b, sd L (dif u v a) x * compF (A i a b) u x *
      pd (sd L (dif u v b)) i.succ x := fun i =>
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((hV a).continuous.mul (hAc i a b).continuous).mul (contDiff_pd_top (hV b) _).continuous
  have c3 : Continuous fun x => ∑ a, sd L (dif u v a) x ^ 2 :=
    continuous_finsetSum _ fun a _ => (hV a).continuous.pow 2
  have c4 : Continuous fun y : Fin d → ℝ => sig m (dif u v) t y ^ 2 :=
    (continuous_sig he m t).pow 2
  have hpt := fun y => pointwise_diff_key hA hF hu hv (t := t) (y := y) hB0 hM0 (hBu y) (hBv y)
    (hMA y) (hMF y) (hMP y) L hL
  have hint : ∫ y in Icc (0 : Fin d → ℝ) 1, (∑ a, sd L (dif u v a) (Fin.cons t y) *
        sd L (fun x => genG A F u a x - genG A F v a x) (Fin.cons t y) +
        ∑ i, ∑ a, ∑ b, sd L (dif u v a) (Fin.cons t y) * compF (A i a b) u (Fin.cons t y) *
          pd (sd L (dif u v b)) i.succ (Fin.cons t y)) ≤
      ∫ y in Icc (0 : Fin d → ℝ) 1, ((1 / 2) * ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2 +
        (1 / 2) * n * D ^ 2 * sig m (dif u v) t y ^ 2) := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun y _ => ?_
    · exact integrableOn_slice (c1.add (continuous_finsetSum _ fun i _ => c2 i)) t
    · exact ((integrableOn_slice c3 t).const_mul _).add ((c4.integrableOn_Icc).const_mul _)
    · refine (hpt y).trans (le_of_eq ?_)
      rw [hD, mul_pow]; ring
  rw [integral_add (integrableOn_slice c1 t)
      (integrableOn_slice (continuous_finsetSum _ fun i _ => c2 i) t),
    integral_finsetSum _ fun i _ => integrableOn_slice (c2 i) t,
    integral_add ((integrableOn_slice c3 t).const_mul _) ((c4.integrableOn_Icc).const_mul _),
    integral_const_mul, integral_const_mul] at hint
  have hsymT : ∀ i, -(1 / 2 * P * n) * ∫ y in Icc (0 : Fin d → ℝ) 1,
      ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2 ≤ ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b,
        sd L (dif u v a) (Fin.cons t y) * compF (A i a b) u (Fin.cons t y) *
          pd (sd L (dif u v b)) i.succ (Fin.cons t y) := by
    intro i
    rw [integral_sym_eq hV hVp (hAc i) (hAp i) (fun a b x => hsym i a b _) t i]
    have hb : ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b, sd L (dif u v a) (Fin.cons t y) *
        pd (compF (A i a b) u) i.succ (Fin.cons t y) * sd L (dif u v b) (Fin.cons t y) ≤
        ∫ y in Icc (0 : Fin d → ℝ) 1, P * n * ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2 := by
      refine setIntegral_mono_on ?_ ((integrableOn_slice c3 t).const_mul _) measurableSet_Icc
        fun y _ => ?_
      · exact integrableOn_slice (continuous_finsetSum _ fun a _ => continuous_finsetSum _
          fun b _ => ((hV a).continuous.mul (contDiff_pd_top (hAc i a b) _).continuous).mul
            (hV b).continuous) t
      · refine sum_mul_mul_le_sq hP0 fun a b => ?_
        have := abs_sd_compF_le_small (r := m) (hA i a b) hu hB0
          (fun b L hL => hBu y b L (by omega)) (hMA y i a b) [i]
          (by simpa using hm1) (by simpa using hm1)
        simpa [sd_cons] using this
    rw [integral_const_mul] at hb
    nlinarith
  have hsum : -(d * (1 / 2 * P * n)) * ∫ y in Icc (0 : Fin d → ℝ) 1,
      ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2 ≤ ∑ i, ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b,
        sd L (dif u v a) (Fin.cons t y) * compF (A i a b) u (Fin.cons t y) *
          pd (sd L (dif u v b)) i.succ (Fin.cons t y) := by
    calc -(d * (1 / 2 * P * n)) * ∫ y in Icc (0 : Fin d → ℝ) 1,
          ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2
        = ∑ _i : Fin d, -(1 / 2 * P * n) * ∫ y in Icc (0 : Fin d → ℝ) 1,
            ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2 := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => hsymT i
  set X := ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2 with hX
  set Y := ∫ y in Icc (0 : Fin d → ℝ) 1, sig m (dif u v) t y ^ 2 with hY
  set I1 := ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (dif u v a) (Fin.cons t y) *
    sd L (fun x => genG A F u a x - genG A F v a x) (Fin.cons t y) with hI1
  have : I1 ≤ 1 / 2 * X + 1 / 2 * n * D ^ 2 * Y + d * (1 / 2 * P * n) * X := by linarith
  have e : (1 / 2 + 1 / 2 * d * n * P) * X + 1 / 2 * n * D ^ 2 * Y =
      1 / 2 * X + 1 / 2 * n * D ^ 2 * Y + d * (1 / 2 * P * n) * X := by ring
  rw [e]
  exact this

/-- `∫ σ² ≤ c ‖e‖²_{H^m}` for the pointwise jet size `σ`. -/
theorem integral_sig_sq_le_energy {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (m : ℕ)
    (t : ℝ) : ∫ y in Icc (0 : Fin d → ℝ) 1, sig m u t y ^ 2 ≤
      (Nsig d n m * ∑ p ∈ Finset.range (m + 1), (d : ℝ) ^ p) * energyQ m u t := by
  have hs := integral_sig_sq_le hu m t
  have hterm : ∑ b, ∑ p ∈ Finset.range (m + 1), ∑ w : Fin p → Fin d,
      ∫ y in Icc (0 : Fin d → ℝ) 1, sd (List.ofFn w).reverse (u b) (Fin.cons t y) ^ 2 ≤
        (∑ p ∈ Finset.range (m + 1), (d : ℝ) ^ p) * energyQ m u t := by
    unfold energyQ
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpq : p ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
    calc ∑ w : Fin p → Fin d, ∫ y in Icc (0 : Fin d → ℝ) 1,
          sd (List.ofFn w).reverse (u b) (Fin.cons t y) ^ 2
        ≤ ∑ _w : Fin p → Fin d, Q m (u b) t :=
          Finset.sum_le_sum fun w _ => term_le_Q (by simp; exact hpq) (u b) t
      _ = (d : ℝ) ^ p * Q m (u b) t := by simp
  refine hs.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hterm (Nsig_nonneg d n m)

/-- **The `H^m` difference energy estimate** (pointwise-bounded form): for smooth real symmetric
`A^i`, smooth `F`, `m ≥ 1` and every `B ≥ 0` there is `K` such that for all smooth periodic `U, V`
whose derivatives of order `≤ m + 1` are bounded by `B` on the slice `t`,
`⟨U - V, G(U) - G(V)⟩_{H^m}(t) ≤ K ‖U - V‖²_{H^m}(t)`. -/
theorem pairQ_genG_sub_le (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {m : ℕ}
    (hm1 : 1 ≤ m) {B : ℝ} (hB0 : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u v : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, ContDiff ℝ ∞ (v b)) → (∀ b, IsSPeriodic (u b)) → (∀ b, IsSPeriodic (v b)) → ∀ t,
      (∀ y b (L : List (Fin d)), L.length ≤ m + 1 → |sd L (u b) (Fin.cons t y)| ≤ B) →
      (∀ y b (L : List (Fin d)), L.length ≤ m + 1 → |sd L (v b) (Fin.cons t y)| ≤ B) →
      pairQ m (dif u v) (fun a x => genG A F u a x - genG A F v a x) t ≤
        K * energyQ m (dif u v) t := by
  -- uniform coefficient bounds
  obtain ⟨M1, hM10, hM1⟩ := exists_bound_family (n := n)
    (Φ := fun p : Fin d × Fin n × Fin n => A p.1 p.2.1 p.2.2) (fun p => hA _ _ _) B m
  set Ψ : (Fin n × Fin n) ⊕ (Fin d × Fin n × Fin n × Fin n) → (Fin (n + n) → ℝ) → ℝ :=
    fun k => Sum.elim (fun p => onPair (hadQ (F p.1) p.2))
      (fun p => onPair (hadQ (A p.1 p.2.1 p.2.2.1) p.2.2.2)) k with hΨ
  have hΨs : ∀ k, ContDiff ℝ ∞ (Ψ k) := by
    intro k; cases k with
    | inl p => exact contDiff_onPair (contDiff_hadQ (hF p.1) p.2)
    | inr p => exact contDiff_onPair (contDiff_hadQ (hA p.1 p.2.1 p.2.2.1) p.2.2.2)
  obtain ⟨M2, hM20, hM2⟩ := exists_bound_family (n := n + n) hΨs B m
  set M := M1 + M2 with hM
  have hM0 : 0 ≤ M := by positivity
  set P := cq m * M * Bc d n m B ^ m with hP
  have hBc := one_le_Bc d n m hB0
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg (cq_nonneg m) hM0) (pow_nonneg (by linarith) _)
  set D := Dcst d n m P (cq m * M * Bc d (n + n) m B ^ m) B with hD
  set cσ := Nsig d n m * ∑ p ∈ Finset.range (m + 1), (d : ℝ) ^ p with hcσ
  have hcσ0 : 0 ≤ cσ := mul_nonneg (Nsig_nonneg d n m) (by positivity)
  set W := ((wordsLE d m).card : ℝ) with hW
  set K := (1 / 2 + 1 / 2 * d * n * P) + W * (1 / 2 * n * D ^ 2 * cσ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun u v hu hv hup hvp t hBu hBv => ?_⟩
  have he := contDiff_dif hu hv
  have hEn := energyQ_nonneg m (dif u v) t
  have hval : ∀ y, ‖vslice u t y‖ ≤ B := fun y =>
    (pi_norm_le_iff_of_nonneg hB0).2 fun b => by
      have := hBu y b [] (Nat.zero_le _); simpa [Real.norm_eq_abs] using this
  have hvalp : ∀ y, ‖vslice (pairF u v) t y‖ ≤ B := fun y =>
    (pi_norm_le_iff_of_nonneg hB0).2 fun c => by
      have := abs_sd_pairF_le (L := []) (x := Fin.cons t y)
        (fun b => hBu y b [] (Nat.zero_le _)) (fun b => hBv y b [] (Nat.zero_le _)) c
      simpa [Real.norm_eq_abs] using this
  have hMA : ∀ y i a b, ∀ k ≤ m, ‖iteratedFDeriv ℝ k (A i a b) (vslice u t y)‖ ≤ M :=
    fun y i a b k hk => (hM1 (i, a, b) _ (hval y) k hk).trans (by linarith)
  have hMF : ∀ y a c, ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (onPair (hadQ (F a) c)) (vslice (pairF u v) t y)‖ ≤ M :=
    fun y a c k hk => (hM2 (Sum.inl (a, c)) _ (hvalp y) k hk).trans (by linarith)
  have hMP : ∀ y i a b c, ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (onPair (hadQ (A i a b) c)) (vslice (pairF u v) t y)‖ ≤ M :=
    fun y i a b c k hk => (hM2 (Sum.inr (i, a, b, c)) _ (hvalp y) k hk).trans (by linarith)
  have hword : ∀ L ∈ wordsLE d m, ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a,
      sd L (dif u v a) (Fin.cons t y) *
        sd L (fun x => genG A F u a x - genG A F v a x) (Fin.cons t y) ≤
      (1 / 2 + 1 / 2 * d * n * P) *
          (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2) +
        (1 / 2) * n * D ^ 2 * (cσ * energyQ m (dif u v) t) := by
    intro L hL
    refine (word_diff_energy_le hA hsym hF hu hv hup hvp hB0 hM0 hm1 hBu hBv hMA hMF hMP L
      (mem_wordsLE.mp hL)).trans ?_
    gcongr
    exact integral_sig_sq_le_energy he m t
  have hsumV : ∑ L ∈ wordsLE d m, ∫ y in Icc (0 : Fin d → ℝ) 1,
      ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2 = energyQ m (dif u v) t := by
    unfold energyQ Q
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [integral_finsetSum _ fun a _ => integrableOn_sq (contDiff_sd L (he a)).continuous t]
  have hpair : pairQ m (dif u v) (fun a x => genG A F u a x - genG A F v a x) t =
      ∑ L ∈ wordsLE d m, ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (dif u v a) (Fin.cons t y) *
        sd L (fun x => genG A F u a x - genG A F v a x) (Fin.cons t y) := by
    unfold pairQ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [integral_finsetSum _ fun a _ => integrableOn_slice (show Continuous fun x =>
      sd L (dif u v a) x * sd L (fun x => genG A F u a x - genG A F v a x) x from
      (contDiff_sd L (he a)).continuous.mul (contDiff_sd L ((contDiff_genG hA hF hu a).sub
        (contDiff_genG hA hF hv a))).continuous) t]
  rw [hpair]
  calc ∑ L ∈ wordsLE d m, ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (dif u v a) (Fin.cons t y) *
        sd L (fun x => genG A F u a x - genG A F v a x) (Fin.cons t y)
      ≤ ∑ L ∈ wordsLE d m, ((1 / 2 + 1 / 2 * d * n * P) *
          (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (dif u v a) (Fin.cons t y) ^ 2) +
        (1 / 2) * n * D ^ 2 * (cσ * energyQ m (dif u v) t)) :=
        Finset.sum_le_sum fun L hL => hword L hL
    _ = (1 / 2 + 1 / 2 * d * n * P) * energyQ m (dif u v) t +
          W * ((1 / 2) * n * D ^ 2 * (cσ * energyQ m (dif u v) t)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumV, Finset.sum_const, nsmul_eq_mul]
    _ = K * energyQ m (dif u v) t := by rw [hK]; ring

end Integrated

/-! ### The `H^q` form and the Galerkin difference inequality in `H^m` -/

section Galerkin

open KatoGalerkin

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- **Sup bounds from the `H^q` norm** (Sobolev embedding on slices): for `m_s > d/2` and
`m_s + m + 1 ≤ q`, every derivative of order `≤ m + 1` of a smooth periodic field is bounded by
`C ‖U‖_{H^q}`. -/
theorem exists_sup_bound {ms m q : ℕ} (hms : (d : ℝ) / 2 < ms) (hq : ms + m + 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, IsSPeriodic (u b)) → ∀ t R, 0 ≤ R → energyQ q u t ≤ R ^ 2 →
      ∀ y b (L : List (Fin d)), L.length ≤ m + 1 → |sd L (u b) (Fin.cons t y)| ≤ C * R := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hms
  refine ⟨Real.sqrt CS, Real.sqrt_nonneg _, fun u hu hup t R hR hE y b L hL => ?_⟩
  have h1 := hsup _ (contDiff_sd L (hu b)) (isSPeriodic_sd L (hup b)) t y
  have h2 : Q ms (sd L (u b)) t ≤ R ^ 2 := by
    refine (Q_sd_le (a := L) (m := ms) (k := q) (by omega) (u b) t).trans ?_
    refine le_trans ?_ hE
    exact Finset.single_le_sum (f := fun a => Q q (u a) t) (fun a _ => Q_nonneg q (u a) t)
      (Finset.mem_univ b)
  have h3 : sd L (u b) (Fin.cons t y) ^ 2 ≤ (Real.sqrt CS * R) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hCS]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hCS)
  exact abs_le_of_sq_le_sq' h3 (by positivity) |> fun h => abs_le.2 h

/-- **The `H^m` difference energy estimate on the `H^q` ball**: for `m ≥ 1`, `m_s > d/2`,
`m_s + m + 1 ≤ q` and every radius `R` there is `K` with
`⟨U - V, G(U) - G(V)⟩_{H^m} ≤ K ‖U - V‖²_{H^m}` for all smooth periodic `U, V` with
`‖U‖_{H^q}, ‖V‖_{H^q} ≤ R`. -/
theorem pairQ_genG_sub_le_Hq (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {ms m q : ℕ}
    (hms : (d : ℝ) / 2 < ms) (hm1 : 1 ≤ m) (hq : ms + m + 1 ≤ q) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u v : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, ContDiff ℝ ∞ (v b)) → (∀ b, IsSPeriodic (u b)) → (∀ b, IsSPeriodic (v b)) → ∀ t,
      energyQ q u t ≤ R ^ 2 → energyQ q v t ≤ R ^ 2 →
      pairQ m (dif u v) (fun a x => genG A F u a x - genG A F v a x) t ≤
        K * energyQ m (dif u v) t := by
  obtain ⟨C, hC0, hC⟩ := exists_sup_bound (d := d) (n := n) hms hq
  obtain ⟨K, hK0, hK⟩ := pairQ_genG_sub_le hA hsym hF hm1 (B := C * R) (by positivity)
  exact ⟨K, hK0, fun u v hu hv hup hvp t hEu hEv =>
    hK u v hu hv hup hvp t (hC u hu hup t R hR hEu) (hC v hv hvp t R hR hEv)⟩

/-- The `H^m` coordinates of a Galerkin state (whose Euclidean norm is the `H^q` norm):
`(hmS a)_{b,k} = √(wq_m(k)/wq_q(k)) a_{b,k}`. -/
def hmS (m q : ℕ) {N : ℕ} (a : GS d n N) : GS d n N :=
  WithLp.toLp 2 fun p => Real.sqrt (wq m p.2.1) / Real.sqrt (wq q p.2.1) * a p

theorem hmS_apply (m q : ℕ) {N : ℕ} (a : GS d n N) (p : Fin n × KatoGalerkin.box (d := d) N) :
    hmS m q a p = Real.sqrt (wq m p.2.1) / Real.sqrt (wq q p.2.1) * a p := rfl

theorem hmS_add (m q : ℕ) {N : ℕ} (a a' : GS d n N) :
    hmS m q (a + a') = hmS m q a + hmS m q a' := by
  ext p; simp only [hmS_apply, PiLp.add_apply, mul_add]

theorem hmS_smul (m q : ℕ) {N : ℕ} (c : ℝ) (a : GS d n N) : hmS m q (c • a) = c • hmS m q a := by
  ext p; simp only [hmS_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem hmS_sub (m q : ℕ) {N : ℕ} (a a' : GS d n N) :
    hmS m q (a - a') = hmS m q a - hmS m q a' := by
  ext p; simp only [hmS_apply, PiLp.sub_apply, mul_sub]

theorem hmS_mid (m q : ℕ) {N : ℕ} (a a' : GS d n N) :
    hmS m q (SpectralGalerkin.mid a a') = SpectralGalerkin.mid (hmS m q a) (hmS m q a') := by
  simp only [SpectralGalerkin.mid, hmS_smul, hmS_add]

theorem hmS_injective (m q : ℕ) {N : ℕ} {a a' : GS d n N} (h : hmS m q a = hmS m q a') :
    a = a' := by
  refine PiLp.ext fun p => ?_
  have := congrArg (fun z : GS d n N => z p) h
  simp only [hmS_apply] at this
  have hpos : 0 < Real.sqrt (wq m p.2.1) / Real.sqrt (wq q p.2.1) :=
    div_pos (Real.sqrt_pos.2 (wq_pos _ _)) (Real.sqrt_pos.2 (wq_pos _ _))
  exact mul_left_cancel₀ hpos.ne' this

theorem hmS_entry (m q : ℕ) {N : ℕ} (a : GS d n N) (p : Fin n × KatoGalerkin.box (d := d) N) :
    hmS m q a p = Real.sqrt (wq m p.2.1) * cf q a p.1 p.2.1 := by
  rw [hmS_apply, cf, dif_pos p.2.2]
  field_simp [sqrt_wq_ne q p.2.1]

/-- The `H^m` inner product of Galerkin states in Fourier form. -/
theorem inner_hmS (m q : ℕ) {N : ℕ} (a a' : GS d n N) :
    ⟪hmS m q a, hmS m q a'⟫ = ∑ b, ∑ k ∈ KatoGalerkin.box (d := d) N,
      cf q a b k * wq m k * cf q a' b k := by
  have e : ⟪hmS m q a, hmS m q a'⟫ = ∑ p, hmS m q a p * hmS m q a' p := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [RCLike.inner_apply', conj_trivial]
  rw [e, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Eq.trans ?_ (Finset.sum_coe_sort (KatoGalerkin.box N)
    (fun k => cf q a b k * wq m k * cf q a' b k))
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hmS_entry, hmS_entry]
  have := Real.mul_self_sqrt (wq_nonneg m k.1)
  linear_combination (cf q a b k.1 * cf q a' b k.1) * this

/-- The `H^m` norm of a Galerkin state is the `H^m` norm of its field. -/
theorem norm_hmS_sq (m q : ℕ) {N : ℕ} (a : GS d n N) (t : ℝ) :
    ‖hmS m q a‖ ^ 2 = energyQ m (fld q a) t := by
  rw [← real_inner_self_eq_norm_sq, inner_hmS, energyQ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [fld, Q_tfs]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem cf_GN (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) {k : Fin d → ℤ}
    (hk : k ∈ KatoGalerkin.box N) : cf q (GN A F q a) b k = coef (genG A F (fld q a) b) 0 k := by
  rw [cf, dif_pos hk]
  show GN A F q a (b, ⟨k, hk⟩) / Real.sqrt (wq q k) = _
  rw [GN_apply]
  field_simp [sqrt_wq_ne q k]

theorem cf_sub' (q : ℕ) {N : ℕ} (a a' : GS d n N) (b : Fin n) (k : Fin d → ℤ) :
    cf q (a - a') b k = cf q a b k - cf q a' b k := by
  unfold cf
  split_ifs with hk
  · rw [PiLp.sub_apply, sub_div]
  · ring

/-- **The projection disappears from the `H^m` pairing**:
`⟪G_N a - G_N a', a - a'⟫_{H^m} = ⟨U - U', G(U) - G(U')⟩_{H^m}` for the fields `U, U'`. -/
theorem inner_hmS_GN_sub (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (m q : ℕ) {N : ℕ} (a a' : GS d n N) :
    ⟪hmS m q (GN A F q a - GN A F q a'), hmS m q (a - a')⟫ =
      pairQ m (dif (fld q a) (fld q a'))
        (fun c x => genG A F (fld q a) c x - genG A F (fld q a') c x) 0 := by
  rw [real_inner_comm, inner_hmS]
  unfold pairQ
  refine Finset.sum_congr rfl fun b _ => ?_
  have hg : ContDiff ℝ ∞ (fun x => genG A F (fld q a) b x - genG A F (fld q a') b x) :=
    (contDiff_genG hA hF (fun c => contDiff_fld q a c) b).sub
      (contDiff_genG hA hF (fun c => contDiff_fld q a' c) b)
  have hgp : IsSPeriodic (fun x => genG A F (fld q a) b x - genG A F (fld q a') b x) :=
    fun k x => by
      simp only [isSPeriodic_genG (fun c => isSPeriodic_fld q a c) b k x,
        isSPeriodic_genG (fun c => isSPeriodic_fld q a' c) b k x]
  have hdif : dif (fld q a) (fld q a') b =
      tfs (KatoGalerkin.box N) (fun k => cf q a b k - cf q a' b k) := by
    funext x; simp only [dif, fld, tfs_sub]
  have h := pairWords_tfs m (KatoGalerkin.box N) (fun k => cf q a b k - cf q a' b k) hg hgp 0
  rw [← hdif] at h
  have e : ∑ L ∈ wordsLE d m, ∫ y in Icc (0 : Fin d → ℝ) 1,
      sd L (dif (fld q a) (fld q a') b) (Fin.cons 0 y) *
        sd L (fun x => genG A F (fld q a) b x - genG A F (fld q a') b x) (Fin.cons 0 y) =
      ∑ L ∈ wordsLE d m, sint (fun x => sd L (dif (fld q a) (fld q a') b) x *
        sd L (fun x => genG A F (fld q a) b x - genG A F (fld q a') b x) x) 0 := rfl
  rw [e, h]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [cf_sub', cf_sub', cf_GN q a b hk, cf_GN q a' b hk,
    coef_sub (contDiff_genG hA hF (fun c => contDiff_fld q a c) b).continuous
      (contDiff_genG hA hF (fun c => contDiff_fld q a' c) b).continuous]

/-- **The cutoff-uniform `H^m` difference inequality of the projected generator**:
`⟪G_N a - G_N a', a - a'⟫_{H^m} ≤ K ‖a - a'‖²_{H^m}` for all cutoffs `N` and all Galerkin states
in the `H^q` ball of radius `R` (`m ≥ 1`, `m_s > d/2`, `m_s + m + 1 ≤ q`). -/
theorem inner_GN_sub_le (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {ms m q : ℕ}
    (hms : (d : ℝ) / 2 < ms) (hm1 : 1 ≤ m) (hq : ms + m + 1 ≤ q) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (a a' : GS d n N), ‖a‖ ≤ R → ‖a'‖ ≤ R →
      ⟪hmS m q (GN A F q a) - hmS m q (GN A F q a'), hmS m q a - hmS m q a'⟫ ≤
        K * ‖hmS m q a - hmS m q a'‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := pairQ_genG_sub_le_Hq hA hsym hF hms hm1 hq hR
  refine ⟨K, hK0, fun N a a' ha ha' => ?_⟩
  rw [← hmS_sub, ← hmS_sub, inner_hmS_GN_sub hA hF, norm_hmS_sq m q _ 0]
  have hE : ∀ z : GS d n N, ‖z‖ ≤ R → energyQ q (fld q z) 0 ≤ R ^ 2 := fun z hz => by
    rw [energyQ_fld]; exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have h := hK (fld q a) (fld q a') (fun c => contDiff_fld q a c) (fun c => contDiff_fld q a' c)
    (fun c => isSPeriodic_fld q a c) (fun c => isSPeriodic_fld q a' c) 0 (hE a ha) (hE a' ha')
  have e : fld q (a - a') = dif (fld q a) (fld q a') := by
    funext c x; simp only [dif, fld, cf_sub', tfs]; rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  exact h

/-- **Discrete causal stability of the midpoint scheme in `H^m`** (`eq:generated-causal`): for
smooth real symmetric `A^i`, smooth `F`, `m ≥ 1`, `m_s > d/2`, `m_s + m + 1 ≤ q` and every radius `R`
there is `K` (depending only on `R` and `A, F, m, m_s, q, d, n`) such that for every cutoff `N`,
every step `τ ≥ 0` with `τK ≤ 1` and any two midpoint trajectories in the `H^q` ball of radius `R`,
`U^{j+1} = U^j + τ G_N(m_U^j)`, `V^{j+1} = V^j + τ (G_N(m_V^j) + r_j)` (`j < n`),
`‖U^n - V^n‖_{H^m} ≤ e^{2Knτ} (‖U^0 - V^0‖_{H^m} + 2τ Σ_{j<n} ‖r_j‖_{H^m})`. -/
theorem midpoint_causal_Hm (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {ms m q : ℕ}
    (hms : (d : ℝ) / 2 < ms) (hm1 : 1 ≤ m) (hq : ms + m + 1 ≤ q) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (τ : ℝ), 0 ≤ τ → τ * K ≤ 1 →
      ∀ (U V r : ℕ → GS d n N) (nn : ℕ), (∀ j ≤ nn, ‖U j‖ ≤ R) → (∀ j ≤ nn, ‖V j‖ ≤ R) →
      (∀ j < nn, U (j + 1) = U j + τ • GN A F q (SpectralGalerkin.mid (U j) (U (j + 1)))) →
      (∀ j < nn, V (j + 1) = V j + τ • (GN A F q (SpectralGalerkin.mid (V j) (V (j + 1))) +
        r j)) →
      ‖hmS m q (U nn) - hmS m q (V nn)‖ ≤ Real.exp (2 * K * (nn * τ)) *
        (‖hmS m q (U 0) - hmS m q (V 0)‖ + 2 * τ * ∑ j ∈ Finset.range nn, ‖hmS m q (r j)‖) := by
  obtain ⟨K, hK0, hK⟩ := inner_GN_sub_le hA hsym hF hms hm1 hq hR
  refine ⟨K, hK0, fun N τ hτ hτK U V r nn hUR hVR hU hV => ?_⟩
  -- transport to `H^m` coordinates
  set G' : GS d n N → GS d n N := fun z =>
    hmS m q (GN A F q (WithLp.toLp 2 fun p => Real.sqrt (wq q p.2.1) / Real.sqrt (wq m p.2.1) *
      z p)) with hG'
  have hinv : ∀ a : GS d n N, (WithLp.toLp 2 fun p => Real.sqrt (wq q p.2.1) /
      Real.sqrt (wq m p.2.1) * (hmS m q a) p : GS d n N) = a := fun a => by
    refine PiLp.ext fun p => ?_
    simp only [hmS_apply]
    show Real.sqrt (wq q p.2.1) / Real.sqrt (wq m p.2.1) *
      (Real.sqrt (wq m p.2.1) / Real.sqrt (wq q p.2.1) * a p) = a p
    field_simp [sqrt_wq_ne q p.2.1, sqrt_wq_ne m p.2.1]
  have hG'S : ∀ a, G' (hmS m q a) = hmS m q (GN A F q a) := fun a => by
    simp only [hG', hinv]
  have hmidR : ∀ (W : ℕ → GS d n N), (∀ j ≤ nn, ‖W j‖ ≤ R) → ∀ j < nn,
      ‖SpectralGalerkin.mid (W j) (W (j + 1))‖ ≤ R := by
    intro W hW j hj
    unfold SpectralGalerkin.mid
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := norm_add_le (W j) (W (j + 1))
    have h1 := hW j hj.le
    have h2 := hW (j + 1) hj
    linarith
  have hU' : ∀ j < nn, hmS m q (U (j + 1)) = hmS m q (U j) +
      τ • G' (SpectralGalerkin.mid (hmS m q (U j)) (hmS m q (U (j + 1)))) := fun j hj => by
    rw [← hmS_mid, hG'S, ← hmS_smul, ← hmS_add, ← hU j hj]
  have hV' : ∀ j < nn, hmS m q (V (j + 1)) = hmS m q (V j) +
      τ • (G' (SpectralGalerkin.mid (hmS m q (V j)) (hmS m q (V (j + 1)))) + hmS m q (r j)) :=
    fun j hj => by
      rw [← hmS_mid, hG'S, ← hmS_add, ← hmS_smul, ← hmS_add, ← hV j hj]
  have hmono : ∀ j < nn,
      ⟪G' (SpectralGalerkin.mid (hmS m q (U j)) (hmS m q (U (j + 1)))) -
        G' (SpectralGalerkin.mid (hmS m q (V j)) (hmS m q (V (j + 1)))),
        SpectralGalerkin.mid (hmS m q (U j)) (hmS m q (U (j + 1))) -
          SpectralGalerkin.mid (hmS m q (V j)) (hmS m q (V (j + 1)))⟫ ≤
        K * ‖SpectralGalerkin.mid (hmS m q (U j)) (hmS m q (U (j + 1))) -
          SpectralGalerkin.mid (hmS m q (V j)) (hmS m q (V (j + 1)))‖ ^ 2 := fun j hj => by
    rw [← hmS_mid, ← hmS_mid, hG'S, hG'S]
    exact hK N _ _ (hmidR U hUR j hj) (hmidR V hVR j hj)
  exact SpectralGalerkin.midpoint_causal hτ hK0 hτK nn hU' hV' hmono

end Galerkin

/-! ### Non-vacuity -/

/-- **Non-vacuity of `midpoint_causal_Hm`** on `𝕋³` (`m_s = 2`, `m = 3`, `q = 6`): for the
symmetric system with `A^1 = σ₁` (`A^2 = A^3 = 0`) and `F(v) = -v`, the hypotheses hold and the
conclusion is available for every radius. -/
example (R : ℝ) (hR : 0 ≤ R) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (τ : ℝ), 0 ≤ τ → τ * K ≤ 1 →
    ∀ (U V r : ℕ → KatoGalerkin.GS 3 2 N) (nn : ℕ), (∀ j ≤ nn, ‖U j‖ ≤ R) →
      (∀ j ≤ nn, ‖V j‖ ≤ R) →
      (∀ j < nn, U (j + 1) = U j + τ • KatoGalerkin.GN KatoGalerkin.exampleA (fun a v => -v a) 6
        (SpectralGalerkin.mid (U j) (U (j + 1)))) →
      (∀ j < nn, V (j + 1) = V j + τ • (KatoGalerkin.GN KatoGalerkin.exampleA (fun a v => -v a) 6
        (SpectralGalerkin.mid (V j) (V (j + 1))) + r j)) →
      ‖hmS 3 6 (U nn) - hmS 3 6 (V nn)‖ ≤ Real.exp (2 * K * (nn * τ)) *
        (‖hmS 3 6 (U 0) - hmS 3 6 (V 0)‖ + 2 * τ * ∑ j ∈ Finset.range nn, ‖hmS 3 6 (r j)‖) :=
  midpoint_causal_Hm (ms := 2) (fun _ _ _ => by unfold KatoGalerkin.exampleA; exact contDiff_const)
    (fun i a b v => by
      unfold KatoGalerkin.exampleA
      fin_cases i <;> fin_cases a <;> fin_cases b <;> simp)
    (fun a => (contDiff_apply ℝ ℝ a).neg) (by norm_num) (by norm_num) (by norm_num) hR
end RenewalGeometry.KatoCausal
