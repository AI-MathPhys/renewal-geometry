/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SlabMoserComposition
import RenewalGeometry.Continuum.FirstOrderSymHypHk
import RenewalGeometry.Analysis.HadamardQuotient

/-!
# Difference stability of quasilinear symmetric hyperbolic systems with first-exit closure

Generic infrastructure (no renewal notions) for `prop:coupled-bootstrap` of the
Einstein–Standard-Model action-closure manuscript (proof of `eq:bootstrap-state`:
"The first term is locally Lipschitz in `H^k`. The second is bounded by `C‖W‖_{H^k}` because the
reference has one additional spatial derivative. For `|α| ≤ k` the commutator estimate … and
`H^k ↪ W^{1,∞}` control the differentiated principal terms. Symmetry and integration by parts on
the closed slice give a positive energy … Integration and Gronwall … Continuity then excludes a
first exit before `T`").

Setting of `SlabSobolevAlgebra` / `QuasilinearSymmetricEnergy`: smooth fields on `ℝ^{1+d}`,
`ℤ^d`-periodic in space, classical squared `H^k` slice norms `Q_k`, the spatial generator
`G(U)_a = F_a(U) - Σ_{i,b} A^i_{ab}(U)∂_iu_b` of `∂_tU + Σ_iA^i(U)∂_iU = F(U)` with smooth real
symmetric `A^i(v)` and smooth `F(v)`.

## Main results

* `appendF`, `compF_hadamard`, **`Q_compF_sub_le`** — the **Lipschitz Moser estimate**
  `Q_k(Φ(V) - Φ(U)) ≤ C(R) Σ_b Q_k(v_b - u_b)` on `H^k` balls (Hadamard quotient + `H^k` algebra);
* **`comm_int_le`** — the **commutator estimate**
  `‖[∂^L, a]∂_iw‖²_{L²} = ∫ (Σ_{(p,q) ∈ splitsNE L} ∂^pa ∂^q∂_iw)² ≤ C Q_k(a) Q_k(w)`, `|L| ≤ k`,
  `k ≥ 2m`, `m > d/2` (Kato–Ponce type, from the slice product estimates);
* **`pairQ_genG_sub_le`** — the **static difference energy inequality**
  `⟨V - U, G(V) - G(U)⟩_{H^k} ≤ K ‖V - U‖²_{H^k}` for `V` in an `H^k` ball and `U` in an
  `H^{k+1}` ball (symmetric integration by parts for the principal term);
* `hasDerivAt_energyQ` — `d/dt ‖W(t)‖²_{H^k} = 2⟨W, ∂_tW⟩_{H^k}`;
* **`difference_bootstrap`** — the **first-exit difference stability theorem**: for a reference
  `U` solving `∂_tU = G(U)` on `[0, T]` with `‖U(t)‖_{H^{k+1}} ≤ R₁` and an approximate solution
  `∂_tV = G(V) + e` whose defect obeys `‖e(t)‖²_{H^k} ≤ Φ(t)` **only while** `‖V - U‖²_{H^k} ≤ ρ`,
  `‖V(t) - U(t)‖²_{H^k} ≤ C_*(‖V(0) - U(0)‖²_{H^k} + ∫₀ᵀΦ)` on all of `[0, T]` once the right side
  is `< ρ`.  No a priori bound on `V` is assumed.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.QLDiff

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### Concatenated fields and the Lipschitz Moser estimate -/

/-- The concatenated field `(u, v) : Fin (n + n) → ST d → ℝ`. -/
def appendF (u v : Fin n → ST d → ℝ) : Fin (n + n) → ST d → ℝ :=
  fun i x => Fin.append (fun b => u b x) (fun b => v b x) i

theorem appendF_castAdd (u v : Fin n → ST d → ℝ) (b : Fin n) :
    appendF u v (Fin.castAdd n b) = u b := by
  funext x; simp [appendF]

theorem appendF_natAdd (u v : Fin n → ST d → ℝ) (b : Fin n) :
    appendF u v (Fin.natAdd n b) = v b := by
  funext x; exact Fin.append_right (fun b => u b x) (fun b => v b x) b

theorem contDiff_appendF {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    (hv : ∀ b, ContDiff ℝ ∞ (v b)) : ∀ i, ContDiff ℝ ∞ (appendF u v i) := by
  intro i
  refine Fin.addCases (fun b => ?_) (fun b => ?_) i
  · rw [appendF_castAdd]; exact hu b
  · rw [appendF_natAdd]; exact hv b

theorem isSPeriodic_appendF {u v : Fin n → ST d → ℝ} (hu : ∀ b, IsSPeriodic (u b))
    (hv : ∀ b, IsSPeriodic (v b)) : ∀ i, IsSPeriodic (appendF u v i) := by
  intro i
  refine Fin.addCases (fun b => ?_) (fun b => ?_) i
  · rw [appendF_castAdd]; exact hu b
  · rw [appendF_natAdd]; exact hv b

theorem energyQ_appendF (k : ℕ) (u v : Fin n → ST d → ℝ) (t : ℝ) :
    energyQ k (appendF u v) t = energyQ k u t + energyQ k v t := by
  unfold energyQ
  rw [Fin.sum_univ_add]
  simp only [appendF_castAdd, appendF_natAdd]

/-- **Hadamard form of a difference of compositions**:
`Φ(V) - Φ(U) = Σ_b (v_b - u_b) · hadQ Φ b (U, V)`. -/
theorem compF_hadamard {Φ : (Fin n → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (u v : Fin n → ST d → ℝ)
    (x : ST d) :
    compF Φ v x - compF Φ u x =
      ∑ b, (v b x - u b x) * compF (Hadamard.hadQ Φ b) (appendF u v) x := by
  have h := Hadamard.hadamard_eq hΦ (fun i => appendF u v i x)
  have hlo : Hadamard.lo (fun i => appendF u v i x) = fun b => u b x := by
    funext b; simp [Hadamard.lo, appendF]
  have hhi : Hadamard.hi (fun i => appendF u v i x) = fun b => v b x := by
    funext b; exact Fin.append_right (fun b => u b x) (fun b => v b x) b
  rw [hlo, hhi] at h
  exact h

/-- The difference field `v - u`. -/
abbrev subF (v u : Fin n → ST d → ℝ) : Fin n → ST d → ℝ := fun b x => v b x - u b x

theorem contDiff_subF {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    (hv : ∀ b, ContDiff ℝ ∞ (v b)) : ∀ b, ContDiff ℝ ∞ (subF v u b) := fun b =>
  (hv b).sub (hu b)

theorem isSPeriodic_subF {u v : Fin n → ST d → ℝ} (hu : ∀ b, IsSPeriodic (u b))
    (hv : ∀ b, IsSPeriodic (v b)) : ∀ b, IsSPeriodic (subF v u b) := fun b k x => by
  simp only [subF, hv b k x, hu b k x]

/-- **Lipschitz Moser estimate on the slices**: for `m > d/2`, `2m ≤ k + 1`, smooth `Φ` and every
radius `R`, there is `C` with `Q_k(Φ(V) - Φ(U))(t) ≤ C Σ_b Q_k(v_b - u_b)(t)` whenever
`‖U(t)‖²_{H^k} + ‖V(t)‖²_{H^k} ≤ R²`. -/
theorem Q_compF_sub_le {m k : ℕ} (hm : (d : ℝ) / 2 < m) (hk : 2 * m ≤ k + 1)
    {Φ : (Fin n → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, ContDiff ℝ ∞ (v b)) → (∀ b, IsSPeriodic (u b)) → (∀ b, IsSPeriodic (v b)) →
      ∀ t, energyQ k u t + energyQ k v t ≤ R ^ 2 →
        Q k (fun x => compF Φ v x - compF Φ u x) t ≤ C * energyQ k (subF v u) t := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  have hK := fun b => SlabMoser.Q_compF_le (d := d) (n := n + n) hm hk
    (Hadamard.contDiff_hadQ hΦ b) hR
  choose K hK0 hK using hK
  have hA0 := algC_nonneg (d := d) k hCS
  have hKs : 0 ≤ ∑ b, K b := Finset.sum_nonneg fun b _ => hK0 b
  refine ⟨n * (algC d k CS * ∑ b, K b), by positivity, ?_⟩
  intro u v hu hv hpu hpv t hE
  set H : Fin n → ST d → ℝ := fun b => compF (Hadamard.hadQ Φ b) (appendF u v) with hHdef
  have hH : ∀ b, ContDiff ℝ ∞ (H b) := fun b =>
    contDiff_compF (Hadamard.contDiff_hadQ hΦ b) (contDiff_appendF hu hv)
  have hHp : ∀ b, IsSPeriodic (H b) := fun b =>
    isSPeriodic_compF _ (isSPeriodic_appendF hpu hpv)
  have hQH : ∀ b, Q k (H b) t ≤ K b := fun b =>
    hK b _ (contDiff_appendF hu hv) (isSPeriodic_appendF hpu hpv) t
      (by rw [energyQ_appendF]; exact hE)
  have heq : (fun x => compF Φ v x - compF Φ u x) = fun x => ∑ b, subF v u b x * H b x :=
    funext fun x => compF_hadamard hΦ u v x
  rw [heq]
  have hw := contDiff_subF hu hv
  have hwp := isSPeriodic_subF hpu hpv
  have hQw : ∀ b, Q k (subF v u b) t ≤ energyQ k (subF v u) t := fun b =>
    Finset.single_le_sum (f := fun b => Q k (subF v u b) t) (fun b _ => Q_nonneg k _ t)
      (Finset.mem_univ b)
  calc Q k (fun x => ∑ b, subF v u b x * H b x) t
      ≤ (Finset.univ : Finset (Fin n)).card * ∑ b, Q k (fun x => subF v u b x * H b x) t :=
        Q_sum_le k Finset.univ (fun b => (hw b).mul (hH b)) t
    _ ≤ n * ∑ b, algC d k CS * energyQ k (subF v u) t * K b := by
        rw [Finset.card_univ, Fintype.card_fin]
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (Nat.cast_nonneg _)
        refine (Q_mul_le hk hCS hsup (hw b) (hH b) (hwp b) (hHp b) t).trans ?_
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hQw b) hA0) (hQH b) (Q_nonneg _ _ _)
          (mul_nonneg hA0 (energyQ_nonneg _ _ _))
    _ = n * (algC d k CS * ∑ b, K b) * energyQ k (subF v u) t := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => by ring

/-! ### The commutator estimate -/

/-- **Commutator (Kato–Ponce type) estimate on the slices**: for `m > d/2` and `k ≥ 2m`, there is
`C` such that for all smooth periodic `a, w`, every word `|L| ≤ k` and every direction `i`,
`∫ (Σ_{(p,q) ∈ splitsNE L} ∂^pa ∂^q∂_iw)² ≤ C Q_k(a) Q_k(w)` on every slice; the left side is
`‖∂^L(a∂_iw) - a∂_i∂^Lw‖²_{L²}`. -/
theorem comm_int_le {m k : ℕ} (hm : (d : ℝ) / 2 < m) (hk : 2 * m ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a w : ST d → ℝ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ w → IsSPeriodic a →
      IsSPeriodic w → ∀ (L : List (Fin d)), L.length ≤ k → ∀ (i : Fin d) (t : ℝ),
        ∫ y in Icc (0 : Fin d → ℝ) 1, ((splitsNE L).map fun p =>
          sd p.1 a (Fin.cons t y) * sd p.2 (pd w i.succ) (Fin.cons t y)).sum ^ 2 ≤
          C * Q k a t * Q k w t := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    exact_mod_cast this
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine ⟨2 ^ (k' + 1) * (2 ^ (k' + 1) * CS), by positivity, ?_⟩
  intro a w ha hw hpa hpw L hL i t
  have hQa := Q_nonneg (k' + 1) a t
  have hQw := Q_nonneg (k' + 1) w t
  set G : List (Fin d) × List (Fin d) → ST d → ℝ := fun p x =>
    sd p.1 a x * sd p.2 (pd w i.succ) x with hG
  have hGc : ∀ p, Continuous (G p) := fun p =>
    (contDiff_sd p.1 ha).continuous.mul (contDiff_sd p.2 (contDiff_pd_top hw _)).continuous
  -- each split term
  have hterm : ∀ p ∈ splitsNE L, ∫ y in Icc (0 : Fin d → ℝ) 1, G p (Fin.cons t y) ^ 2 ≤
      CS * Q (k' + 1) a t * Q (k' + 1) w t := by
    intro p hp
    obtain ⟨hps, hp1⟩ := mem_splitsNE hp
    have hlen := length_of_mem_splits hps
    obtain ⟨j, r, hr⟩ := List.exists_cons_of_ne_nil hp1
    have hsd : sd p.1 a = sd r (pd a j.succ) := by rw [hr, sd_cons]
    have hrl : r.length + p.2.length ≤ k' := by
      rw [hr] at hlen; simp only [List.length_cons] at hlen; omega
    have ha' : ContDiff ℝ ∞ (pd a j.succ) := contDiff_pd_top ha _
    have hw' : ContDiff ℝ ∞ (pd w i.succ) := contDiff_pd_top hw _
    have hpa' : IsSPeriodic (pd a j.succ) := isSPeriodic_pd hpa _
    have hpw' : IsSPeriodic (pd w i.succ) := isSPeriodic_pd hpw _
    have hQa' : Q k' (pd a j.succ) t ≤ Q (k' + 1) a t := Q_pd_le j a t
    have hQw' : Q k' (pd w i.succ) t ≤ Q (k' + 1) w t := Q_pd_le i w t
    have hGp : ∀ y, G p (Fin.cons t y) = sd r (pd a j.succ) (Fin.cons t y) *
        sd p.2 (pd w i.succ) (Fin.cons t y) := fun y => by simp only [hG, hsd]
    simp_rw [hGp]
    by_cases hcase : r.length + m ≤ k'
    · refine (split_int_le_left ha' hw' (S := CS * Q k' (pd a j.succ) t) fun y =>
        (hsup _ (contDiff_sd r ha') (isSPeriodic_sd r hpa') t y).trans
          (mul_le_mul_of_nonneg_left (Q_sd_le hcase _ t) hCS)).trans ?_
      have h2 : ∫ y in Icc (0 : Fin d → ℝ) 1, sd p.2 (pd w i.succ) (Fin.cons t y) ^ 2 ≤
          Q (k' + 1) w t := (term_le_Q (by omega) _ t).trans hQw'
      exact mul_le_mul (mul_le_mul_of_nonneg_left hQa' hCS) h2
        (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (mul_nonneg hCS hQa)
    · have hcase' : p.2.length + m ≤ k' := by omega
      refine (split_int_le_right ha' hw' (S := CS * Q k' (pd w i.succ) t) fun y =>
        (hsup _ (contDiff_sd p.2 hw') (isSPeriodic_sd p.2 hpw') t y).trans
          (mul_le_mul_of_nonneg_left (Q_sd_le hcase' _ t) hCS)).trans ?_
      have h2 : ∫ y in Icc (0 : Fin d → ℝ) 1, sd r (pd a j.succ) (Fin.cons t y) ^ 2 ≤
          Q (k' + 1) a t := (term_le_Q (by omega) _ t).trans hQa'
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hQw' hCS) h2
        (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _)
        (mul_nonneg hCS hQw)).trans_eq (by ring)
  -- pointwise Cauchy–Schwarz over the list and integration
  have hlen : ((splitsNE L).length : ℝ) ≤ 2 ^ (k' + 1) := by
    have := (length_splitsNE_le L).trans (Nat.pow_le_pow_right (by norm_num) hL)
    exact_mod_cast this
  have hc2 : ∀ p, Continuous fun x => G p x ^ 2 := fun p => (hGc p).pow 2
  calc ∫ y in Icc (0 : Fin d → ℝ) 1, ((splitsNE L).map fun p => G p (Fin.cons t y)).sum ^ 2
      ≤ ∫ y in Icc (0 : Fin d → ℝ) 1, (splitsNE L).length *
          ((splitsNE L).map fun p => G p (Fin.cons t y) ^ 2).sum := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun y _ =>
          list_sum_sq_le _ (fun p => G p (Fin.cons t y))
        · have : ∀ y, ((splitsNE L).map fun p => G p (Fin.cons t y)).sum =
              ∑ q : Fin (splitsNE L).length, G (splitsNE L)[q.1] (Fin.cons t y) := fun y =>
            (Fin.sum_univ_fun_getElem _ (fun p => G p (Fin.cons t y))).symm
          simp_rw [this]
          exact integrableOn_slice ((continuous_finsetSum _ fun q _ => hGc _).pow 2) t
        · refine Integrable.const_mul ?_ _
          have : ∀ y, ((splitsNE L).map fun p => G p (Fin.cons t y) ^ 2).sum =
              ∑ q : Fin (splitsNE L).length, G (splitsNE L)[q.1] (Fin.cons t y) ^ 2 := fun y =>
            (Fin.sum_univ_fun_getElem _ (fun p => G p (Fin.cons t y) ^ 2)).symm
          simp_rw [this]
          exact integrable_finsetSum _ fun q _ => integrableOn_slice (hc2 _) t
    _ = (splitsNE L).length * ((splitsNE L).map fun p =>
          ∫ y in Icc (0 : Fin d → ℝ) 1, G p (Fin.cons t y) ^ 2).sum := by
        rw [integral_const_mul, integral_list_sum_slice (splitsNE L)
          (F := fun p x => G p x ^ 2) hc2 t]
    _ ≤ 2 ^ (k' + 1) * ((splitsNE L).length * (CS * Q (k' + 1) a t * Q (k' + 1) w t)) := by
        refine mul_le_mul hlen (list_sum_const_le _ hterm) ?_ (by positivity)
        exact List.sum_nonneg (by
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨p, _, rfl⟩ := hx
          exact setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _)
    _ ≤ 2 ^ (k' + 1) * (2 ^ (k' + 1) * (CS * Q (k' + 1) a t * Q (k' + 1) w t)) := by
        gcongr
    _ = 2 ^ (k' + 1) * (2 ^ (k' + 1) * CS) * Q (k' + 1) a t * Q (k' + 1) w t := by ring

/-! ### The static difference energy inequality -/

section Static

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

theorem pd_sub_eq {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (μ : Fin (d + 1)) (x : ST d) : pd (fun x => f x - g x) μ x = pd f μ x - pd g μ x := by
  unfold SobolevOpen.pd
  have h : HasFDerivAt (fun x => f x - g x) (fderiv ℝ f x - fderiv ℝ g x) x :=
    ((hf.differentiable (by simp)) x).hasFDerivAt.sub ((hg.differentiable (by simp)) x).hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The lower-order difference `F_a(V) - F_a(U)`. -/
def Xt (F : Fin n → (Fin n → ℝ) → ℝ) (u v : Fin n → ST d → ℝ) (a : Fin n) : ST d → ℝ :=
  fun x => compF (F a) v x - compF (F a) u x

/-- The coefficient-difference term `(A^i_{ab}(V) - A^i_{ab}(U)) ∂_iu_b`. -/
def Yt (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (u v : Fin n → ST d → ℝ) (i : Fin d)
    (a b : Fin n) : ST d → ℝ :=
  fun x => (compF (A i a b) v x - compF (A i a b) u x) * pd (u b) i.succ x

/-- The commutator `[∂^L, A^i_{ab}(V)]∂_iw_b` in Leibniz form. -/
def commT (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (u v : Fin n → ST d → ℝ)
    (L : List (Fin d)) (i : Fin d) (a b : Fin n) (x : ST d) : ℝ :=
  ((splitsNE L).map fun p => sd p.1 (compF (A i a b) v) x *
    sd p.2 (pd (subF v u b) i.succ) x).sum

/-- The generator difference
`G(V)_a - G(U)_a = (F_a(V) - F_a(U)) - Σ_{i,b}(A^i_{ab}(V)∂_iw_b + (A^i_{ab}(V) - A^i_{ab}(U))∂_iu_b)`. -/
theorem genG_sub_eq {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    (hv : ∀ b, ContDiff ℝ ∞ (v b)) (a : Fin n) :
    (fun x => genG A F v a x - genG A F u a x) = fun x => Xt F u v a x -
      ∑ i, ∑ b, (compF (A i a b) v x * pd (subF v u b) i.succ x + Yt A u v i a b x) := by
  funext x
  have hpd : ∀ (i : Fin d) b, pd (subF v u b) i.succ x = pd (v b) i.succ x - pd (u b) i.succ x :=
    fun i b => pd_sub_eq (hv b) (hu b) _ x
  have e : ∀ (i : Fin d) b, compF (A i a b) v x * pd (subF v u b) i.succ x + Yt A u v i a b x =
      compF (A i a b) v x * pd (v b) i.succ x - compF (A i a b) u x * pd (u b) i.succ x := by
    intro i b; rw [hpd]; simp only [Yt]; ring
  simp only [e, Finset.sum_sub_distrib, genG, Xt]
  ring

/-- **The word derivative of the generator difference** in commutator form. -/
theorem sd_genG_sub (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (hv : ∀ b, ContDiff ℝ ∞ (v b))
    (a : Fin n) (L : List (Fin d)) (x : ST d) :
    sd L (fun x => genG A F v a x - genG A F u a x) x = sd L (Xt F u v a) x -
      ∑ i, ∑ b, (compF (A i a b) v x * pd (sd L (subF v u b)) i.succ x +
        commT A u v L i a b x + sd L (Yt A u v i a b) x) := by
  have hw := contDiff_subF hu hv
  have hAv : ∀ i a b, ContDiff ℝ ∞ (compF (A i a b) v) := fun i a b => contDiff_compF (hA i a b) hv
  have hAu : ∀ i a b, ContDiff ℝ ∞ (compF (A i a b) u) := fun i a b => contDiff_compF (hA i a b) hu
  have hX : ContDiff ℝ ∞ (Xt F u v a) := (contDiff_compF (hF a) hv).sub (contDiff_compF (hF a) hu)
  have hP : ∀ i b, ContDiff ℝ ∞ (fun x => compF (A i a b) v x * pd (subF v u b) i.succ x) :=
    fun i b => (hAv i a b).mul (contDiff_pd_top (hw b) _)
  have hY : ∀ i b, ContDiff ℝ ∞ (Yt A u v i a b) := fun i b =>
    ((hAv i a b).sub (hAu i a b)).mul (contDiff_pd_top (hu b) _)
  have hPY : ∀ i b, ContDiff ℝ ∞ (fun x => compF (A i a b) v x * pd (subF v u b) i.succ x +
      Yt A u v i a b x) := fun i b => (hP i b).add (hY i b)
  have hS : ContDiff ℝ ∞ (fun x => ∑ i, ∑ b, (compF (A i a b) v x * pd (subF v u b) i.succ x +
      Yt A u v i a b x)) := ContDiff.sum fun i _ => ContDiff.sum fun b _ => hPY i b
  rw [genG_sub_eq hu hv a, sd_sub L hX hS]
  beta_reduce
  rw [sd_sum L Finset.univ (f := fun i x => ∑ b, (compF (A i a b) v x * pd (subF v u b) i.succ x +
      Yt A u v i a b x)) (fun i => ContDiff.sum fun b _ => hPY i b)]
  beta_reduce
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sd_sum L Finset.univ (f := fun b x => compF (A i a b) v x * pd (subF v u b) i.succ x +
      Yt A u v i a b x) (fun b => hPY i b)]
  beta_reduce
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sd_add L (hP i b) (hY i b)]
  beta_reduce
  rw [sd_mul_comm L (hAv i a b) (contDiff_pd_top (hw b) _) x, sd_pd L (hw b) i]
  simp only [commT]

/-- The pointwise algebra of the word estimate. -/
theorem pointwise_alg (s Xv : Fin n → ℝ) (P C Y : Fin d → Fin n → Fin n → ℝ) :
    ∑ a, s a * (Xv a - ∑ i, ∑ b, (P i a b + C i a b + Y i a b)) ≤
      (1 / 2) * ∑ a, s a ^ 2 + ∑ a, Xv a ^ 2 +
        2 * d * n * ∑ a, ∑ i, ∑ b, (C i a b ^ 2 + Y i a b ^ 2) -
        ∑ a, ∑ i, ∑ b, s a * P i a b := by
  have hcs : ∀ z : Fin d → Fin n → ℝ, (∑ i, ∑ b, z i b) ^ 2 ≤ d * n * ∑ i, ∑ b, z i b ^ 2 := by
    intro z
    have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => ∑ b, z i b)
    have h2 : ∀ i, (∑ b, z i b) ^ 2 ≤ n * ∑ b, z i b ^ 2 := fun i => by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun b => z i b)
      simpa using this
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    calc (∑ i, ∑ b, z i b) ^ 2 ≤ d * ∑ i, (∑ b, z i b) ^ 2 := h1
      _ ≤ d * ∑ i, (n * ∑ b, z i b ^ 2) := by gcongr with i; exact h2 i
      _ = d * n * ∑ i, ∑ b, z i b ^ 2 := by rw [← Finset.mul_sum]; ring
  have hrow : ∀ a, s a * (Xv a - ∑ i, ∑ b, (P i a b + C i a b + Y i a b)) ≤
      (1 / 2) * s a ^ 2 + Xv a ^ 2 + 2 * d * n * ∑ i, ∑ b, (C i a b ^ 2 + Y i a b ^ 2) -
        ∑ i, ∑ b, s a * P i a b := by
    intro a
    set S := ∑ i, ∑ b, (C i a b + Y i a b) with hS
    have hsplit : s a * (Xv a - ∑ i, ∑ b, (P i a b + C i a b + Y i a b)) =
        s a * (Xv a - S) - ∑ i, ∑ b, s a * P i a b := by
      rw [hS]
      simp only [Finset.sum_add_distrib, mul_sub, mul_add, Finset.mul_sum]
      ring
    have h1 : S ^ 2 ≤ d * n * ∑ i, ∑ b, (C i a b + Y i a b) ^ 2 := hcs _
    have h2 : ∑ i, ∑ b, (C i a b + Y i a b) ^ 2 ≤ 2 * ∑ i, ∑ b, (C i a b ^ 2 + Y i a b ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      nlinarith [sq_nonneg (C i a b - Y i a b)]
    have hdn : (0 : ℝ) ≤ d * n := by positivity
    have h3 : S ^ 2 ≤ 2 * d * n * ∑ i, ∑ b, (C i a b ^ 2 + Y i a b ^ 2) := by
      calc S ^ 2 ≤ d * n * ∑ i, ∑ b, (C i a b + Y i a b) ^ 2 := h1
        _ ≤ d * n * (2 * ∑ i, ∑ b, (C i a b ^ 2 + Y i a b ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hdn
        _ = 2 * d * n * ∑ i, ∑ b, (C i a b ^ 2 + Y i a b ^ 2) := by ring
    rw [hsplit]
    nlinarith [sq_nonneg (s a - (Xv a - S)), sq_nonneg (Xv a + S)]
  calc ∑ a, s a * (Xv a - ∑ i, ∑ b, (P i a b + C i a b + Y i a b))
      ≤ ∑ a, ((1 / 2) * s a ^ 2 + Xv a ^ 2 + 2 * d * n * ∑ i, ∑ b, (C i a b ^ 2 + Y i a b ^ 2) -
        ∑ i, ∑ b, s a * P i a b) := Finset.sum_le_sum fun a _ => hrow a
    _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]


/-- Splitting a slice integral of a linear combination of continuous functions. -/
theorem sliceInt_split {f1 f2 f3 f4 : ST d → ℝ} (c1 : Continuous f1) (c2 : Continuous f2)
    (c3 : Continuous f3) (c4 : Continuous f4) (α γ t : ℝ) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, (α * f1 (Fin.cons t y) + f2 (Fin.cons t y) +
      γ * f3 (Fin.cons t y) - f4 (Fin.cons t y)) =
      α * (∫ y in Icc (0 : Fin d → ℝ) 1, f1 (Fin.cons t y)) +
        (∫ y in Icc (0 : Fin d → ℝ) 1, f2 (Fin.cons t y)) +
        γ * (∫ y in Icc (0 : Fin d → ℝ) 1, f3 (Fin.cons t y)) -
        (∫ y in Icc (0 : Fin d → ℝ) 1, f4 (Fin.cons t y)) := by
  have i1 := integrableOn_slice c1 t
  have i2 := integrableOn_slice c2 t
  have i3 := integrableOn_slice c3 t
  have i4 := integrableOn_slice c4 t
  have j1 : Integrable (fun y : Fin d → ℝ => α * f1 (Fin.cons t y))
      (volume.restrict (Icc (0 : Fin d → ℝ) 1)) := i1.const_mul _
  have j3 : Integrable (fun y : Fin d → ℝ => γ * f3 (Fin.cons t y))
      (volume.restrict (Icc (0 : Fin d → ℝ) 1)) := i3.const_mul _
  have j12 : Integrable (fun y : Fin d → ℝ => α * f1 (Fin.cons t y) + f2 (Fin.cons t y))
      (volume.restrict (Icc (0 : Fin d → ℝ) 1)) := j1.add i2
  have j123 : Integrable (fun y : Fin d → ℝ => α * f1 (Fin.cons t y) + f2 (Fin.cons t y) +
      γ * f3 (Fin.cons t y)) (volume.restrict (Icc (0 : Fin d → ℝ) 1)) := j12.add j3
  rw [integral_sub j123 i4, integral_add j12 j3, integral_add j1 i2, integral_const_mul,
    integral_const_mul]

/-- **The principal term after symmetric integration by parts**: for a symmetric smooth periodic
matrix field `B_{ab}` with `|∂_iB_{ab}| ≤ P` on the slice,
`-∫ Σ_{a,b} V_a B_{ab} ∂_iV_b ≤ ½ P n ∫ Σ_a V_a²`. -/
theorem neg_int_sym_le {V : Fin n → ST d → ℝ} (hV : ∀ a, ContDiff ℝ ∞ (V a))
    (hVp : ∀ a, IsSPeriodic (V a)) {B : Fin n → Fin n → ST d → ℝ}
    (hB : ∀ a b, ContDiff ℝ ∞ (B a b)) (hBp : ∀ a b, IsSPeriodic (B a b))
    (hsym : ∀ a b x, B a b x = B b a x) (t : ℝ) (i : Fin d) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ a b (y : Fin d → ℝ), |pd (B a b) i.succ (Fin.cons t y)| ≤ P) :
    -(∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b, V a (Fin.cons t y) * B a b (Fin.cons t y) *
        pd (V b) i.succ (Fin.cons t y)) ≤
      1 / 2 * (P * n) * ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, V a (Fin.cons t y) ^ 2 := by
  rw [integral_sym_eq hV hVp hB hBp hsym t i]
  have c1 : Continuous fun x => ∑ a, V a x ^ 2 :=
    continuous_finsetSum _ fun a _ => (hV a).continuous.pow 2
  have hb : ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b, V a (Fin.cons t y) *
      pd (B a b) i.succ (Fin.cons t y) * V b (Fin.cons t y) ≤
      ∫ y in Icc (0 : Fin d → ℝ) 1, P * n * ∑ a, V a (Fin.cons t y) ^ 2 := by
    refine setIntegral_mono_on ?_ ((integrableOn_slice c1 t).const_mul _) measurableSet_Icc
      fun y _ => sum_mul_mul_le_sq hP0 fun a b => hP a b y
    exact integrableOn_slice (continuous_finsetSum _ fun a _ => continuous_finsetSum _
      fun b _ => ((hV a).continuous.mul (contDiff_pd_top (hB a b) _).continuous).mul
        (hV b).continuous) t
  rw [integral_const_mul] at hb
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The word estimate** of the static difference inequality, given the bounds on the pieces. -/
theorem word_diff_le (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (hv : ∀ b, ContDiff ℝ ∞ (v b))
    (hpu : ∀ b, IsSPeriodic (u b)) (hpv : ∀ b, IsSPeriodic (v b)) {k : ℕ} {L : List (Fin d)}
    (hLk : L.length ≤ k) {t E BX BC BY P : ℝ} (hP0 : 0 ≤ P)
    (hX : ∀ a, Q k (Xt F u v a) t ≤ BX * E)
    (hC : ∀ i a b, ∫ y in Icc (0 : Fin d → ℝ) 1, commT A u v L i a b (Fin.cons t y) ^ 2 ≤ BC * E)
    (hY : ∀ i a b, Q k (Yt A u v i a b) t ≤ BY * E)
    (hPb : ∀ i a b (y : Fin d → ℝ), |pd (compF (A i a b) v) i.succ (Fin.cons t y)| ≤ P) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (subF v u a) (Fin.cons t y) *
        sd L (fun x => genG A F v a x - genG A F u a x) (Fin.cons t y) ≤
      (1 / 2 + 1 / 2 * d * (P * n)) *
          (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (subF v u a) (Fin.cons t y) ^ 2) +
        (n * BX + 2 * d * n * (n * d * n * (BC + BY))) * E := by
  have hw := contDiff_subF hu hv
  have hwp := isSPeriodic_subF hpu hpv
  have hAv : ∀ i a b, ContDiff ℝ ∞ (compF (A i a b) v) := fun i a b => contDiff_compF (hA i a b) hv
  have hAu : ∀ i a b, ContDiff ℝ ∞ (compF (A i a b) u) := fun i a b => contDiff_compF (hA i a b) hu
  have hAvp : ∀ i a b, IsSPeriodic (compF (A i a b) v) := fun i a b => isSPeriodic_compF _ hpv
  set sw : Fin n → ST d → ℝ := fun a => sd L (subF v u a) with hsw
  have hs : ∀ a, ContDiff ℝ ∞ (sw a) := fun a => contDiff_sd L (hw a)
  have hsp : ∀ a, IsSPeriodic (sw a) := fun a => isSPeriodic_sd L (hwp a)
  have hXc : ∀ a, Continuous (sd L (Xt F u v a)) := fun a =>
    (contDiff_sd L ((contDiff_compF (hF a) hv).sub (contDiff_compF (hF a) hu))).continuous
  have hYs : ∀ i a b, ContDiff ℝ ∞ (Yt A u v i a b) := fun i a b =>
    ((hAv i a b).sub (hAu i a b)).mul (contDiff_pd_top (hu b) _)
  have hYc : ∀ i a b, Continuous (sd L (Yt A u v i a b)) := fun i a b =>
    (contDiff_sd L (hYs i a b)).continuous
  have hCc' : ∀ i a b, Continuous (commT A u v L i a b) := fun i a b =>
    continuous_list_sum _ fun p _ => (contDiff_sd p.1 (hAv i a b)).continuous.mul
      (contDiff_sd p.2 (contDiff_pd_top (hw b) _)).continuous
  -- the four integrands
  set f1 : ST d → ℝ := fun x => ∑ a, sw a x ^ 2 with hf1
  set f2 : ST d → ℝ := fun x => ∑ a, sd L (Xt F u v a) x ^ 2 with hf2
  set f3 : ST d → ℝ := fun x => ∑ a, ∑ i, ∑ b,
    (commT A u v L i a b x ^ 2 + sd L (Yt A u v i a b) x ^ 2) with hf3
  set f4 : ST d → ℝ := fun x => ∑ a, ∑ i, ∑ b, sw a x * (compF (A i a b) v x *
      pd (sw b) i.succ x) with hf4
  have c1 : Continuous f1 := continuous_finsetSum _ fun a _ => (hs a).continuous.pow 2
  have c2 : Continuous f2 := continuous_finsetSum _ fun a _ => (hXc a).pow 2
  have c3 : Continuous f3 := continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun b _ => ((hCc' i a b).pow 2).add ((hYc i a b).pow 2)
  have c4 : Continuous f4 := continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun b _ => (hs a).continuous.mul ((hAv i a b).continuous.mul
      (contDiff_pd_top (hs b) _).continuous)
  have hlhs : Continuous fun x => ∑ a, sw a x *
      sd L (fun x => genG A F v a x - genG A F u a x) x :=
    continuous_finsetSum _ fun a _ => (hs a).continuous.mul (contDiff_sd L
      ((contDiff_genG hA hF hv a).sub (contDiff_genG hA hF hu a))).continuous
  -- pointwise
  have hpt : ∀ x, ∑ a, sw a x * sd L (fun x => genG A F v a x - genG A F u a x) x ≤
      (1 / 2) * f1 x + f2 x + 2 * d * n * f3 x - f4 x := by
    intro x
    simp only [sd_genG_sub hA hF hu hv _ L x]
    have := pointwise_alg (d := d) (fun a => sw a x) (fun a => sd L (Xt F u v a) x)
      (fun i a b => compF (A i a b) v x * pd (sw b) i.succ x)
      (fun i a b => commT A u v L i a b x) (fun i a b => sd L (Yt A u v i a b) x)
    simpa only [hf1, hf2, hf3, hf4, hsw] using this
  have hI : ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sw a (Fin.cons t y) *
      sd L (fun x => genG A F v a x - genG A F u a x) (Fin.cons t y) ≤
      (1 / 2) * (∫ y in Icc (0 : Fin d → ℝ) 1, f1 (Fin.cons t y)) +
        (∫ y in Icc (0 : Fin d → ℝ) 1, f2 (Fin.cons t y)) +
        2 * d * n * (∫ y in Icc (0 : Fin d → ℝ) 1, f3 (Fin.cons t y)) -
        (∫ y in Icc (0 : Fin d → ℝ) 1, f4 (Fin.cons t y)) := by
    rw [← sliceInt_split c1 c2 c3 c4]
    exact setIntegral_mono_on (integrableOn_slice hlhs t)
      (integrableOn_slice (f := fun x => (1 / 2) * f1 x + f2 x + 2 * d * n * f3 x - f4 x)
        (((continuous_const.mul c1).add c2).add (continuous_const.mul c3) |>.sub c4) t)
      measurableSet_Icc fun y _ => hpt _
  -- `∫ f2`
  have hb2 : ∫ y in Icc (0 : Fin d → ℝ) 1, f2 (Fin.cons t y) ≤ n * BX * E := by
    simp only [hf2]
    rw [integral_finsetSum (f := fun a y => sd L (Xt F u v a) (Fin.cons t y) ^ 2) _
      fun a _ => integrableOn_sq (hXc a) t]
    calc ∑ a, ∫ y in Icc (0 : Fin d → ℝ) 1, sd L (Xt F u v a) (Fin.cons t y) ^ 2
        ≤ ∑ _a : Fin n, BX * E := Finset.sum_le_sum fun a _ => (term_le_Q hLk _ t).trans (hX a)
      _ = n * BX * E := by simp; ring
  -- `∫ f3`
  have hb3 : ∫ y in Icc (0 : Fin d → ℝ) 1, f3 (Fin.cons t y) ≤ n * d * n * (BC + BY) * E := by
    have hterm : ∀ i a b, ∫ y in Icc (0 : Fin d → ℝ) 1, (commT A u v L i a b (Fin.cons t y) ^ 2 +
        sd L (Yt A u v i a b) (Fin.cons t y) ^ 2) ≤ (BC + BY) * E := by
      intro i a b
      rw [integral_add (integrableOn_sq (hCc' i a b) t) (integrableOn_sq (hYc i a b) t)]
      have := add_le_add (hC i a b) ((term_le_Q hLk _ t).trans (hY i a b))
      linarith
    simp only [hf3]
    rw [integral_finsetSum (f := fun a y => ∑ i, ∑ b, (commT A u v L i a b (Fin.cons t y) ^ 2 +
        sd L (Yt A u v i a b) (Fin.cons t y) ^ 2)) _
      fun a _ => integrableOn_slice (f := fun x => ∑ i, ∑ b, (commT A u v L i a b x ^ 2 +
        sd L (Yt A u v i a b) x ^ 2)) (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun b _ => ((hCc' i a b).pow 2).add ((hYc i a b).pow 2)) t]
    calc ∑ a, ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ i, ∑ b, (commT A u v L i a b (Fin.cons t y) ^ 2 +
          sd L (Yt A u v i a b) (Fin.cons t y) ^ 2)
        ≤ ∑ _a : Fin n, ∑ _i : Fin d, ∑ _b : Fin n, (BC + BY) * E := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [integral_finsetSum (f := fun i y => ∑ b, (commT A u v L i a b (Fin.cons t y) ^ 2 +
              sd L (Yt A u v i a b) (Fin.cons t y) ^ 2)) _
            fun i _ => integrableOn_slice (f := fun x => ∑ b, (commT A u v L i a b x ^ 2 +
              sd L (Yt A u v i a b) x ^ 2)) (continuous_finsetSum _
            fun b _ => ((hCc' i a b).pow 2).add ((hYc i a b).pow 2)) t]
          refine Finset.sum_le_sum fun i _ => ?_
          rw [integral_finsetSum (f := fun b y => commT A u v L i a b (Fin.cons t y) ^ 2 +
              sd L (Yt A u v i a b) (Fin.cons t y) ^ 2) _ fun b _ => integrableOn_slice
            (f := fun x => commT A u v L i a b x ^ 2 + sd L (Yt A u v i a b) x ^ 2)
            (((hCc' i a b).pow 2).add ((hYc i a b).pow 2)) t]
          exact Finset.sum_le_sum fun b _ => hterm i a b
      _ = n * d * n * (BC + BY) * E := by simp; ring
  -- `-∫ f4`
  have hb4 : -(∫ y in Icc (0 : Fin d → ℝ) 1, f4 (Fin.cons t y)) ≤
      1 / 2 * d * (P * n) * (∫ y in Icc (0 : Fin d → ℝ) 1, f1 (Fin.cons t y)) := by
    have hf4' : ∀ x, f4 x = ∑ i, ∑ a, ∑ b, sw a x * compF (A i a b) v x * pd (sw b) i.succ x := by
      intro x
      simp only [hf4, mul_assoc]
      rw [Finset.sum_comm]
    have hci : ∀ i, Continuous fun x => ∑ a, ∑ b, sw a x * compF (A i a b) v x *
        pd (sw b) i.succ x := fun i => continuous_finsetSum _ fun a _ =>
      continuous_finsetSum _ fun b _ => ((hs a).continuous.mul (hAv i a b).continuous).mul
        (contDiff_pd_top (hs b) _).continuous
    simp_rw [hf4']
    rw [integral_finsetSum (f := fun i y => ∑ a, ∑ b, sw a (Fin.cons t y) *
        compF (A i a b) v (Fin.cons t y) * pd (sw b) i.succ (Fin.cons t y)) _
      fun i _ => integrableOn_slice (hci i) t, ← Finset.sum_neg_distrib]
    calc ∑ i, -(∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b, sw a (Fin.cons t y) *
          compF (A i a b) v (Fin.cons t y) * pd (sw b) i.succ (Fin.cons t y))
        ≤ ∑ _i : Fin d, 1 / 2 * (P * n) * ∫ y in Icc (0 : Fin d → ℝ) 1, f1 (Fin.cons t y) :=
          Finset.sum_le_sum fun i _ => neg_int_sym_le hs hsp (B := fun a b => compF (A i a b) v)
            (fun a b => hAv i a b) (fun a b => hAvp i a b) (fun a b x => hsym i a b _) t i hP0
            (fun a b y => hPb i a b y)
      _ = 1 / 2 * d * (P * n) * (∫ y in Icc (0 : Fin d → ℝ) 1, f1 (Fin.cons t y)) := by
          simp; ring
  have hdn : (0 : ℝ) ≤ 2 * d * n := by positivity
  have hb3' := mul_le_mul_of_nonneg_left hb3 hdn
  calc _ ≤ _ := hI
    _ ≤ (1 / 2 + 1 / 2 * d * (P * n)) * (∫ y in Icc (0 : Fin d → ℝ) 1, f1 (Fin.cons t y)) +
        (n * BX + 2 * d * n * (n * d * n * (BC + BY))) * E := by nlinarith

/-- **The static difference energy inequality** (`prop:coupled-bootstrap`, proof of
`eq:actual-jet-gauge-energy`): on `𝕋^d`, for `m > d/2`, `k ≥ 2m`, smooth real symmetric `A^i(v)`,
smooth `F(v)` and every radius `R`, there is `K` such that for all smooth periodic `U` (reference)
and `V` (approximate) with `‖U(t)‖²_{H^k} + ‖V(t)‖²_{H^k} ≤ R²` and `‖U(t)‖²_{H^{k+1}} ≤ R²`,
`⟨V - U, G(V) - G(U)⟩_{H^k}(t) ≤ K ‖V(t) - U(t)‖²_{H^k}`.  The proof: Lipschitz Moser for
`F(V) - F(U)` and `A(V) - A(U)`, the reference's extra derivative for `(A(V) - A(U))∂U`, the
commutator estimate for `[∂^L, A(V)]∂(V - U)`, and symmetric integration by parts with
`‖∂A(V)‖_∞ ≤ C(R)` (`H^k ↪ W^{1,∞}`) for the principal term. -/
theorem pairQ_genG_sub_le {m k : ℕ} (hm : (d : ℝ) / 2 < m) (hk : 2 * m ≤ k)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u v : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, ContDiff ℝ ∞ (v b)) → (∀ b, IsSPeriodic (u b)) → (∀ b, IsSPeriodic (v b)) → ∀ t,
      energyQ k u t + energyQ k v t ≤ R ^ 2 → energyQ (k + 1) u t ≤ R ^ 2 →
      pairQ k (subF v u) (fun a x => genG A F v a x - genG A F u a x) t ≤
        K * energyQ k (subF v u) t := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    exact_mod_cast this
  have hk1 : 2 * m ≤ k + 1 := by omega
  have hCF := fun a => Q_compF_sub_le hm hk1 (hF a) hR
  choose CF hCF0 hCF using hCF
  have hCA := fun (p : Fin d × Fin n × Fin n) => Q_compF_sub_le hm hk1 (hA p.1 p.2.1 p.2.2) hR
  choose CA hCA0 hCA using hCA
  have hKA := fun (p : Fin d × Fin n × Fin n) =>
    SlabMoser.Q_compF_le hm hk1 (hA p.1 p.2.1 p.2.2) hR
  choose KA hKA0 hKA using hKA
  obtain ⟨Cc, hCc0, hCc⟩ := comm_int_le hm hk
  set CFs := ∑ a, CF a with hCFs
  set CAs := ∑ p, CA p with hCAs
  set KAs := ∑ p, KA p with hKAs
  have hCFs0 : 0 ≤ CFs := Finset.sum_nonneg fun a _ => hCF0 a
  have hCAs0 : 0 ≤ CAs := Finset.sum_nonneg fun p _ => hCA0 p
  have hKAs0 : 0 ≤ KAs := Finset.sum_nonneg fun p _ => hKA0 p
  have hCF_le : ∀ a, CF a ≤ CFs := fun a =>
    Finset.single_le_sum (f := CF) (fun a _ => hCF0 a) (Finset.mem_univ a)
  have hCA_le : ∀ p, CA p ≤ CAs := fun p =>
    Finset.single_le_sum (f := CA) (fun p _ => hCA0 p) (Finset.mem_univ p)
  have hKA_le : ∀ p, KA p ≤ KAs := fun p =>
    Finset.single_le_sum (f := KA) (fun p _ => hKA0 p) (Finset.mem_univ p)
  have hal := algC_nonneg (d := d) k hCS
  set P := Real.sqrt (CS * KAs) with hP
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  set Kw : ℝ := 1 / 2 + 1 / 2 * d * (P * n) with hKw
  set Kc : ℝ := n * CFs + 2 * d * n * (n * d * n * (Cc * KAs + algC d k CS * CAs * R ^ 2))
    with hKc
  set W : ℝ := ((wordsLE d k).card : ℝ) with hW
  have hKw0 : 0 ≤ Kw := by positivity
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨Kw + W * Kc, by positivity, ?_⟩
  intro u v hu hv hpu hpv t hE hE1
  have hw := contDiff_subF hu hv
  have hwp := isSPeriodic_subF hpu hpv
  set E := energyQ k (subF v u) t with hEdef
  have hE0 : 0 ≤ E := energyQ_nonneg _ _ _
  have hEv : energyQ k v t ≤ R ^ 2 := by linarith [energyQ_nonneg k u t]
  have hQw : ∀ b, Q k (subF v u b) t ≤ E := fun b =>
    Finset.single_le_sum (f := fun b => Q k (subF v u b) t) (fun b _ => Q_nonneg k _ t)
      (Finset.mem_univ b)
  have hAv : ∀ i a b, ContDiff ℝ ∞ (compF (A i a b) v) := fun i a b => contDiff_compF (hA i a b) hv
  have hAu : ∀ i a b, ContDiff ℝ ∞ (compF (A i a b) u) := fun i a b => contDiff_compF (hA i a b) hu
  have hAvp : ∀ i a b, IsSPeriodic (compF (A i a b) v) := fun i a b => isSPeriodic_compF _ hpv
  have hAup : ∀ i a b, IsSPeriodic (compF (A i a b) u) := fun i a b => isSPeriodic_compF _ hpu
  have hQAv : ∀ i a b, Q k (compF (A i a b) v) t ≤ KAs := fun i a b =>
    (hKA (i, a, b) v hv hpv t hEv).trans (hKA_le _)
  have hPb : ∀ i a b (y : Fin d → ℝ), |pd (compF (A i a b) v) i.succ (Fin.cons t y)| ≤ P := by
    intro i a b y
    refine Real.abs_le_sqrt ?_
    have h1 := hsup _ (contDiff_pd_top (hAv i a b) i.succ) (isSPeriodic_pd (hAvp i a b) _) t y
    have h2 : Q m (pd (compF (A i a b) v) i.succ) t ≤ KAs :=
      ((Q_pd_le i _ t).trans (Q_mono (by omega) _ t)).trans (hQAv i a b)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hCS)
  have hX : ∀ a, Q k (Xt F u v a) t ≤ CFs * E := fun a =>
    (hCF a u v hu hv hpu hpv t hE).trans (mul_le_mul_of_nonneg_right (hCF_le a) hE0)
  have hC : ∀ L : List (Fin d), L.length ≤ k → ∀ i a b, ∫ y in Icc (0 : Fin d → ℝ) 1,
      commT A u v L i a b (Fin.cons t y) ^ 2 ≤ (Cc * KAs) * E := by
    intro L hLk i a b
    refine (hCc (compF (A i a b) v) (subF v u b) (hAv i a b) (hw b) (hAvp i a b) (hwp b)
      L hLk i t).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hQAv i a b) hCc0) (hQw b) (Q_nonneg _ _ _)
      (mul_nonneg hCc0 hKAs0)
  have hY : ∀ i a b, Q k (Yt A u v i a b) t ≤ (algC d k CS * CAs * R ^ 2) * E := by
    intro i a b
    have hdiff : ContDiff ℝ ∞ (fun x => compF (A i a b) v x - compF (A i a b) u x) :=
      (hAv i a b).sub (hAu i a b)
    have hdp : IsSPeriodic (fun x => compF (A i a b) v x - compF (A i a b) u x) :=
      fun k x => by simp only [hAvp i a b k x, hAup i a b k x]
    have h1 := Q_mul_le hk1 hCS hsup hdiff (contDiff_pd_top (hu b) i.succ) hdp
      (isSPeriodic_pd (hpu b) _) t
    have h2 : Q k (fun x => compF (A i a b) v x - compF (A i a b) u x) t ≤ CAs * E :=
      (hCA (i, a, b) u v hu hv hpu hpv t hE).trans
        (mul_le_mul_of_nonneg_right (hCA_le _) hE0)
    have h3 : Q k (pd (u b) i.succ) t ≤ R ^ 2 :=
      (Q_pd_le i _ t).trans ((Finset.single_le_sum (f := fun b => Q (k + 1) (u b) t)
        (fun b _ => Q_nonneg _ _ t) (Finset.mem_univ b)).trans hE1)
    calc Q k (Yt A u v i a b) t ≤ algC d k CS *
          Q k (fun x => compF (A i a b) v x - compF (A i a b) u x) t *
          Q k (pd (u b) i.succ) t := h1
      _ ≤ algC d k CS * (CAs * E) * R ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 hal) h3 (Q_nonneg _ _ _)
            (mul_nonneg hal (mul_nonneg hCAs0 hE0))
      _ = algC d k CS * CAs * R ^ 2 * E := by ring
  have hword : ∀ L ∈ wordsLE d k, ∫ y in Icc (0 : Fin d → ℝ) 1,
      ∑ a, sd L (subF v u a) (Fin.cons t y) *
        sd L (fun x => genG A F v a x - genG A F u a x) (Fin.cons t y) ≤
      Kw * (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (subF v u a) (Fin.cons t y) ^ 2) +
        Kc * E := fun L hL =>
    word_diff_le hA hsym hF hu hv hpu hpv (mem_wordsLE.mp hL) hP0 hX
      (hC L (mem_wordsLE.mp hL)) hY hPb
  have hsumV : ∑ L ∈ wordsLE d k, ∫ y in Icc (0 : Fin d → ℝ) 1,
      ∑ a, sd L (subF v u a) (Fin.cons t y) ^ 2 = E := by
    rw [hEdef]
    unfold energyQ Q
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [integral_finsetSum (f := fun a y => sd L (subF v u a) (Fin.cons t y) ^ 2) _
      fun a _ => integrableOn_sq (contDiff_sd L (hw a)).continuous t]
  have hpair : pairQ k (subF v u) (fun a x => genG A F v a x - genG A F u a x) t =
      ∑ L ∈ wordsLE d k, ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (subF v u a) (Fin.cons t y) *
        sd L (fun x => genG A F v a x - genG A F u a x) (Fin.cons t y) := by
    unfold pairQ
    beta_reduce
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [integral_finsetSum (f := fun a y => sd L (subF v u a) (Fin.cons t y) *
        sd L (fun x => genG A F v a x - genG A F u a x) (Fin.cons t y)) _
      fun a _ => integrableOn_slice ((contDiff_sd L (hw a)).continuous.mul
      (contDiff_sd L ((contDiff_genG hA hF hv a).sub (contDiff_genG hA hF hu a))).continuous) t]
  rw [hpair]
  calc ∑ L ∈ wordsLE d k, ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (subF v u a) (Fin.cons t y) *
        sd L (fun x => genG A F v a x - genG A F u a x) (Fin.cons t y)
      ≤ ∑ L ∈ wordsLE d k, (Kw * (∫ y in Icc (0 : Fin d → ℝ) 1,
          ∑ a, sd L (subF v u a) (Fin.cons t y) ^ 2) + Kc * E) :=
        Finset.sum_le_sum fun L hL => hword L hL
    _ = Kw * E + W * Kc * E := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumV, Finset.sum_const, nsmul_eq_mul]
        ring
    _ = (Kw + W * Kc) * E := by ring

end Static


/-! ### The time derivative of the `H^k` energy -/

section Dynamic

/-- The time derivative of a slice integral of a smooth function. -/
theorem hasDerivAt_sliceInt_d {P : ST d → ℝ} (hP : ContDiff ℝ ∞ P) (t : ℝ) :
    HasDerivAt (fun s => ∫ y in Icc (0 : Fin d → ℝ) 1, P (Fin.cons s y))
      (∫ y in Icc (0 : Fin d → ℝ) 1, pd P 0 (Fin.cons t y)) t := by
  have hcT : Continuous (pd P 0) := (contDiff_pd_top hP 0).continuous
  set K : Set (ST d) := (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : ST d)) ''
    (Icc (t - 1) (t + 1) ×ˢ Icc 0 1)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image continuous_cons2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcT.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc (0 : Fin d → ℝ) 1))
    (F := fun s y => P (Fin.cons s y)) (F' := fun s y => pd P 0 (Fin.cons s y))
    (x₀ := t) (bound := fun _ => C) (s := Ioo (t - 1) (t + 1))
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    (Eventually.of_forall fun s => (hP.continuous.comp (continuous_cons s)).aestronglyMeasurable)
    (integrableOn_slice hP.continuous t)
    ((hcT.comp (continuous_cons t)).aestronglyMeasurable)
    (by
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall fun y hy s hs => ?_
      exact hC _ ⟨(s, y), ⟨Ioo_subset_Icc_self hs, hy⟩, rfl⟩)
    (integrable_const C)
    (Eventually.of_forall fun y s _ => hasDerivAt_time y ((hP.differentiable (by simp)) _))
  exact key.2

/-- Spatial word derivatives commute with the time derivative. -/
theorem sd_pd_time : ∀ (L : List (Fin d)) {f : ST d → ℝ}, ContDiff ℝ ∞ f →
    sd L (pd f 0) = pd (sd L f) 0
  | [], _, _ => rfl
  | j :: L, f, hf => by
    rw [sd_cons, sd_cons]
    have hc : pd (pd f 0) j.succ = pd (pd f j.succ) 0 :=
      funext fun x => pd_pd_comm (hf.of_le (by norm_cast)) 0 j.succ x
    rw [hc]
    exact sd_pd_time L (contDiff_pd_top hf j.succ)

/-- **`d/dt ‖W(t)‖²_{H^k} = 2⟨W, ∂_tW⟩_{H^k}`** for smooth fields. -/
theorem hasDerivAt_energyQ (k : ℕ) {w : Fin n → ST d → ℝ} (hw : ∀ b, ContDiff ℝ ∞ (w b))
    (t : ℝ) : HasDerivAt (energyQ k w) (2 * pairQ k w (fun a => pd (w a) 0) t) t := by
  have hterm : ∀ a, ∀ L ∈ wordsLE d k, HasDerivAt
      (fun s => ∫ y in Icc (0 : Fin d → ℝ) 1, sd L (w a) (Fin.cons s y) ^ 2)
      (2 * ∫ y in Icc (0 : Fin d → ℝ) 1, sd L (w a) (Fin.cons t y) *
        sd L (pd (w a) 0) (Fin.cons t y)) t := by
    intro a L _
    have hs := contDiff_sd L (hw a)
    have h := hasDerivAt_sliceInt_d (P := fun x => sd L (w a) x ^ 2) (hs.pow 2) t
    have hpd : ∀ x, pd (fun x => sd L (w a) x ^ 2) 0 x =
        2 * (sd L (w a) x * sd L (pd (w a) 0) x) := by
      intro x
      rw [sd_pd_time L (hw a)]
      have := SobolevOpen.pd_mul (hs.of_le (by norm_cast)) (hs.of_le (by norm_cast)) 0 x
      simp only [sq] at this ⊢
      rw [this]; ring
    simp only [hpd] at h
    rwa [integral_const_mul] at h
  have hsum : HasDerivAt (energyQ k w) (∑ a, ∑ L ∈ wordsLE d k,
      2 * ∫ y in Icc (0 : Fin d → ℝ) 1, sd L (w a) (Fin.cons t y) *
        sd L (pd (w a) 0) (Fin.cons t y)) t := by
    have : energyQ k w = fun s => ∑ a, ∑ L ∈ wordsLE d k,
        ∫ y in Icc (0 : Fin d → ℝ) 1, sd L (w a) (Fin.cons s y) ^ 2 := by
      funext s; rfl
    rw [this]
    exact HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun L hL => hterm a L hL
  convert hsum using 1
  unfold pairQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

theorem continuous_pairQ (k : ℕ) {w v : Fin n → ST d → ℝ} (hw : ∀ b, ContDiff ℝ ∞ (w b))
    (hv : ∀ b, ContDiff ℝ ∞ (v b)) : Continuous (pairQ k w v) := by
  unfold pairQ
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun L _ =>
    continuous_sliceInt (f := fun x => sd L (w a) x * sd L (v a) x)
      ((contDiff_sd L (hw a)).continuous.mul (contDiff_sd L (hv a)).continuous)

theorem continuous_energyQ (k : ℕ) {w : Fin n → ST d → ℝ} (hw : ∀ b, ContDiff ℝ ∞ (w b)) :
    Continuous (energyQ k w) := by
  unfold energyQ
  exact continuous_finsetSum _ fun a _ => continuous_Q k (hw a)

/-- `⟨w, e⟩_{H^k} ≤ ½‖w‖²_{H^k} + ½‖e‖²_{H^k}`. -/
theorem pairQ_le (k : ℕ) {w e : Fin n → ST d → ℝ} (hw : ∀ b, ContDiff ℝ ∞ (w b))
    (he : ∀ b, ContDiff ℝ ∞ (e b)) (t : ℝ) :
    pairQ k w e t ≤ 1 / 2 * energyQ k w t + 1 / 2 * energyQ k e t := by
  unfold pairQ energyQ Q
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun L _ => ?_
  have cw := (contDiff_sd L (hw a)).continuous
  have ce := (contDiff_sd L (he a)).continuous
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrableOn_sq cw t).const_mul _) ((integrableOn_sq ce t).const_mul _)]
  refine setIntegral_mono_on (integrableOn_slice (f := fun x => sd L (w a) x * sd L (e a) x)
    (cw.mul ce) t) (((integrableOn_sq cw t).const_mul _).add ((integrableOn_sq ce t).const_mul _))
    measurableSet_Icc fun y _ => ?_
  nlinarith [sq_nonneg (sd L (w a) (Fin.cons t y) - sd L (e a) (Fin.cons t y))]

/-- On a slice of the slab, the time derivative of the difference splits into the generator
difference and the defect. -/
theorem pairQ_dt_eq {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) (k : ℕ) {T : ℝ}
    {u v e : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (hv : ∀ b, ContDiff ℝ ∞ (v b))
    (he : ∀ b, ContDiff ℝ ∞ (e b))
    (hU : ∀ a, ∀ x : ST d, x 0 ∈ Icc 0 T → pd (u a) 0 x = genG A F u a x)
    (hV : ∀ a, ∀ x : ST d, x 0 ∈ Icc 0 T → pd (v a) 0 x = genG A F v a x + e a x)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    pairQ k (subF v u) (fun a => pd (subF v u a) 0) t =
      pairQ k (subF v u) (fun a x => genG A F v a x - genG A F u a x) t +
        pairQ k (subF v u) e t := by
  have hw := contDiff_subF hu hv
  have hG : ∀ a, ContDiff ℝ ∞ (fun x => genG A F v a x - genG A F u a x) := fun a =>
    (contDiff_genG hA hF hv a).sub (contDiff_genG hA hF hu a)
  have hslab : ∀ a, ∀ x : ST d, x 0 ∈ Icc 0 T →
      pd (subF v u a) 0 x = (genG A F v a x - genG A F u a x) + e a x := by
    intro a x hx
    rw [pd_sub_eq (hv a) (hu a), hV a x hx, hU a x hx]; ring
  unfold pairQ
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun L _ => ?_
  have hsd : ∀ y, sd L (pd (subF v u a) 0) (Fin.cons t y) =
      sd L (fun x => genG A F v a x - genG A F u a x) (Fin.cons t y) +
        sd L (e a) (Fin.cons t y) := by
    intro y
    have h1 := sd_congr_slab (T := T) L (contDiff_pd_top (hw a) 0) ((hG a).add (he a))
      (hslab a) (Fin.cons t y) (by rw [cons_zero_eq]; exact ht)
    rw [h1, sd_add L (hG a) (he a)]
  have cw := (contDiff_sd L (hw a)).continuous
  have cG := (contDiff_sd L (hG a)).continuous
  have ce := (contDiff_sd L (he a)).continuous
  simp_rw [hsd, mul_add]
  rw [integral_add (integrableOn_slice (f := fun x => sd L (subF v u a) x *
      sd L (fun x => genG A F v a x - genG A F u a x) x) (cw.mul cG) t)
    (integrableOn_slice (f := fun x => sd L (subF v u a) x * sd L (e a) x) (cw.mul ce) t)]

/-- `‖V‖²_{H^k} ≤ 2‖V - U‖²_{H^k} + 2‖U‖²_{H^k}`. -/
theorem energyQ_le_sub (k : ℕ) {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    (hv : ∀ b, ContDiff ℝ ∞ (v b)) (t : ℝ) :
    energyQ k v t ≤ 2 * energyQ k (subF v u) t + 2 * energyQ k u t := by
  unfold energyQ
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have e : v b = fun x => subF v u b x + u b x := by funext x; simp [subF]
  rw [e]
  exact Q_add_le k (contDiff_subF hu hv b) (hu b) t

/-- **First-exit difference stability for quasilinear symmetric hyperbolic systems**
(`prop:coupled-bootstrap`, `eq:actual-jet-gauge-energy`, `eq:actual-jet-integrated-stability`,
first-exit closure).  Fix `m > d/2`, `k ≥ 2m`, smooth real symmetric `A^i(v)`, smooth `F(v)`, a
time `T ≥ 0`, a reference bound `R₁` and a tube radius `ρ > 0` (in squared `H^k` norm).  There is
`C_* ≥ 1` such that: if the reference `U` solves `∂_tU = G(U)` on `[0, T] × 𝕋^d` with
`‖U(t)‖²_{H^{k+1}} ≤ R₁²`, the approximate field `V` satisfies `∂_tV = G(V) + e` there, and the
defect obeys `‖e(t)‖²_{H^k} ≤ Φ(t)` **at the times at which `V` is in the tube**
`‖V(t) - U(t)‖²_{H^k} ≤ ρ` (`Φ ≥ 0` continuous), then
`C_*(‖V(0) - U(0)‖²_{H^k} + ∫₀ᵀΦ) < ρ` implies
`‖V(t) - U(t)‖²_{H^k} ≤ C_*(‖V(0) - U(0)‖²_{H^k} + ∫₀ᵀΦ)` for all `t ∈ [0, T]`.
Only the existence of the smooth field `V` on the slab is used; no a priori bound for `V`. -/
theorem difference_bootstrap {m k : ℕ} (hm : (d : ℝ) / 2 < m) (hk : 2 * m ≤ k)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {T R₁ ρ : ℝ} (hT : 0 ≤ T) (hR₁ : 0 ≤ R₁) (hρ : 0 < ρ) :
    ∃ Cst : ℝ, 1 ≤ Cst ∧ ∀ u v e : Fin n → ST d → ℝ,
      (∀ b, ContDiff ℝ ∞ (u b)) → (∀ b, ContDiff ℝ ∞ (v b)) → (∀ b, ContDiff ℝ ∞ (e b)) →
      (∀ b, IsSPeriodic (u b)) → (∀ b, IsSPeriodic (v b)) →
      (∀ t ∈ Icc 0 T, energyQ (k + 1) u t ≤ R₁ ^ 2) →
      (∀ a, ∀ x : ST d, x 0 ∈ Icc 0 T → pd (u a) 0 x = genG A F u a x) →
      (∀ a, ∀ x : ST d, x 0 ∈ Icc 0 T → pd (v a) 0 x = genG A F v a x + e a x) →
      ∀ Φ : ℝ → ℝ, ContinuousOn Φ (Icc 0 T) → (∀ t ∈ Icc 0 T, 0 ≤ Φ t) →
      (∀ t ∈ Icc 0 T, energyQ k (subF v u) t ≤ ρ → energyQ k e t ≤ Φ t) →
      Cst * (energyQ k (subF v u) 0 + ∫ s in (0 : ℝ)..T, Φ s) < ρ →
      ∀ t ∈ Icc 0 T, energyQ k (subF v u) t ≤
        Cst * (energyQ k (subF v u) 0 + ∫ s in (0 : ℝ)..T, Φ s) := by
  set R := Real.sqrt (2 * ρ + 3 * R₁ ^ 2) with hRdef
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 2 * ρ + 3 * R₁ ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨K, hK0, hK⟩ := pairQ_genG_sub_le hm hk hA hsym hF hR
  set c := 2 * K + 1 with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨Real.exp (c * T), Real.one_le_exp (by positivity), ?_⟩
  intro u v e hu hv he hpu hpv hU1 hUeq hVeq Φ hΦc hΦ0 hforce hsmall
  have hw := contDiff_subF hu hv
  set E := energyQ k (subF v u) with hEdef
  set B := Real.exp (c * T) * (E 0 + ∫ s in (0 : ℝ)..T, Φ s) with hB
  have hEc : Continuous E := continuous_energyQ k hw
  have hIΦ : 0 ≤ ∫ s in (0 : ℝ)..T, Φ s :=
    intervalIntegral.integral_nonneg hT fun s hs => hΦ0 s hs
  have hE00 : 0 ≤ E 0 := energyQ_nonneg _ _ _
  have h0 : E 0 ≤ B := by
    have : E 0 ≤ E 0 + ∫ s in (0 : ℝ)..T, Φ s := by linarith
    exact this.trans (le_mul_of_one_le_left (by positivity) (Real.one_le_exp (by positivity)))
  -- the derivative bound inside the tube
  set D := fun s => 2 * pairQ k (subF v u) (fun a => pd (subF v u a) 0) s with hD
  have hDc : Continuous D := continuous_const.mul
    (continuous_pairQ k hw fun a => contDiff_pd_top (hw a) 0)
  have hderiv : ∀ s, HasDerivAt E (D s) s := fun s => hasDerivAt_energyQ k hw s
  have hDle : ∀ s ∈ Icc 0 T, E s ≤ ρ → D s ≤ c * E s + Φ s := by
    intro s hs hEs
    have hsplit := pairQ_dt_eq hA hF k hu hv he hUeq hVeq hs
    have hEu : energyQ k u s ≤ R₁ ^ 2 := by
      refine le_trans ?_ (hU1 s hs)
      exact Finset.sum_le_sum fun b _ => Q_mono (Nat.le_succ k) _ _
    have hEv := energyQ_le_sub k hu hv s
    have hball : energyQ k u s + energyQ k v s ≤ R ^ 2 := by rw [hR2]; linarith
    have hball1 : energyQ (k + 1) u s ≤ R ^ 2 := by
      rw [hR2]; nlinarith [hU1 s hs, sq_nonneg R₁]
    have h1 := hK u v hu hv hpu hpv s hball hball1
    have h2 := pairQ_le k hw he s
    have h3 := hforce s hs hEs
    simp only [hD]
    rw [hsplit]
    have hEs0 : 0 ≤ E s := energyQ_nonneg _ _ _
    nlinarith
  -- the first-exit argument
  refine ODECutoff.firstExit_le hEc.continuousOn hsmall h0 fun t ht hle => ?_
  have hii : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc 0 T) → ∀ τ ∈ Icc 0 t,
      IntervalIntegrable f volume 0 τ := fun hf τ hτ =>
    (hf.mono (Icc_subset_Icc le_rfl (hτ.2.trans ht.2))).intervalIntegrable_of_Icc hτ.1
  have hstep : ∀ τ ∈ Icc 0 t, E τ ≤ (E 0 + ∫ s in (0 : ℝ)..T, Φ s) +
      c * ∫ s in (0 : ℝ)..τ, E s := by
    intro τ hτ
    have hftc : ∫ s in (0 : ℝ)..τ, D s = E τ - E 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
        (hDc.intervalIntegrable 0 τ)
    have hmono : ∫ s in (0 : ℝ)..τ, D s ≤ ∫ s in (0 : ℝ)..τ, (c * E s + Φ s) :=
      intervalIntegral.integral_mono_on hτ.1 (hDc.intervalIntegrable 0 τ)
        (hii ((continuous_const.mul hEc).continuousOn.add hΦc) τ hτ) fun s hs =>
          hDle s ⟨hs.1, hs.2.trans (hτ.2.trans ht.2)⟩ (hle s ⟨hs.1, hs.2.trans hτ.2⟩)
    have hsplit : ∫ s in (0 : ℝ)..τ, (c * E s + Φ s) =
        c * (∫ s in (0 : ℝ)..τ, E s) + ∫ s in (0 : ℝ)..τ, Φ s := by
      rw [intervalIntegral.integral_add ((hEc.intervalIntegrable 0 τ).const_mul c)
        (hii hΦc τ hτ), intervalIntegral.integral_const_mul]
    have hΦT : ∫ s in (0 : ℝ)..τ, Φ s ≤ ∫ s in (0 : ℝ)..T, Φ s := by
      refine intervalIntegral.integral_mono_interval le_rfl hτ.1 (hτ.2.trans ht.2) ?_
        (hΦc.intervalIntegrable_of_Icc hT)
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
      exact hΦ0 s ⟨hs.1.le, hs.2⟩
    linarith
  have hg := FOSymHk.integral_gronwall ht.1 hc0 hEc.continuousOn hstep t ⟨ht.1, le_rfl⟩
  refine hg.trans ?_
  rw [hB, mul_comm (Real.exp (c * T))]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  exact mul_le_mul_of_nonneg_left ht.2 hc0

end Dynamic

/-! ### Non-vacuity -/

/-- **Non-vacuity of `difference_bootstrap`**: the constant-coefficient system `∂_tU = 0` on `𝕋³`
(`A^i = 0`, `F = 0`, `k = 4`), the reference `U = 0`, the approximate field `V = 0` with zero
defect satisfy every hypothesis. -/
example (n : ℕ) : ∃ Cst : ℝ, 1 ≤ Cst ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    energyQ 4 (subF (fun (_ : Fin n) (_ : ST 3) => (0 : ℝ)) fun _ _ => 0) t ≤
      Cst * (energyQ 4 (subF (fun (_ : Fin n) (_ : ST 3) => (0 : ℝ)) fun _ _ => 0) 0 +
        ∫ s in (0 : ℝ)..1, (0 : ℝ)) := by
  obtain ⟨Cst, h1, h⟩ := difference_bootstrap (d := 3) (n := n) (m := 2) (k := 4)
    (A := fun _ _ _ _ => 0) (F := fun _ _ => 0) (by norm_num) (by norm_num)
    (fun _ _ _ => contDiff_const) (fun _ _ _ _ => rfl) (fun _ => contDiff_const)
    (T := 1) (R₁ := 0) (ρ := 1) zero_le_one le_rfl one_pos
  have hz : ∀ (q : ℕ) (t : ℝ),
      energyQ q (subF (fun (_ : Fin n) (_ : ST 3) => (0 : ℝ)) fun _ _ => 0) t = 0 := by
    intro q t
    unfold energyQ
    refine Finset.sum_eq_zero fun b _ => ?_
    have e : subF (fun (_ : Fin n) (_ : ST 3) => (0 : ℝ)) (fun _ _ => 0) b = fun _ => (0 : ℝ) := by
      funext x; simp [subF]
    rw [e, Q_const]; simp
  refine ⟨Cst, h1, h _ _ (fun _ _ => 0) (fun _ => contDiff_const) (fun _ => contDiff_const)
    (fun _ => contDiff_const) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun t _ => ?_)
    (fun a x _ => ?_) (fun a x _ => ?_) (fun _ => 0) continuousOn_const (fun _ _ => le_rfl)
    (fun t _ _ => ?_) ?_⟩
  · have := Q_const (d := 3) 5 0 0
    unfold energyQ
    simp [Q_const]
  · simp [genG, pd_const, compF]
  · simp [genG, pd_const, compF]
  · unfold energyQ; simp [Q_const]
  · rw [hz]; simp
end RenewalGeometry.QLDiff
