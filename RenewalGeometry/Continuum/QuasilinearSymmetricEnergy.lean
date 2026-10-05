/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SlabSobolevAlgebra
import RenewalGeometry.Continuum.SlabCoefficientCalculus
import RenewalGeometry.Analysis.CompositionDifferenceBounds
import RenewalGeometry.Analysis.PeriodicCubeSobolevInterpolation

/-!
# The `H^q` energy inequality of a quasilinear symmetric hyperbolic system

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` and
`lem:generated-physical-identification` of the Einstein–Standard-Model action-closure manuscript
(`app:generated-dynamics`, `eq:generated-Galerkin`: "the symmetry of the principal matrices
implies that the `H^q` energy estimate for the Galerkin system has constants independent of `N`").

Setting: the slab calculus of `SlabSobolevAlgebra` (space-time `ℝ^{1+d}`, fields smooth and
`ℤ^d`-periodic in space, slices integrated over `[0,1]^d`, classical `H^q` slice norms
`Q q f t = Σ_{|w| ≤ q} ∫ |∂^w f(t,·)|²` along spatial words).  A first-order quasilinear system
`∂_tU + Σ_i A^i(U) ∂_iU = F(U)` for `U = (u_b)_{b < n}` with smooth real symmetric matrices
`A^i(v)` and smooth `F(v)` (`v ∈ ℝ^n`) has the spatial generator
`G(U)_a = F_a(U) - Σ_{i,b} A^i_{ab}(U) ∂_i u_b`.

## Main results

* `norm_le_sum_basis` — a multilinear map on `ℝ^d` is controlled by its values on basis vectors:
  `‖T‖ ≤ Σ_{w ∈ d^p} |T(e_{w_1}, …, e_{w_p})|`.
* `norm_iteratedFDeriv_comp_le_tame` — the **tame Faà di Bruno bound**: if the derivatives of `J`
  of orders `1 … r` are bounded by `B ≥ 1` at `z` and `N ≤ 2r + 1`, then
  `‖D^N(G ∘ J)(z)‖ ≤ #OFP(N) M B^N (1 + Σ_{r < p ≤ N} ‖D^pJ(z)‖)` (at most one factor of a
  Faà di Bruno product has order `> r`).
* `abs_sd_compF_le`, `abs_sd_compF_le_small` — the tame pointwise bounds for `∂^L Φ(U)` along
  words, the low-order derivatives being bounded by `B₀`;
* `sd_mul_comm`, `sd_pd`, `integral_sym_eq` — the commutator form of the Leibniz rule, the
  commutation of word and partial derivatives, and **symmetric integration by parts**
  `∫ Σ V_a A_{ab} ∂_iV_b = -½ ∫ Σ V_a (∂_iA_{ab}) V_b`;
* **`pairQ_genG_le`** — **the `H^q` energy inequality**: for `m > d/2`, `q ≥ 2m` and every radius
  `R`, there is `K = K(R)` such that every smooth periodic field with `‖U‖²_{H^q} ≤ R²` has
  `⟨U, G(U)⟩_{H^q} ≤ K (1 + ‖U‖²_{H^q})`, `G(U) = F(U) - Σ_i A^i(U)∂_iU` (the cutoff-independent
  energy hypothesis of `SpectralGalerkin.galerkin_exists` / `midpoint_recursion`).

Disclosed: the coefficients `A^i`, `F` are smooth on all of `ℝ^n` (a chart is handled by a
smooth cutoff extension); `T^d = ℝ^d/ℤ^d` with the unit cube; the Sobolev norm sums all ordered
words of length `≤ q`.
-/

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.QLEnergy

set_option linter.unusedSectionVars false

/-! ### Multilinear maps on `ℝ^d` and the tame Faà di Bruno bound -/

section Generic

/-- A continuous multilinear map on `ℝ^d` is bounded by the sum of its values on basis vectors. -/
theorem norm_le_sum_basis {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => ι → ℝ) F) :
    ‖T‖ ≤ ∑ w : Fin p → ι, ‖T (PeriodicSobInterp.evw w)‖ := by
  refine T.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = fun l => ∑ i, v l i • (Pi.single i 1 : ι → ℝ) := by
    funext l j
    simp [Finset.sum_apply, Pi.single_apply]
  have hexp : T v = ∑ w : Fin p → ι, (∏ l, v l (w l)) • T (PeriodicSobInterp.evw w) := by
    conv_lhs => rw [hv]
    rw [T.map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← T.map_smul_univ]
    rfl
  rw [hexp]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [norm_smul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun l _ => norm_le_pi_norm (v l) (w l)

variable {E X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two distinct parts of an ordered finpartition of `Fin N` have total size at most `N`. -/
theorem partSize_add_le {N : ℕ} (c : OrderedFinpartition N) {m₁ m₂ : Fin c.length}
    (h : m₁ ≠ m₂) : c.partSize m₁ + c.partSize m₂ ≤ N := by
  have hcard := Fintype.card_le_of_injective _ c.emb_injective
  rw [Fintype.card_sigma, Fintype.card_fin] at hcard
  simp only [Fintype.card_fin] at hcard
  have hsub : ∑ m ∈ ({m₁, m₂} : Finset (Fin c.length)), c.partSize m ≤
      ∑ m, c.partSize m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _
  rw [Finset.sum_pair h] at hsub
  omega

/-- **Tame Faà di Bruno bound**: if `‖D^kG(J z)‖ ≤ M` (`k ≤ N`), `‖D^pJ(z)‖ ≤ B` for
`1 ≤ p ≤ r` (`B ≥ 1`) and `N ≤ 2r + 1`, then
`‖D^N(G ∘ J)(z)‖ ≤ #OFP(N) · M · B^N · (1 + Σ_{r < p ≤ N} ‖D^pJ(z)‖)`. -/
theorem norm_iteratedFDeriv_comp_le_tame {G : X → F} {J : E → X} {z : E} {N r : ℕ}
    (hG : ContDiffAt ℝ N G (J z)) (hJ : ContDiffAt ℝ N J z) {M B : ℝ} (hB1 : 1 ≤ B)
    (hM : ∀ k ≤ N, ‖iteratedFDeriv ℝ k G (J z)‖ ≤ M)
    (hB : ∀ p, 1 ≤ p → p ≤ r → ‖iteratedFDeriv ℝ p J z‖ ≤ B) (hNr : N ≤ 2 * r + 1) :
    ‖iteratedFDeriv ℝ N (G ∘ J) z‖ ≤ Fintype.card (OrderedFinpartition N) * M * B ^ N *
      (1 + ∑ p ∈ Finset.Ioc r N, ‖iteratedFDeriv ℝ p J z‖) := by
  have hB0 : 0 ≤ B := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _))
  set S := ∑ p ∈ Finset.Ioc r N, ‖iteratedFDeriv ℝ p J z‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [CompDiff.iteratedFDeriv_comp_eq_sum hG hJ]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ c : OrderedFinpartition N, ‖c.compAlongOrderedFinpartition
      (iteratedFDeriv ℝ c.length G (J z)) (fun m => iteratedFDeriv ℝ (c.partSize m) J z)‖ ≤
        M * (B ^ N * (1 + S)) := by
    intro c
    refine (c.norm_compAlongOrderedFinpartition_le _ _).trans ?_
    refine mul_le_mul (hM _ c.length_le) ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM0
    -- the product: at most one factor has order `> r`
    set x : Fin c.length → ℝ := fun m => ‖iteratedFDeriv ℝ (c.partSize m) J z‖ with hx
    have hsmall : ∀ m, c.partSize m ≤ r → x m ≤ B := fun m hm =>
      hB _ (c.partSize_pos m) hm
    have hbig : ∀ m, r < c.partSize m → x m ≤ S := fun m hm =>
      Finset.single_le_sum (f := fun p => ‖iteratedFDeriv ℝ p J z‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_Ioc.2 ⟨hm, c.partSize_le m⟩)
    have hlen : B ^ c.length ≤ B ^ N := pow_le_pow_right₀ hB1 c.length_le
    by_cases hex : ∃ m₀, r < c.partSize m₀
    · obtain ⟨m₀, hm₀⟩ := hex
      have hothers : ∀ m ∈ Finset.univ.erase m₀, x m ≤ B := by
        intro m hm
        have hne : m ≠ m₀ := Finset.ne_of_mem_erase hm
        refine hsmall m ?_
        by_contra hcon
        push Not at hcon
        have := partSize_add_le c hne
        omega
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m₀)]
      have h1 : ∏ m ∈ Finset.univ.erase m₀, x m ≤ B ^ (c.length - 1) := by
        calc ∏ m ∈ Finset.univ.erase m₀, x m ≤ ∏ _m ∈ Finset.univ.erase m₀, B :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _) hothers
          _ = B ^ (c.length - 1) := by
              rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
                Finset.card_univ, Fintype.card_fin]
      have h2 : B ^ (c.length - 1) ≤ B ^ N :=
        pow_le_pow_right₀ hB1 ((Nat.sub_le _ _).trans c.length_le)
      have h3 : x m₀ ≤ S := hbig m₀ hm₀
      have hBN : 0 ≤ B ^ N := pow_nonneg hB0 _
      calc x m₀ * ∏ m ∈ Finset.univ.erase m₀, x m ≤ S * B ^ N :=
            mul_le_mul h3 (h1.trans h2) (Finset.prod_nonneg fun _ _ => norm_nonneg _) hS0
        _ ≤ B ^ N * (1 + S) := by nlinarith
    · push Not at hex
      calc ∏ m, x m ≤ ∏ _m : Fin c.length, B :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun m _ => hsmall m (hex m)
        _ = B ^ c.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ B ^ N * (1 + S) := by
            have : B ^ N ≤ B ^ N * (1 + S) := le_mul_of_one_le_right (pow_nonneg hB0 _)
              (by linarith)
            linarith
  calc ∑ c : OrderedFinpartition N, ‖c.compAlongOrderedFinpartition
        (iteratedFDeriv ℝ c.length G (J z)) (fun m => iteratedFDeriv ℝ (c.partSize m) J z)‖
      ≤ ∑ _c : OrderedFinpartition N, M * (B ^ N * (1 + S)) := Finset.sum_le_sum fun c _ => hterm c
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Generic

/-! ### Words and Fréchet derivatives on slices -/

section Slice

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

variable {d : ℕ}

/-- Iterated partials along a tuple are the iterated Fréchet derivative on basis vectors. -/
theorem iterPd_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : (ι → ℝ) → E} (hg : ContDiff ℝ ∞ g) :
    ∀ {m : ℕ} (w : Fin m → ι),
      SobolevBoxCr.iterPd g w = PeriodicSobInterp.Fm g m (PeriodicSobInterp.evw w)
  | 0, w => by
    funext y
    simp [SobolevBoxCr.iterPd, PeriodicSobInterp.Fm]
  | m + 1, w => by
    have ih := iterPd_eq hg (Fin.tail w)
    simp only [SobolevBoxCr.iterPd]
    rw [ih, PeriodicSobInterp.pd_Fm hg]
    congr 1
    conv_rhs => rw [← Fin.cons_self_tail w, PeriodicSobInterp.evw_cons]

/-- The slice `y ↦ f(t, y)`. -/
abbrev slice (f : ST d → ℝ) (t : ℝ) : (Fin d → ℝ) → ℝ := fun y => f (Fin.cons t y)

theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST d → E}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) : ContDiff ℝ ∞ (fun y : Fin d → ℝ => f (Fin.cons t y)) :=
  hf.comp (contDiff_cons t)

theorem sd_eq_Fm {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) {m : ℕ} (w : Fin m → Fin d)
    (y : Fin d → ℝ) :
    sd (List.ofFn w).reverse f (Fin.cons t y) =
      iteratedFDeriv ℝ m (slice f t) y (PeriodicSobInterp.evw w) := by
  rw [← iterPd_slice hf t w y, iterPd_eq (contDiff_slice hf t)]
  rfl

theorem norm_evw_prod {m : ℕ} (w : Fin m → Fin d) :
    ∏ l, ‖PeriodicSobInterp.evw w l‖ = 1 := by
  simp [PeriodicSobInterp.evw, Pi.norm_single]

/-- `|∂^L f(t, y)| ≤ ‖D^{|L|} f(t, ·)(y)‖`. -/
theorem abs_sd_le {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (L : List (Fin d))
    (y : Fin d → ℝ) : |sd L f (Fin.cons t y)| ≤ ‖iteratedFDeriv ℝ L.length (slice f t) y‖ := by
  have e : L = (List.ofFn L.reverse.get).reverse := by rw [List.ofFn_get, List.reverse_reverse]
  have h := sd_eq_Fm hf t L.reverse.get y
  rw [← e] at h
  rw [h, ← Real.norm_eq_abs]
  refine ((iteratedFDeriv ℝ _ (slice f t) y).le_opNorm _).trans ?_
  rw [norm_evw_prod, mul_one, List.length_reverse]

/-- `‖D^p f(t, ·)(y)‖ ≤ Σ_{w ∈ d^p} |∂^w f(t, y)|`. -/
theorem norm_iteratedFDeriv_slice_le {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (p : ℕ)
    (y : Fin d → ℝ) : ‖iteratedFDeriv ℝ p (slice f t) y‖ ≤
      ∑ w : Fin p → Fin d, |sd (List.ofFn w).reverse f (Fin.cons t y)| := by
  refine (norm_le_sum_basis _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [sd_eq_Fm hf t w y, Real.norm_eq_abs]

variable {n : ℕ}

/-- The vector slice `y ↦ (u_b(t, y))_b`. -/
abbrev vslice (u : Fin n → ST d → ℝ) (t : ℝ) : (Fin d → ℝ) → Fin n → ℝ :=
  fun y b => u b (Fin.cons t y)

theorem contDiff_vslice {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (t : ℝ) :
    ContDiff ℝ ∞ (vslice u t) :=
  contDiff_pi.2 fun b => contDiff_slice (hu b) t

/-- `‖D^p U(t,·)(y)‖ ≤ Σ_b ‖D^p u_b(t,·)(y)‖`. -/
theorem norm_iteratedFDeriv_vslice_le {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    (t : ℝ) (p : ℕ) (y : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ p (vslice u t) y‖ ≤ ∑ b, ‖iteratedFDeriv ℝ p (slice (u b) t) y‖ := by
  have hcomp : ∀ b, iteratedFDeriv ℝ p (slice (u b) t) y =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).compContinuousMultilinearMap
        (iteratedFDeriv ℝ p (vslice u t) y) := by
    intro b
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).iteratedFDeriv_comp_left
      (contDiff_vslice hu t).contDiffAt (x := y) (i := p) (PeriodicSobInterp.natCast_le_infty p)
    rw [← this]
    rfl
  refine (iteratedFDeriv ℝ p (vslice u t) y).opNorm_le_bound
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  rw [Finset.sum_mul]
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun b _ =>
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))).2 fun b => ?_
  have h1 : ‖iteratedFDeriv ℝ p (vslice u t) y v b‖ ≤
      ‖iteratedFDeriv ℝ p (slice (u b) t) y‖ * ∏ i, ‖v i‖ := by
    calc ‖iteratedFDeriv ℝ p (vslice u t) y v b‖ =
        ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).compContinuousMultilinearMap
          (iteratedFDeriv ℝ p (vslice u t) y) v‖ := rfl
      _ ≤ ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).compContinuousMultilinearMap
          (iteratedFDeriv ℝ p (vslice u t) y)‖ * ∏ i, ‖v i‖ := ContinuousMultilinearMap.le_opNorm _ v
      _ = _ := by rw [← hcomp b]
  exact h1.trans (Finset.single_le_sum (f := fun b => ‖iteratedFDeriv ℝ p (slice (u b) t) y‖ *
    ∏ i, ‖v i‖) (fun b _ => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ =>
      norm_nonneg _)) (Finset.mem_univ b))

/-- The pointwise size of the derivatives of order `≤ q`:
`σ = Σ_b Σ_{p ≤ q} Σ_{w ∈ d^p} |∂^w u_b(t, y)|`. -/
def sig (q : ℕ) (u : Fin n → ST d → ℝ) (t : ℝ) (y : Fin d → ℝ) : ℝ :=
  ∑ b, ∑ p ∈ Finset.range (q + 1), ∑ w : Fin p → Fin d,
    |sd (List.ofFn w).reverse (u b) (Fin.cons t y)|

theorem sig_nonneg (q : ℕ) (u : Fin n → ST d → ℝ) (t : ℝ) (y : Fin d → ℝ) : 0 ≤ sig q u t y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    abs_nonneg _

theorem norm_iteratedFDeriv_vslice_le_sig {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    (t : ℝ) {p q : ℕ} (hpq : p ≤ q) (y : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ p (vslice u t) y‖ ≤ sig q u t y := by
  refine (norm_iteratedFDeriv_vslice_le hu t p y).trans ?_
  unfold sig
  refine Finset.sum_le_sum fun b _ => ?_
  refine (norm_iteratedFDeriv_slice_le (hu b) t p y).trans ?_
  exact Finset.single_le_sum (f := fun p => ∑ w : Fin p → Fin d,
    |sd (List.ofFn w).reverse (u b) (Fin.cons t y)|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hpq))

theorem sum_Ioc_le_sig {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (t : ℝ)
    {r N q : ℕ} (hNq : N ≤ q) (y : Fin d → ℝ) :
    ∑ p ∈ Finset.Ioc r N, ‖iteratedFDeriv ℝ p (vslice u t) y‖ ≤
      (q + 1 : ℝ) * sig q u t y := by
  calc ∑ p ∈ Finset.Ioc r N, ‖iteratedFDeriv ℝ p (vslice u t) y‖
      ≤ ∑ _p ∈ Finset.Ioc r N, sig q u t y := Finset.sum_le_sum fun p hp =>
        norm_iteratedFDeriv_vslice_le_sig hu t
          ((Finset.mem_Ioc.1 hp).2.trans hNq) y
    _ = (Finset.Ioc r N).card * sig q u t y := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q + 1 : ℝ) * sig q u t y := by
        refine mul_le_mul_of_nonneg_right ?_ (sig_nonneg q u t y)
        have : (Finset.Ioc r N).card ≤ q + 1 := by
          rw [Nat.card_Ioc]; omega
        exact_mod_cast this

end Slice

/-! ### Compositions, commutators and the symmetric integration by parts -/

section Calculus

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

variable {d n : ℕ}

/-- The composition `x ↦ Φ(U(x))` of a function of the field values with the field. -/
abbrev compF (Φ : (Fin n → ℝ) → ℝ) (u : Fin n → ST d → ℝ) : ST d → ℝ :=
  fun x => Φ (fun b => u b x)

theorem contDiff_compF {Φ : (Fin n → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {u : Fin n → ST d → ℝ}
    (hu : ∀ b, ContDiff ℝ ∞ (u b)) : ContDiff ℝ ∞ (compF Φ u) :=
  hΦ.comp (contDiff_pi.2 hu)

theorem isSPeriodic_compF (Φ : (Fin n → ℝ) → ℝ) {u : Fin n → ST d → ℝ}
    (hu : ∀ b, IsSPeriodic (u b)) : IsSPeriodic (compF Φ u) := fun k x => by
  simp only [compF, hu _ k x]

/-- The Faà di Bruno constant `Σ_{p ≤ q} #OFP(p)`. -/
def cq (q : ℕ) : ℝ := ∑ p ∈ Finset.range (q + 1), (Fintype.card (OrderedFinpartition p) : ℝ)

theorem card_OFP_le_cq {p q : ℕ} (hpq : p ≤ q) :
    (Fintype.card (OrderedFinpartition p) : ℝ) ≤ cq q :=
  Finset.single_le_sum (f := fun p => (Fintype.card (OrderedFinpartition p) : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hpq))

theorem cq_nonneg (q : ℕ) : 0 ≤ cq q := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- The derivative bound of the field slice used in the Faà di Bruno estimate. -/
def Bc (d n r : ℕ) (B0 : ℝ) : ℝ := 1 + n * ((d : ℝ) + 1) ^ r * B0

theorem one_le_Bc (d n r : ℕ) {B0 : ℝ} (hB0 : 0 ≤ B0) : 1 ≤ Bc d n r B0 := by
  unfold Bc; have : 0 ≤ (n : ℝ) * ((d : ℝ) + 1) ^ r * B0 := by positivity
  linarith

theorem norm_iteratedFDeriv_vslice_le_Bc {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    {t : ℝ} {y : Fin d → ℝ} {r : ℕ} {B0 : ℝ} (hB0 : 0 ≤ B0)
    (hB : ∀ b (L : List (Fin d)), L.length ≤ r → |sd L (u b) (Fin.cons t y)| ≤ B0)
    {p : ℕ} (hpr : p ≤ r) : ‖iteratedFDeriv ℝ p (vslice u t) y‖ ≤ Bc d n r B0 := by
  refine (norm_iteratedFDeriv_vslice_le hu t p y).trans ?_
  have h1 : ∀ b, ‖iteratedFDeriv ℝ p (slice (u b) t) y‖ ≤ ((d : ℝ) + 1) ^ r * B0 := by
    intro b
    refine (norm_iteratedFDeriv_slice_le (hu b) t p y).trans ?_
    calc ∑ w : Fin p → Fin d, |sd (List.ofFn w).reverse (u b) (Fin.cons t y)|
        ≤ ∑ _w : Fin p → Fin d, B0 := Finset.sum_le_sum fun w _ =>
          hB b _ (by simp; exact hpr)
      _ = (d : ℝ) ^ p * B0 := by simp
      _ ≤ ((d : ℝ) + 1) ^ r * B0 := by
          gcongr
          calc (d : ℝ) ^ p ≤ ((d : ℝ) + 1) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) _
            _ ≤ ((d : ℝ) + 1) ^ r := pow_le_pow_right₀ (by linarith) hpr
  calc ∑ b, ‖iteratedFDeriv ℝ p (slice (u b) t) y‖ ≤ ∑ _b : Fin n, ((d : ℝ) + 1) ^ r * B0 :=
        Finset.sum_le_sum fun b _ => h1 b
    _ = n * ((d : ℝ) + 1) ^ r * B0 := by simp; ring
    _ ≤ Bc d n r B0 := by unfold Bc; linarith

/-- **Tame pointwise bound for a composition along a word**: if the field derivatives of order
`≤ r` are bounded by `B₀` at `(t, y)` and `‖D^kΦ(U(t,y))‖ ≤ M` (`k ≤ q`), then for every word with
`|L| ≤ q`, `|L| ≤ 2r + 1`:
`|∂^L Φ(U)(t, y)| ≤ c_q M B^q (1 + (q + 1) σ(t, y))`. -/
theorem abs_sd_compF_le {Φ : (Fin n → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {u : Fin n → ST d → ℝ}
    (hu : ∀ b, ContDiff ℝ ∞ (u b)) {t : ℝ} {y : Fin d → ℝ} {r q : ℕ} {B0 M : ℝ}
    (hB0 : 0 ≤ B0)
    (hB : ∀ b (L : List (Fin d)), L.length ≤ r → |sd L (u b) (Fin.cons t y)| ≤ B0)
    (hM : ∀ k ≤ q, ‖iteratedFDeriv ℝ k Φ (vslice u t y)‖ ≤ M) (L : List (Fin d))
    (hLq : L.length ≤ q) (hLr : L.length ≤ 2 * r + 1) :
    |sd L (compF Φ u) (Fin.cons t y)| ≤
      cq q * M * Bc d n r B0 ^ q * (1 + (q + 1) * sig q u t y) := by
  have hBc := one_le_Bc d n r hB0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _))
  have hσ := sig_nonneg q u t y
  refine (abs_sd_le (contDiff_compF hΦ hu) t L y).trans ?_
  have hslice : slice (compF Φ u) t = Φ ∘ vslice u t := rfl
  rw [hslice]
  have htame := norm_iteratedFDeriv_comp_le_tame (G := Φ) (J := vslice u t) (z := y)
    (N := L.length) (r := r) (hΦ.contDiffAt.of_le (PeriodicSobInterp.natCast_le_infty _))
    ((contDiff_vslice hu t).contDiffAt.of_le (PeriodicSobInterp.natCast_le_infty _)) hBc
    (fun k hk => hM k (hk.trans hLq))
    (fun p _ hp => norm_iteratedFDeriv_vslice_le_Bc hu hB0 hB hp) hLr
  refine htame.trans ?_
  have h1 := card_OFP_le_cq hLq
  have h2 : Bc d n r B0 ^ L.length ≤ Bc d n r B0 ^ q := pow_le_pow_right₀ hBc hLq
  have h3 := sum_Ioc_le_sig hu t (r := r) hLq y
  have h4 : 0 ≤ ∑ p ∈ Finset.Ioc r L.length, ‖iteratedFDeriv ℝ p (vslice u t) y‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB0' : 0 ≤ Bc d n r B0 ^ L.length := pow_nonneg (by linarith) _
  calc (Fintype.card (OrderedFinpartition L.length) : ℝ) * M * Bc d n r B0 ^ L.length *
        (1 + ∑ p ∈ Finset.Ioc r L.length, ‖iteratedFDeriv ℝ p (vslice u t) y‖)
      ≤ cq q * M * Bc d n r B0 ^ q * (1 + (q + 1) * sig q u t y) := by
        have hcqM : 0 ≤ cq q * M := mul_nonneg (cq_nonneg q) hM0
        gcongr

/-- The small-order version: for `|L| ≤ r`, `|∂^L Φ(U)(t, y)| ≤ c_q M B^q`. -/
theorem abs_sd_compF_le_small {Φ : (Fin n → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) {t : ℝ} {y : Fin d → ℝ} {r q : ℕ}
    {B0 M : ℝ} (hB0 : 0 ≤ B0)
    (hB : ∀ b (L : List (Fin d)), L.length ≤ r → |sd L (u b) (Fin.cons t y)| ≤ B0)
    (hM : ∀ k ≤ q, ‖iteratedFDeriv ℝ k Φ (vslice u t y)‖ ≤ M) (L : List (Fin d))
    (hLq : L.length ≤ q) (hLr : L.length ≤ r) :
    |sd L (compF Φ u) (Fin.cons t y)| ≤ cq q * M * Bc d n r B0 ^ q := by
  have hBc := one_le_Bc d n r hB0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _))
  refine (abs_sd_le (contDiff_compF hΦ hu) t L y).trans ?_
  have hslice : slice (compF Φ u) t = Φ ∘ vslice u t := rfl
  rw [hslice]
  have hloc := CompDiff.norm_iteratedFDeriv_comp_le_local (G := Φ) (J := vslice u t) (z := y)
    (N := L.length) (hΦ.contDiffAt.of_le (PeriodicSobInterp.natCast_le_infty _))
    ((contDiff_vslice hu t).contDiffAt.of_le (PeriodicSobInterp.natCast_le_infty _)) hBc
    (fun k hk => hM k (hk.trans hLq))
    (fun p _ hp => norm_iteratedFDeriv_vslice_le_Bc hu hB0 hB (hp.trans hLr))
  refine hloc.trans ?_
  have h1 := card_OFP_le_cq hLq
  have h2 : Bc d n r B0 ^ L.length ≤ Bc d n r B0 ^ q := pow_le_pow_right₀ hBc hLq
  gcongr
  exact mul_nonneg (cq_nonneg q) hM0

/-! #### The splittings with a nonempty left part -/

/-- The splittings `(a, b)` of a word whose left part `a` is nonempty. -/
def splitsNE {α : Type*} [DecidableEq α] (L : List α) : List (List α × List α) :=
  (splits L).filter fun p => p.1 ≠ []

theorem sum_splits_eq {α : Type*} [DecidableEq α] (F : List α × List α → ℝ) :
    ∀ L : List α, ((splits L).map F).sum = F ([], L) + ((splitsNE L).map F).sum
  | [] => by simp [splits, splitsNE]
  | μ :: L => by
    have ih := sum_splits_eq (fun p => F (p.1, μ :: p.2)) L
    simp only [splits, splitsNE, List.filter_append, List.map_append, List.sum_append] at ih ⊢
    have hA : (List.map (fun p => (μ :: p.1, p.2)) (splits L)).filter
        (fun p : List α × List α => decide (p.1 ≠ [])) =
        List.map (fun p => (μ :: p.1, p.2)) (splits L) := by
      rw [List.filter_eq_self]
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨q, _, rfl⟩ := hp
      simp
    have hB : (List.map (fun p => (p.1, μ :: p.2)) (splits L)).filter
        (fun p : List α × List α => decide (p.1 ≠ [])) =
        List.map (fun p => (p.1, μ :: p.2))
          ((splits L).filter fun p : List α × List α => decide (p.1 ≠ [])) := by
      rw [List.filter_map]
      rfl
    rw [hA, hB]
    simp only [List.map_map]
    have ih' : (List.map (F ∘ fun p => (p.1, μ :: p.2)) (splits L)).sum = F ([], μ :: L) +
        (List.map (F ∘ fun p => (p.1, μ :: p.2))
          ((splits L).filter fun p => decide (p.1 ≠ []))).sum := ih
    rw [ih']
    ring

theorem mem_splitsNE {α : Type*} [DecidableEq α] {L : List α} {p : List α × List α}
    (hp : p ∈ splitsNE L) : p ∈ splits L ∧ p.1 ≠ [] := by
  unfold splitsNE at hp
  rw [List.mem_filter] at hp
  exact ⟨hp.1, by simpa using hp.2⟩

theorem length_splitsNE_le {α : Type*} [DecidableEq α] (L : List α) :
    (splitsNE L).length ≤ 2 ^ L.length := by
  unfold splitsNE
  exact (List.length_filter_le _ _).trans (le_of_eq (length_splits L))

/-- **The commutator form of the Leibniz rule**:
`∂^L(φ v) = φ ∂^L v + Σ_{(a,b) ∈ splitsNE L} ∂^aφ ∂^b v`. -/
theorem sd_mul_comm (L : List (Fin d)) {φ v : ST d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hv : ContDiff ℝ ∞ v) (x : ST d) :
    sd L (fun x => φ x * v x) x =
      φ x * sd L v x + ((splitsNE L).map fun p => sd p.1 φ x * sd p.2 v x).sum := by
  rw [sd_mul L hφ hv x, sum_splits_eq (fun p => sd p.1 φ x * sd p.2 v x) L]
  rfl

/-- Spatial word derivatives commute with spatial partial derivatives. -/
theorem sd_pd : ∀ (L : List (Fin d)) {f : ST d → ℝ}, ContDiff ℝ ∞ f → ∀ i : Fin d,
    sd L (pd f i.succ) = pd (sd L f) i.succ
  | [], _, _, _ => rfl
  | j :: L, f, hf, i => by
    rw [sd_cons, sd_cons]
    have hc : pd (pd f i.succ) j.succ = pd (pd f j.succ) i.succ :=
      funext fun x => pd_pd_comm (hf.of_le (by norm_cast)) i.succ j.succ x
    rw [hc]
    exact sd_pd L (contDiff_pd_top hf j.succ) i

/-! #### Symmetric integration by parts on a slice -/

/-- **Symmetric integration by parts**: for smooth periodic `V_a` and a symmetric smooth periodic
matrix field `A_{ab}`, `∫ Σ_{a,b} V_a A_{ab} ∂_iV_b = -½ ∫ Σ_{a,b} V_a (∂_iA_{ab}) V_b` on every
slice. -/
theorem integral_sym_eq {V : Fin n → ST d → ℝ} (hV : ∀ a, ContDiff ℝ ∞ (V a))
    (hVp : ∀ a, IsSPeriodic (V a)) {A : Fin n → Fin n → ST d → ℝ}
    (hA : ∀ a b, ContDiff ℝ ∞ (A a b)) (hAp : ∀ a b, IsSPeriodic (A a b))
    (hsym : ∀ a b x, A a b x = A b a x) (t : ℝ) (i : Fin d) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b, V a (Fin.cons t y) * A a b (Fin.cons t y) *
        pd (V b) i.succ (Fin.cons t y) =
      -(1 / 2) * ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b, V a (Fin.cons t y) *
        pd (A a b) i.succ (Fin.cons t y) * V b (Fin.cons t y) := by
  set h : ST d → ℝ := fun x => ∑ a, ∑ b, V a x * A a b x * V b x with hh
  have hterm : ∀ a b, ContDiff ℝ ∞ (fun x => V a x * A a b x * V b x) := fun a b =>
    ((hV a).mul (hA a b)).mul (hV b)
  have hhs : ContDiff ℝ ∞ h := ContDiff.sum fun a _ => ContDiff.sum fun b _ => hterm a b
  have hhp : IsSPeriodic h := fun k x => by simp only [hh, hVp _ k x, hAp _ _ k x]
  have hpd : ∀ x, pd h i.succ x = 2 * ∑ a, ∑ b, V a x * A a b x * pd (V b) i.succ x +
      ∑ a, ∑ b, V a x * pd (A a b) i.succ x * V b x := by
    intro x
    have e1 : pd h i.succ x = ∑ a, ∑ b, pd (fun x => V a x * A a b x * V b x) i.succ x := by
      have := sd_sum [i] Finset.univ (f := fun a x => ∑ b, V a x * A a b x * V b x)
        (fun a => ContDiff.sum fun b _ => hterm a b)
      have e := congrFun this x
      simp only [sd_cons, sd_nil] at e
      rw [show h = fun x => ∑ a, ∑ b, V a x * A a b x * V b x from rfl, e]
      refine Finset.sum_congr rfl fun a _ => ?_
      have := sd_sum [i] Finset.univ (f := fun b x => V a x * A a b x * V b x)
        (fun b => hterm a b)
      have e' := congrFun this x
      simp only [sd_cons, sd_nil] at e'
      exact e'
    have e2 : ∀ a b, pd (fun x => V a x * A a b x * V b x) i.succ x =
        pd (V a) i.succ x * A a b x * V b x + V a x * pd (A a b) i.succ x * V b x +
          V a x * A a b x * pd (V b) i.succ x := by
      intro a b
      rw [SobolevOpen.pd_mul (((hV a).mul (hA a b)).of_le (by exact_mod_cast le_top))
        ((hV b).of_le (by exact_mod_cast le_top)),
        SobolevOpen.pd_mul ((hV a).of_le (by exact_mod_cast le_top))
          ((hA a b).of_le (by exact_mod_cast le_top))]
      ring
    rw [e1]
    simp only [e2, Finset.sum_add_distrib]
    have hswap : ∑ a, ∑ b, pd (V a) i.succ x * A a b x * V b x =
        ∑ a, ∑ b, V a x * A a b x * pd (V b) i.succ x := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hsym b a x]; ring
    rw [hswap]; ring
  have h0 := integral_slice_pd_eq_zero (hhs.of_le (by exact_mod_cast le_top)) hhp t i
  simp_rw [hpd] at h0
  have hc1 : Continuous fun x => ∑ a, ∑ b, V a x * A a b x * pd (V b) i.succ x :=
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((hV a).continuous.mul (hA a b).continuous).mul (contDiff_pd_top (hV b) _).continuous
  have hc2 : Continuous fun x => ∑ a, ∑ b, V a x * pd (A a b) i.succ x * V b x :=
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((hV a).continuous.mul (contDiff_pd_top (hA a b) _).continuous).mul (hV b).continuous
  rw [integral_add ((integrableOn_slice hc1 t).const_mul 2) (integrableOn_slice hc2 t),
    integral_const_mul] at h0
  linarith

end Calculus

/-! ### The `H^q` energy inequality -/

section Energy

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

variable {d n : ℕ}

/-- A uniform bound for the derivatives of order `≤ q` of finitely many smooth functions on the
ball `‖v‖ ≤ B₀`. -/
theorem exists_bound_family {κ : Type*} [Fintype κ] {Φ : κ → (Fin n → ℝ) → ℝ}
    (hΦ : ∀ k, ContDiff ℝ ∞ (Φ k)) (B0 : ℝ) (q : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k (v : Fin n → ℝ), ‖v‖ ≤ B0 → ∀ j ≤ q,
      ‖iteratedFDeriv ℝ j (Φ k) v‖ ≤ M := by
  have hb : ∀ k (j : ℕ), ∃ C : ℝ, ∀ v ∈ Metric.closedBall (0 : Fin n → ℝ) B0,
      ‖iteratedFDeriv ℝ j (Φ k) v‖ ≤ C := fun k j =>
    (isCompact_closedBall _ _).exists_bound_of_continuousOn
      ((hΦ k).continuous_iteratedFDeriv (PeriodicSobInterp.natCast_le_infty j)).continuousOn
  choose C hC using hb
  refine ⟨∑ k, ∑ j ∈ Finset.range (q + 1), max 0 (C k j), by positivity, fun k v hv j hj => ?_⟩
  have hv' : v ∈ Metric.closedBall (0 : Fin n → ℝ) B0 := by simpa using hv
  calc ‖iteratedFDeriv ℝ j (Φ k) v‖ ≤ max 0 (C k j) := (hC k j v hv').trans (le_max_right _ _)
    _ ≤ ∑ j ∈ Finset.range (q + 1), max 0 (C k j) :=
        Finset.single_le_sum (f := fun j => max 0 (C k j)) (fun _ _ => le_max_left _ _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    _ ≤ ∑ k, ∑ j ∈ Finset.range (q + 1), max 0 (C k j) :=
        Finset.single_le_sum (f := fun k => ∑ j ∈ Finset.range (q + 1), max 0 (C k j))
          (fun _ _ => by positivity) (Finset.mem_univ k)

/-- Every word of length `≤ q` is one of the terms of `σ`. -/
theorem abs_sd_le_sig (u : Fin n → ST d → ℝ) (t : ℝ) (y : Fin d → ℝ) (b : Fin n)
    {q : ℕ} {L : List (Fin d)} (hL : L.length ≤ q) :
    |sd L (u b) (Fin.cons t y)| ≤ sig q u t y := by
  have e : L = (List.ofFn L.reverse.get).reverse := by rw [List.ofFn_get, List.reverse_reverse]
  have hlen : L.reverse.length ≤ q := by rw [List.length_reverse]; exact hL
  unfold sig
  calc |sd L (u b) (Fin.cons t y)|
      = |sd (List.ofFn L.reverse.get).reverse (u b) (Fin.cons t y)| := by rw [← e]
    _ ≤ ∑ w : Fin L.reverse.length → Fin d, |sd (List.ofFn w).reverse (u b) (Fin.cons t y)| :=
        Finset.single_le_sum (f := fun w : Fin L.reverse.length → Fin d =>
          |sd (List.ofFn w).reverse (u b) (Fin.cons t y)|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ _)
    _ ≤ ∑ p ∈ Finset.range (q + 1), ∑ w : Fin p → Fin d,
          |sd (List.ofFn w).reverse (u b) (Fin.cons t y)| :=
        Finset.single_le_sum (f := fun p => ∑ w : Fin p → Fin d,
          |sd (List.ofFn w).reverse (u b) (Fin.cons t y)|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hlen))
    _ ≤ ∑ b, ∑ p ∈ Finset.range (q + 1), ∑ w : Fin p → Fin d,
          |sd (List.ofFn w).reverse (u b) (Fin.cons t y)| :=
        Finset.single_le_sum (f := fun b => ∑ p ∈ Finset.range (q + 1), ∑ w : Fin p → Fin d,
          |sd (List.ofFn w).reverse (u b) (Fin.cons t y)|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ b)

/-- The number of terms of `σ`. -/
def Nsig (d n q : ℕ) : ℝ := n * ∑ p ∈ Finset.range (q + 1), (d : ℝ) ^ p

theorem Nsig_nonneg (d n q : ℕ) : 0 ≤ Nsig d n q := by unfold Nsig; positivity

theorem continuous_sig {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (q : ℕ) (t : ℝ) :
    Continuous (sig q u t) := by
  unfold sig
  refine continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun p _ =>
    continuous_finsetSum _ fun w _ => ?_
  exact ((contDiff_sd _ (hu b)).continuous.comp (continuous_cons t)).abs

/-- `∫ σ² ≤ N_σ² Σ_b Q_q(u_b)`. -/
theorem integral_sig_sq_le {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (q : ℕ)
    (t : ℝ) : ∫ y in Icc (0 : Fin d → ℝ) 1, sig q u t y ^ 2 ≤
      Nsig d n q * ∑ b, ∑ p ∈ Finset.range (q + 1), ∑ w : Fin p → Fin d,
        ∫ y in Icc (0 : Fin d → ℝ) 1, sd (List.ofFn w).reverse (u b) (Fin.cons t y) ^ 2 := by
  -- pointwise Cauchy–Schwarz over the finite index set
  set ι := Σ (_ : Fin n), Σ (p : Finset.range (q + 1)), (Fin p.1 → Fin d)
  set g : ι → (Fin d → ℝ) → ℝ := fun i y => |sd (List.ofFn i.2.2).reverse (u i.1) (Fin.cons t y)|
  have hsig : ∀ y, sig q u t y = ∑ i : ι, g i y := by
    intro y
    unfold sig
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Fintype.sum_sigma]
    rw [← Finset.sum_coe_sort (Finset.range (q + 1))]
  have hcard : (Fintype.card ι : ℝ) = Nsig d n q := by
    simp only [ι, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin, Nsig]
    push_cast
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    rw [← Finset.sum_coe_sort (Finset.range (q + 1))]
  have hgc : ∀ i, Continuous (g i) := fun i =>
    ((contDiff_sd _ (hu i.1)).continuous.comp (continuous_cons t)).abs
  have hpt : ∀ y, sig q u t y ^ 2 ≤ Nsig d n q * ∑ i : ι, g i y ^ 2 := by
    intro y
    rw [hsig y, ← hcard]
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => g i y)
    rwa [Finset.card_univ] at this
  calc ∫ y in Icc (0 : Fin d → ℝ) 1, sig q u t y ^ 2
      ≤ ∫ y in Icc (0 : Fin d → ℝ) 1, Nsig d n q * ∑ i : ι, g i y ^ 2 :=
        setIntegral_mono_on ((continuous_sig hu q t).pow 2).integrableOn_Icc
          ((continuous_const.mul (continuous_finsetSum _ fun i _ => (hgc i).pow 2)).integrableOn_Icc)
          measurableSet_Icc fun y _ => hpt y
    _ = Nsig d n q * ∑ i : ι, ∫ y in Icc (0 : Fin d → ℝ) 1, g i y ^ 2 := by
        rw [integral_const_mul, integral_finset_sum]
        intro i _
        exact (show Continuous fun y => g i y ^ 2 from (hgc i).pow 2).integrableOn_Icc
    _ = _ := by
        congr 1
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Fintype.sum_sigma, ← Finset.sum_coe_sort (Finset.range (q + 1))]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun w _ => ?_
        simp only [g, sq_abs]

end Energy

/-! ### The generator and the static `H^q` energy inequality -/

section Generator

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

variable {d n : ℕ}

/-- The spatial generator `G(U)_a = F_a(U) - Σ_{i,b} A^i_{ab}(U) ∂_i u_b` of the quasilinear
system `∂_tU + Σ_i A^i(U)∂_iU = F(U)`. -/
def genG (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    (u : Fin n → ST d → ℝ) (a : Fin n) : ST d → ℝ :=
  fun x => compF (F a) u x - ∑ i, ∑ b, compF (A i a b) u x * pd (u b) i.succ x

/-- The squared `H^q` energy `Σ_a Q_q(u_a)(t)`. -/
def energyQ (q : ℕ) (u : Fin n → ST d → ℝ) (t : ℝ) : ℝ := ∑ a, Q q (u a) t

/-- The `H^q` pairing `⟨u, v⟩_{H^q}(t) = Σ_a Σ_{|L| ≤ q} ∫ ∂^L u_a ∂^L v_a`. -/
def pairQ (q : ℕ) (u v : Fin n → ST d → ℝ) (t : ℝ) : ℝ :=
  ∑ a, ∑ L ∈ wordsLE d q, ∫ y in Icc (0 : Fin d → ℝ) 1,
    sd L (u a) (Fin.cons t y) * sd L (v a) (Fin.cons t y)

theorem energyQ_nonneg (q : ℕ) (u : Fin n → ST d → ℝ) (t : ℝ) : 0 ≤ energyQ q u t :=
  Finset.sum_nonneg fun a _ => Q_nonneg q (u a) t

theorem contDiff_genG {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    (a : Fin n) : ContDiff ℝ ∞ (genG A F u a) :=
  (contDiff_compF (hF a) hu).sub (ContDiff.sum fun i _ => ContDiff.sum fun b _ =>
    (contDiff_compF (hA i a b) hu).mul (contDiff_pd_top (hu b) _))

/-- The word derivative of the generator in commutator form. -/
theorem sd_genG {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (a : Fin n) (L : List (Fin d))
    (x : ST d) :
    sd L (genG A F u a) x = sd L (compF (F a) u) x - ∑ i, ∑ b,
      (compF (A i a b) u x * pd (sd L (u b)) i.succ x +
        ((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
          sd p.2 (pd (u b) i.succ) x).sum) := by
  have hprod : ∀ i b, ContDiff ℝ ∞ (fun x => compF (A i a b) u x * pd (u b) i.succ x) :=
    fun i b => (contDiff_compF (hA i a b) hu).mul (contDiff_pd_top (hu b) _)
  unfold genG
  rw [sd_sub L (contDiff_compF (hF a) hu) (ContDiff.sum fun i _ => ContDiff.sum fun b _ =>
    hprod i b)]
  simp only
  congr 1
  rw [sd_sum L Finset.univ (fun i => ContDiff.sum fun b _ => hprod i b)]
  simp only
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sd_sum L Finset.univ (fun b => hprod i b)]
  simp only
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sd_mul_comm L (contDiff_compF (hA i a b) hu) (contDiff_pd_top (hu b) _) x,
    sd_pd L (hu b) i]

end Generator

/-! ### Pointwise and integrated energy bounds -/

section Bounds

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

variable {d n : ℕ}

/-- The constant of the pointwise commutator bound. -/
def Ecst (d n q : ℕ) (B0 P : ℝ) : ℝ := P + d * n * (2 ^ q * ((B0 + 1) * P))

/-- **Pointwise commutator bound**: under the low-order bounds `|∂^{L'}u_b| ≤ B₀` (`|L'| ≤ r`),
`q ≤ 2r`, and the coefficient bounds `‖D^kΦ(U)‖ ≤ M`, with `P = c_q M B^q` and
`S = 1 + (q + 1) σ`: for every word `|L| ≤ q`,
`Σ_a ∂^Lu_a ∂^L G_a + Σ_{i,a,b} ∂^Lu_a A^i_{ab}(U) ∂_i∂^Lu_b ≤ ½ Σ_a (∂^Lu_a)² + ½ n E² S²`. -/
theorem pointwise_key {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    {t : ℝ} {y : Fin d → ℝ} {r q : ℕ} {B0 M : ℝ} (hB0 : 0 ≤ B0) (hM0 : 0 ≤ M)
    (hB : ∀ b (L : List (Fin d)), L.length ≤ r → |sd L (u b) (Fin.cons t y)| ≤ B0)
    (hMF : ∀ a, ∀ k ≤ q, ‖iteratedFDeriv ℝ k (F a) (vslice u t y)‖ ≤ M)
    (hMA : ∀ i a b, ∀ k ≤ q, ‖iteratedFDeriv ℝ k (A i a b) (vslice u t y)‖ ≤ M)
    (hqr : q ≤ 2 * r) (L : List (Fin d)) (hL : L.length ≤ q) :
    ∑ a, sd L (u a) (Fin.cons t y) * sd L (genG A F u a) (Fin.cons t y) +
        ∑ i, ∑ a, ∑ b, sd L (u a) (Fin.cons t y) * compF (A i a b) u (Fin.cons t y) *
          pd (sd L (u b)) i.succ (Fin.cons t y) ≤
      (1 / 2) * ∑ a, sd L (u a) (Fin.cons t y) ^ 2 +
        (1 / 2) * n * (Ecst d n q B0 (cq q * M * Bc d n r B0 ^ q) *
          (1 + (q + 1) * sig q u t y)) ^ 2 := by
  set x : ST d := Fin.cons t y with hx
  set P := cq q * M * Bc d n r B0 ^ q with hP
  set S := 1 + (q + 1 : ℝ) * sig q u t y with hS
  have hσ := sig_nonneg q u t y
  have hS1 : 1 ≤ S := by have : 0 ≤ (q + 1 : ℝ) * sig q u t y := by positivity
                         linarith
  have hσS : sig q u t y ≤ S := by
    have : sig q u t y ≤ (q + 1 : ℝ) * sig q u t y := le_mul_of_one_le_left hσ (by linarith)
    linarith
  have hBc := one_le_Bc d n r hB0
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg (cq_nonneg q) hM0) (pow_nonneg (by linarith) _)
  -- the commutator terms
  have hcomm : ∀ i a b, |((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
      sd p.2 (pd (u b) i.succ) x).sum| ≤ 2 ^ q * ((B0 + 1) * P * S) := by
    intro i a b
    refine (list_abs_sum_le _ _).trans ?_
    have hterm : ∀ p ∈ splitsNE L, |sd p.1 (compF (A i a b) u) x * sd p.2 (pd (u b) i.succ) x|
        ≤ (B0 + 1) * P * S := by
      intro p hp
      obtain ⟨hps, hp1⟩ := mem_splitsNE hp
      have hlen := length_of_mem_splits hps
      have hp1pos : 1 ≤ p.1.length := List.length_pos_iff.2 hp1
      have hsd2 : sd p.2 (pd (u b) i.succ) x = sd (i :: p.2) (u b) x := rfl
      rw [abs_mul, hsd2]
      by_cases hsmall : (i :: p.2).length ≤ r
      · have h1 := abs_sd_compF_le (hA i a b) hu hB0 hB (hMA i a b) p.1 (by omega) (by omega)
        have h2 := hB b (i :: p.2) hsmall
        calc |sd p.1 (compF (A i a b) u) x| * |sd (i :: p.2) (u b) x| ≤ P * S * B0 :=
              mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          _ ≤ (B0 + 1) * P * S := by nlinarith [mul_nonneg hP0 (by linarith : (0:ℝ) ≤ S)]
      · push Not at hsmall
        simp only [List.length_cons] at hsmall
        have h1 := abs_sd_compF_le_small (hA i a b) hu hB0 hB (hMA i a b) p.1 (by omega)
          (by omega)
        have h2 : |sd (i :: p.2) (u b) x| ≤ sig q u t y :=
          abs_sd_le_sig u t y b (by simp; omega)
        calc |sd p.1 (compF (A i a b) u) x| * |sd (i :: p.2) (u b) x| ≤ P * sig q u t y :=
              mul_le_mul h1 h2 (abs_nonneg _) hP0
          _ ≤ P * S := mul_le_mul_of_nonneg_left hσS hP0
          _ ≤ (B0 + 1) * P * S := by
              have : 0 ≤ P * S := mul_nonneg hP0 (by linarith)
              nlinarith
    calc ((splitsNE L).map fun p => |sd p.1 (compF (A i a b) u) x *
          sd p.2 (pd (u b) i.succ) x|).sum
        ≤ ((splitsNE L).map fun _ => (B0 + 1) * P * S).sum :=
          List.sum_le_sum fun p hp => hterm p hp
      _ = (splitsNE L).length * ((B0 + 1) * P * S) := by
          rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ ≤ 2 ^ q * ((B0 + 1) * P * S) := by
          have h1 : ((splitsNE L).length : ℝ) ≤ 2 ^ q := by
            have := (length_splitsNE_le L).trans (Nat.pow_le_pow_right (by norm_num) hL)
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
  -- the forcing term
  have hFt : ∀ a, |sd L (compF (F a) u) x| ≤ P * S := fun a =>
    abs_sd_compF_le (hF a) hu hB0 hB (hMF a) L hL (by omega)
  -- combine
  have hrow : ∀ a, |sd L (compF (F a) u) x - ∑ i, ∑ b,
      ((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
        sd p.2 (pd (u b) i.succ) x).sum| ≤ Ecst d n q B0 P * S := by
    intro a
    refine (abs_sub _ _).trans ?_
    have h2 : |∑ i, ∑ b, ((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
        sd p.2 (pd (u b) i.succ) x).sum| ≤ d * n * (2 ^ q * ((B0 + 1) * P * S)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |∑ b, ((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
            sd p.2 (pd (u b) i.succ) x).sum|
          ≤ ∑ _i : Fin d, (n * (2 ^ q * ((B0 + 1) * P * S))) := by
            refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc ∑ b, |((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
                  sd p.2 (pd (u b) i.succ) x).sum| ≤ ∑ _b : Fin n, 2 ^ q * ((B0 + 1) * P * S) :=
                  Finset.sum_le_sum fun b _ => hcomm i a b
              _ = n * (2 ^ q * ((B0 + 1) * P * S)) := by simp
        _ = d * n * (2 ^ q * ((B0 + 1) * P * S)) := by simp; ring
    calc |sd L (compF (F a) u) x| + |∑ i, ∑ b, ((splitsNE L).map fun p =>
          sd p.1 (compF (A i a b) u) x * sd p.2 (pd (u b) i.succ) x).sum|
        ≤ P * S + d * n * (2 ^ q * ((B0 + 1) * P * S)) := add_le_add (hFt a) h2
      _ = Ecst d n q B0 P * S := by unfold Ecst; ring
  have hident : ∑ a, sd L (u a) x * sd L (genG A F u a) x +
      ∑ i, ∑ a, ∑ b, sd L (u a) x * compF (A i a b) u x * pd (sd L (u b)) i.succ x =
      ∑ a, sd L (u a) x * (sd L (compF (F a) u) x - ∑ i, ∑ b,
        ((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
          sd p.2 (pd (u b) i.succ) x).sum) := by
    simp only [sd_genG hA hF hu, Finset.sum_add_distrib, mul_sub, mul_add, Finset.mul_sum,
      Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i a => ∑ b, sd L (u a) x * compF (A i a b) u x *
      pd (sd L (u b)) i.succ x)]
    simp only [mul_assoc]
    ring
  rw [hident]
  have hE0 : 0 ≤ Ecst d n q B0 P := by unfold Ecst; positivity
  calc ∑ a, sd L (u a) x * (sd L (compF (F a) u) x - ∑ i, ∑ b,
        ((splitsNE L).map fun p => sd p.1 (compF (A i a b) u) x *
          sd p.2 (pd (u b) i.succ) x).sum)
      ≤ ∑ a, |sd L (u a) x| * (Ecst d n q B0 P * S) := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hrow a) (abs_nonneg _)
    _ ≤ ∑ a, ((1 / 2) * sd L (u a) x ^ 2 + (1 / 2) * (Ecst d n q B0 P * S) ^ 2) := by
        refine Finset.sum_le_sum fun a _ => ?_
        have := two_mul_le_add_sq |sd L (u a) x| (Ecst d n q B0 P * S)
        rw [sq_abs] at this
        nlinarith
    _ = (1 / 2) * ∑ a, sd L (u a) x ^ 2 + (1 / 2) * n * (Ecst d n q B0 P * S) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp; ring

end Bounds

/-! ### The integrated energy inequality -/

section Main

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

variable {d n : ℕ}

theorem sum_mul_mul_le_sq {V : Fin n → ℝ} {c : Fin n → Fin n → ℝ} {P : ℝ} (hP : 0 ≤ P)
    (hc : ∀ a b, |c a b| ≤ P) :
    ∑ a, ∑ b, V a * c a b * V b ≤ P * n * ∑ a, V a ^ 2 := by
  calc ∑ a, ∑ b, V a * c a b * V b ≤ ∑ a, ∑ b, |V a| * P * |V b| := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul, abs_mul]
        gcongr
        exact hc a b
    _ = P * (∑ a, |V a|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
    _ ≤ P * (n * ∑ a, V a ^ 2) := by
        gcongr
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
          (f := fun a => |V a|)
        simpa [sq_abs] using this
    _ = P * n * ∑ a, V a ^ 2 := by ring

/-- **The energy inequality on one word**: under the low-order bounds on the whole slice,
`∫ Σ_a ∂^Lu_a ∂^LG_a ≤ (½ + ½ d n P) ∫ Σ_a (∂^Lu_a)² + ½ n ∫ (E S)²`. -/
theorem word_energy_le {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {u : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b)) (hup : ∀ b, IsSPeriodic (u b))
    {t : ℝ} {r q : ℕ} {B0 M : ℝ} (hB0 : 0 ≤ B0) (hM0 : 0 ≤ M) (hr : 1 ≤ r) (hq1 : 1 ≤ q)
    (hB : ∀ y b (L : List (Fin d)), L.length ≤ r → |sd L (u b) (Fin.cons t y)| ≤ B0)
    (hMF : ∀ y a, ∀ k ≤ q, ‖iteratedFDeriv ℝ k (F a) (vslice u t y)‖ ≤ M)
    (hMA : ∀ y i a b, ∀ k ≤ q, ‖iteratedFDeriv ℝ k (A i a b) (vslice u t y)‖ ≤ M)
    (hqr : q ≤ 2 * r) (L : List (Fin d)) (hL : L.length ≤ q) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (u a) (Fin.cons t y) *
        sd L (genG A F u a) (Fin.cons t y) ≤
      (1 / 2 + 1 / 2 * d * n * (cq q * M * Bc d n r B0 ^ q)) *
          (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (u a) (Fin.cons t y) ^ 2) +
        (1 / 2) * n * ∫ y in Icc (0 : Fin d → ℝ) 1,
          (Ecst d n q B0 (cq q * M * Bc d n r B0 ^ q) * (1 + (q + 1) * sig q u t y)) ^ 2 := by
  set P := cq q * M * Bc d n r B0 ^ q with hP
  set E := Ecst d n q B0 P with hE
  have hBc := one_le_Bc d n r hB0
  have hP0 : 0 ≤ P := mul_nonneg (mul_nonneg (cq_nonneg q) hM0) (pow_nonneg (by linarith) _)
  -- continuity of the integrands
  have hV : ∀ a, ContDiff ℝ ∞ (sd L (u a)) := fun a => contDiff_sd L (hu a)
  have hVp : ∀ a, IsSPeriodic (sd L (u a)) := fun a => isSPeriodic_sd L (hup a)
  have hAc : ∀ i a b, ContDiff ℝ ∞ (compF (A i a b) u) := fun i a b => contDiff_compF (hA i a b) hu
  have hAp : ∀ i a b, IsSPeriodic (compF (A i a b) u) := fun i a b =>
    isSPeriodic_compF (A i a b) hup
  have hG : ∀ a, ContDiff ℝ ∞ (genG A F u a) := contDiff_genG hA hF hu
  have c1 : Continuous fun x => ∑ a, sd L (u a) x * sd L (genG A F u a) x :=
    continuous_finsetSum _ fun a _ => (hV a).continuous.mul (contDiff_sd L (hG a)).continuous
  have c2 : ∀ i, Continuous fun x => ∑ a, ∑ b, sd L (u a) x * compF (A i a b) u x *
      pd (sd L (u b)) i.succ x := fun i =>
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((hV a).continuous.mul (hAc i a b).continuous).mul (contDiff_pd_top (hV b) _).continuous
  have c3 : Continuous fun x => ∑ a, sd L (u a) x ^ 2 :=
    continuous_finsetSum _ fun a _ => (hV a).continuous.pow 2
  have c4 : Continuous fun y : Fin d → ℝ => (E * (1 + (q + 1) * sig q u t y)) ^ 2 :=
    (continuous_const.mul (continuous_const.add (continuous_const.mul
      (continuous_sig hu q t)))).pow 2
  -- pointwise inequality, integrated
  have hpt := fun y => pointwise_key hA hF hu (t := t) (y := y) hB0 hM0 (hB y) (hMF y) (hMA y)
    hqr L hL
  have hint : ∫ y in Icc (0 : Fin d → ℝ) 1, (∑ a, sd L (u a) (Fin.cons t y) *
        sd L (genG A F u a) (Fin.cons t y) + ∑ i, ∑ a, ∑ b, sd L (u a) (Fin.cons t y) *
          compF (A i a b) u (Fin.cons t y) * pd (sd L (u b)) i.succ (Fin.cons t y)) ≤
      ∫ y in Icc (0 : Fin d → ℝ) 1, ((1 / 2) * ∑ a, sd L (u a) (Fin.cons t y) ^ 2 +
        (1 / 2) * n * (E * (1 + (q + 1) * sig q u t y)) ^ 2) := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun y _ => hpt y
    · exact integrableOn_slice (c1.add (continuous_finsetSum _ fun i _ => c2 i)) t
    · exact ((integrableOn_slice c3 t).const_mul _).add
        ((c4.integrableOn_Icc).const_mul _)
  rw [integral_add (integrableOn_slice c1 t)
      (integrableOn_slice (continuous_finsetSum _ fun i _ => c2 i) t),
    integral_finset_sum _ fun i _ => integrableOn_slice (c2 i) t,
    integral_add ((integrableOn_slice c3 t).const_mul _) ((c4.integrableOn_Icc).const_mul _),
    integral_const_mul, integral_const_mul] at hint
  -- the symmetric terms
  have hsymT : ∀ i, -(1 / 2 * P * n) * ∫ y in Icc (0 : Fin d → ℝ) 1,
      ∑ a, sd L (u a) (Fin.cons t y) ^ 2 ≤ ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b,
        sd L (u a) (Fin.cons t y) * compF (A i a b) u (Fin.cons t y) *
          pd (sd L (u b)) i.succ (Fin.cons t y) := by
    intro i
    rw [integral_sym_eq hV hVp (hAc i) (hAp i) (fun a b x => hsym i a b _) t i]
    have hb : ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b, sd L (u a) (Fin.cons t y) *
        pd (compF (A i a b) u) i.succ (Fin.cons t y) * sd L (u b) (Fin.cons t y) ≤
        ∫ y in Icc (0 : Fin d → ℝ) 1, P * n * ∑ a, sd L (u a) (Fin.cons t y) ^ 2 := by
      refine setIntegral_mono_on ?_ ((integrableOn_slice c3 t).const_mul _) measurableSet_Icc
        fun y _ => ?_
      · exact integrableOn_slice (continuous_finsetSum _ fun a _ => continuous_finsetSum _
          fun b _ => ((hV a).continuous.mul (contDiff_pd_top (hAc i a b) _).continuous).mul
            (hV b).continuous) t
      · refine sum_mul_mul_le_sq hP0 fun a b => ?_
        have := abs_sd_compF_le_small (hA i a b) hu hB0 (hB y) (hMA y i a b) [i]
          (by simpa using hq1) (by simpa using hr)
        simpa [sd_cons] using this
    rw [integral_const_mul] at hb
    nlinarith
  have hsum : -(d * (1 / 2 * P * n)) * ∫ y in Icc (0 : Fin d → ℝ) 1,
      ∑ a, sd L (u a) (Fin.cons t y) ^ 2 ≤ ∑ i, ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b,
        sd L (u a) (Fin.cons t y) * compF (A i a b) u (Fin.cons t y) *
          pd (sd L (u b)) i.succ (Fin.cons t y) := by
    calc -(d * (1 / 2 * P * n)) * ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (u a) (Fin.cons t y) ^ 2
        = ∑ _i : Fin d, -(1 / 2 * P * n) * ∫ y in Icc (0 : Fin d → ℝ) 1,
            ∑ a, sd L (u a) (Fin.cons t y) ^ 2 := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => hsymT i
  set X := ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (u a) (Fin.cons t y) ^ 2 with hX
  set Y := ∫ y in Icc (0 : Fin d → ℝ) 1, (E * (1 + (q + 1) * sig q u t y)) ^ 2 with hY
  set I1 := ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (u a) (Fin.cons t y) *
    sd L (genG A F u a) (Fin.cons t y) with hI1
  set I2 := ∑ i, ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, ∑ b,
    sd L (u a) (Fin.cons t y) * compF (A i a b) u (Fin.cons t y) *
      pd (sd L (u b)) i.succ (Fin.cons t y) with hI2
  have : I1 ≤ 1 / 2 * X + 1 / 2 * n * Y + d * (1 / 2 * P * n) * X := by linarith
  have e : (1 / 2 + 1 / 2 * d * n * P) * X + 1 / 2 * n * Y =
      1 / 2 * X + 1 / 2 * n * Y + d * (1 / 2 * P * n) * X := by ring
  rw [e]
  exact this

end Main

/-! ### The `H^q` energy inequality with an `N`-independent constant -/

section Theorem

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

variable {d n : ℕ}

theorem one_add_sq_le (a : ℝ) : (1 + a) ^ 2 ≤ 2 + 2 * a ^ 2 := by nlinarith [sq_nonneg (1 - a)]

/-- **The `H^q` energy inequality of a quasilinear symmetric hyperbolic system**
(`app:generated-dynamics`, `eq:generated-Galerkin`): on `𝕋^d`, for `m > d/2` and `q ≥ 2m`, smooth
real symmetric coefficient matrices `A^i(v)` and smooth `F(v)` (`v ∈ ℝ^n`), and every radius
`R ≥ 0`, there is `K` such that every smooth spatially periodic field `U = (u_b)` with
`‖U(t)‖²_{H^q} ≤ R²` satisfies
`⟨U, G(U)⟩_{H^q}(t) ≤ K (1 + ‖U(t)‖²_{H^q})`,
`G(U) = F(U) - Σ_i A^i(U) ∂_iU`.  `K` depends only on `R`, `q`, `m`, `d`, `n`, `A`, `F` — not on
`U`; in particular it is the same for every spectral Galerkin truncation (the orthogonal
projection disappears from the pairing, `SpectralGalerkin.inner_proj_eq`).  The proof is the
classical one: commutator form of the Leibniz rule along words, the tame Faà di Bruno bound with
the low-order derivatives controlled by the Sobolev embedding, and symmetric integration by parts
for the principal term. -/
theorem pairQ_genG_le {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, IsSPeriodic (u b)) → ∀ t, energyQ q u t ≤ R ^ 2 →
        pairQ q u (genG A F u) t ≤ K * (1 + energyQ q u t) := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    exact_mod_cast this
  obtain ⟨r, hr⟩ : ∃ r, r = q - m := ⟨_, rfl⟩
  have hqr : q ≤ 2 * r := by omega
  have hr1 : 1 ≤ r := by omega
  have hq1 : 1 ≤ q := by omega
  set B0 := Real.sqrt CS * R with hB0
  have hB00 : 0 ≤ B0 := by positivity
  -- uniform coefficient bounds on the ball `‖v‖ ≤ B₀`
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
  refine ⟨K, hK0, fun u hu hup t hEt => ?_⟩
  have hEn := energyQ_nonneg q u t
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
  have hMF : ∀ y a, ∀ k ≤ q, ‖iteratedFDeriv ℝ k (F a) (vslice u t y)‖ ≤ M := fun y a k hk =>
    hM (Sum.inl a) _ (hval y) k hk
  have hMA : ∀ y i a b, ∀ k ≤ q, ‖iteratedFDeriv ℝ k (A i a b) (vslice u t y)‖ ≤ M :=
    fun y i a b k hk => hM (Sum.inr (i, a, b)) _ (hval y) k hk
  -- the word estimates
  have hword : ∀ L ∈ wordsLE d q, ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (u a) (Fin.cons t y) *
      sd L (genG A F u a) (Fin.cons t y) ≤
        (1 / 2 + 1 / 2 * d * n * P) *
          (∫ y in Icc (0 : Fin d → ℝ) 1, ∑ a, sd L (u a) (Fin.cons t y) ^ 2) +
        (1 / 2) * n * ∫ y in Icc (0 : Fin d → ℝ) 1, (E * (1 + (q + 1) * sig q u t y)) ^ 2 :=
    fun L hL => word_energy_le hA hsym hF hu hup hB00 hM0 hr1 hq1 hB hMF hMA hqr L
      (mem_wordsLE.mp hL)
  -- the `σ` integral
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
  -- sum over the words
  have hsumV : ∑ L ∈ wordsLE d q, ∫ y in Icc (0 : Fin d → ℝ) 1,
      ∑ a, sd L (u a) (Fin.cons t y) ^ 2 = energyQ q u t := by
    unfold energyQ Q
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [integral_finset_sum _ fun a _ => integrableOn_sq (contDiff_sd L (hu a)).continuous t]
  have hpair : pairQ q u (genG A F u) t = ∑ L ∈ wordsLE d q, ∫ y in Icc (0 : Fin d → ℝ) 1,
      ∑ a, sd L (u a) (Fin.cons t y) * sd L (genG A F u a) (Fin.cons t y) := by
    unfold pairQ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [integral_finset_sum _ fun a _ => integrableOn_slice (show Continuous fun x =>
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

end Theorem

/-! ### Non-vacuity -/

section NonVacuity

open SymHypEnergy SlabWaveHk

/-- The hypotheses of `pairQ_genG_le` are satisfiable: on `𝕋³` (`m = 2`, `q = 4`), the identity
principal matrices `A^i = I` (symmetric, constant), `F = 0`, every radius; and constant fields
are smooth and spatially periodic. -/
example (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : Fin n → ST 3 → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, IsSPeriodic (u b)) → ∀ t, energyQ 4 u t ≤ R ^ 2 →
        pairQ 4 u (genG (fun _ a b _ => if a = b then (1 : ℝ) else 0) (fun _ _ => 0) u) t ≤
          K * (1 + energyQ 4 u t) :=
  pairQ_genG_le (m := 2) (by norm_num) (by norm_num) (fun _ _ _ => contDiff_const)
    (fun _ a b _ => by by_cases h : a = b <;> simp [h, eq_comm]) (fun _ => contDiff_const) hR

example (n : ℕ) (c : Fin n → ℝ) :
    (∀ b, ContDiff ℝ ∞ (fun _ : ST 3 => c b)) ∧ ∀ b, IsSPeriodic (fun _ : ST 3 => c b) :=
  ⟨fun _ => contDiff_const, fun _ _ _ => rfl⟩

end NonVacuity

end RenewalGeometry.QLEnergy
