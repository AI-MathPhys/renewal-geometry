/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniform bounds for iterated Fréchet derivatives on open sets, vector-field jets and locality
  (infrastructure for `lem:supp-open-local-jets`; emergent-spacetime manuscript)

Let `E, F, G` be real normed spaces and `U ⊆ E` open.

* `DerivBound f U K M`: `f` is `C^∞` on `U` and `‖D^k f(x)‖ ≤ M` for all `x ∈ U`, `k ≤ K`
  (the operator norms of the iterated Fréchet derivatives `iteratedFDeriv ℝ k f x`).
  Closure rules with explicit constants: `DerivBound.add`, `sub`, `neg`, `sum`, `clm_comp`
  (left composition with a continuous linear map, constant `‖L‖ M`), `bilinear` (Leibniz rule,
  constant `‖B‖ 2^K M₁ M₂`), `comp_clm` (right composition with a continuous linear map,
  constant `M max(1, ‖L‖)^K`), `const`, `clm` (a continuous linear map on a bounded set),
  `fderiv` (one order is consumed).
* `vfJet F j`: the successive vector jets `J₀ = id`, `J_{j+1}(X) = DJ_j(X)[F(X)]` of a vector
  field (so `J₁ = F`).  `vfJet_bound`: if `DerivBound F U K M`, then
  `DerivBound (J_{j+1}) U (K - j) ((2^K M)^j M)` for `j ≤ K`, and
  `vfJet_norm_le`: `‖J_j(X)‖ ≤ (2^K M)^{j-1} ‖F(X)‖` for `1 ≤ j ≤ K + 1`.
* `iteratedDeriv_eq_vfJet`: along an exact solution `X' = F(X)` on an open time set, the `j`-th
  time derivative is `J_j(X(t))`.
* `vfJet_proj`: if `P(F X) = Q X` on `U` for continuous linear `P, Q`, then
  `P(J_{j+1} X) = Q(J_j X)` on `U` (for the writer: the `q`-jet of order `j + 1` is the
  `v`-jet of order `j`).
* `fderiv_local`, `vfJet_local`: **locality**.  If a family of continuous linear "restrictions"
  `P ρ` is monotone and the field is local with radius `R` (`P (ρ + R) X = P (ρ + R) X'` implies
  `P ρ (F X) = P ρ (F X')`), then `J_j` is local with radius `R j`.
-/

open Set Filter Topology Function
open scoped ContDiff BigOperators

namespace RenewalGeometry.IteratedDerivBounds

noncomputable section

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
  [NormedSpace ℝ H]

/-- `f` is `C^∞` on `U` and its iterated Fréchet derivatives of order `≤ K` are bounded by `M`
in operator norm at every point of `U`. -/
structure DerivBound (f : E → F) (U : Set E) (K : ℕ) (M : ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ ∞ f U
  bound : ∀ x ∈ U, ∀ k ≤ K, ‖iteratedFDeriv ℝ k f x‖ ≤ M

namespace DerivBound

variable {U : Set E} {K : ℕ} {M M₁ M₂ : ℝ}

theorem contDiffAt {f : E → F} (h : DerivBound f U K M) (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ f x :=
  h.contDiffOn.contDiffAt (hU.mem_nhds hx)

theorem mono {f : E → F} (h : DerivBound f U K M) {K' : ℕ} {M' : ℝ} (hK : K' ≤ K)
    (hM : M ≤ M') : DerivBound f U K' M' :=
  ⟨h.contDiffOn, fun x hx k hk => (h.bound x hx k (hk.trans hK)).trans hM⟩

theorem subset {f : E → F} (h : DerivBound f U K M) {U' : Set E} (hU' : U' ⊆ U) :
    DerivBound f U' K M :=
  ⟨h.contDiffOn.mono hU', fun x hx k hk => h.bound x (hU' hx) k hk⟩

theorem nonneg {f : E → F} (h : DerivBound f U K M) {x : E} (hx : x ∈ U) : 0 ≤ M :=
  (norm_nonneg _).trans (h.bound x hx 0 (Nat.zero_le _))

theorem norm_le {f : E → F} (h : DerivBound f U K M) {x : E} (hx : x ∈ U) : ‖f x‖ ≤ M := by
  have := h.bound x hx 0 (Nat.zero_le _)
  rwa [norm_iteratedFDeriv_zero] at this

theorem norm_fderiv_le {f : E → F} (h : DerivBound f U K M) (hK : 1 ≤ K) {x : E} (hx : x ∈ U) :
    ‖fderiv ℝ f x‖ ≤ M := by
  have := h.bound x hx 1 hK
  rwa [norm_iteratedFDeriv_one] at this

theorem add {f g : E → F} (hf : DerivBound f U K M₁) (hg : DerivBound g U K M₂) (hU : IsOpen U) :
    DerivBound (fun x => f x + g x) U K (M₁ + M₂) := by
  refine ⟨hf.contDiffOn.add hg.contDiffOn, fun x hx k hk => ?_⟩
  have e : iteratedFDeriv ℝ k (fun x => f x + g x) x =
      iteratedFDeriv ℝ k f x + iteratedFDeriv ℝ k g x :=
    iteratedFDeriv_add_apply ((hf.contDiffAt hU hx).of_le (by exact_mod_cast le_top))
      ((hg.contDiffAt hU hx).of_le (by exact_mod_cast le_top))
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hf.bound x hx k hk) (hg.bound x hx k hk))

theorem neg {f : E → F} (hf : DerivBound f U K M) : DerivBound (fun x => -f x) U K M := by
  refine ⟨hf.contDiffOn.neg, fun x hx k hk => ?_⟩
  have e : iteratedFDeriv ℝ k (fun x => -f x) x = -iteratedFDeriv ℝ k f x :=
    iteratedFDeriv_neg_apply
  rw [e, norm_neg]
  exact hf.bound x hx k hk

theorem sub {f g : E → F} (hf : DerivBound f U K M₁) (hg : DerivBound g U K M₂) (hU : IsOpen U) :
    DerivBound (fun x => f x - g x) U K (M₁ + M₂) := by
  have := hf.add hg.neg hU
  simpa [sub_eq_add_neg] using this

theorem sum {ι : Type*} (s : Finset ι) {f : ι → E → F} {M : ι → ℝ}
    (hf : ∀ i ∈ s, DerivBound (f i) U K (M i)) (hU : IsOpen U) :
    DerivBound (fun x => ∑ i ∈ s, f i x) U K (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨contDiffOn_const, fun x hx k hk => ?_⟩
    simp only [Finset.sum_empty]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hk0)]; simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)) hU

theorem clm_comp {f : E → F} (hf : DerivBound f U K M) (hU : IsOpen U) (L : F →L[ℝ] G) :
    DerivBound (fun x => L (f x)) U K (‖L‖ * M) := by
  refine ⟨L.contDiff.comp_contDiffOn hf.contDiffOn, fun x hx k hk => ?_⟩
  have h := L.norm_iteratedFDeriv_comp_left (n := k) (hf.contDiffAt hU hx)
    (by exact_mod_cast le_top)
  exact h.trans (mul_le_mul_of_nonneg_left (hf.bound x hx k hk) (norm_nonneg _))

theorem bilinear {f : E → F} {g : E → G} (hf : DerivBound f U K M₁) (hg : DerivBound g U K M₂)
    (hU : IsOpen U) (B : F →L[ℝ] G →L[ℝ] H) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) :
    DerivBound (fun x => B (f x) (g x)) U K (‖B‖ * 2 ^ K * M₁ * M₂) := by
  refine ⟨B.isBoundedBilinearMap.contDiff.comp_contDiffOn (hf.contDiffOn.prodMk hg.contDiffOn),
    fun x hx k hk => ?_⟩
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear hf.contDiffOn hg.contDiffOn
    hU.uniqueDiffOn hx (n := k) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hU hx] at h
  refine h.trans ?_
  have hs : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f U x‖ *
      ‖iteratedFDerivWithin ℝ (k - i) g U x‖ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        M₁ * M₂ := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [iteratedFDerivWithin_of_isOpen i hU hx, iteratedFDerivWithin_of_isOpen (k - i) hU hx]
    have h1 := hf.bound x hx i (hi'.trans hk)
    have h2 := hg.bound x hx (k - i) ((Nat.sub_le k i).trans hk)
    have hc : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
    have := mul_le_mul h1 h2 (norm_nonneg _) hM₁
    calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖
        = (k.choose i : ℝ) * (‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖) := by
          ring
      _ ≤ (k.choose i : ℝ) * (M₁ * M₂) := mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M₁ * M₂ = 2 ^ k * M₁ * M₂ := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    congr 2
    exact_mod_cast Nat.sum_range_choose k
  have h2k : (2 : ℝ) ^ k ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hk
  calc ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f U x‖ *
        ‖iteratedFDerivWithin ℝ (k - i) g U x‖ ≤ ‖B‖ * (2 ^ k * M₁ * M₂) := by
        rw [← hsum]; exact mul_le_mul_of_nonneg_left hs (norm_nonneg B)
    _ ≤ ‖B‖ * (2 ^ K * M₁ * M₂) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg B)
        have := mul_nonneg hM₁ hM₂
        nlinarith
    _ = ‖B‖ * 2 ^ K * M₁ * M₂ := by ring

/-- Iterated derivative of a right composition with a continuous linear map, on open sets. -/
theorem iteratedFDeriv_comp_clm {g : F → G} {V : Set F} (hg : ContDiffOn ℝ ∞ g V) (hV : IsOpen V)
    (L : E →L[ℝ] F) {x : E} (hx : L x ∈ V) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y => g (L y)) x =
      (iteratedFDeriv ℝ k g (L x)).compContinuousLinearMap fun _ => L := by
  have hpre : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hg hV.uniqueDiffOn hpre.uniqueDiffOn hx
    (i := k) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hpre (show x ∈ L ⁻¹' V from hx),
    iteratedFDerivWithin_of_isOpen k hV hx] at h
  exact h

theorem comp_clm {g : F → G} {V : Set F} (hg : DerivBound g V K M) (hV : IsOpen V)
    (L : E →L[ℝ] F) (hmaps : MapsTo L U V) :
    DerivBound (fun x => g (L x)) U K (M * max 1 ‖L‖ ^ K) := by
  refine ⟨hg.contDiffOn.comp L.contDiff.contDiffOn hmaps, fun x hx k hk => ?_⟩
  rw [iteratedFDeriv_comp_clm hg.contDiffOn hV L (hmaps hx) k]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hM := hg.nonneg (hmaps hx)
  have h1 := hg.bound (L x) (hmaps hx) k hk
  have h2 : ∏ _i : Fin k, ‖L‖ ≤ max 1 ‖L‖ ^ K := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ‖L‖ ^ k ≤ max 1 ‖L‖ ^ k := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) k
      _ ≤ max 1 ‖L‖ ^ K := pow_le_pow_right₀ (le_max_left _ _) hk
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM

theorem const (c : F) (U : Set E) (K : ℕ) : DerivBound (fun _ : E => c) U K ‖c‖ := by
  refine ⟨contDiffOn_const, fun x _ k _ => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hk0)]; simp

theorem norm_iteratedFDeriv_clm_le (L : E →L[ℝ] F) (x : E) (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k L x‖ ≤ ‖L‖ := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have hfd : fderiv ℝ (L : E → F) = fun _ => L := funext fun _ => L.fderiv
  rw [hfd]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hn)]; simp

theorem clm (L : E →L[ℝ] F) {R : ℝ} (_hR : 0 ≤ R) (hU : U ⊆ Metric.closedBall 0 R) (K : ℕ) :
    DerivBound (fun x => L x) U K (‖L‖ * max 1 R) := by
  refine ⟨L.contDiff.contDiffOn, fun x hx k hk => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [norm_iteratedFDeriv_zero]
    have hxR : ‖x‖ ≤ R := by simpa using hU hx
    exact (L.le_opNorm x).trans (mul_le_mul_of_nonneg_left (hxR.trans (le_max_right _ _))
      (norm_nonneg _))
  · refine (norm_iteratedFDeriv_clm_le L x k hk0).trans ?_
    exact le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)

theorem fderiv {f : E → F} (hf : DerivBound f U (K + 1) M) (hU : IsOpen U) :
    DerivBound (fderiv ℝ f) U K M := by
  refine ⟨hf.contDiffOn.fderiv_of_isOpen hU (by exact_mod_cast le_top), fun x hx k hk => ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact hf.bound x hx (k + 1) (by omega)


theorem pi {ι : Type*} [Fintype ι] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
    [∀ i, NormedSpace ℝ (F' i)] {f : ∀ i, E → F' i} (hf : ∀ i, DerivBound (f i) U K M)
    (hU : IsOpen U) (hM : 0 ≤ M) : DerivBound (fun x i => f i x) U K M := by
  have hC : ContDiffOn ℝ ∞ (fun x i => f i x) U := contDiffOn_pi.2 fun i => (hf i).contDiffOn
  refine ⟨hC, fun x hx k hk => ?_⟩
  refine ContinuousMultilinearMap.opNorm_le_bound hM fun m => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  have h := congrArg (fun L => L m) ((ContinuousLinearMap.proj (R := ℝ) (φ := F') i).iteratedFDeriv_comp_left
    (hC.contDiffAt (hU.mem_nhds hx)) (i := k) (by exact_mod_cast le_top))
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at h
  have e : (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := F') i) ∘ fun x i => f i x) = f i := rfl
  rw [e] at h
  have h2 : (iteratedFDeriv ℝ k (fun x i => f i x) x m) i = iteratedFDeriv ℝ k (f i) x m := h.symm
  rw [h2]
  exact ((iteratedFDeriv ℝ k (f i) x).le_opNorm m).trans
    (mul_le_mul_of_nonneg_right ((hf i).bound x hx k hk) (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem prod {f : E → F} {g : E → G} (hf : DerivBound f U K M₁) (hg : DerivBound g U K M₂)
    (hU : IsOpen U) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) :
    DerivBound (fun x => (f x, g x)) U K (M₁ + M₂) := by
  have h1 := hf.clm_comp hU (ContinuousLinearMap.inl ℝ F G)
  have h2 := hg.clm_comp hU (ContinuousLinearMap.inr ℝ F G)
  have h := h1.add h2 hU
  have e : (fun x => (ContinuousLinearMap.inl ℝ F G) (f x) + (ContinuousLinearMap.inr ℝ F G) (g x)) =
      fun x => (f x, g x) := by funext x; simp
  rw [e] at h
  refine h.mono le_rfl ?_
  have a1 : ‖ContinuousLinearMap.inl ℝ F G‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ℝ F G
  have a2 : ‖ContinuousLinearMap.inr ℝ F G‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ F G
  have := mul_le_mul_of_nonneg_right a1 hM₁
  have := mul_le_mul_of_nonneg_right a2 hM₂
  linarith

theorem congr {f g : E → F} (h : DerivBound f U K M) (hfg : ∀ x, f x = g x) :
    DerivBound g U K M := by
  have : f = g := funext hfg
  exact this ▸ h

end DerivBound

/-! ### Jets of a vector field -/

/-- The successive vector jets of a vector field: `J₀ = id`, `J_{j+1}(X) = DJ_j(X)[F(X)]`. -/
def vfJet (F : E → E) : ℕ → E → E
  | 0 => id
  | j + 1 => fun X => _root_.fderiv ℝ (vfJet F j) X (F X)

theorem vfJet_zero (F : E → E) : vfJet F 0 = id := rfl

theorem vfJet_succ (F : E → E) (j : ℕ) (X : E) :
    vfJet F (j + 1) X = _root_.fderiv ℝ (vfJet F j) X (F X) := rfl

theorem vfJet_one (F : E → E) : vfJet F 1 = F := by
  funext X
  rw [vfJet_succ, vfJet_zero, fderiv_id]
  rfl

theorem vfJet_contDiffOn {F : E → E} {U : Set E} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) :
    ∀ j, ContDiffOn ℝ ∞ (vfJet F j) U
  | 0 => contDiffOn_id
  | j + 1 => by
    have h := vfJet_contDiffOn hF hU j
    have hd : ContDiffOn ℝ ∞ (_root_.fderiv ℝ (vfJet F j)) U :=
      h.fderiv_of_isOpen hU (by exact_mod_cast le_top)
    exact hd.clm_apply hF

/-- **Bounds for the vector jets.**  If `DerivBound F U K M`, then for `j ≤ K` the jet
`J_{j+1}` has derivatives of order `≤ K - j` bounded by `(2^K M)^j M` on `U`. -/
theorem vfJet_bound {F : E → E} {U : Set E} {K : ℕ} {M : ℝ} (hF : DerivBound F U K M)
    (hU : IsOpen U) (hM : 0 ≤ M) :
    ∀ j ≤ K, DerivBound (vfJet F (j + 1)) U (K - j) ((2 ^ K * M) ^ j * M)
  | 0, _ => by simpa [vfJet_one] using hF
  | j + 1, hj => by
    have ih := vfJet_bound hF hU hM j (by omega)
    have hd : DerivBound (_root_.fderiv ℝ (vfJet F (j + 1))) U (K - (j + 1))
        ((2 ^ K * M) ^ j * M) := by
      have e : K - j = K - (j + 1) + 1 := by omega
      rw [e] at ih
      exact ih.fderiv hU
    have hF' : DerivBound F U (K - (j + 1)) M := hF.mono (Nat.sub_le _ _) le_rfl
    have hMj : 0 ≤ (2 ^ K * M) ^ j * M := by positivity
    have hb := hd.bilinear hF' hU (ContinuousLinearMap.id ℝ (E →L[ℝ] E)) hMj hM
    have heq : (fun X => (ContinuousLinearMap.id ℝ (E →L[ℝ] E))
        (_root_.fderiv ℝ (vfJet F (j + 1)) X) (F X)) = vfJet F (j + 1 + 1) := by
      funext X; rfl
    rw [heq] at hb
    refine hb.mono le_rfl ?_
    have hid : ‖ContinuousLinearMap.id ℝ (E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h2 : (2 : ℝ) ^ (K - (j + 1)) ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    have hA : 0 ≤ (2 : ℝ) ^ (K - (j + 1)) * ((2 ^ K * M) ^ j * M) * M := by positivity
    calc ‖ContinuousLinearMap.id ℝ (E →L[ℝ] E)‖ * 2 ^ (K - (j + 1)) * ((2 ^ K * M) ^ j * M) * M
        = ‖ContinuousLinearMap.id ℝ (E →L[ℝ] E)‖ * (2 ^ (K - (j + 1)) *
            ((2 ^ K * M) ^ j * M) * M) := by ring
      _ ≤ 1 * (2 ^ K * ((2 ^ K * M) ^ j * M) * M) := by
          refine mul_le_mul hid ?_ hA zero_le_one
          have := mul_nonneg hMj hM
          nlinarith
      _ = (2 ^ K * M) ^ (j + 1) * M := by ring

/-- **Zeroth-order jet bound**: `‖J_j(X)‖ ≤ (2^K M)^{j-1} ‖F(X)‖` for `1 ≤ j ≤ K + 1`. -/
theorem vfJet_norm_le {F : E → E} {U : Set E} {K : ℕ} {M : ℝ} (hF : DerivBound F U K M)
    (hU : IsOpen U) (hM : 0 ≤ M) {X : E} (hX : X ∈ U) :
    ∀ j, 1 ≤ j → j ≤ K + 1 → ‖vfJet F j X‖ ≤ (2 ^ K * M) ^ (j - 1) * ‖F X‖ := by
  intro j hj1 hjK
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [vfJet_one]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hb := vfJet_bound hF hU hM i (by omega)
  have hd := hb.norm_fderiv_le (by omega) hX
  rw [vfJet_succ]
  have hFX := norm_nonneg (F X)
  have h2 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  calc ‖_root_.fderiv ℝ (vfJet F (i + 1)) X (F X)‖
      ≤ ‖_root_.fderiv ℝ (vfJet F (i + 1)) X‖ * ‖F X‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (2 ^ K * M) ^ i * M * ‖F X‖ := mul_le_mul_of_nonneg_right hd hFX
    _ ≤ (2 ^ K * M) ^ (i + 1 + 1 - 1) * ‖F X‖ := by
        rw [show i + 1 + 1 - 1 = i + 1 by omega, pow_succ]
        have : 0 ≤ (2 ^ K * M) ^ i := by positivity
        have h3 : (2 ^ K * M) ^ i * M ≤ (2 ^ K * M) ^ i * (2 ^ K * M) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hM h2) this
        exact mul_le_mul_of_nonneg_right h3 hFX

/-- **Time derivatives along an exact solution** are the vector jets:
if `X' = F(X)` with `X(t) ∈ U` on an open time set `S`, then `X⁽ʲ⁾(t) = J_j(X(t))` on `S`. -/
theorem iteratedDeriv_eq_vfJet {F : E → E} {U : Set E} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {S : Set ℝ} (hS : IsOpen S) {X : ℝ → E} (hXU : ∀ t ∈ S, X t ∈ U)
    (hX : ∀ t ∈ S, HasDerivAt X (F (X t)) t) :
    ∀ j, ∀ t ∈ S, iteratedDeriv j X t = vfJet F j (X t)
  | 0, t, _ => by simp [vfJet_zero]
  | j + 1, t, ht => by
    have ih := iteratedDeriv_eq_vfJet hF hU hS hXU hX j
    have hev : iteratedDeriv j X =ᶠ[𝓝 t] fun s => vfJet F j (X s) :=
      Filter.eventually_of_mem (hS.mem_nhds ht) fun s hs => ih s hs
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hJ : DifferentiableAt ℝ (vfJet F j) (X t) :=
      ((vfJet_contDiffOn hF hU j).contDiffAt (hU.mem_nhds (hXU t ht))).differentiableAt
        (by simp)
    have := hJ.hasFDerivAt.comp_hasDerivAt t (hX t ht)
    exact this.deriv

/-- **Time derivatives of a linear image of an exact solution**: if `X' = F(X)` with `X(t) ∈ U`
on an open time set `S` and `P` is continuous linear, then `(P ∘ X)⁽ʲ⁾(t) = P(J_j(X(t)))`. -/
theorem iteratedDeriv_clm_eq_vfJet {F : E → E} {U : Set E} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {S : Set ℝ} (hS : IsOpen S) {X : ℝ → E} (hXU : ∀ t ∈ S, X t ∈ U)
    (hX : ∀ t ∈ S, HasDerivAt X (F (X t)) t) (P : E →L[ℝ] G) :
    ∀ j, ∀ t ∈ S, iteratedDeriv j (fun τ => P (X τ)) t = P (vfJet F j (X t))
  | 0, t, _ => by simp [vfJet_zero]
  | j + 1, t, ht => by
    have ih := iteratedDeriv_clm_eq_vfJet hF hU hS hXU hX P j
    have hev : iteratedDeriv j (fun τ => P (X τ)) =ᶠ[𝓝 t] fun s => P (vfJet F j (X s)) :=
      Filter.eventually_of_mem (hS.mem_nhds ht) fun s hs => ih s hs
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hJ : DifferentiableAt ℝ (vfJet F j) (X t) :=
      ((vfJet_contDiffOn hF hU j).contDiffAt (hU.mem_nhds (hXU t ht))).differentiableAt
        (by simp)
    have := P.hasFDerivAt.comp_hasDerivAt t (hJ.hasFDerivAt.comp_hasDerivAt t (hX t ht))
    exact this.deriv


/-- Shifted form of `iteratedDeriv_clm_eq_vfJet`: along an exact solution,
`∂_t^k [P(J_j(X(t)))] = P(J_{j+k}(X(t)))`. -/
theorem iteratedDeriv_clm_vfJet_eq {F : E → E} {U : Set E} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {S : Set ℝ} (hS : IsOpen S) {X : ℝ → E} (hXU : ∀ t ∈ S, X t ∈ U)
    (hX : ∀ t ∈ S, HasDerivAt X (F (X t)) t) (P : E →L[ℝ] G) (j : ℕ) :
    ∀ k, ∀ t ∈ S, iteratedDeriv k (fun τ => P (vfJet F j (X τ))) t = P (vfJet F (j + k) (X t))
  | 0, t, _ => by simp
  | k + 1, t, ht => by
    have ih := iteratedDeriv_clm_vfJet_eq hF hU hS hXU hX P j k
    have hev : iteratedDeriv k (fun τ => P (vfJet F j (X τ))) =ᶠ[𝓝 t]
        fun s => P (vfJet F (j + k) (X s)) :=
      Filter.eventually_of_mem (hS.mem_nhds ht) fun s hs => ih s hs
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hJ : DifferentiableAt ℝ (vfJet F (j + k)) (X t) :=
      ((vfJet_contDiffOn hF hU (j + k)).contDiffAt (hU.mem_nhds (hXU t ht))).differentiableAt
        (by simp)
    have := P.hasFDerivAt.comp_hasDerivAt t (hJ.hasFDerivAt.comp_hasDerivAt t (hX t ht))
    rw [← add_assoc]
    exact this.deriv

/-- **Projection relation for jets.**  If `P (F X) = Q X` on the open set `U` for continuous
linear `P, Q`, then `P (J_{j+1} X) = Q (J_j X)` on `U` for every `j`. -/
theorem vfJet_proj {F : E → E} {U : Set E} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (P Q : E →L[ℝ] G) (hPQ : ∀ X ∈ U, P (F X) = Q X) :
    ∀ j, ∀ X ∈ U, P (vfJet F (j + 1) X) = Q (vfJet F j X)
  | 0, X, hX => by simpa [vfJet_one, vfJet_zero] using hPQ X hX
  | j + 1, X, hX => by
    have ih := vfJet_proj hF hU P Q hPQ j
    have hd1 : DifferentiableAt ℝ (vfJet F (j + 1)) X :=
      ((vfJet_contDiffOn hF hU (j + 1)).contDiffAt (hU.mem_nhds hX)).differentiableAt
        (by simp)
    have hd0 : DifferentiableAt ℝ (vfJet F j) X :=
      ((vfJet_contDiffOn hF hU j).contDiffAt (hU.mem_nhds hX)).differentiableAt
        (by simp)
    have hev : (fun Y => P (vfJet F (j + 1) Y)) =ᶠ[𝓝 X] fun Y => Q (vfJet F j Y) :=
      Filter.eventually_of_mem (hU.mem_nhds hX) fun Y hY => ih Y hY
    have h1 : _root_.fderiv ℝ (fun Y => P (vfJet F (j + 1) Y)) X =
        P.comp (_root_.fderiv ℝ (vfJet F (j + 1)) X) := (P.hasFDerivAt.comp X hd1.hasFDerivAt).fderiv
    have h0 : _root_.fderiv ℝ (fun Y => Q (vfJet F j Y)) X =
        Q.comp (_root_.fderiv ℝ (vfJet F j) X) := (Q.hasFDerivAt.comp X hd0.hasFDerivAt).fderiv
    have hfd := hev.fderiv_eq (𝕜 := ℝ)
    rw [h1, h0] at hfd
    have := congrArg (fun L : E →L[ℝ] G => L (F X)) hfd
    simpa [vfJet_succ] using this

/-! ### Locality -/

/-- **Derivatives of local maps are local.**  Let `f` be differentiable on the open set `U`,
`P : E → W` linear and `Q : G →L[ℝ] W'`.  If `Q (f X)` depends only on `P X` for `X ∈ U`,
then `Q (Df(X)[Y])` depends only on `(P X, P Y)`. -/
theorem fderiv_local {W W' : Type*} [AddCommGroup W] [Module ℝ W] [NormedAddCommGroup W']
    [NormedSpace ℝ W'] {f : E → G} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (P : E →ₗ[ℝ] W) (Q : G →L[ℝ] W')
    (hloc : ∀ X ∈ U, ∀ X' ∈ U, P X = P X' → Q (f X) = Q (f X'))
    {X X' : E} (hX : X ∈ U) (hX' : X' ∈ U) (hPX : P X = P X') {Y Y' : E} (hPY : P Y = P Y') :
    Q (_root_.fderiv ℝ f X Y) = Q (_root_.fderiv ℝ f X' Y') := by
  have hline : ∀ (Z V : E), Z ∈ U → HasDerivAt (fun t : ℝ => Q (f (Z + t • V)))
      (Q (_root_.fderiv ℝ f Z V)) 0 := by
    intro Z V hZ
    have hd : DifferentiableAt ℝ f Z := hf.differentiableAt (hU.mem_nhds hZ)
    have hl : HasDerivAt (fun t : ℝ => Z + t • V) V 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add Z
    have hc := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    exact Q.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hev : (fun t : ℝ => Q (f (X + t • Y))) =ᶠ[𝓝 0] fun t => Q (f (X' + t • Y')) := by
    have h1 : ∀ᶠ t : ℝ in 𝓝 0, X + t • Y ∈ U := by
      have hc : Continuous fun t : ℝ => X + t • Y := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hX)
    have h2 : ∀ᶠ t : ℝ in 𝓝 0, X' + t • Y' ∈ U := by
      have hc : Continuous fun t : ℝ => X' + t • Y' := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hX')
    filter_upwards [h1, h2] with t ht1 ht2
    refine hloc _ ht1 _ ht2 ?_
    rw [map_add, map_add, map_smul, map_smul, hPX, hPY]
  exact (hline X Y hX).unique ((hline X' Y' hX').congr_of_eventuallyEq hev)

/-- **Locality of the vector jets.**  Let `P ρ : E →L[ℝ] E` be a family of continuous linear
"restrictions to the radius-`ρ` neighbourhood" with `P ρ' = P ρ' ∘ P ρ` for `ρ' ≤ ρ`, and let the
field have radius `R`: `P (ρ + R) X = P (ρ + R) X'` implies `P ρ (F X) = P ρ (F X')` on `U`.
Then `J_j` has radius `R j`. -/
theorem vfJet_local {F : E → E} {U : Set E} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (P : ℕ → E →L[ℝ] E) (hmono : ∀ ρ ρ', ρ' ≤ ρ → ∀ X, P ρ' (P ρ X) = P ρ' X) (R : ℕ)
    (hloc : ∀ ρ, ∀ X ∈ U, ∀ X' ∈ U, P (ρ + R) X = P (ρ + R) X' → P ρ (F X) = P ρ (F X')) :
    ∀ j ρ, ∀ X ∈ U, ∀ X' ∈ U, P (ρ + R * j) X = P (ρ + R * j) X' →
      P ρ (vfJet F j X) = P ρ (vfJet F j X')
  | 0, ρ, X, _, X', _, h => by simpa [vfJet_zero] using h
  | j + 1, ρ, X, hX, X', hX', h => by
    have ih := vfJet_local hF hU P hmono R hloc j
    have hres : ∀ ρ' ≤ ρ + R * (j + 1), P ρ' X = P ρ' X' := by
      intro ρ' hρ'
      rw [← hmono _ _ hρ' X, ← hmono _ _ hρ' X', h]
    have hPX : P (ρ + R * j) X = P (ρ + R * j) X' := hres _ (by nlinarith)
    have hPF : P (ρ + R * j) (F X) = P (ρ + R * j) (F X') :=
      hloc (ρ + R * j) X hX X' hX' (hres _ (by ring_nf; omega))
    have hdiff : DifferentiableOn ℝ (vfJet F j) U :=
      (vfJet_contDiffOn hF hU j).differentiableOn (by simp)
    rw [vfJet_succ, vfJet_succ]
    exact fderiv_local hU hdiff (P (ρ + R * j)).toLinearMap (P ρ) (fun Z hZ Z' hZ' hZZ' =>
      ih ρ Z hZ Z' hZ' hZZ') hX hX' hPX hPF

end

end RenewalGeometry.IteratedDerivBounds
