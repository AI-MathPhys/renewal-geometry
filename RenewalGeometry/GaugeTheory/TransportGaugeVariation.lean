/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.TransportPlaquetteConsistency

/-!
# The first variation of parallel transports in the connection (dual-number transports)

Einstein–SM action-closure manuscript, proof of `prop:mesh-consistency`: "These expansions also
hold after one field or metric variation.  To see this without interchanging an uncontrolled
limit and derivative, differentiate the transport equation itself.  If `U(t,s)` is transport along
a path and `a` is the connection variation, its derivative is a single integral of
`U(t,u)a(u)U(u,s)` …  A second Taylor expansion gives the derivative of each displayed remainder,
bounded by `Ch`."

Generic infrastructure (no renewal notions), for a complete normed real algebra `𝔸` with `‖1‖ = 1`.
The device is the **dual-number algebra** `𝔻 = 𝔸[ε]/(ε²) = TrivSqZeroExt 𝔸 𝔸` with the `ℓ¹` norm
`‖x + εy‖ = ‖x‖ + ‖y‖` (Mathlib's `TrivSqZeroExt.instL1NormedAlgebra`), itself a complete normed
real algebra with `‖1‖ = 1`, so that **every value-level transport/plaquette estimate of
`TransportPlaquetteConsistency` applies verbatim in `𝔻`** and its `ε`-part is the first variation.

* `IsTransport.dual_fst`, `IsTransport.hasDerivWithinAt_dual_snd`: a transport `Û` of the dual
  coefficient `ω + εα` has `fst Û` a transport of `ω` and `V = snd Û` solving the variational
  equation `V' = -(ωV + αU)`.
* `hasDerivAt_transport_param` (**differentiability of transports in the connection**): if `U_t`
  is the transport of `ω + tα` (all with `U_t(0) = 1`), then `t ↦ U_t(h)` is differentiable at
  `t = 0` with derivative `snd Û(h)` (Grönwall on `U_t - U - tV`, which solves
  `R' = -(ω + tα)R - t²αV`).
* `hasDerivAt_backwardLink`, `hasDerivAt_forwardLink`: the edge links of
  `TransportPlaquetteConsistency` along the connection line `A + t a` are differentiable at
  `t = 0`, with derivative the `ε`-part of the link of the dual connection `A + εa`.
* `norm_snd_backwardLink_sub_le` (**the edge expansion after one gauge variation**):
  `‖δU_μ(x)[a] - h a_μ(x)‖ ≤ C h²` (the first-order edge expansion `U = I + hA + O(h²)` of the
  paper, differentiated in the connection), obtained from `norm_backwardLink_sub_le` in `𝔻`.
* `hasDerivAt_higgsLink_gauge`, `norm_higgsLink_gauge_variation_sub_le`: the gauge variation of
  the comparison Higgs link `K^h = h⁻¹(U_μ(x)H(x+he_μ) - H(x))` is
  `δK^h[a] = h⁻¹ δU_μ(x)[a] H(x+he_μ) = a_μ(x)H(x) + O(h)`.
* `hasDerivAt_linkPlaquette`, `norm_snd_linkPlaquette_sub_le` (**the plaquette after one gauge
  variation**): the link plaquette `U_μ(x)U_ν(x+he_μ)U_μ(x+he_ν)⁻¹U_ν(x)⁻¹` is differentiable along
  `A + t a` with derivative the `ε`-part of the dual plaquette, and
  `δU_{μν}[a] = h² δ𝔽_{μν} + O(h³)`, `δ𝔽_{μν} = ∂_μa_ν - ∂_νa_μ + [A_μ,a_ν] + [a_μ,A_ν]`
  (`norm_linkPlaquette_sub_curvature_le` in the dual numbers, with derivatives
  `dualDeriv` of the dual connection).

Not covered here: the variation of the plaquette logarithm, the metric (coframe) variations of the
spin connection, and the assembly of `eq:mesh-C1` (which needs the smooth comparison
reconstruction `𝒥_h`).
-/

open Set Filter Topology Asymptotics
open scoped NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.TransportGaugeVariation

open PathOrderedExp TransportPlaquetteConsistency TrivSqZeroExt

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- The dual numbers `𝔸[ε]/(ε²)`. -/
local notation "𝔻" => TrivSqZeroExt 𝔸 𝔸

/-! ### Dual numbers -/

section Dual

/-- `x + ε y`. -/
def dual (x y : 𝔸) : 𝔻 := inl x + inr y

@[simp] theorem dual_fst (x y : 𝔸) : (dual x y).fst = x := by simp [dual]

@[simp] theorem dual_snd (x y : 𝔸) : (dual x y).snd = y := by simp [dual]

theorem norm_dual (x y : 𝔸) : ‖dual x y‖ = ‖x‖ + ‖y‖ := by
  rw [norm_def, dual_fst, dual_snd]

theorem neg_dual (x y : 𝔸) : -dual x y = dual (-x) (-y) := by
  ext <;> simp

theorem norm_fst_le (z : 𝔻) : ‖z.fst‖ ≤ ‖z‖ := by
  rw [norm_def]; linarith [norm_nonneg z.snd]

theorem norm_snd_le (z : 𝔻) : ‖z.snd‖ ≤ ‖z‖ := by
  rw [norm_def]; linarith [norm_nonneg z.fst]

/-- `fst` as a continuous linear map. -/
def fstL : 𝔻 →L[ℝ] 𝔸 :=
  ⟨{ toFun := fun z => z.fst, map_add' := fst_add, map_smul' := fun c z => fst_smul c z },
    TrivSqZeroExt.continuous_fst⟩

/-- `snd` as a continuous linear map. -/
def sndL : 𝔻 →L[ℝ] 𝔸 :=
  ⟨{ toFun := fun z => z.snd, map_add' := snd_add, map_smul' := fun c z => snd_smul c z },
    TrivSqZeroExt.continuous_snd⟩

@[simp] theorem fstL_apply (z : 𝔻) : fstL z = z.fst := rfl
@[simp] theorem sndL_apply (z : 𝔻) : sndL z = z.snd := rfl

theorem snd_mul' (z w : 𝔻) : (z * w).snd = z.fst * w.snd + z.snd * w.fst := by
  rw [snd_mul, smul_eq_mul, op_smul_eq_mul]

theorem fst_mul' (z w : 𝔻) : (z * w).fst = z.fst * w.fst := fst_mul z w

end Dual

/-! ### Transports of dual coefficients -/

section DualTransport

variable {ω α : ℝ → 𝔸} {a b : ℝ} {Û : ℝ → TrivSqZeroExt 𝔸 𝔸}

theorem IsTransport.dual_fst (hU : IsTransport (fun t => dual (ω t) (α t)) a b Û) :
    IsTransport ω a b (fun t => (Û t).fst) := by
  intro t ht
  have := fstL.hasFDerivAt.comp_hasDerivWithinAt t (hU t ht)
  simpa [Function.comp_def, fst_mul'] using this

theorem IsTransport.hasDerivWithinAt_dual_snd
    (hU : IsTransport (fun t => dual (ω t) (α t)) a b Û) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun t => (Û t).snd) (-(ω t * (Û t).snd + α t * (Û t).fst)) (Icc a b) t := by
  have := sndL.hasFDerivAt.comp_hasDerivWithinAt t (hU t ht)
  simpa [Function.comp_def, snd_mul'] using this

/-- `gronwallBound 0 K ε x ≤ ε x e^{Kx}` for `K, ε, x ≥ 0`. -/
theorem gronwallBound_zero_le {K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    gronwallBound 0 K ε x ≤ ε * x * Real.exp (K * x) := by
  rcases hK.eq_or_lt with h0 | hpos
  · subst h0
    simp only [gronwallBound_K0, zero_add, zero_mul, Real.exp_zero, mul_one, le_refl]
  · rw [gronwallBound_of_K_ne_0 hpos.ne']
    simp only [zero_mul, zero_add]
    have h1 := PathOrderedExp.exp_sub_one_le_mul_exp (K * x)
    calc ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε * x * Real.exp (K * x) := by field_simp

/-- **Transports are differentiable in the connection.**  Let `U_t` be the transport of
`ω + tα` on `[0,h]` with `U_t(0) = 1` (for every `t`) and `Û` the transport of the dual
coefficient `ω + εα` with `Û(0) = 1`.  Then `U_0 = fst Û` on `[0,h]` and `t ↦ U_t(h)` has
derivative `snd Û(h)` at `t = 0`. -/
theorem hasDerivAt_transport_param {h Kω Kα : ℝ} (hh : 0 ≤ h)
    (hKω : ∀ s ∈ Icc 0 h, ‖ω s‖ ≤ Kω) (hKα : ∀ s ∈ Icc 0 h, ‖α s‖ ≤ Kα)
    (U : ℝ → ℝ → 𝔸) (hU : ∀ t, IsTransport (fun s => ω s + t • α s) 0 h (U t))
    (hU0 : ∀ t, U t 0 = 1)
    (hÛ : IsTransport (fun s => dual (ω s) (α s)) 0 h Û) (hÛ0 : Û 0 = 1) :
    (Û h).fst = U 0 h ∧ HasDerivAt (fun t => U t h) (Û h).snd 0 := by
  have hKω0 : 0 ≤ Kω := (norm_nonneg _).trans (hKω 0 ⟨le_rfl, hh⟩)
  have hKα0 : 0 ≤ Kα := (norm_nonneg _).trans (hKα 0 ⟨le_rfl, hh⟩)
  -- the zeroth component
  have hfst : IsTransport ω 0 h (fun s => (Û s).fst) := IsTransport.dual_fst hÛ
  have hU0' : IsTransport ω 0 h (U 0) := by simpa using hU 0
  have heq : EqOn (U 0) (fun s => (Û s).fst) (Icc 0 h) :=
    transport_unique hKω hU0' hfst (by simp [hU0, hÛ0])
  refine ⟨(heq ⟨hh, le_rfl⟩).symm, ?_⟩
  -- the bound on the variation `V = snd Û`
  set Vb : ℝ := Real.exp ((Kω + Kα) * h)
  have hKd : ∀ s ∈ Icc 0 h, ‖dual (ω s) (α s)‖ ≤ Kω + Kα := fun s hs => by
    rw [norm_dual]; exact add_le_add (hKω s hs) (hKα s hs)
  have hVb : ∀ s ∈ Icc 0 h, ‖(Û s).snd‖ ≤ Vb := by
    intro s hs
    have h1 := norm_transport_le hKd hÛ s hs
    rw [hÛ0, norm_one, one_mul, sub_zero] at h1
    refine (norm_snd_le _).trans (h1.trans (Real.exp_le_exp.2 ?_))
    exact mul_le_mul_of_nonneg_left hs.2 (by positivity)
  -- the remainder estimate
  have hR : ∀ t : ℝ, |t| ≤ 1 → ‖U t h - U 0 h - t • (Û h).snd‖ ≤
      (Kα * Vb * h * Real.exp ((Kω + Kα) * h)) * t ^ 2 := by
    intro t ht
    set R : ℝ → 𝔸 := fun s => U t s - (Û s).fst - t • (Û s).snd with hRdef
    have hcont : ContinuousOn R (Icc 0 h) :=
      (((hU t).continuousOn.sub hfst.continuousOn).sub
        ((TrivSqZeroExt.continuous_snd.comp_continuousOn hÛ.continuousOn).const_smul t))
    have hderiv : ∀ s ∈ Icc 0 h, HasDerivWithinAt R
        (-((ω s + t • α s) * R s) - t ^ 2 • (α s * (Û s).snd)) (Icc 0 h) s := by
      intro s hs
      have h1 := hU t s hs
      have h2 := hfst s hs
      have h3 := (IsTransport.hasDerivWithinAt_dual_snd hÛ hs).const_smul t
      refine ((h1.sub h2).sub h3).congr_deriv ?_
      simp only [hRdef, smul_add, smul_neg, mul_sub, sub_mul, add_mul, mul_add, smul_mul_assoc,
        mul_smul_comm, smul_smul, sq]
      abel
    have hderiv' : ∀ s ∈ Ico 0 h, HasDerivWithinAt R
        (-((ω s + t • α s) * R s) - t ^ 2 • (α s * (Û s).snd)) (Ici s) s := by
      intro s hs
      have hmem : Icc 0 h ∈ 𝓝[≥] s :=
        Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)
      exact (hderiv s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin hmem
    have hbound : ∀ s ∈ Ico 0 h, ‖-((ω s + t • α s) * R s) - t ^ 2 • (α s * (Û s).snd)‖ ≤
        (Kω + Kα) * ‖R s‖ + t ^ 2 * (Kα * Vb) := by
      intro s hs
      have hs' := Ico_subset_Icc_self hs
      have hωt : ‖ω s + t • α s‖ ≤ Kω + Kα := by
        refine (norm_add_le _ _).trans (add_le_add (hKω s hs') ?_)
        rw [norm_smul, Real.norm_eq_abs]
        calc |t| * ‖α s‖ ≤ 1 * Kα := mul_le_mul ht (hKα s hs') (norm_nonneg _) zero_le_one
          _ = Kα := one_mul _
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_neg]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hωt (norm_nonneg _))
      · rw [norm_smul, Real.norm_eq_abs, abs_pow, sq_abs]
        refine mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans ?_) (by positivity)
        exact mul_le_mul (hKα s hs') (hVb s hs') (norm_nonneg _) hKα0
    have hR0 : ‖R 0‖ ≤ 0 := by
      simp [hRdef, hU0, hÛ0]
    have hG := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv' hR0 hbound h
      ⟨hh, le_rfl⟩
    rw [sub_zero] at hG
    have hG' := hG.trans (gronwallBound_zero_le (by positivity) (by positivity) hh)
    have hRh : R h = U t h - U 0 h - t • (Û h).snd := by
      simp only [hRdef, heq ⟨hh, le_rfl⟩]
    rw [← hRh]
    refine hG'.trans (le_of_eq ?_)
    ring
  -- conclude
  rw [hasDerivAt_iff_isLittleO]
  have hO : (fun t : ℝ => U t h - U 0 h - (t - 0) • (Û h).snd) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine IsBigO.of_bound (Kα * Vb * h * Real.exp ((Kω + Kα) * h)) ?_
    have hI : Set.Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [hI] with t ht
    have ht' : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
    rw [sub_zero, Real.norm_eq_abs (t ^ 2), abs_of_nonneg (sq_nonneg t)]
    exact hR t ht'
  simpa using hO.trans_isLittleO (isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num))

end DualTransport


/-! ### The edge links along a connection line -/

section Links

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dual_sub (x y x' y' : 𝔸) : dual x y - dual x' y' = dual (x - x') (y - y') := by
  ext <;> simp

theorem continuous_dual {A a : E → 𝔸} (hA : Continuous A) (ha : Continuous a) :
    Continuous fun y => dual (A y) (a y) :=
  (TrivSqZeroExt.continuous_inl.comp hA).add (TrivSqZeroExt.continuous_inr.comp ha)

theorem norm_line_le {A a : E → 𝔸} {K Ka : ℝ} (hK : ∀ y, ‖A y‖ ≤ K) (hKa : ∀ y, ‖a y‖ ≤ Ka)
    (t : ℝ) (y : E) : ‖(A + t • a) y‖ ≤ K + |t| * Ka := by
  refine (norm_add_le _ _).trans (add_le_add (hK y) ?_)
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hKa y) (abs_nonneg t)

/-- **The backward edge link is differentiable in the connection**: along the line `A + t a`,
`t ↦ U_μ(x)[A + t a]` has derivative at `t = 0` the `ε`-part of the backward link of the dual
connection `A + εa`, whose `1`-part is the link of `A`. -/
theorem hasDerivAt_backwardLink {A a : E → 𝔸} (hA : Continuous A) (ha : Continuous a) {K Ka : ℝ}
    (hK : ∀ y, ‖A y‖ ≤ K) (hKa : ∀ y, ‖a y‖ ≤ Ka) (e x : E) {h : ℝ} (hh : 0 ≤ h) :
    (backwardLink (fun y => dual (A y) (a y)) e x h).fst = backwardLink A e x h ∧
      HasDerivAt (fun t : ℝ => backwardLink (A + t • a) e x h)
        (backwardLink (fun y => dual (A y) (a y)) e x h).snd 0 := by
  have hex : ∀ t : ℝ, ∃ U : ℝ → 𝔸, U 0 = 1 ∧
      IsTransport (fun s => -(A + t • a) (x + (h - s) • e)) 0 h U ∧
      backwardLink (A + t • a) e x h = U h := fun t =>
    exists_backwardLink (hA.add (ha.const_smul t)) (norm_line_le hK hKa t) e x hh
  choose U hU0 hU hUe using hex
  have hKd : ∀ y, ‖dual (A y) (a y)‖ ≤ K + Ka := fun y => by
    rw [norm_dual]; exact add_le_add (hK y) (hKa y)
  obtain ⟨Û, hÛ0, hÛ, hÛe⟩ := exists_backwardLink (A := fun y => dual (A y) (a y))
    (continuous_dual hA ha) hKd e x hh
  have hU' : ∀ t, IsTransport (fun s => -A (x + (h - s) • e) + t • -a (x + (h - s) • e)) 0 h
      (U t) := fun t => by
    have e1 : (fun s => -(A + t • a) (x + (h - s) • e)) =
        fun s => -A (x + (h - s) • e) + t • -a (x + (h - s) • e) := by
      funext s; simp only [Pi.add_apply, Pi.smul_apply, smul_neg, neg_add]
    rw [← e1]; exact hU t
  have hÛ' : IsTransport (fun s => dual (-A (x + (h - s) • e)) (-a (x + (h - s) • e))) 0 h Û := by
    have e1 : (fun s => -(fun y => dual (A y) (a y)) (x + (h - s) • e)) =
        fun s => dual (-A (x + (h - s) • e)) (-a (x + (h - s) • e)) := by
      funext s; exact neg_dual _ _
    rw [← e1]; exact hÛ
  obtain ⟨h1, h2⟩ := hasDerivAt_transport_param (ω := fun s => -A (x + (h - s) • e))
    (α := fun s => -a (x + (h - s) • e)) (Kω := K) (Kα := Ka) hh
    (fun s _ => by rw [norm_neg]; exact hK _) (fun s _ => by rw [norm_neg]; exact hKa _)
    U hU' hU0 hÛ' hÛ0
  have hA0 : backwardLink A e x h = U 0 h := by
    rw [← hUe 0]; congr 1; funext y; simp
  refine ⟨by rw [hÛe, hA0, h1], ?_⟩
  rw [hÛe]
  exact h2.congr_of_eventuallyEq (Eventually.of_forall fun t => hUe t)

/-- **The forward edge link is differentiable in the connection** (the inverse links of the
plaquette). -/
theorem hasDerivAt_forwardLink {A a : E → 𝔸} (hA : Continuous A) (ha : Continuous a) {K Ka : ℝ}
    (hK : ∀ y, ‖A y‖ ≤ K) (hKa : ∀ y, ‖a y‖ ≤ Ka) (e x : E) {h : ℝ} (hh : 0 ≤ h) :
    (forwardLink (fun y => dual (A y) (a y)) e x h).fst = forwardLink A e x h ∧
      HasDerivAt (fun t : ℝ => forwardLink (A + t • a) e x h)
        (forwardLink (fun y => dual (A y) (a y)) e x h).snd 0 := by
  have hex : ∀ t : ℝ, ∃ U : ℝ → 𝔸, U 0 = 1 ∧
      IsTransport (fun s => (A + t • a) (x + s • e)) 0 h U ∧
      forwardLink (A + t • a) e x h = U h := fun t =>
    exists_forwardLink (hA.add (ha.const_smul t)) (norm_line_le hK hKa t) e x hh
  choose U hU0 hU hUe using hex
  have hKd : ∀ y, ‖dual (A y) (a y)‖ ≤ K + Ka := fun y => by
    rw [norm_dual]; exact add_le_add (hK y) (hKa y)
  obtain ⟨Û, hÛ0, hÛ, hÛe⟩ := exists_forwardLink (A := fun y => dual (A y) (a y))
    (continuous_dual hA ha) hKd e x hh
  obtain ⟨h1, h2⟩ := hasDerivAt_transport_param (ω := fun s => A (x + s • e))
    (α := fun s => a (x + s • e)) (Kω := K) (Kα := Ka) hh
    (fun s _ => hK _) (fun s _ => hKa _) U hU hU0 hÛ hÛ0
  have hA0 : forwardLink A e x h = U 0 h := by
    rw [← hUe 0]; congr 1; funext y; simp
  refine ⟨by rw [hÛe, hA0, h1], ?_⟩
  rw [hÛe]
  exact h2.congr_of_eventuallyEq (Eventually.of_forall fun t => hUe t)

/-- **The edge expansion after one gauge variation**: the first variation
`δU_μ(x)[a] = d/dt U_μ(x)[A + t a]|₀` of the backward link satisfies
`‖δU_μ(x)[a] - h a(x)‖ ≤ ((K + K_a)² e^{K + K_a} + Λ + Λ_a) h²` for `Λ`-, `Λ_a`-Lipschitz
connection and variation bounded by `K`, `K_a` (`norm_backwardLink_sub_le` in the dual
numbers). -/
theorem norm_snd_backwardLink_sub_le {A a : E → 𝔸} {K Ka Λ Λa : ℝ} (hΛ : 0 ≤ Λ) (hΛa : 0 ≤ Λa)
    (hA : ∀ y z, ‖A y - A z‖ ≤ Λ * ‖y - z‖) (ha : ∀ y z, ‖a y - a z‖ ≤ Λa * ‖y - z‖)
    (hK : ∀ y, ‖A y‖ ≤ K) (hKa : ∀ y, ‖a y‖ ≤ Ka) {e : E} (he : ‖e‖ ≤ 1) (x : E) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ‖(backwardLink (fun y => dual (A y) (a y)) e x h).snd - h • a x‖ ≤
      ((K + Ka) ^ 2 * Real.exp (K + Ka) + (Λ + Λa)) * h ^ 2 := by
  have hb := norm_backwardLink_sub_le (A := fun y => dual (A y) (a y)) (K := K + Ka)
    (Λ := Λ + Λa) (by positivity) (fun y z => by
      rw [dual_sub, norm_dual, add_mul]; exact add_le_add (hA y z) (ha y z))
    (fun y => by rw [norm_dual]; exact add_le_add (hK y) (hKa y)) he x hh hh1
  refine le_trans ?_ hb
  have e1 : (backwardLink (fun y => dual (A y) (a y)) e x h).snd - h • a x =
      (backwardLink (fun y => dual (A y) (a y)) e x h - (1 + h • dual (A x) (a x))).snd := by
    simp
  rw [e1]
  exact norm_snd_le _

end Links

/-! ### The gauge variation of the comparison Higgs link -/

section Higgs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [Nontrivial F]

/-- The gauge variation of the comparison Higgs link
`K^h_μ(x) = h⁻¹(U_μ(x) H(x + he_μ) - H(x))` along `A + t a` is `h⁻¹ δU_μ(x)[a] H(x + he_μ)`. -/
theorem hasDerivAt_higgsLink_gauge {A a : E → F →L[ℝ] F} (hA : Continuous A) (ha : Continuous a)
    {K Ka : ℝ} (hK : ∀ y, ‖A y‖ ≤ K) (hKa : ∀ y, ‖a y‖ ≤ Ka) (H : E → F) (e x : E) {h : ℝ}
    (hh : 0 ≤ h) :
    HasDerivAt (fun t : ℝ => h⁻¹ • (backwardLink (A + t • a) e x h (H (x + h • e)) - H x))
      (h⁻¹ • (backwardLink (fun y => dual (A y) (a y)) e x h).snd (H (x + h • e))) 0 := by
  have hU := (hasDerivAt_backwardLink hA ha hK hKa e x hh).2
  have := (((ContinuousLinearMap.apply ℝ F (H (x + h • e))).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hU).sub_const (H x)).const_smul h⁻¹
  exact this

/-- **The Higgs link after one gauge variation**: `δK^h_μ(x)[a] = a_μ(x) H(x) + O(h)`, with
`‖H‖ ≤ B` and `‖H(x + he) - H(x)‖ ≤ L₁ h`. -/
theorem norm_higgsLink_gauge_variation_sub_le {A a : E → F →L[ℝ] F} {K Ka Λ Λa B L₁ : ℝ}
    (hΛ : 0 ≤ Λ) (hΛa : 0 ≤ Λa)
    (hA : ∀ y z, ‖A y - A z‖ ≤ Λ * ‖y - z‖) (ha : ∀ y z, ‖a y - a z‖ ≤ Λa * ‖y - z‖)
    (hK : ∀ y, ‖A y‖ ≤ K) (hKa : ∀ y, ‖a y‖ ≤ Ka) {H : E → F} (hB : ∀ y, ‖H y‖ ≤ B)
    {e : E} (he : ‖e‖ ≤ 1) (x : E) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hL : ‖H (x + h • e) - H x‖ ≤ L₁ * h) :
    ‖h⁻¹ • (backwardLink (fun y => dual (A y) (a y)) e x h).snd (H (x + h • e)) - a x (H x)‖ ≤
      (((K + Ka) ^ 2 * Real.exp (K + Ka) + (Λ + Λa)) * B + Ka * L₁) * h := by
  set δU := (backwardLink (fun y => dual (A y) (a y)) e x h).snd
  have h1 := norm_snd_backwardLink_sub_le hΛ hΛa hA ha hK hKa he x hh.le hh1
  have e1 : h⁻¹ • δU (H (x + h • e)) - a x (H x) =
      h⁻¹ • (δU - h • a x) (H (x + h • e)) + a x (H (x + h • e) - H x) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_sub, smul_smul,
      inv_mul_cancel₀ hh.ne', one_smul, map_sub]
    abel
  rw [e1]
  refine (norm_add_le _ _).trans ?_
  have t1 : ‖h⁻¹ • (δU - h • a x) (H (x + h • e))‖ ≤
      ((K + Ka) ^ 2 * Real.exp (K + Ka) + (Λ + Λa)) * B * h := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hh.le)]
    calc h⁻¹ * ‖(δU - h • a x) (H (x + h • e))‖
        ≤ h⁻¹ * (‖δU - h • a x‖ * ‖H (x + h • e)‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by positivity)
      _ ≤ h⁻¹ * ((((K + Ka) ^ 2 * Real.exp (K + Ka) + (Λ + Λa)) * h ^ 2) * B) := by
          gcongr
          exact hB _
      _ = ((K + Ka) ^ 2 * Real.exp (K + Ka) + (Λ + Λa)) * B * h := by
          field_simp
  have t2 : ‖a x (H (x + h • e) - H x)‖ ≤ Ka * L₁ * h := by
    calc ‖a x (H (x + h • e) - H x)‖ ≤ ‖a x‖ * ‖H (x + h • e) - H x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ Ka * (L₁ * h) := mul_le_mul (hKa x) hL (norm_nonneg _)
          ((norm_nonneg _).trans (hKa x))
      _ = Ka * L₁ * h := by ring
  linarith

end Higgs

/-! ### The plaquette after one gauge variation -/

section Plaquette

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Product rule in dual-number form. -/
theorem hasDerivAt_mul_dual {f g : ℝ → 𝔸} {z w : TrivSqZeroExt 𝔸 𝔸}
    (hf : HasDerivAt f z.snd 0) (hf0 : f 0 = z.fst) (hg : HasDerivAt g w.snd 0)
    (hg0 : g 0 = w.fst) :
    HasDerivAt (fun t => f t * g t) (z * w).snd 0 ∧ f 0 * g 0 = (z * w).fst := by
  refine ⟨(hf.mul hg).congr_deriv ?_, by rw [hf0, hg0, fst_mul']⟩
  rw [snd_mul', hf0, hg0, add_comm]

/-- `inl` as a continuous linear map. -/
def inlL : 𝔸 →L[ℝ] TrivSqZeroExt 𝔸 𝔸 :=
  ⟨{ toFun := inl, map_add' := fun x y => inl_add (M := 𝔸) x y,
      map_smul' := fun c x => inl_smul (M := 𝔸) c x }, TrivSqZeroExt.continuous_inl⟩

/-- `inr` as a continuous linear map. -/
def inrL : 𝔸 →L[ℝ] TrivSqZeroExt 𝔸 𝔸 :=
  ⟨{ toFun := inr, map_add' := fun x y => inr_add (R := 𝔸) x y,
      map_smul' := fun c x => inr_smul (R := 𝔸) c x }, TrivSqZeroExt.continuous_inr⟩

theorem norm_inlL_le : ‖(inlL : 𝔸 →L[ℝ] TrivSqZeroExt 𝔸 𝔸)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    show ‖(inl z : TrivSqZeroExt 𝔸 𝔸)‖ ≤ 1 * ‖z‖
    rw [norm_inl, one_mul]

theorem norm_inrL_le : ‖(inrL : 𝔸 →L[ℝ] TrivSqZeroExt 𝔸 𝔸)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    show ‖(inr z : TrivSqZeroExt 𝔸 𝔸)‖ ≤ 1 * ‖z‖
    rw [norm_inr, one_mul]

/-- The derivative field of a dual connection `A + εa`. -/
def dualDeriv (T S : E →L[ℝ] 𝔸) : E →L[ℝ] TrivSqZeroExt 𝔸 𝔸 := inlL.comp T + inrL.comp S

theorem dualDeriv_apply (T S : E →L[ℝ] 𝔸) (u : E) : dualDeriv T S u = dual (T u) (S u) := rfl

theorem norm_dualDeriv_le (T S : E →L[ℝ] 𝔸) : ‖dualDeriv T S‖ ≤ ‖T‖ + ‖S‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right norm_inlL_le (norm_nonneg T))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right norm_inrL_le (norm_nonneg S))

theorem dualDeriv_sub (T S T' S' : E →L[ℝ] 𝔸) :
    dualDeriv T S - dualDeriv T' S' = dualDeriv (T - T') (S - S') := by
  simp only [dualDeriv, ContinuousLinearMap.comp_sub]
  abel

theorem hasFDerivAt_dual {A a : E → 𝔸} {A' a' : E →L[ℝ] 𝔸} {y : E} (hA : HasFDerivAt A A' y)
    (ha : HasFDerivAt a a' y) :
    HasFDerivAt (fun y => dual (A y) (a y)) (dualDeriv A' a') y :=
  (inlL.hasFDerivAt.comp y hA).add (inrL.hasFDerivAt.comp y ha)

/-- The link plaquette `U_μ(x)U_ν(x+he_μ)U_μ(x+he_ν)⁻¹U_ν(x)⁻¹` of a connection pair. -/
def linkPlaquette {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [NormOneClass 𝔅]
    [CompleteSpace 𝔅] (Aμ Aν : E → 𝔅) (eμ eν x : E) (h : ℝ) : 𝔅 :=
  backwardLink Aμ eμ x h * backwardLink Aν eν (x + h • eμ) h *
    Ring.inverse (backwardLink Aμ eμ (x + h • eν) h) * Ring.inverse (backwardLink Aν eν x h)

/-- **The plaquette is differentiable in the connection**, with derivative the `ε`-part of the
plaquette of the dual connection `A + εa`. -/
theorem hasDerivAt_linkPlaquette {Aμ Aν aμ aν : E → 𝔸} (hAμ : Continuous Aμ)
    (hAν : Continuous Aν) (haμ : Continuous aμ) (haν : Continuous aν) {K Ka : ℝ}
    (hKμ : ∀ y, ‖Aμ y‖ ≤ K) (hKν : ∀ y, ‖Aν y‖ ≤ K) (hKaμ : ∀ y, ‖aμ y‖ ≤ Ka)
    (hKaν : ∀ y, ‖aν y‖ ≤ Ka) (eμ eν x : E) {h : ℝ} (hh : 0 ≤ h) :
    HasDerivAt (fun t : ℝ => linkPlaquette (Aμ + t • aμ) (Aν + t • aν) eμ eν x h)
      (linkPlaquette (fun y => dual (Aμ y) (aμ y)) (fun y => dual (Aν y) (aν y)) eμ eν x h).snd
      0 := by
  have hKd : ∀ {A a : E → 𝔸}, (∀ y, ‖A y‖ ≤ K) → (∀ y, ‖a y‖ ≤ Ka) →
      ∀ y, ‖dual (A y) (a y)‖ ≤ K + Ka := fun hA ha y => by
    rw [norm_dual]; exact add_le_add (hA y) (ha y)
  -- rewrite the inverse links as forward links, for every `t` and for the dual connection
  have hinv : ∀ t : ℝ, linkPlaquette (Aμ + t • aμ) (Aν + t • aν) eμ eν x h =
      backwardLink (Aμ + t • aμ) eμ x h * backwardLink (Aν + t • aν) eν (x + h • eμ) h *
        forwardLink (Aμ + t • aμ) eμ (x + h • eν) h * forwardLink (Aν + t • aν) eν x h := by
    intro t
    rw [linkPlaquette, ring_inverse_backwardLink (hAμ.add (haμ.const_smul t))
      (norm_line_le hKμ hKaμ t) eμ _ hh, ring_inverse_backwardLink (hAν.add (haν.const_smul t))
      (norm_line_le hKν hKaν t) eν _ hh]
  have hinvD : linkPlaquette (fun y => dual (Aμ y) (aμ y)) (fun y => dual (Aν y) (aν y))
      eμ eν x h =
      backwardLink (fun y => dual (Aμ y) (aμ y)) eμ x h *
        backwardLink (fun y => dual (Aν y) (aν y)) eν (x + h • eμ) h *
        forwardLink (fun y => dual (Aμ y) (aμ y)) eμ (x + h • eν) h *
        forwardLink (fun y => dual (Aν y) (aν y)) eν x h := by
    rw [linkPlaquette, ring_inverse_backwardLink (continuous_dual hAμ haμ) (hKd hKμ hKaμ) eμ _ hh,
      ring_inverse_backwardLink (continuous_dual hAν haν) (hKd hKν hKaν) eν _ hh]
  obtain ⟨b1, d1⟩ := hasDerivAt_backwardLink hAμ haμ hKμ hKaμ eμ x hh
  obtain ⟨b2, d2⟩ := hasDerivAt_backwardLink hAν haν hKν hKaν eν (x + h • eμ) hh
  obtain ⟨b3, d3⟩ := hasDerivAt_forwardLink hAμ haμ hKμ hKaμ eμ (x + h • eν) hh
  obtain ⟨b4, d4⟩ := hasDerivAt_forwardLink hAν haν hKν hKaν eν x hh
  have z : ∀ {A : E → 𝔸} (a : E → 𝔸), A + (0 : ℝ) • a = A := fun a => by simp
  obtain ⟨m12, v12⟩ := hasDerivAt_mul_dual d1 (by rw [z, ← b1]) d2 (by rw [z, ← b2])
  obtain ⟨m123, v123⟩ := hasDerivAt_mul_dual m12 v12 d3 (by rw [z, ← b3])
  obtain ⟨m, -⟩ := hasDerivAt_mul_dual m123 v123 d4 (by rw [z, ← b4])
  rw [hinvD]
  exact m.congr_of_eventuallyEq (Eventually.of_forall fun t => hinv t)

/-- **The plaquette after one gauge variation**: with connection components `A_μ, A_ν` and
variations `a_μ, a_ν` bounded by `K`, `K_a`, with derivatives bounded by `D`, `D_a` and
`L`-, `L_a`-Lipschitz, the first variation `δU_{μν}` of the link plaquette satisfies
`‖δU_{μν}(x)[a] - h² δ𝔽_{μν}(x)‖ ≤ C h³`, where
`δ𝔽_{μν} = ∂_μa_ν - ∂_νa_μ + [A_μ, a_ν] + [a_μ, A_ν]` is the variation of the curvature
(`norm_linkPlaquette_sub_curvature_le` in the dual numbers). -/
theorem norm_snd_linkPlaquette_sub_le {Aμ Aν aμ aν : E → 𝔸} {Aμ' Aν' aμ' aν' : E → E →L[ℝ] 𝔸}
    {K Ka D Da L La : ℝ} (hAμ : ∀ y, HasFDerivAt Aμ (Aμ' y) y)
    (hAν : ∀ y, HasFDerivAt Aν (Aν' y) y) (haμ : ∀ y, HasFDerivAt aμ (aμ' y) y)
    (haν : ∀ y, HasFDerivAt aν (aν' y) y)
    (hKμ : ∀ y, ‖Aμ y‖ ≤ K) (hKν : ∀ y, ‖Aν y‖ ≤ K) (hKaμ : ∀ y, ‖aμ y‖ ≤ Ka)
    (hKaν : ∀ y, ‖aν y‖ ≤ Ka) (hDμ : ∀ y, ‖Aμ' y‖ ≤ D) (hDν : ∀ y, ‖Aν' y‖ ≤ D)
    (hDaμ : ∀ y, ‖aμ' y‖ ≤ Da) (hDaν : ∀ y, ‖aν' y‖ ≤ Da)
    (hLμ : ∀ y z, ‖Aμ' y - Aμ' z‖ ≤ L * ‖y - z‖) (hLν : ∀ y z, ‖Aν' y - Aν' z‖ ≤ L * ‖y - z‖)
    (hLaμ : ∀ y z, ‖aμ' y - aμ' z‖ ≤ La * ‖y - z‖) (hLaν : ∀ y z, ‖aν' y - aν' z‖ ≤ La * ‖y - z‖)
    {eμ eν : E} (heμ : ‖eμ‖ ≤ 1) (heν : ‖eν‖ ≤ 1) (hL : 0 ≤ L) (hLa : 0 ≤ La) (x : E) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ‖(linkPlaquette (fun y => dual (Aμ y) (aμ y)) (fun y => dual (Aν y) (aν y)) eμ eν x h).snd -
        h ^ 2 • (aν' x eμ - aμ' x eν +
          (Aμ x * aν x + aμ x * Aν x - Aν x * aμ x - aν x * Aμ x))‖ ≤
      plaquetteConst (max (K + Ka) (D + Da)) (K + Ka) (4 * (L + La)) * h ^ 3 := by
  have hb := norm_linkPlaquette_sub_curvature_le (Aμ := fun y => dual (Aμ y) (aμ y))
    (Aν := fun y => dual (Aν y) (aν y)) (Aμ' := fun y => dualDeriv (Aμ' y) (aμ' y))
    (Aν' := fun y => dualDeriv (Aν' y) (aν' y)) (K := K + Ka) (D := D + Da) (L := L + La)
    (fun y => hasFDerivAt_dual (hAμ y) (haμ y)) (fun y => hasFDerivAt_dual (hAν y) (haν y))
    (fun y => by rw [norm_dual]; exact add_le_add (hKμ y) (hKaμ y))
    (fun y => by rw [norm_dual]; exact add_le_add (hKν y) (hKaν y))
    (fun y => (norm_dualDeriv_le _ _).trans (add_le_add (hDμ y) (hDaμ y)))
    (fun y => (norm_dualDeriv_le _ _).trans (add_le_add (hDν y) (hDaν y)))
    (fun y z => by
      rw [dualDeriv_sub]
      refine (norm_dualDeriv_le _ _).trans ?_
      rw [add_mul]; exact add_le_add (hLμ y z) (hLaμ y z))
    (fun y z => by
      rw [dualDeriv_sub]
      refine (norm_dualDeriv_le _ _).trans ?_
      rw [add_mul]; exact add_le_add (hLν y z) (hLaν y z))
    heμ heν (by positivity) x hh hh1
  refine le_trans (le_of_eq ?_) ((norm_snd_le _).trans hb)
  congr 1
  simp only [linkPlaquette, snd_sub, snd_add, snd_one, snd_smul, dualDeriv_apply, dual_snd,
    snd_mul', dual_fst, zero_add]
  congr 1
  abel

end Plaquette
end RenewalGeometry.TransportGaugeVariation
