/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TorusBoxRestriction
import RenewalGeometry.Analysis.TorusBosonicCompactness
import RenewalGeometry.Analysis.TorusSobolevFractionalLp

/-!
# A-priori Sobolev bounds imply bosonic strong compactness on a box

Generic form (no renewal notions) of `prop:sobolev-bosonic` of the Einstein–Standard-Model
action-closure manuscript on a bounded region rendered as an open box `Q = Π (a_i, b_i)`, with the
fractional Sobolev spaces `H^s(Q)` the **restriction spaces** of `TorusBoxRestriction.lean`: a field
on `Q` is bounded in `H^s(Q)` when it agrees a.e. on `Q` with the pull-back `U ∘ chart` of periodic
functions `U` bounded in `H^s(𝕋^ι)` (torus of period `L ≥ max (b_i - a_i)` with corner `a`).

* `memW12_congr_ae`: `W^{1,2}(Ω)` is invariant under a.e. modification on `Ω`.
* `tendsto_w12_chart`: strong `H¹(𝕋^ι)` convergence of the representatives gives strong
  `W^{1,2}(Q)` convergence of the box fields (with the canonical weak gradients
  `L⁻¹ (∇U) ∘ chart`), by the restriction inequality and `hasWeakPartial_chart`.
* `eLpNorm_box_le_of_memH`: the box `L^p` bound from the torus embedding `H^s ⊂ L^p`
  (`TorusSobolevFractionalLp`).
* **`sobolev_bosonic_box`** (`prop:sobolev-bosonic`, box form): frames bounded in `H^{s_e}(Q)`
  (`s_e > max(1, d/2)`), potentials and Higgs components bounded in `H^{s_A}(Q)`, `H^{s_H}(Q)`
  (`> max(1, d/4)`) and banks in a compact set: along one subsequence `e_h → e` in `W^{1,2}(Q)` and
  in `L^∞(Q)`, `A_h → A` and `H_h → H` in `W^{1,2}(Q)` and `L⁴(Q)`, the curvatures
  `F_{A_h} = dA_h + A_h ∧ A_h → F_A` and `D_{A_h}H_h → D_AH` in `L²(Q)` (built from the weak
  gradients on `Q`), and the banks converge; on `ι = Fin 4` with `s_e = 2 + σ`, `s_A = s_H = 1 + σ`
  this is `eq:apriori-bosonic-convergence`, and `sobolev_bosonic_box_four` adds the uniform
  `L^{4+δ}(Q)` bound on `H_h`, `δ = min σ 1`.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal ContDiff Real

noncomputable section

namespace RenewalGeometry.SobolevOpen
namespace TorusChart

open TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### `W^{1,2}` under a.e. modification -/

theorem test_pd_eq_zero_off' {Ω : Set (ι → ℝ)} {φ : (ι → ℝ) → ℝ} (hφ : IsTest Ω φ) (i : ι)
    {x : ι → ℝ} (hx : x ∉ Ω) : pd φ i x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx ((hφ.pd i).subset h)

theorem test_eq_zero_off' {Ω : Set (ι → ℝ)} {φ : (ι → ℝ) → ℝ} (hφ : IsTest Ω φ)
    {x : ι → ℝ} (hx : x ∉ Ω) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hφ.subset h)

/-- `W^{1,2}(Ω)` is invariant under a.e. modification on `Ω`. -/
theorem memW12_congr_ae {Ω : Set (ι → ℝ)} (hΩ : MeasurableSet Ω) {u u' : (ι → ℝ) → ℂ}
    {g g' : ι → (ι → ℝ) → ℂ} (h : MemW12 Ω u g) (hu : u =ᵐ[volume.restrict Ω] u')
    (hg : ∀ i, g i =ᵐ[volume.restrict Ω] g' i) : MemW12 Ω u' g' := by
  refine ⟨h.memLp.ae_eq hu, fun i => (h.memLp_grad i).ae_eq (hg i), fun i φ hφ => ?_⟩
  have hu' := (ae_restrict_iff' hΩ).mp hu
  have hg' := (ae_restrict_iff' hΩ).mp (hg i)
  have e1 : ∫ x, ((pd φ i x : ℝ) : ℂ) * u' x = ∫ x, ((pd φ i x : ℝ) : ℂ) * u x := by
    refine integral_congr_ae (hu'.mono fun x hx => ?_)
    by_cases hxΩ : x ∈ Ω
    · simp only [hx hxΩ]
    · simp [test_pd_eq_zero_off' hφ i hxΩ]
  have e2 : ∫ x, ((φ x : ℝ) : ℂ) * g' i x = ∫ x, ((φ x : ℝ) : ℂ) * g i x := by
    refine integral_congr_ae (hg'.mono fun x hx => ?_)
    by_cases hxΩ : x ∈ Ω
    · simp only [hx hxΩ]
    · simp [test_eq_zero_off' hφ hxΩ]
  rw [e1, e2]
  exact h.weak i φ hφ

/-! ### Transfer from the torus to the box -/

variable {Q : Set (ι → ℝ)} {c : ι → ℝ} {L : ℝ}

theorem eLpNorm_two_sub_le_sobNorm {f g : L²(UnitAddTorus ι)} (hf : MemH 1 f) (hg : MemH 1 g) :
    eLpNorm (⇑f - ⇑g) 2 volume ≤ ENNReal.ofReal (sobNorm 1 ⇑(f - g)) := by
  rw [eLpNorm_coe_sub_eq, ← sobNorm_zero_eq_norm]
  exact ENNReal.ofReal_le_ofReal (sobNorm_mono zero_le_one (memH_Lp_sub hf hg))

theorem tendsto_L2_of_H1 {f : ℕ → L²(UnitAddTorus ι)} {f₀ : L²(UnitAddTorus ι)}
    (hf : ∀ k, MemH 1 (f k)) (hf₀ : MemH 1 f₀)
    (hconv : Tendsto (fun k => sobSq 1 ⇑(f k - f₀)) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (⇑(f k) - ⇑f₀) 2 volume) atTop (𝓝 0) := by
  have h := ENNReal.tendsto_ofReal ((Real.continuous_sqrt.tendsto 0).comp hconv)
  simp only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
    fun k => eLpNorm_two_sub_le_sobNorm (hf k) hf₀

/-- `L^p` convergence on the torus gives `L^p` convergence of the pull-backs on `Q`. -/
theorem tendsto_chart_eLpNorm {E : Type*} [NormedAddCommGroup E] {p : ℝ} (hp : 0 < p)
    (hL : 0 < L) (hQ : Q ⊆ cubeAt c L) {V : ℕ → UnitAddTorus ι → E} {V₀ : UnitAddTorus ι → E}
    (h : Tendsto (fun k => eLpNorm (V k - V₀) (ENNReal.ofReal p) volume) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((fun x => V k (chart c L x)) - fun x => V₀ (chart c L x))
      (ENNReal.ofReal p) (volume.restrict Q)) atTop (𝓝 0) := by
  have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (L ^ ((Fintype.card ι : ℝ) / p))) h
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun k => zero_le)
    fun k => eLpNorm_chart_le hL hQ (V k - V₀) hp

/-- a.e.-equal sequences have the same `L^p` limits. -/
theorem tendsto_eLpNorm_congr {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {p : ℝ≥0∞} {u v : ℕ → X → E} {u₀ v₀ : X → E} (h : ∀ k, u k =ᵐ[μ] v k)
    (h₀ : u₀ =ᵐ[μ] v₀) (hv : Tendsto (fun k => eLpNorm (v k - v₀) p μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (u k - u₀) p μ) atTop (𝓝 0) :=
  hv.congr fun k => eLpNorm_congr_ae ((h k).sub h₀).symm

/-- The canonical weak gradient on the box of a pulled-back torus function. -/
def boxGrad (c : ι → ℝ) (L : ℝ) (U : L²(UnitAddTorus ι)) : ι → (ι → ℝ) → ℂ :=
  fun i x => (L⁻¹ : ℂ) * weakDeriv i U (chart c L x)

/-- **Strong `H¹(𝕋^ι)` convergence of the representatives gives strong `W^{1,2}(Q)` convergence
of the box fields.** -/
theorem tendsto_w12_chart (hL : 0 < L) (hQ : Q ⊆ cubeAt c L) {f : ℕ → L²(UnitAddTorus ι)}
    {f₀ : L²(UnitAddTorus ι)} (hf : ∀ k, MemH 1 (f k)) (hf₀ : MemH 1 f₀)
    (hconv : Tendsto (fun k => sobSq 1 ⇑(f k - f₀)) atTop (𝓝 0)) {u : ℕ → (ι → ℝ) → ℂ}
    (hu : ∀ k, u k =ᵐ[volume.restrict Q] fun x => f k (chart c L x)) :
    Tendsto (fun k => w12Norm Q (u k - fun x => f₀ (chart c L x))
      (boxGrad c L (f k) - boxGrad c L f₀)) atTop (𝓝 0) := by
  unfold w12Norm
  rw [show (0 : ℝ≥0∞) = 0 + ∑ i : ι, 0 by simp]
  refine Tendsto.add ?_ (tendsto_finset_sum _ fun i _ => ?_)
  · have h0 : Tendsto (fun k => eLpNorm (⇑(f k) - ⇑f₀) (ENNReal.ofReal 2) volume) atTop (𝓝 0) := by
      rw [ENNReal.ofReal_ofNat]; exact tendsto_L2_of_H1 hf hf₀ hconv
    have h1 := tendsto_chart_eLpNorm (by norm_num) hL hQ h0
    rw [ENNReal.ofReal_ofNat] at h1
    exact tendsto_eLpNorm_congr hu (EventuallyEq.refl _ _) h1
  · have h0 : Tendsto (fun k => eLpNorm (⇑(weakDeriv i (f k)) - ⇑(weakDeriv i f₀))
        (ENNReal.ofReal 2) volume) atTop (𝓝 0) := by
      rw [ENNReal.ofReal_ofNat]; exact tendsto_weakDeriv hf hf₀ hconv
    have h1 := tendsto_chart_eLpNorm (by norm_num) hL hQ h0
    rw [ENNReal.ofReal_ofNat] at h1
    have h2 := ENNReal.Tendsto.const_mul (a := ‖(L⁻¹ : ℂ)‖ₑ) h1 (Or.inr enorm_ne_top)
    simp only [mul_zero] at h2
    refine h2.congr fun k => ?_
    have he : (boxGrad c L (f k) - boxGrad c L f₀) i = (L⁻¹ : ℂ) •
        ((fun x => weakDeriv i (f k) (chart c L x)) - fun x => weakDeriv i f₀ (chart c L x)) := by
      funext x
      simp only [boxGrad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
    rw [he, eLpNorm_const_smul]

/-- The box `L^p` bound: if `u = U ∘ chart` a.e. on `Q` with `U ∈ H^s(𝕋^ι)`,
`s > d(1/2 - 1/p)`, then `‖u‖_{L^p(Q)} ≤ L^{d/p} C_{p,s} ‖U‖_{H^s}`. -/
theorem eLpNorm_box_le_of_memH {p s : ℝ} (hp : 2 ≤ p)
    (hs : (Fintype.card ι : ℝ) * (1 / 2 - 1 / p) < s) (hL : 0 < L) (hQ : Q ⊆ cubeAt c L)
    {U : L²(UnitAddTorus ι)} (hU : MemH s U) {u : (ι → ℝ) → ℂ}
    (hu : u =ᵐ[volume.restrict Q] fun x => U (chart c L x)) :
    eLpNorm u (ENNReal.ofReal p) (volume.restrict Q) ≤
      ENNReal.ofReal (L ^ ((Fintype.card ι : ℝ) / p)) *
        ENNReal.ofReal (FracLp.lpConst ι p s * sobNorm s U) := by
  rw [eLpNorm_congr_ae hu]
  refine (eLpNorm_chart_le hL hQ (⇑U) (by linarith)).trans ?_
  gcongr
  exact FracLp.eLpNorm_le_of_memH_Lp hp hs U hU

/-! ### The torus extraction with membership of the limits -/

/-- The extraction step of `sobolev_bosonic_torus`, keeping the regularity of the limits
(`e₀ ∈ H^{s_e}`, `A₀ ∈ H^{s_A}`, `H₀ ∈ H^{s_H}`). -/
theorem torus_extract {Je r r' : Type*} [Fintype Je] [Fintype r] [Fintype r'] {m : ℕ}
    {se sA sH : ℝ} (hse1 : 1 < se) (hse : (Fintype.card ι : ℝ) / 2 < se) (hsA1 : 1 < sA)
    (hsA : (Fintype.card ι : ℝ) / 4 < sA) (hsH1 : 1 < sH) (hsH : (Fintype.card ι : ℝ) / 4 < sH)
    {B : ℝ} (e : ℕ → Je → L²(UnitAddTorus ι)) (A : ℕ → ι → r → r → L²(UnitAddTorus ι))
    (H : ℕ → r' → L²(UnitAddTorus ι))
    (he : ∀ k j, MemH se (e k j)) (heB : ∀ k j, sobSq se (e k j) ≤ B)
    (hA : ∀ k μ a b, MemH sA (A k μ a b)) (hAB : ∀ k μ a b, sobSq sA (A k μ a b) ≤ B)
    (hH : ∀ k a, MemH sH (H k a)) (hHB : ∀ k a, sobSq sH (H k a) ≤ B)
    (θ : ℕ → Fin m → ℝ) {Kθ : Set (Fin m → ℝ)} (hKθ : IsCompact Kθ) (hθ : ∀ k, θ k ∈ Kθ) :
    ∃ (φ : ℕ → ℕ) (e₀ : Je → L²(UnitAddTorus ι)) (A₀ : ι → r → r → L²(UnitAddTorus ι))
      (H₀ : r' → L²(UnitAddTorus ι)) (θ₀ : Fin m → ℝ) (E : ℕ → Je → C(UnitAddTorus ι, ℂ))
      (E₀ : Je → C(UnitAddTorus ι, ℂ)), StrictMono φ ∧
      (∀ j, MemH se (e₀ j)) ∧ (∀ μ a b, MemH sA (A₀ μ a b)) ∧ (∀ a, MemH sH (H₀ a)) ∧
      (∀ j, Tendsto (fun k => sobSq 1 ⇑(e (φ k) j - e₀ j)) atTop (𝓝 0)) ∧
      (∀ k j, ⇑(e k j) =ᵐ[volume] ⇑(E k j)) ∧ (∀ j, ⇑(e₀ j) =ᵐ[volume] ⇑(E₀ j)) ∧
      (∀ j, Tendsto (fun k => ‖E (φ k) j - E₀ j‖) atTop (𝓝 0)) ∧
      (∀ μ a b, Tendsto (fun k => sobSq 1 ⇑(A (φ k) μ a b - A₀ μ a b)) atTop (𝓝 0)) ∧
      (∀ μ a b, Tendsto (fun k => eLpNorm (⇑(A (φ k) μ a b) - ⇑(A₀ μ a b)) 4 volume) atTop
        (𝓝 0)) ∧
      (∀ a, Tendsto (fun k => sobSq 1 ⇑(H (φ k) a - H₀ a)) atTop (𝓝 0)) ∧
      (∀ a, Tendsto (fun k => eLpNorm (⇑(H (φ k) a) - ⇑(H₀ a)) 4 volume) atTop (𝓝 0)) ∧
      θ₀ ∈ Kθ ∧ Tendsto (fun k => θ (φ k)) atTop (𝓝 θ₀) := by
  classical
  obtain ⟨θ₀, hθ₀, ψ, hψ, hθlim⟩ := hKθ.tendsto_subseq hθ
  have hD : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  set te : ℝ := (max 1 ((Fintype.card ι : ℝ) / 2) + se) / 2 with hte
  set tA : ℝ := (max 1 ((Fintype.card ι : ℝ) / 4) + sA) / 2 with htA
  set tH : ℝ := (max 1 ((Fintype.card ι : ℝ) / 4) + sH) / 2 with htH
  have hm1 := le_max_left (1 : ℝ) ((Fintype.card ι : ℝ) / 2)
  have hm2 := le_max_right (1 : ℝ) ((Fintype.card ι : ℝ) / 2)
  have hm3 := le_max_left (1 : ℝ) ((Fintype.card ι : ℝ) / 4)
  have hm4 := le_max_right (1 : ℝ) ((Fintype.card ι : ℝ) / 4)
  have hmax2 : max 1 ((Fintype.card ι : ℝ) / 2) < se := max_lt hse1 hse
  have hmaxA : max 1 ((Fintype.card ι : ℝ) / 4) < sA := max_lt hsA1 hsA
  have hmaxH : max 1 ((Fintype.card ι : ℝ) / 4) < sH := max_lt hsH1 hsH
  have hte1 : 1 < te := by rw [hte]; linarith
  have hte2 : (Fintype.card ι : ℝ) / 2 < te := by rw [hte]; linarith
  have htes : te < se := by rw [hte]; linarith
  have htA1 : 1 < tA := by rw [htA]; linarith
  have htA4 : (Fintype.card ι : ℝ) / 4 < tA := by rw [htA]; linarith
  have htAs : tA < sA := by rw [htA]; linarith
  have htH1 : 1 < tH := by rw [htH]; linarith
  have htH4 : (Fintype.card ι : ℝ) / 4 < tH := by rw [htH]; linarith
  have htHs : tH < sH := by rw [htH]; linarith
  let J := Je ⊕ ((ι × r × r) ⊕ r')
  let F : ℕ → J → L²(UnitAddTorus ι) := fun k =>
    Sum.elim (e (ψ k)) (Sum.elim (fun q => A (ψ k) q.1 q.2.1 q.2.2) (H (ψ k)))
  let s : J → ℝ := Sum.elim (fun _ => se) (Sum.elim (fun _ => sA) (fun _ => sH))
  let t : J → ℝ := Sum.elim (fun _ => te) (Sum.elim (fun _ => tA) (fun _ => tH))
  have hts : ∀ j, t j < s j := by
    intro j; rcases j with j | j | j
    · exact htes
    · exact htAs
    · exact htHs
  have hs0 : ∀ j, 0 ≤ s j := by
    intro j; rcases j with j | j | j
    · show 0 ≤ se; linarith
    · show 0 ≤ sA; linarith
    · show 0 ≤ sH; linarith
  have hF : ∀ k j, MemH (s j) (F k j) := by
    intro k j; rcases j with j | ⟨μ, a, b⟩ | a
    · exact he _ j
    · exact hA _ μ a b
    · exact hH _ a
  have hFB : ∀ k j, sobSq (s j) (F k j) ≤ B := by
    intro k j; rcases j with j | ⟨μ, a, b⟩ | a
    · exact heB _ j
    · exact hAB _ μ a b
    · exact hHB _ a
  obtain ⟨φ', g, hφ', hgs, hdm, hdlim⟩ := rellich_L2_family t s hts hs0 F hF hFB
  set φ := ψ ∘ φ'
  set e₀ : Je → L²(UnitAddTorus ι) := fun j => g (Sum.inl j)
  set A₀ : ι → r → r → L²(UnitAddTorus ι) := fun μ a b => g (Sum.inr (Sum.inl (μ, a, b)))
  set H₀ : r' → L²(UnitAddTorus ι) := fun a => g (Sum.inr (Sum.inr a))
  have hee : ∀ j, Tendsto (fun k => sobSq te ⇑(e (φ k) j - e₀ j)) atTop (𝓝 0) :=
    fun j => hdlim (Sum.inl j)
  have heem : ∀ k j, MemH te ⇑(e (φ k) j - e₀ j) := fun k j => hdm k (Sum.inl j)
  have he₀ : ∀ j, MemH se (e₀ j) := fun j => hgs (Sum.inl j)
  have hAA : ∀ μ a b, Tendsto (fun k => sobSq tA ⇑(A (φ k) μ a b - A₀ μ a b)) atTop (𝓝 0) :=
    fun μ a b => hdlim (Sum.inr (Sum.inl (μ, a, b)))
  have hAAm : ∀ k μ a b, MemH tA ⇑(A (φ k) μ a b - A₀ μ a b) := fun k μ a b =>
    hdm k (Sum.inr (Sum.inl (μ, a, b)))
  have hA₀ : ∀ μ a b, MemH sA (A₀ μ a b) := fun μ a b => hgs (Sum.inr (Sum.inl (μ, a, b)))
  have hHH : ∀ a, Tendsto (fun k => sobSq tH ⇑(H (φ k) a - H₀ a)) atTop (𝓝 0) :=
    fun a => hdlim (Sum.inr (Sum.inr a))
  have hHHm : ∀ k a, MemH tH ⇑(H (φ k) a - H₀ a) := fun k a => hdm k (Sum.inr (Sum.inr a))
  have hH₀ : ∀ a, MemH sH (H₀ a) := fun a => hgs (Sum.inr (Sum.inr a))
  have lower : ∀ {t' t : ℝ} {u : ℕ → UnitAddTorus ι → ℂ}, t' ≤ t → (∀ k, MemH t (u k)) →
      Tendsto (fun k => sobSq t (u k)) atTop (𝓝 0) →
      Tendsto (fun k => sobSq t' (u k)) atTop (𝓝 0) := fun h hm hl =>
    squeeze_zero (fun k => sobSq_nonneg _ _) (fun k => coeffSobSq_mono h (hm k)) hl
  choose E hE using fun k j => exists_continuous_of_memH hse (e k j) (he k j)
  choose E₀ hE₀ using fun j => exists_continuous_of_memH hse (e₀ j) (he₀ j)
  have hEunif : ∀ j, Tendsto (fun k => ‖E (φ k) j - E₀ j‖) atTop (𝓝 0) := by
    intro j
    have hdiff : ∀ k, mFourierCoeff ⇑(E (φ k) j - E₀ j) = mFourierCoeff ⇑(e (φ k) j - e₀ j) := by
      intro k; funext n
      rw [mFourierCoeff_continuous_sub, mFourierCoeff_Lp_sub, (hE (φ k) j).2.2.1 n,
        (hE₀ j).2.2.1 n]
    have hbound : ∀ k, ‖E (φ k) j - E₀ j‖ ≤
        embConst ι te * Real.sqrt (sobSq te ⇑(e (φ k) j - e₀ j)) := by
      intro k
      have hmk : MemH te ⇑(E (φ k) j - E₀ j) := by
        show CoeffMemH te _; rw [hdiff]; exact heem k j
      have := norm_le_of_memH hte2 _ hmk
      unfold sobNorm sobSq at this
      rw [hdiff] at this
      exact this
    have hl : Tendsto (fun k => embConst ι te * Real.sqrt (sobSq te ⇑(e (φ k) j - e₀ j))) atTop
        (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp (hee j)).const_mul (embConst ι te)
      simpa [Function.comp_def] using this
    exact squeeze_zero (fun k => norm_nonneg _) hbound hl
  exact ⟨φ, e₀, A₀, H₀, θ₀, E, E₀, hψ.comp hφ', he₀, hA₀, hH₀,
    fun j => lower hte1.le (heem · j) (hee j),
    fun k j => (hE k j).2.1, fun j => (hE₀ j).2.1, hEunif,
    fun μ a b => lower htA1.le (hAAm · μ a b) (hAA μ a b),
    fun μ a b => tendsto_eLpNorm_four_of_H htA4 (fun k => (hA (φ k) μ a b).mono htAs.le)
      ((hA₀ μ a b).mono htAs.le) (hAA μ a b),
    fun a => lower htH1.le (hHHm · a) (hHH a),
    fun a => tendsto_eLpNorm_four_of_H htH4 (fun k => (hH (φ k) a).mono htHs.le)
      ((hH₀ a).mono htHs.le) (hHH a),
    hθ₀, hθlim.comp hφ'.tendsto_atTop⟩

/-! ### Box curvature, covariant derivative, and convergence calculus -/

/-- The curvature `F_{μν} = ∂_μA_ν - ∂_νA_μ + [A_μ, A_ν]` on `Q`, from the potentials and their
weak gradients (`gA μ a b i = ∂_i A_μ^{ab}`). -/
def boxCurv {r : Type*} [Fintype r] (A : ι → r → r → (ι → ℝ) → ℂ)
    (gA : ι → r → r → ι → (ι → ℝ) → ℂ) (μ ν : ι) (a b : r) (x : ι → ℝ) : ℂ :=
  (gA ν a b μ x - gA μ a b ν x) + ∑ e, (A μ a e x * A ν e b x - A ν a e x * A μ e b x)

/-- The covariant derivative `(D_AH)^a_μ = ∂_μH^a + Σ R_{a q} A_μ^{q₂q₃} H^{q₁}` on `Q`. -/
def boxCovD {r r' : Type*} [Fintype r] [Fintype r'] (R : r' → r' → r → r → ℂ)
    (A : ι → r → r → (ι → ℝ) → ℂ) (H : r' → (ι → ℝ) → ℂ) (gH : r' → ι → (ι → ℝ) → ℂ) (μ : ι)
    (a : r') (x : ι → ℝ) : ℂ :=
  gH a μ x + ∑ q : r' × r × r, R a q.1 q.2.1 q.2.2 • (A μ q.2.1 q.2.2 x * H q.1 x)

section Calculus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem tendsto_eLpNorm_add2 {f g : ℕ → X → ℂ} (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (hg : ∀ k, AEStronglyMeasurable (g k) μ)
    (hf0 : Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0))
    (hg0 : Tendsto (fun k => eLpNorm (g k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k + g k) 2 μ) atTop (𝓝 0) := by
  have h := hf0.add hg0
  simp only [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
    fun k => eLpNorm_add_le (hf k) (hg k) (by norm_num)

theorem tendsto_eLpNorm_sub2 {f g : ℕ → X → ℂ} (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (hg : ∀ k, AEStronglyMeasurable (g k) μ)
    (hf0 : Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0))
    (hg0 : Tendsto (fun k => eLpNorm (g k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k - g k) 2 μ) atTop (𝓝 0) := by
  have h := hf0.add hg0
  simp only [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
    fun k => eLpNorm_sub_le (hf k) (hg k) (by norm_num)

theorem tendsto_eLpNorm_sum2 {κ : Type*} (s : Finset κ) {f : κ → ℕ → X → ℂ}
    (hf : ∀ i ∈ s, ∀ k, AEStronglyMeasurable (f i k) μ)
    (hf0 : ∀ i ∈ s, Tendsto (fun k => eLpNorm (f i k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (∑ i ∈ s, f i k) 2 μ) atTop (𝓝 0) := by
  have h := tendsto_finset_sum s hf0
  simp only [Finset.sum_const_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
    fun k => eLpNorm_sum_le (fun i hi => hf i hi k) (by norm_num)

theorem tendsto_eLpNorm_const_smul2 (a : ℂ) {f : ℕ → X → ℂ}
    (hf0 : Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (a • f k) 2 μ) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul (a := ‖a‖ₑ) hf0 (Or.inr enorm_ne_top)
  simp only [mul_zero] at h
  exact h.congr fun k => (eLpNorm_const_smul a (f k) 2 μ).symm

end Calculus

/-- The `L²(Q)` convergence of the canonical gradients. -/
theorem tendsto_boxGrad (hL : 0 < L) (hQ : Q ⊆ cubeAt c L) {f : ℕ → L²(UnitAddTorus ι)}
    {f₀ : L²(UnitAddTorus ι)} (hf : ∀ k, MemH 1 (f k)) (hf₀ : MemH 1 f₀)
    (hconv : Tendsto (fun k => sobSq 1 ⇑(f k - f₀)) atTop (𝓝 0)) (i : ι) :
    Tendsto (fun k => eLpNorm (boxGrad c L (f k) i - boxGrad c L f₀ i) 2 (volume.restrict Q))
      atTop (𝓝 0) := by
  have h := tendsto_w12_chart hL hQ hf hf₀ hconv (u := fun k x => f k (chart c L x))
    (fun k => EventuallyEq.refl _ _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
    fun k => ?_
  unfold w12Norm
  refine le_add_left (Finset.single_le_sum (f := fun i => eLpNorm
    ((boxGrad c L (f k) - boxGrad c L f₀) i) 2 (volume.restrict Q)) (fun _ _ => zero_le)
    (Finset.mem_univ i))

/-- `L⁴(Q)` membership of a pull-back. -/
theorem memLp_four_chart (hL : 0 < L) (hQ : Q ⊆ cubeAt c L) {U : L²(UnitAddTorus ι)}
    (hU : MemLp (⇑U) 4 volume) {u : (ι → ℝ) → ℂ}
    (hu : u =ᵐ[volume.restrict Q] fun x => U (chart c L x)) (hum : AEStronglyMeasurable u
      (volume.restrict Q)) : MemLp u 4 (volume.restrict Q) := by
  refine ⟨hum, ?_⟩
  rw [eLpNorm_congr_ae hu]
  have h := eLpNorm_chart_le hL hQ (⇑U) (p := 4) (by norm_num)
  rw [show ENNReal.ofReal 4 = 4 by norm_num] at h
  exact h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU.2)

section BoxConvergence

variable {μ₀ : Measure (ι → ℝ)} {r r' : Type*} [Fintype r] [Fintype r']

/-- Curvature convergence on a measure space from `L²` convergence of the gradients and `L⁴`
convergence of the potentials. -/
theorem tendsto_boxCurv {A : ℕ → ι → r → r → (ι → ℝ) → ℂ} {A₀ : ι → r → r → (ι → ℝ) → ℂ}
    {gA : ℕ → ι → r → r → ι → (ι → ℝ) → ℂ} {gA₀ : ι → r → r → ι → (ι → ℝ) → ℂ}
    (hAm : ∀ k μ a b, AEStronglyMeasurable (A k μ a b) μ₀) (hA₀ : ∀ μ a b, MemLp (A₀ μ a b) 4 μ₀)
    (hgm : ∀ k μ a b i, AEStronglyMeasurable (gA k μ a b i) μ₀)
    (hg₀m : ∀ μ a b i, AEStronglyMeasurable (gA₀ μ a b i) μ₀)
    (hA4 : ∀ μ a b, Tendsto (fun k => eLpNorm (A k μ a b - A₀ μ a b) 4 μ₀) atTop (𝓝 0))
    (hg2 : ∀ μ a b i, Tendsto (fun k => eLpNorm (gA k μ a b i - gA₀ μ a b i) 2 μ₀) atTop (𝓝 0))
    (μ ν : ι) (a b : r) :
    Tendsto (fun k => eLpNorm (boxCurv (A k) (gA k) μ ν a b - boxCurv A₀ gA₀ μ ν a b) 2 μ₀)
      atTop (𝓝 0) := by
  have hprod : ∀ (μ ν : ι) (a e b : r), Tendsto (fun k => eLpNorm
      (A k μ a e * A k ν e b - A₀ μ a e * A₀ ν e b) 2 μ₀) atTop (𝓝 0) := fun μ ν a e b =>
    TorusSobolev.tendsto_eLpNorm_mul_of_L4 (fun k => hAm k μ a e) (fun k => hAm k ν e b) (hA₀ μ a e)
      (hA₀ ν e b) (hA4 μ a e) (hA4 ν e b)
  have hpm : ∀ (μ ν : ι) (a e b : r) k, AEStronglyMeasurable
      (A k μ a e * A k ν e b - A₀ μ a e * A₀ ν e b) μ₀ := fun μ ν a e b k =>
    ((hAm k μ a e).mul (hAm k ν e b)).sub ((hA₀ μ a e).1.mul (hA₀ ν e b).1)
  have hdm : ∀ (μ : ι) (a b : r) (i : ι) k, AEStronglyMeasurable
      (gA k μ a b i - gA₀ μ a b i) μ₀ := fun μ a b i k => (hgm k μ a b i).sub (hg₀m μ a b i)
  have he : ∀ k, boxCurv (A k) (gA k) μ ν a b - boxCurv A₀ gA₀ μ ν a b =
      ((gA k ν a b μ - gA₀ ν a b μ) - (gA k μ a b ν - gA₀ μ a b ν)) +
        ∑ e, ((A k μ a e * A k ν e b - A₀ μ a e * A₀ ν e b) -
          (A k ν a e * A k μ e b - A₀ ν a e * A₀ μ e b)) := by
    intro k
    funext x
    simp only [boxCurv, Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.mul_apply,
      Finset.sum_sub_distrib]
    ring
  simp only [he]
  refine tendsto_eLpNorm_add2 (fun k => (hdm ν a b μ k).sub (hdm μ a b ν k))
    (fun k => Finset.aestronglyMeasurable_sum _ fun e _ => (hpm μ ν a e b k).sub
      (hpm ν μ a e b k)) (tendsto_eLpNorm_sub2 (hdm ν a b μ) (hdm μ a b ν) (hg2 ν a b μ)
      (hg2 μ a b ν)) ?_
  exact tendsto_eLpNorm_sum2 _ (fun e _ k => (hpm μ ν a e b k).sub (hpm ν μ a e b k))
    fun e _ => tendsto_eLpNorm_sub2 (hpm μ ν a e b) (hpm ν μ a e b) (hprod μ ν a e b)
      (hprod ν μ a e b)

/-- Covariant-derivative convergence on a measure space. -/
theorem tendsto_boxCovD (R : r' → r' → r → r → ℂ) {A : ℕ → ι → r → r → (ι → ℝ) → ℂ}
    {A₀ : ι → r → r → (ι → ℝ) → ℂ} {H : ℕ → r' → (ι → ℝ) → ℂ} {H₀ : r' → (ι → ℝ) → ℂ}
    {gH : ℕ → r' → ι → (ι → ℝ) → ℂ} {gH₀ : r' → ι → (ι → ℝ) → ℂ}
    (hAm : ∀ k μ a b, AEStronglyMeasurable (A k μ a b) μ₀) (hA₀ : ∀ μ a b, MemLp (A₀ μ a b) 4 μ₀)
    (hHm : ∀ k a, AEStronglyMeasurable (H k a) μ₀) (hH₀ : ∀ a, MemLp (H₀ a) 4 μ₀)
    (hgm : ∀ k a i, AEStronglyMeasurable (gH k a i) μ₀)
    (hg₀m : ∀ a i, AEStronglyMeasurable (gH₀ a i) μ₀)
    (hA4 : ∀ μ a b, Tendsto (fun k => eLpNorm (A k μ a b - A₀ μ a b) 4 μ₀) atTop (𝓝 0))
    (hH4 : ∀ a, Tendsto (fun k => eLpNorm (H k a - H₀ a) 4 μ₀) atTop (𝓝 0))
    (hg2 : ∀ a i, Tendsto (fun k => eLpNorm (gH k a i - gH₀ a i) 2 μ₀) atTop (𝓝 0))
    (μ : ι) (a : r') :
    Tendsto (fun k => eLpNorm (boxCovD R (A k) (H k) (gH k) μ a - boxCovD R A₀ H₀ gH₀ μ a) 2 μ₀)
      atTop (𝓝 0) := by
  have hprod : ∀ q : r' × r × r, Tendsto (fun k => eLpNorm
      (A k μ q.2.1 q.2.2 * H k q.1 - A₀ μ q.2.1 q.2.2 * H₀ q.1) 2 μ₀) atTop (𝓝 0) := fun q =>
    TorusSobolev.tendsto_eLpNorm_mul_of_L4 (fun k => hAm k μ q.2.1 q.2.2) (fun k => hHm k q.1)
      (hA₀ μ q.2.1 q.2.2) (hH₀ q.1) (hA4 μ q.2.1 q.2.2) (hH4 q.1)
  have hpm : ∀ (q : r' × r × r) k, AEStronglyMeasurable
      (A k μ q.2.1 q.2.2 * H k q.1 - A₀ μ q.2.1 q.2.2 * H₀ q.1) μ₀ := fun q k =>
    ((hAm k μ q.2.1 q.2.2).mul (hHm k q.1)).sub ((hA₀ μ q.2.1 q.2.2).1.mul (hH₀ q.1).1)
  have he : ∀ k, boxCovD R (A k) (H k) (gH k) μ a - boxCovD R A₀ H₀ gH₀ μ a =
      (gH k a μ - gH₀ a μ) + ∑ q : r' × r × r, R a q.1 q.2.1 q.2.2 •
        (A k μ q.2.1 q.2.2 * H k q.1 - A₀ μ q.2.1 q.2.2 * H₀ q.1) := by
    intro k
    funext x
    simp only [boxCovD, Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.mul_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, mul_sub]
    ring
  simp only [he]
  refine tendsto_eLpNorm_add2 (fun k => (hgm k a μ).sub (hg₀m a μ))
    (fun k => Finset.aestronglyMeasurable_sum _ fun q _ => (hpm q k).const_smul _) (hg2 a μ) ?_
  exact tendsto_eLpNorm_sum2 _ (fun q _ k => (hpm q k).const_smul _)
    fun q _ => tendsto_eLpNorm_const_smul2 _ (hprod q)

end BoxConvergence

/-! ### The assembly -/

theorem box_subset_cubeAt {a b : ι → ℝ} {L : ℝ} (hside : ∀ i, b i - a i ≤ L) :
    box a b ⊆ cubeAt a L := fun x hx i => by
  have h := hx i (mem_univ i)
  exact ⟨h.1, by linarith [h.2, hside i]⟩

/-- **`prop:sobolev-bosonic` on a box** (restriction-space rendering of `H^s(K)`).  Let
`Q = Π (a_i, b_i)` and `L ≥ max (b_i - a_i)`.  Frame components `e_h`, potentials `A_h`
(`r × r` matrices) and Higgs components `H_h` on `Q` agreeing a.e. on `Q` with the pull-backs of
periodic functions bounded in `H^{s_e}`, `H^{s_A}`, `H^{s_H}` (`s_e > max(1, d/2)`,
`s_A, s_H > max(1, d/4)`), and banks `θ_h` in a compact set.  Then the fields lie in `W^{1,2}(Q)`
(with the canonical weak gradients), and along one subsequence: `e_h → e` in `W^{1,2}(Q)` and in
`L^∞(Q)`; `A_h → A`, `H_h → H` in `W^{1,2}(Q)` and in `L⁴(Q)`; `F_{A_h} → F_A` and
`D_{A_h}H_h → D_AH` in `L²(Q)` (curvature and covariant derivative from the weak gradients on
`Q`); `θ_h → θ ∈ K_θ`. -/
theorem sobolev_bosonic_box {Je r r' : Type*} [Fintype Je] [Fintype r] [Fintype r'] {m : ℕ}
    {se sA sH : ℝ} (hse1 : 1 < se) (hse : (Fintype.card ι : ℝ) / 2 < se) (hsA1 : 1 < sA)
    (hsA : (Fintype.card ι : ℝ) / 4 < sA) (hsH1 : 1 < sH) (hsH : (Fintype.card ι : ℝ) / 4 < sH)
    (R : r' → r' → r → r → ℂ) {B : ℝ} {a b : ι → ℝ} {L : ℝ} (hL : 0 < L)
    (hside : ∀ i, b i - a i ≤ L)
    (e : ℕ → Je → L²(UnitAddTorus ι)) (A : ℕ → ι → r → r → L²(UnitAddTorus ι))
    (H : ℕ → r' → L²(UnitAddTorus ι))
    (he : ∀ k j, MemH se (e k j)) (heB : ∀ k j, sobSq se (e k j) ≤ B)
    (hA : ∀ k μ p q, MemH sA (A k μ p q)) (hAB : ∀ k μ p q, sobSq sA (A k μ p q) ≤ B)
    (hH : ∀ k p, MemH sH (H k p)) (hHB : ∀ k p, sobSq sH (H k p) ≤ B)
    (eQ : ℕ → Je → (ι → ℝ) → ℂ) (AQ : ℕ → ι → r → r → (ι → ℝ) → ℂ)
    (HQ : ℕ → r' → (ι → ℝ) → ℂ)
    (heQ : ∀ k j, eQ k j =ᵐ[volume.restrict (box a b)] fun x => e k j (chart a L x))
    (hAQ : ∀ k μ p q, AQ k μ p q =ᵐ[volume.restrict (box a b)] fun x => A k μ p q (chart a L x))
    (hHQ : ∀ k p, HQ k p =ᵐ[volume.restrict (box a b)] fun x => H k p (chart a L x))
    (θ : ℕ → Fin m → ℝ) {Kθ : Set (Fin m → ℝ)} (hKθ : IsCompact Kθ) (hθ : ∀ k, θ k ∈ Kθ) :
    ∃ (φ : ℕ → ℕ) (e₀ : Je → (ι → ℝ) → ℂ) (ge₀ : Je → ι → (ι → ℝ) → ℂ)
      (A₀ : ι → r → r → (ι → ℝ) → ℂ) (gA₀ : ι → r → r → ι → (ι → ℝ) → ℂ)
      (H₀ : r' → (ι → ℝ) → ℂ) (gH₀ : r' → ι → (ι → ℝ) → ℂ) (θ₀ : Fin m → ℝ), StrictMono φ ∧
      (∀ k j, MemW12 (box a b) (eQ k j) (boxGrad a L (e k j))) ∧
      (∀ k μ p q, MemW12 (box a b) (AQ k μ p q) (boxGrad a L (A k μ p q))) ∧
      (∀ k p, MemW12 (box a b) (HQ k p) (boxGrad a L (H k p))) ∧
      (∀ j, MemW12 (box a b) (e₀ j) (ge₀ j)) ∧ (∀ μ p q, MemW12 (box a b) (A₀ μ p q) (gA₀ μ p q)) ∧
      (∀ p, MemW12 (box a b) (H₀ p) (gH₀ p)) ∧
      (∀ j, Tendsto (fun k => w12Norm (box a b) (eQ (φ k) j - e₀ j)
        (boxGrad a L (e (φ k) j) - ge₀ j)) atTop (𝓝 0)) ∧
      (∀ j, Tendsto (fun k => eLpNorm (eQ (φ k) j - e₀ j) ⊤ (volume.restrict (box a b))) atTop
        (𝓝 0)) ∧
      (∀ μ p q, Tendsto (fun k => w12Norm (box a b) (AQ (φ k) μ p q - A₀ μ p q)
        (boxGrad a L (A (φ k) μ p q) - gA₀ μ p q)) atTop (𝓝 0)) ∧
      (∀ μ p q, Tendsto (fun k => eLpNorm (AQ (φ k) μ p q - A₀ μ p q) 4
        (volume.restrict (box a b))) atTop (𝓝 0)) ∧
      (∀ p, Tendsto (fun k => w12Norm (box a b) (HQ (φ k) p - H₀ p)
        (boxGrad a L (H (φ k) p) - gH₀ p)) atTop (𝓝 0)) ∧
      (∀ p, Tendsto (fun k => eLpNorm (HQ (φ k) p - H₀ p) 4 (volume.restrict (box a b))) atTop
        (𝓝 0)) ∧
      (∀ μ ν p q, Tendsto (fun k => eLpNorm (boxCurv (AQ (φ k))
        (fun μ p q => boxGrad a L (A (φ k) μ p q)) μ ν p q - boxCurv A₀ gA₀ μ ν p q) 2
          (volume.restrict (box a b))) atTop (𝓝 0)) ∧
      (∀ μ p, Tendsto (fun k => eLpNorm (boxCovD R (AQ (φ k)) (HQ (φ k))
        (fun p => boxGrad a L (H (φ k) p)) μ p - boxCovD R A₀ H₀ gH₀ μ p) 2
          (volume.restrict (box a b))) atTop (𝓝 0)) ∧
      θ₀ ∈ Kθ ∧ Tendsto (fun k => θ (φ k)) atTop (𝓝 θ₀) := by
  set Q := box a b with hQdef
  have hQm : MeasurableSet Q := (isOpen_box a b).measurableSet
  have hQf : volume Q ≠ ⊤ := volume_box_ne_top a b
  have hQ : Q ⊆ cubeAt a L := box_subset_cubeAt hside
  obtain ⟨φ, eT, AT, HT, θ₀, E, E₀, hφ, heT, hAT, hHT, he1, hEae, hE₀ae, hEunif, hA1, hA4, hH1,
    hH4, hθ₀, hθlim⟩ := torus_extract hse1 hse hsA1 hsA hsH1 hsH e A H he heB hA hAB hH hHB θ
      hKθ hθ
  have hm1 : ∀ {s : ℝ} {U : L²(UnitAddTorus ι)}, 1 < s → MemH s U → MemH 1 U := fun hs hU =>
    hU.mono hs.le
  -- the box fields and limits
  have hW : ∀ (U : L²(UnitAddTorus ι)), MemH 1 U → ∀ u : (ι → ℝ) → ℂ,
      u =ᵐ[volume.restrict Q] (fun x => U (chart a L x)) → MemW12 Q u (boxGrad a L U) :=
    fun U hU u hu => memW12_congr_ae hQm (memW12_chart hQm hQf hL hQ hU) hu.symm
      fun i => EventuallyEq.refl _ _
  have hWe : ∀ k j, MemW12 Q (eQ k j) (boxGrad a L (e k j)) := fun k j =>
    hW _ (hm1 hse1 (he k j)) _ (heQ k j)
  have hWA : ∀ k μ p q, MemW12 Q (AQ k μ p q) (boxGrad a L (A k μ p q)) := fun k μ p q =>
    hW _ (hm1 hsA1 (hA k μ p q)) _ (hAQ k μ p q)
  have hWH : ∀ k p, MemW12 Q (HQ k p) (boxGrad a L (H k p)) := fun k p =>
    hW _ (hm1 hsH1 (hH k p)) _ (hHQ k p)
  set e₀ : Je → (ι → ℝ) → ℂ := fun j x => eT j (chart a L x)
  set A₀ : ι → r → r → (ι → ℝ) → ℂ := fun μ p q x => AT μ p q (chart a L x)
  set H₀ : r' → (ι → ℝ) → ℂ := fun p x => HT p (chart a L x)
  have hWe₀ : ∀ j, MemW12 Q (e₀ j) (boxGrad a L (eT j)) := fun j =>
    hW _ (hm1 hse1 (heT j)) _ (EventuallyEq.refl _ _)
  have hWA₀ : ∀ μ p q, MemW12 Q (A₀ μ p q) (boxGrad a L (AT μ p q)) := fun μ p q =>
    hW _ (hm1 hsA1 (hAT μ p q)) _ (EventuallyEq.refl _ _)
  have hWH₀ : ∀ p, MemW12 Q (H₀ p) (boxGrad a L (HT p)) := fun p =>
    hW _ (hm1 hsH1 (hHT p)) _ (EventuallyEq.refl _ _)
  -- `L⁴` convergence on the box
  have hL4 : ∀ {f : ℕ → L²(UnitAddTorus ι)} {f₀ : L²(UnitAddTorus ι)} {u : ℕ → (ι → ℝ) → ℂ},
      Tendsto (fun k => eLpNorm (⇑(f k) - ⇑f₀) 4 volume) atTop (𝓝 0) →
      (∀ k, u k =ᵐ[volume.restrict Q] fun x => f k (chart a L x)) →
      Tendsto (fun k => eLpNorm (u k - fun x => f₀ (chart a L x)) 4 (volume.restrict Q)) atTop
        (𝓝 0) := by
    intro f f₀ u h hu
    have h0 : Tendsto (fun k => eLpNorm ((fun k => ⇑(f k)) k - ⇑f₀) (ENNReal.ofReal 4) volume)
        atTop (𝓝 0) := by rw [show ENNReal.ofReal 4 = 4 by norm_num]; exact h
    have h1 := tendsto_chart_eLpNorm (by norm_num) hL hQ h0
    rw [show ENNReal.ofReal 4 = 4 by norm_num] at h1
    exact tendsto_eLpNorm_congr hu (EventuallyEq.refl _ _) h1
  have hAQ4 : ∀ μ p q, Tendsto (fun k => eLpNorm (AQ (φ k) μ p q - A₀ μ p q) 4
      (volume.restrict Q)) atTop (𝓝 0) := fun μ p q => hL4 (hA4 μ p q) (fun k => hAQ _ μ p q)
  have hHQ4 : ∀ p, Tendsto (fun k => eLpNorm (HQ (φ k) p - H₀ p) 4 (volume.restrict Q)) atTop
      (𝓝 0) := fun p => hL4 (hH4 p) (fun k => hHQ _ p)
  -- `L⁴` membership of the limits
  have hA₀4 : ∀ μ p q, MemLp (A₀ μ p q) 4 (volume.restrict Q) := fun μ p q =>
    memLp_four_chart hL hQ (memLp_four_of_memH hsA _ (hAT μ p q)) (EventuallyEq.refl _ _)
      (hWA₀ μ p q).memLp.1
  have hH₀4 : ∀ p, MemLp (H₀ p) 4 (volume.restrict Q) := fun p =>
    memLp_four_chart hL hQ (memLp_four_of_memH hsH _ (hHT p)) (EventuallyEq.refl _ _)
      (hWH₀ p).memLp.1
  refine ⟨φ, e₀, fun j => boxGrad a L (eT j), A₀, fun μ p q => boxGrad a L (AT μ p q), H₀,
    fun p => boxGrad a L (HT p), θ₀, hφ, hWe, hWA, hWH, hWe₀, hWA₀, hWH₀,
    fun j => tendsto_w12_chart hL hQ (fun k => hm1 hse1 (he _ j)) (hm1 hse1 (heT j)) (he1 j)
      (fun k => heQ _ j), ?_,
    fun μ p q => tendsto_w12_chart hL hQ (fun k => hm1 hsA1 (hA _ μ p q))
      (hm1 hsA1 (hAT μ p q)) (hA1 μ p q) (fun k => hAQ _ μ p q), hAQ4,
    fun p => tendsto_w12_chart hL hQ (fun k => hm1 hsH1 (hH _ p)) (hm1 hsH1 (hHT p)) (hH1 p)
      (fun k => hHQ _ p), hHQ4, ?_, ?_, hθ₀, hθlim⟩
  · -- uniform convergence of the frames
    intro j
    have hb : ∀ k, eLpNorm (eQ (φ k) j - e₀ j) ⊤ (volume.restrict Q) ≤
        ENNReal.ofReal ‖E (φ k) j - E₀ j‖ := by
      intro k
      rw [eLpNorm_exponent_top]
      refine eLpNormEssSup_le_of_ae_bound ?_
      filter_upwards [heQ (φ k) j, ae_chart_of_ae hL hQ (hEae (φ k) j),
        ae_chart_of_ae hL hQ (hE₀ae j)] with x h1 h2 h3
      simp only [Pi.sub_apply, e₀]
      rw [h1, h2, h3, ← ContinuousMap.sub_apply]
      exact ContinuousMap.norm_coe_le_norm _ _
    have hl := ENNReal.tendsto_ofReal (hEunif j)
    rw [ENNReal.ofReal_zero] at hl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun k => zero_le) hb
  · -- curvature
    intro μ ν p q
    exact tendsto_boxCurv (fun k μ p q => (hWA (φ k) μ p q).memLp.1) hA₀4
      (fun k μ p q i => ((hWA (φ k) μ p q).memLp_grad i).1)
      (fun μ p q i => ((hWA₀ μ p q).memLp_grad i).1) hAQ4
      (fun μ p q i => tendsto_boxGrad hL hQ (fun k => hm1 hsA1 (hA _ μ p q))
        (hm1 hsA1 (hAT μ p q)) (hA1 μ p q) i) μ ν p q
  · -- covariant derivative
    intro μ p
    exact tendsto_boxCovD R (fun k μ p q => (hWA (φ k) μ p q).memLp.1) hA₀4
      (fun k p => (hWH (φ k) p).memLp.1) hH₀4
      (fun k p i => ((hWH (φ k) p).memLp_grad i).1) (fun p i => ((hWH₀ p).memLp_grad i).1)
      hAQ4 hHQ4 (fun p i => tendsto_boxGrad hL hQ (fun k => hm1 hsH1 (hH _ p))
        (hm1 hsH1 (hHT p)) (hH1 p) i) μ p

/-- **`prop:sobolev-bosonic` (box rendering, four dimensions)**: with `s_e = 2 + σ`,
`s_A = s_H = 1 + σ` on `ι = Fin 4`, all the convergences of `sobolev_bosonic_box`
(`eq:apriori-bosonic-convergence`) hold along one subsequence, and moreover the Higgs fields are
uniformly bounded in `L^{4+δ}(Q)`, `δ = min σ 1 > 0` depending only on `σ`. -/
theorem sobolev_bosonic_box_four {Je r r' : Type*} [Fintype Je] [Fintype r] [Fintype r'] {m : ℕ}
    {σ : ℝ} (hσ : 0 < σ) (R : r' → r' → r → r → ℂ) {B : ℝ} {a b : Fin 4 → ℝ} {L : ℝ}
    (hL : 0 < L) (hside : ∀ i, b i - a i ≤ L)
    (e : ℕ → Je → L²(UnitAddTorus (Fin 4))) (A : ℕ → Fin 4 → r → r → L²(UnitAddTorus (Fin 4)))
    (H : ℕ → r' → L²(UnitAddTorus (Fin 4)))
    (he : ∀ k j, MemH (2 + σ) (e k j)) (heB : ∀ k j, sobSq (2 + σ) (e k j) ≤ B)
    (hA : ∀ k μ p q, MemH (1 + σ) (A k μ p q)) (hAB : ∀ k μ p q, sobSq (1 + σ) (A k μ p q) ≤ B)
    (hH : ∀ k p, MemH (1 + σ) (H k p)) (hHB : ∀ k p, sobSq (1 + σ) (H k p) ≤ B)
    (eQ : ℕ → Je → (Fin 4 → ℝ) → ℂ) (AQ : ℕ → Fin 4 → r → r → (Fin 4 → ℝ) → ℂ)
    (HQ : ℕ → r' → (Fin 4 → ℝ) → ℂ)
    (heQ : ∀ k j, eQ k j =ᵐ[volume.restrict (box a b)] fun x => e k j (chart a L x))
    (hAQ : ∀ k μ p q, AQ k μ p q =ᵐ[volume.restrict (box a b)] fun x => A k μ p q (chart a L x))
    (hHQ : ∀ k p, HQ k p =ᵐ[volume.restrict (box a b)] fun x => H k p (chart a L x))
    (θ : ℕ → Fin m → ℝ) {Kθ : Set (Fin m → ℝ)} (hKθ : IsCompact Kθ) (hθ : ∀ k, θ k ∈ Kθ) :
    (∃ (φ : ℕ → ℕ) (e₀ : Je → (Fin 4 → ℝ) → ℂ) (ge₀ : Je → Fin 4 → (Fin 4 → ℝ) → ℂ)
      (A₀ : Fin 4 → r → r → (Fin 4 → ℝ) → ℂ) (gA₀ : Fin 4 → r → r → Fin 4 → (Fin 4 → ℝ) → ℂ)
      (H₀ : r' → (Fin 4 → ℝ) → ℂ) (gH₀ : r' → Fin 4 → (Fin 4 → ℝ) → ℂ) (θ₀ : Fin m → ℝ),
      StrictMono φ ∧
      (∀ k j, MemW12 (box a b) (eQ k j) (boxGrad a L (e k j))) ∧
      (∀ k μ p q, MemW12 (box a b) (AQ k μ p q) (boxGrad a L (A k μ p q))) ∧
      (∀ k p, MemW12 (box a b) (HQ k p) (boxGrad a L (H k p))) ∧
      (∀ j, MemW12 (box a b) (e₀ j) (ge₀ j)) ∧ (∀ μ p q, MemW12 (box a b) (A₀ μ p q) (gA₀ μ p q)) ∧
      (∀ p, MemW12 (box a b) (H₀ p) (gH₀ p)) ∧
      (∀ j, Tendsto (fun k => w12Norm (box a b) (eQ (φ k) j - e₀ j)
        (boxGrad a L (e (φ k) j) - ge₀ j)) atTop (𝓝 0)) ∧
      (∀ j, Tendsto (fun k => eLpNorm (eQ (φ k) j - e₀ j) ⊤ (volume.restrict (box a b))) atTop
        (𝓝 0)) ∧
      (∀ μ p q, Tendsto (fun k => w12Norm (box a b) (AQ (φ k) μ p q - A₀ μ p q)
        (boxGrad a L (A (φ k) μ p q) - gA₀ μ p q)) atTop (𝓝 0)) ∧
      (∀ μ p q, Tendsto (fun k => eLpNorm (AQ (φ k) μ p q - A₀ μ p q) 4
        (volume.restrict (box a b))) atTop (𝓝 0)) ∧
      (∀ p, Tendsto (fun k => w12Norm (box a b) (HQ (φ k) p - H₀ p)
        (boxGrad a L (H (φ k) p) - gH₀ p)) atTop (𝓝 0)) ∧
      (∀ p, Tendsto (fun k => eLpNorm (HQ (φ k) p - H₀ p) 4 (volume.restrict (box a b))) atTop
        (𝓝 0)) ∧
      (∀ μ ν p q, Tendsto (fun k => eLpNorm (boxCurv (AQ (φ k))
        (fun μ p q => boxGrad a L (A (φ k) μ p q)) μ ν p q - boxCurv A₀ gA₀ μ ν p q) 2
          (volume.restrict (box a b))) atTop (𝓝 0)) ∧
      (∀ μ p, Tendsto (fun k => eLpNorm (boxCovD R (AQ (φ k)) (HQ (φ k))
        (fun p => boxGrad a L (H (φ k) p)) μ p - boxCovD R A₀ H₀ gH₀ μ p) 2
          (volume.restrict (box a b))) atTop (𝓝 0)) ∧
      θ₀ ∈ Kθ ∧ Tendsto (fun k => θ (φ k)) atTop (𝓝 θ₀)) ∧
    ∃ δ > (0 : ℝ), ∃ C : ℝ, ∀ k p, eLpNorm (HQ k p) (ENNReal.ofReal (4 + δ))
      (volume.restrict (box a b)) ≤ ENNReal.ofReal C := by
  have hcard : (Fintype.card (Fin 4) : ℝ) = 4 := by simp
  refine ⟨sobolev_bosonic_box (by linarith) (by rw [hcard]; linarith) (by linarith)
    (by rw [hcard]; linarith) (by linarith) (by rw [hcard]; linarith) R hL hside e A H he heB
    hA hAB hH hHB eQ AQ HQ heQ hAQ hHQ θ hKθ hθ, min σ 1, lt_min hσ one_pos,
    L ^ ((4 : ℝ) / (4 + min σ 1)) * (FracLp.lpConst (Fin 4) (4 + min σ 1) (1 + σ) *
      Real.sqrt B), fun k p => ?_⟩
  have hp : (2 : ℝ) ≤ 4 + min σ 1 := by have := lt_min hσ one_pos; linarith
  have hb := eLpNorm_box_le_of_memH hp (FracLp.exponent_four σ hσ) hL (box_subset_cubeAt hside)
    (hH k p) (hHQ k p)
  rw [hcard] at hb
  refine hb.trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (hHB k p)) (FracLp.lpConst_nonneg hp (FracLp.exponent_four σ hσ)))
    (by positivity))

/-- Non-vacuity of `sobolev_bosonic_box_four`: its hypotheses hold on the unit box for the constant
monomial (`σ = 1`), with an empty coefficient bank. -/
example : ∃ φ : ℕ → ℕ, StrictMono φ := by
  set u : L²(UnitAddTorus (Fin 4)) := (mFourier (0 : Fin 4 → ℤ)).toLp 2 volume ℂ
  have hmem : ∀ s : ℝ, MemH s u := by
    intro s
    have := memH_mFourier (d := Fin 4) s 0
    unfold MemH CoeffMemH at this ⊢
    simp_rw [u, mFourierCoeff_toLp]
    exact this
  have hsq : ∀ s : ℝ, sobSq s u ≤ 1 := by
    intro s
    have h := sobSq_mFourier (d := Fin 4) s 0
    have e : sobSq s u = sobSq s ⇑(mFourier (0 : Fin 4 → ℤ)) := by
      unfold sobSq coeffSobSq
      simp_rw [u, mFourierCoeff_toLp]
    rw [e, h, show sobWeight (0 : Fin 4 → ℤ) = 1 by simp [sobWeight], Real.one_rpow]
  obtain ⟨⟨φ, -, -, -, -, -, -, -, hφ, -⟩, -⟩ := sobolev_bosonic_box_four (Je := Fin 1)
    (r := Fin 1) (r' := Fin 1) (m := 0) (σ := 1) one_pos (fun _ _ _ _ => 0) (B := 1)
    (a := 0) (b := 1) (L := 1) one_pos (fun i => by simp) (fun _ _ => u) (fun _ _ _ _ => u)
    (fun _ _ => u) (fun _ _ => hmem _) (fun _ _ => hsq _) (fun _ _ _ _ => hmem _)
    (fun _ _ _ _ => hsq _) (fun _ _ => hmem _) (fun _ _ => hsq _)
    (fun _ _ x => u (chart 0 1 x)) (fun _ _ _ _ x => u (chart 0 1 x)) (fun _ _ x => u (chart 0 1 x))
    (fun _ _ => EventuallyEq.refl _ _) (fun _ _ _ _ => EventuallyEq.refl _ _)
    (fun _ _ => EventuallyEq.refl _ _) (fun _ => 0) isCompact_singleton (fun _ => rfl)
  exact ⟨φ, hφ⟩

end TorusChart
end RenewalGeometry.SobolevOpen
