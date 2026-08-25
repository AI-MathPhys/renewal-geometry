/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Relation-valued compactness and tracewise weak closure

Machinery for `thm:GT-relation-valued-limit`.  Compact response graphs `Γ n ⊆ X × Y` converging
in Hausdorff distance to a compact `Γ` (TR.7), together with continuous defects `𝔡 n` converging
uniformly to `𝔡` and vanishing uniformly on `Γ n` (TR.8), give `𝔡 = 0` on `Γ`
(`defect_eq_zero_on_limit`).

The single-valued clause is formalized under the *equicontinuous fibre* hypothesis
`EquicontinuousFibres` (fibres over nearby base points are eventually uniformly close): then the
limit relation has a uniform modulus (`limit_modulus`), its fibres are singletons, and it is the
graph of a continuous response on its domain (`limit_is_graph`).  The literal fibre-diameter
condition (TR.9) alone does not suffice: the graphs of `x ↦ clamp (n x)` have singleton fibres
but converge in Hausdorff distance to a set containing a vertical segment.
-/

open Filter Topology Set Metric

namespace NCG
namespace RelationValued

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Hausdorff convergence of nonempty compact graphs `Γ n` to a nonempty compact `Γ` (TR.7). -/
structure HausdorffLimit (Γ : ℕ → Set (X × Y)) (Γlim : Set (X × Y)) : Prop where
  nonempty : ∀ n, (Γ n).Nonempty
  compact : ∀ n, IsCompact (Γ n)
  limit_nonempty : Γlim.Nonempty
  limit_compact : IsCompact Γlim
  tendsto : Tendsto (fun n => hausdorffDist (Γ n) Γlim) atTop (𝓝 0)

/-- Approximating points: every `p ∈ Γ` is the limit of points `q n ∈ Γ n`. -/
theorem exists_approx {Γ : ℕ → Set (X × Y)} {Γlim : Set (X × Y)} (h : HausdorffLimit Γ Γlim)
    {p : X × Y} (hp : p ∈ Γlim) :
    ∃ q : ℕ → X × Y, (∀ n, q n ∈ Γ n) ∧ Tendsto q atTop (𝓝 p) := by
  have hfin : ∀ n, hausdorffEDist (Γ n) Γlim ≠ ⊤ := fun n =>
    hausdorffEDist_ne_top_of_nonempty_of_bounded (h.nonempty n) h.limit_nonempty
      (h.compact n).isBounded h.limit_compact.isBounded
  have hex : ∀ n, ∃ q ∈ Γ n, dist q p < hausdorffDist (Γ n) Γlim + 1 / ((n : ℝ) + 1) := fun n =>
    exists_dist_lt_of_hausdorffDist_lt' hp (lt_add_of_pos_right _ (by positivity)) (hfin n)
  choose q hq hqd using hex
  refine ⟨q, hq, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : Tendsto (fun n : ℕ => hausdorffDist (Γ n) Γlim + 1 / ((n : ℝ) + 1)) atTop
      (𝓝 0) := by
    have := h.tendsto.add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this
  exact squeeze_zero (fun n => dist_nonneg) (fun n => (hqd n).le) hbound

/-- **(TR.8) closure**: a continuous defect family converging uniformly and vanishing uniformly on
`Γ n` vanishes on the Hausdorff limit `Γ`. -/
theorem defect_eq_zero_on_limit {Γ : ℕ → Set (X × Y)} {Γlim : Set (X × Y)}
    (h : HausdorffLimit Γ Γlim) {𝔡 : ℕ → X × Y → ℝ} {𝔡lim : X × Y → ℝ}
    (hcont : ∀ n, Continuous (𝔡 n)) (hnonneg : ∀ n p, 0 ≤ 𝔡 n p)
    (hunif : TendstoUniformly 𝔡 𝔡lim atTop)
    (hvan : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ p ∈ Γ n, 𝔡 n p < ε) {p : X × Y} (hp : p ∈ Γlim) :
    𝔡lim p = 0 := by
  obtain ⟨q, hq, hqp⟩ := exists_approx h hp
  have hlim_cont : Continuous 𝔡lim := hunif.continuous (Eventually.of_forall hcont).frequently
  have h1 : Tendsto (fun n => 𝔡 n (q n)) atTop (𝓝 (𝔡lim p)) :=
    hunif.tendsto_comp hlim_cont.continuousAt hqp
  have h2 : Tendsto (fun n => 𝔡 n (q n)) atTop (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha (hnonneg n _),
      fun a ha => ?_⟩
    filter_upwards [hvan a ha] with n hn
    exact hn _ (hq n)
  exact tendsto_nhds_unique h1 h2

/-- Equicontinuous fibres: responses over nearby base points are eventually uniformly close. -/
def EquicontinuousFibres (Γ : ℕ → Set (X × Y)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
    ∀ p ∈ Γ n, ∀ p' ∈ Γ n, dist p.1 p'.1 < δ → dist p.2 p'.2 < ε

/-- **Uniform modulus of the limit relation** under equicontinuous fibres. -/
theorem limit_modulus {Γ : ℕ → Set (X × Y)} {Γlim : Set (X × Y)} (h : HausdorffLimit Γ Γlim)
    (hfib : EquicontinuousFibres Γ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ p ∈ Γlim, ∀ p' ∈ Γlim, dist p.1 p'.1 < δ → dist p.2 p'.2 ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hev⟩ := hfib (ε / 3) (by positivity)
  refine ⟨δ / 2, by positivity, fun p hp p' hp' hpp' => ?_⟩
  obtain ⟨q, hq, hqp⟩ := exists_approx h hp
  obtain ⟨q', hq', hqp'⟩ := exists_approx h hp'
  -- pick `n` with both approximants within `η = min (δ/4) (ε/3)`
  set η : ℝ := min (δ / 4) (ε / 3) with hη
  have hηpos : 0 < η := by positivity
  have e1 : ∀ᶠ n in atTop, dist (q n) p < η := (tendsto_iff_dist_tendsto_zero.mp hqp).eventually
    (gt_mem_nhds hηpos)
  have e2 : ∀ᶠ n in atTop, dist (q' n) p' < η :=
    (tendsto_iff_dist_tendsto_zero.mp hqp').eventually (gt_mem_nhds hηpos)
  obtain ⟨n, hn1, hn2, hn3⟩ := (e1.and (e2.and hev)).exists
  have hfst : ∀ a b : X × Y, dist a.1 b.1 ≤ dist a b := fun a b => by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hsnd : ∀ a b : X × Y, dist a.2 b.2 ≤ dist a b := fun a b => by
    rw [Prod.dist_eq]; exact le_max_right _ _
  have hx1 : dist (q n).1 p.1 < η := lt_of_le_of_lt (hfst _ _) hn1
  have hx2 : dist (q' n).1 p'.1 < η := lt_of_le_of_lt (hfst _ _) hn2
  have hy1 : dist (q n).2 p.2 < η := lt_of_le_of_lt (hsnd _ _) hn1
  have hy2 : dist (q' n).2 p'.2 < η := lt_of_le_of_lt (hsnd _ _) hn2
  have hηδ : η ≤ δ / 4 := min_le_left _ _
  have hηε : η ≤ ε / 3 := min_le_right _ _
  have hbase : dist (q n).1 (q' n).1 < δ := by
    calc dist (q n).1 (q' n).1 ≤ dist (q n).1 p.1 + dist p.1 p'.1 + dist p'.1 (q' n).1 :=
          dist_triangle4 _ _ _ _
      _ < η + δ / 2 + η := by
          rw [dist_comm p'.1]
          linarith
      _ ≤ δ := by linarith
  have hfibre := hn3 (q n) (hq n) (q' n) (hq' n) hbase
  calc dist p.2 p'.2 ≤ dist p.2 (q n).2 + dist (q n).2 (q' n).2 + dist (q' n).2 p'.2 :=
        dist_triangle4 _ _ _ _
    _ ≤ η + ε / 3 + η := by
        rw [dist_comm p.2]
        linarith
    _ ≤ ε := by linarith

/-- Under equicontinuous fibres the limit fibres are singletons. -/
theorem limit_fibre_subsingleton {Γ : ℕ → Set (X × Y)} {Γlim : Set (X × Y)}
    (h : HausdorffLimit Γ Γlim) (hfib : EquicontinuousFibres Γ) {x : X} {y y' : Y}
    (hy : (x, y) ∈ Γlim) (hy' : (x, y') ∈ Γlim) : y = y' := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨δ, hδ, hmod⟩ := limit_modulus h hfib ε hε
  exact hmod (x, y) hy (x, y') hy' (by simpa using hδ)

/-- **Relation-to-function passage**: under equicontinuous fibres the limit relation is the graph
of a continuous response on its domain `Prod.fst '' Γ`. -/
theorem limit_is_graph {Γ : ℕ → Set (X × Y)} {Γlim : Set (X × Y)} (h : HausdorffLimit Γ Γlim)
    (hfib : EquicontinuousFibres Γ) :
    ∃ f : X → Y, ContinuousOn f (Prod.fst '' Γlim) ∧
      Γlim = {p : X × Y | p.1 ∈ Prod.fst '' Γlim ∧ p.2 = f p.1} := by
  classical
  have hex : ∀ x : X, x ∈ Prod.fst '' Γlim → ∃ y, (x, y) ∈ Γlim := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  choose f hf using hex
  let g : X → Y := fun x =>
    if hx : x ∈ Prod.fst '' Γlim then f x hx else h.limit_nonempty.some.2
  have hg : ∀ x (hx : x ∈ Prod.fst '' Γlim), (x, g x) ∈ Γlim := by
    intro x hx
    simp only [g, dif_pos hx]
    exact hf x hx
  refine ⟨g, ?_, ?_⟩
  · rw [Metric.continuousOn_iff]
    intro b hb ε hε
    obtain ⟨δ, hδ, hmod⟩ := limit_modulus h hfib (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun a ha hab => ?_⟩
    have := hmod (a, g a) (hg a ha) (b, g b) (hg b hb) hab
    linarith
  · ext p
    constructor
    · intro hp
      have hdom : p.1 ∈ Prod.fst '' Γlim := ⟨p, hp, rfl⟩
      refine ⟨hdom, limit_fibre_subsingleton h hfib (x := p.1) hp (hg p.1 hdom)⟩
    · rintro ⟨hdom, hp2⟩
      have : p = (p.1, g p.1) := Prod.ext rfl hp2
      rw [this]
      exact hg p.1 hdom

/-- **`thm:GT-relation-valued-limit`**, the defect-closure clause (TR.7)+(TR.8) and the
single-valued continuous-response clause under equicontinuous fibres. -/
theorem relation_valued_limit {Γ : ℕ → Set (X × Y)} {Γlim : Set (X × Y)} (h : HausdorffLimit Γ Γlim)
    {ι : Type*} {𝔡 : ι → ℕ → X × Y → ℝ} {𝔡lim : ι → X × Y → ℝ}
    (hcont : ∀ j n, Continuous (𝔡 j n)) (hnonneg : ∀ j n p, 0 ≤ 𝔡 j n p)
    (hunif : ∀ j, TendstoUniformly (𝔡 j) (𝔡lim j) atTop)
    (hvan : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ p ∈ Γ n, 𝔡 j n p < ε) :
    (∀ p ∈ Γlim, ∀ j, 𝔡lim j p = 0) ∧
      (EquicontinuousFibres Γ → ∃ f : X → Y, ContinuousOn f (Prod.fst '' Γlim) ∧
        Γlim = {p : X × Y | p.1 ∈ Prod.fst '' Γlim ∧ p.2 = f p.1}) :=
  ⟨fun _p hp j => defect_eq_zero_on_limit h (hcont j) (hnonneg j) (hunif j) (hvan j) hp,
    fun hfib => limit_is_graph h hfib⟩

end RelationValued
end NCG
