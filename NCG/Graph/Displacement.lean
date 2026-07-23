/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.Multigraph

/-!
# The displacement semigroupoid and the return-span completion

**Definition `def:displacement-semigroupoid`**: each edge of the control
graph carries a displacement `ξ(e) ∈ Γ`; walk displacements add along
concatenation, so the displacement sets
`𝓜_{st} = {Σ_{e∈p} ξ(e) : p : s → t}` form a **semigroupoid**:
`𝓜_{st} + 𝓜_{tu} ⊆ 𝓜_{su}` (`NCG.Multigraph.displacementSet_add_mem`).

**Theorem `thm:full-rank-returns`** (geometric core): if every positive
multiple of a reachable displacement stays within bounded distance of
the real return span `W`, then the displacement already lies in `W` —
`n·dist(u, W) = dist(n·u, W) ≤ K` forces `dist(u, W) = 0`
(`NCG.mem_of_forall_multiple_infDist_le`).  This is the bounded
return-completion step that gives `rank Γ_ret = r_mon` and hence
`b_eff = r_mon − 1`, `q_alg = 1 + b_eff`. -/

namespace NCG

namespace Multigraph

variable {G : Multigraph} {Γ : Type*} [AddCommGroup Γ]

/-- The **displacement** of a walk: the signed sum of edge displacements
(Definition `def:displacement-semigroupoid`). -/
def Walk.displacement (ξ : G.E → Γ) : ∀ {u v : G.V}, G.Walk u v → Γ
  | _, _, .nil _ => 0
  | _, _, .fwd e p => ξ e + p.displacement ξ
  | _, _, .bwd e p => -ξ e + p.displacement ξ

@[simp]
theorem Walk.displacement_nil (ξ : G.E → Γ) (v : G.V) :
    (Walk.nil (G := G) v).displacement ξ = 0 := rfl

/-- Displacements add along concatenation of walks. -/
theorem Walk.displacement_append (ξ : G.E → Γ) {u v w : G.V}
    (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).displacement ξ
      = p.displacement ξ + q.displacement ξ := by
  induction p with
  | nil v => simp [Walk.nil_append]
  | fwd e p ih =>
      change ξ _ + (p.append q).displacement ξ = _
      rw [ih]
      change _ = ξ _ + p.displacement ξ + q.displacement ξ
      abel
  | bwd e p ih =>
      change -ξ _ + (p.append q).displacement ξ = _
      rw [ih]
      change _ = -ξ _ + p.displacement ξ + q.displacement ξ
      abel

/-- The **displacement set** `𝓜_{uv}` of a state pair
(Definition `def:displacement-semigroupoid`). -/
def displacementSet (ξ : G.E → Γ) (u v : G.V) : Set Γ :=
  Set.range fun p : G.Walk u v => p.displacement ξ

/-- **The semigroupoid law** `𝓜_{uv} + 𝓜_{vw} ⊆ 𝓜_{uw}`
(Definition `def:displacement-semigroupoid`). -/
theorem displacementSet_add_mem (ξ : G.E → Γ) {u v w : G.V} {d d' : Γ}
    (hd : d ∈ displacementSet ξ u v)
    (hd' : d' ∈ displacementSet ξ v w) :
    d + d' ∈ displacementSet ξ u w := by
  obtain ⟨p, rfl⟩ := hd
  obtain ⟨q, rfl⟩ := hd'
  exact ⟨p.append q, Walk.displacement_append ξ p q⟩

end Multigraph

/-! ### The bounded return-completion step (`thm:full-rank-returns`) -/

open Metric Pointwise

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Scaling homogeneity of the distance to a submodule. -/
theorem infDist_smul_submodule (W : Submodule ℝ V) (u : V) {c : ℝ}
    (hc : c ≠ 0) :
    Metric.infDist (c • u) (W : Set V) = |c| * Metric.infDist u W := by
  have hset : c • (W : Set V) = (W : Set V) := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact W.smul_mem c hy
    · intro hw
      exact ⟨c⁻¹ • w, W.smul_mem c⁻¹ hw, by
        change c • (c⁻¹ • w) = w
        rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  calc Metric.infDist (c • u) (W : Set V)
      = Metric.infDist (c • u) (c • (W : Set V)) := by rw [hset]
    _ = ‖c‖ * Metric.infDist u (W : Set V) := infDist_smul₀ hc _ u
    _ = |c| * Metric.infDist u (W : Set V) := by rw [Real.norm_eq_abs]

/-- **Theorem `thm:full-rank-returns`, geometric core** (bounded return
completion): if all positive multiples of `u` stay within distance `K`
of the closed real span `W` of the return lattice, then `u ∈ W`.  Hence
reachable displacements lie in the return span and
`rank Γ_ret = r_mon`. -/
theorem mem_of_forall_multiple_infDist_le [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (u : V) {K : ℝ}
    (h : ∀ n : ℕ, 0 < n → Metric.infDist ((n : ℝ) • u) (W : Set V) ≤ K) :
    u ∈ W := by
  have hd0 : Metric.infDist u (W : Set V) = 0 := by
    by_contra hne
    have hpos : 0 < Metric.infDist u (W : Set V) :=
      lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hne)
    have hK1 : Metric.infDist u (W : Set V) ≤ K := by
      have h1 := h 1 (by norm_num)
      rw [infDist_smul_submodule W u
        (by norm_num : ((1:ℕ):ℝ) ≠ 0)] at h1
      simpa using h1
    obtain ⟨n, hn⟩ := exists_nat_gt (K / Metric.infDist u (W : Set V))
    have hratio : 0 < K / Metric.infDist u (W : Set V) := by
      have hKpos : 0 < K := lt_of_lt_of_le hpos hK1
      positivity
    have hn0 : 0 < n := by exact_mod_cast hratio.trans hn
    have hK := h n hn0
    rw [infDist_smul_submodule W u
      (by exact_mod_cast hn0.ne' : ((n:ℕ):ℝ) ≠ 0)] at hK
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n:ℕ):ℝ))] at hK
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have hclosed : IsClosed (W : Set V) :=
    Submodule.closed_of_finiteDimensional W
  rw [← Metric.mem_closure_iff_infDist_zero ⟨0, W.zero_mem⟩] at hd0
  rwa [hclosed.closure_eq] at hd0

end NCG
