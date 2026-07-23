/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.Multigraph
import Mathlib

/-!
# Edge-labelled instruments and multiplicative path weights

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:ray-bi-instrument` — ray-homogeneous bi-instruments: ordered
  carriers with positive reference vectors, positive branch maps
  `F_e, R_e` scaling the reference rays by strictly positive weights
  `p⁺_e, p⁻_e`;
* `prop:multiplicative-path-weights` — accumulated branch maps scale
  the reference rays by the products `W_±(γ) = ∏ p^±_{e_k}`, which
  are multiplicative under concatenation;
* `def:instrument-congruence` — path congruences compatible with
  both weights;
* `thm:path-weight-descent` — the weights descend to a path quotient
  iff the congruence is instrument compatible; equality of
  accumulated branch maps — or merely of their actions on the
  reference rays — is sufficient;
* `prop:kraus-invariance` — the ray coefficient depends only on the
  CP branch map: isometric mixing of a Kraus family leaves the
  branch map, hence all path weights, unchanged;
* `thm:block-petz-reverse` — for the block reset instrument the
  stationary Petz reverse of a branch is
  `(π_x p_e/π_y) Tr(·) ρ_x`; the reversed branches sum to a
  trace-preserving channel, and the same-orientation edge affinity
  is `log(π_{s(e)} p_e/(π_{t(e)} p_{ē}))`.
-/

namespace NCG.Upstream

open NCG

/-! ## Directed paths in a multigraph -/

/-- A directed path `e_n ⋯ e_1` with `t(e_k) = s(e_{k+1})`. -/
inductive DirPath (G : Multigraph) : G.V → G.V → Type _
  | nil (v : G.V) : DirPath G v v
  | cons (e : G.E) {w : G.V} (p : DirPath G (G.tgt e) w) :
      DirPath G (G.src e) w

namespace DirPath

variable {G : Multigraph}

/-- Concatenation of directed paths. -/
def append : ∀ {u v w : G.V},
    DirPath G u v → DirPath G v w → DirPath G u w
  | _, _, _, .nil _, q => q
  | _, _, _, .cons e p, q => .cons e (p.append q)

@[simp] theorem nil_append {v w : G.V} (q : DirPath G v w) :
    (DirPath.nil v).append q = q := by
  simp [DirPath.append]

@[simp] theorem cons_append (e : G.E) {v w : G.V}
    (p : DirPath G (G.tgt e) v) (q : DirPath G v w) :
    (DirPath.cons e p).append q = DirPath.cons e (p.append q) := by
  simp [DirPath.append]

end DirPath

/-! ## `def:ray-bi-instrument` -/

variable {G : Multigraph} {X : G.V → Type*}
  [∀ x, AddCommGroup (X x)] [∀ x, Module ℝ (X x)]
  [∀ x, PartialOrder (X x)]
  [∀ x, NoZeroSMulDivisors ℝ (X x)]

/-- **Definition `def:ray-bi-instrument`**: a ray-homogeneous
bi-instrument — positive branch maps `F_e` (renewal) and `R_e`
(anti-renewal, reindexed in the same orientation) scaling positive
reference vectors by strictly positive edge weights. -/
structure RayBiInstrument (G : Multigraph) (X : G.V → Type*)
    [∀ x, AddCommGroup (X x)] [∀ x, Module ℝ (X x)]
    [∀ x, PartialOrder (X x)] where
  /-- The positive reference vector at each vertex. -/
  η : ∀ x, X x
  η_pos : ∀ x, 0 < η x
  /-- The renewal branch maps. -/
  F : ∀ e : G.E, X (G.src e) →ₗ[ℝ] X (G.tgt e)
  /-- The anti-renewal branch maps (same orientation). -/
  R : ∀ e : G.E, X (G.src e) →ₗ[ℝ] X (G.tgt e)
  F_pos : ∀ (e : G.E) (v : X (G.src e)), 0 ≤ v → 0 ≤ F e v
  R_pos : ∀ (e : G.E) (v : X (G.src e)), 0 ≤ v → 0 ≤ R e v
  /-- The forward edge weights `p⁺`. -/
  wp : G.E → ℝ
  /-- The backward edge weights `p⁻`. -/
  wm : G.E → ℝ
  wp_pos : ∀ e, 0 < wp e
  wm_pos : ∀ e, 0 < wm e
  hF : ∀ e, F e (η (G.src e)) = wp e • η (G.tgt e)
  hR : ∀ e, R e (η (G.src e)) = wm e • η (G.tgt e)

namespace RayBiInstrument

variable (I : RayBiInstrument G X)

theorem η_ne_zero (x : G.V) : I.η x ≠ 0 := (I.η_pos x).ne'

/-! ## `prop:multiplicative-path-weights` -/

/-- The forward path weight `W₊(γ) = ∏ p⁺_{e_k}`. -/
def weightP : ∀ {x y : G.V}, DirPath G x y → ℝ
  | _, _, .nil _ => 1
  | _, _, .cons e p => I.wp e * weightP p

/-- The backward path weight `W₋(γ) = ∏ p⁻_{e_k}`. -/
def weightM : ∀ {x y : G.V}, DirPath G x y → ℝ
  | _, _, .nil _ => 1
  | _, _, .cons e p => I.wm e * weightM p

@[simp] theorem weightP_nil (v : G.V) :
    I.weightP (DirPath.nil v) = 1 := by
  simp [weightP]

@[simp] theorem weightP_cons (e : G.E) {w : G.V}
    (p : DirPath G (G.tgt e) w) :
    I.weightP (DirPath.cons e p) = I.wp e * I.weightP p := by
  simp [weightP]

@[simp] theorem weightM_nil (v : G.V) :
    I.weightM (DirPath.nil v) = 1 := by
  simp [weightM]

@[simp] theorem weightM_cons (e : G.E) {w : G.V}
    (p : DirPath G (G.tgt e) w) :
    I.weightM (DirPath.cons e p) = I.wm e * I.weightM p := by
  simp [weightM]

/-- The accumulated renewal branch map `F_γ`. -/
def mapF : ∀ {x y : G.V}, DirPath G x y → (X x →ₗ[ℝ] X y)
  | _, _, .nil _ => LinearMap.id
  | _, _, .cons e p => (mapF p).comp (I.F e)

/-- The accumulated anti-renewal branch map `R_γ`. -/
def mapR : ∀ {x y : G.V}, DirPath G x y → (X x →ₗ[ℝ] X y)
  | _, _, .nil _ => LinearMap.id
  | _, _, .cons e p => (mapR p).comp (I.R e)

@[simp] theorem mapF_nil (v : G.V) :
    I.mapF (DirPath.nil v) = LinearMap.id := by
  simp [mapF]

@[simp] theorem mapF_cons (e : G.E) {w : G.V}
    (p : DirPath G (G.tgt e) w) :
    I.mapF (DirPath.cons e p) = (I.mapF p).comp (I.F e) := by
  simp [mapF]

@[simp] theorem mapR_nil (v : G.V) :
    I.mapR (DirPath.nil v) = LinearMap.id := by
  simp [mapR]

@[simp] theorem mapR_cons (e : G.E) {w : G.V}
    (p : DirPath G (G.tgt e) w) :
    I.mapR (DirPath.cons e p) = (I.mapR p).comp (I.R e) := by
  simp [mapR]

/-- **Proposition `prop:multiplicative-path-weights` (renewal)**:
`F_γ η_{s(γ)} = W₊(γ) η_{t(γ)}`. -/
theorem mapF_eta : ∀ {x y : G.V} (γ : DirPath G x y),
    I.mapF γ (I.η x) = I.weightP γ • I.η y
  | _, _, .nil v => by simp
  | _, _, .cons e p => by
    rw [mapF_cons, LinearMap.comp_apply, I.hF e, map_smul,
      mapF_eta p, smul_smul, weightP_cons]

/-- **Proposition `prop:multiplicative-path-weights`
(anti-renewal)**: `R_γ η_{s(γ)} = W₋(γ) η_{t(γ)}`. -/
theorem mapR_eta : ∀ {x y : G.V} (γ : DirPath G x y),
    I.mapR γ (I.η x) = I.weightM γ • I.η y
  | _, _, .nil v => by simp
  | _, _, .cons e p => by
    rw [mapR_cons, LinearMap.comp_apply, I.hR e, map_smul,
      mapR_eta p, smul_smul, weightM_cons]

/-- **Proposition `prop:multiplicative-path-weights`
(multiplicativity)**: `W₊(γ₂γ₁) = W₊(γ₂) W₊(γ₁)`. -/
theorem weightP_append : ∀ {u v w : G.V} (p : DirPath G u v)
    (q : DirPath G v w),
    I.weightP (p.append q) = I.weightP p * I.weightP q
  | _, _, _, .nil _, q => by
    rw [DirPath.nil_append, weightP_nil, one_mul]
  | _, _, _, .cons e p, q => by
    rw [DirPath.cons_append, weightP_cons, weightP_append p q,
      weightP_cons]
    ring

theorem weightM_append : ∀ {u v w : G.V} (p : DirPath G u v)
    (q : DirPath G v w),
    I.weightM (p.append q) = I.weightM p * I.weightM q
  | _, _, _, .nil _, q => by
    rw [DirPath.nil_append, weightM_nil, one_mul]
  | _, _, _, .cons e p, q => by
    rw [DirPath.cons_append, weightM_cons, weightM_append p q,
      weightM_cons]
    ring

/-! ## `def:instrument-congruence` and `thm:path-weight-descent` -/

/-- **Definition `def:instrument-congruence`**: a path congruence is
instrument compatible when related paths carry equal forward and
backward weights. -/
def InstrumentCompatible
    (rel : ∀ {x y : G.V}, DirPath G x y → DirPath G x y → Prop) :
    Prop :=
  ∀ {x y : G.V} (γ γ' : DirPath G x y), rel γ γ' →
    I.weightP γ = I.weightP γ' ∧ I.weightM γ = I.weightM γ'

/-- **Theorem `thm:path-weight-descent` (descent criterion)**: the
weights descend (uniquely) to the path quotient iff the congruence
is instrument compatible. -/
theorem weight_descent
    (rel : ∀ {x y : G.V}, DirPath G x y → DirPath G x y → Prop) :
    ((∀ x y : G.V, ∃ WP WM :
        Quot (rel (x := x) (y := y)) → ℝ,
        (∀ γ, WP (Quot.mk _ γ) = I.weightP γ)
          ∧ ∀ γ, WM (Quot.mk _ γ) = I.weightM γ))
      ↔ I.InstrumentCompatible @rel := by
  constructor
  · intro h x y γ γ' hrel
    obtain ⟨WP, WM, hWP, hWM⟩ := h x y
    constructor
    · rw [← hWP γ, ← hWP γ', Quot.sound hrel]
    · rw [← hWM γ, ← hWM γ', Quot.sound hrel]
  · intro h x y
    exact ⟨Quot.lift I.weightP (fun γ γ' hrel => (h γ γ' hrel).1),
      Quot.lift I.weightM (fun γ γ' hrel => (h γ γ' hrel).2),
      fun γ => rfl, fun γ => rfl⟩

/-- Weights are determined by the action on the reference ray. -/
theorem weight_eq_of_ray_eq {x y : G.V} {γ γ' : DirPath G x y}
    (hray : I.mapF γ (I.η x) = I.mapF γ' (I.η x)) :
    I.weightP γ = I.weightP γ' := by
  rw [I.mapF_eta γ, I.mapF_eta γ'] at hray
  have h := sub_eq_zero.mpr hray
  rw [← sub_smul] at h
  rcases smul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (I.η_ne_zero y)

theorem weightM_eq_of_ray_eq {x y : G.V} {γ γ' : DirPath G x y}
    (hray : I.mapR γ (I.η x) = I.mapR γ' (I.η x)) :
    I.weightM γ = I.weightM γ' := by
  rw [I.mapR_eta γ, I.mapR_eta γ'] at hray
  have h := sub_eq_zero.mpr hray
  rw [← sub_smul] at h
  rcases smul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (I.η_ne_zero y)

/-- **Theorem `thm:path-weight-descent` (sufficient conditions)**:
equality of accumulated branch maps — or merely of their actions on
the reference rays — makes a congruence instrument compatible. -/
theorem instrumentCompatible_of_map_eq
    (rel : ∀ {x y : G.V}, DirPath G x y → DirPath G x y → Prop)
    (hmaps : ∀ {x y : G.V} (γ γ' : DirPath G x y), rel γ γ' →
      I.mapF γ (I.η x) = I.mapF γ' (I.η x)
        ∧ I.mapR γ (I.η x) = I.mapR γ' (I.η x)) :
    I.InstrumentCompatible @rel := by
  intro x y γ γ' hrel
  exact ⟨I.weight_eq_of_ray_eq (hmaps γ γ' hrel).1,
    I.weightM_eq_of_ray_eq (hmaps γ γ' hrel).2⟩

end RayBiInstrument

/-! ## `prop:kraus-invariance` -/

section Kraus

variable {d : ℕ}

/-- The CP map of a Kraus family. -/
noncomputable def krausMap {ι : Type*} [Fintype ι]
    (K : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ :=
  fun ρ => ∑ a, K a * ρ * star (K a)

/-- **Proposition `prop:kraus-invariance` (isometric mixing)**:
Kraus families related by an isometric change of section define the
same CP branch map. -/
theorem krausMap_isometric_mix {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι]
    (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (K' : κ → Matrix (Fin d) (Fin d) ℂ)
    (u : κ → ι → ℂ)
    (hiso : ∀ b c : ι,
      ∑ a, star (u a b) * u a c = if b = c then 1 else 0)
    (hmix : ∀ a, K' a = ∑ b, u a b • K b) :
    krausMap K' = krausMap K := by
  funext ρ
  unfold krausMap
  have hδ : ∀ b c : ι, ∑ a, u a b * star (u a c)
      = if b = c then 1 else 0 := by
    intro b c
    calc ∑ a, u a b * star (u a c)
        = star (∑ a, star (u a b) * u a c) := by
          rw [star_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [star_mul, star_star]
          ring
      _ = star (if b = c then (1 : ℂ) else 0) := by rw [hiso b c]
      _ = if b = c then 1 else 0 := by split_ifs <;> simp
  have hterm : ∀ a : κ, K' a * ρ * star (K' a)
      = ∑ b, ∑ c, (u a b * star (u a c))
          • (K b * ρ * star (K c)) := by
    intro a
    rw [hmix a]
    have h1 : star (∑ b, u a b • K b)
        = ∑ c, star (u a c) • star (K c) := by
      rw [star_sum]
      exact Finset.sum_congr rfl fun c _ => star_smul _ _
    rw [h1, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm]
  calc ∑ a : κ, K' a * ρ * star (K' a)
      = ∑ a : κ, ∑ b, ∑ c, (u a b * star (u a c))
          • (K b * ρ * star (K c)) :=
        Finset.sum_congr rfl fun a _ => hterm a
    _ = ∑ b, ∑ c, (∑ a : κ, u a b * star (u a c))
          • (K b * ρ * star (K c)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ b, ∑ c, (if b = c then (1 : ℂ) else 0)
          • (K b * ρ * star (K c)) := by
        refine Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        rw [hδ b c]
    _ = ∑ b, K b * ρ * star (K b) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp [ite_smul]
  -- goal closed by the calc

/-- **Proposition `prop:kraus-invariance` (ray coefficient)**: the
coefficient scaling the reference ray depends only on the branch
map — equal branch maps (e.g. isometrically mixed Kraus families)
have equal ray coefficients; the path weights and affinity are
therefore Kraus-representation independent. -/
theorem krausMap_ray_coeff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (K' : κ → Matrix (Fin d) (Fin d) ℂ)
    (h : krausMap K = krausMap K')
    (η ξ : Matrix (Fin d) (Fin d) ℂ) (hξ : ξ ≠ 0) (c c' : ℂ)
    (hc : krausMap K η = c • ξ) (hc' : krausMap K' η = c' • ξ) :
    c = c' := by
  have h1 : c • ξ = c' • ξ := by
    rw [← hc, ← hc', h]
  have h2 : (c - c') • ξ = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hξ

end Kraus

/-! ## `thm:block-petz-reverse` -/

section BlockPetz

variable {Ax Ay : Type*} [Ring Ax] [Algebra ℂ Ax]
  [Ring Ay] [Algebra ℂ Ay]
variable (τx : Ax →ₗ[ℂ] ℂ) (τy : Ay →ₗ[ℂ] ℂ)
variable (σx : Ax) (σy σyi : Ay)

/-- The Schrödinger reset branch `𝓘_e(σ) = p_e Tr(σ) ρ_y`
(with `ρ_y = σ_y²`). -/
noncomputable def blockBranch (pe : ℝ) (σ : Ax) : Ay :=
  ((pe : ℂ) * τx σ) • (σy * σy)

/-- Its Heisenberg adjoint `𝓘_e^*(a) = p_e Tr(ρ_y a) 1_x`. -/
noncomputable def blockBranchHeis (pe : ℝ) (a : Ay) : Ax :=
  ((pe : ℂ) * τy ((σy * σy) * a)) • (1 : Ax)

/-- The adjoint satisfies the defining trace pairing. -/
theorem blockBranch_pairing (pe : ℝ) (σ : Ax) (a : Ay) :
    τy (blockBranch τx σy pe σ * a)
      = τx (σ * blockBranchHeis τy σy pe a) := by
  unfold blockBranch blockBranchHeis
  rw [smul_mul_assoc, map_smul, mul_smul_comm, map_smul, mul_one]
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-- The stationary Petz reverse of the branch,
`Γ_{D_x} ∘ 𝓘_e^* ∘ Γ_{D_y}⁻¹` with `D_x = π_x ρ_x`. -/
noncomputable def blockPetzReverse (πx πy pe : ℝ) (τ : Ay) : Ax :=
  (πx : ℂ) • (σx * blockBranchHeis τy σy pe
    ((πy : ℂ)⁻¹ • (σyi * τ * σyi)) * σx)

/-- **Theorem `thm:block-petz-reverse` (the boxed formula)**: the
stationary Petz reverse of the reset branch `e : x → y` is
`𝓘_e^←(τ) = (π_x p_e/π_y) Tr(τ) ρ_x`. -/
theorem blockPetzReverse_formula
    (hτyc : ∀ a b : Ay, τy (a * b) = τy (b * a))
    (hσy : σy * σyi = 1) (hσyi : σyi * σy = 1)
    (πx πy pe : ℝ) (hπy : πy ≠ 0) (τ : Ay) :
    blockPetzReverse τy σx σy σyi πx πy pe τ
      = (((πx * pe / πy : ℝ) : ℂ) * τy τ) • (σx * σx) := by
  unfold blockPetzReverse blockBranchHeis
  have hτ : τy ((σy * σy) * ((πy : ℂ)⁻¹ • (σyi * τ * σyi)))
      = (πy : ℂ)⁻¹ * τy τ := by
    rw [mul_smul_comm, map_smul, smul_eq_mul]
    congr 1
    calc τy ((σy * σy) * (σyi * τ * σyi))
        = τy ((σy * (σy * σyi)) * (τ * σyi)) := by
          congr 1
          noncomm_ring
      _ = τy (σy * (τ * σyi)) := by rw [hσy, mul_one]
      _ = τy ((τ * σyi) * σy) := hτyc _ _
      _ = τy (τ * (σyi * σy)) := by
          congr 1
          noncomm_ring
      _ = τy τ := by rw [hσyi, mul_one]
  rw [hτ]
  rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul]
  congr 1
  have hπyc : (πy : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hπy
  push_cast
  field_simp

/-- **Theorem `thm:block-petz-reverse` (trace preservation)**: the
reversed branches sum to a trace-preserving channel — the reversed
traces `(π_x p_e/π_y) Tr(τ)` over all incoming branches sum to
`Tr(τ)` by stationarity of `π`. -/
theorem blockPetzReverse_trace_sum {ι : Type*} (s : Finset ι)
    (πs ps : ι → ℝ) (πy : ℝ) (hπy : πy ≠ 0)
    (hstat : ∑ e ∈ s, πs e * ps e = πy) (t : ℂ) :
    ∑ e ∈ s, (((πs e * ps e / πy : ℝ) : ℂ) * t) = t := by
  rw [← Finset.sum_mul]
  rw [show ∑ e ∈ s, ((πs e * ps e / πy : ℝ) : ℂ)
      = ((∑ e ∈ s, πs e * ps e) / πy : ℝ) from by
    push_cast [Finset.sum_div]
    rfl]
  rw [hstat, div_self hπy, Complex.ofReal_one, one_mul]

/-- **Theorem `thm:block-petz-reverse` (edge affinity)**: with the
same-orientation backward weight `p⁻_e = π_{t(e)} p_{ē}/π_{s(e)}`,
the edge affinity is
`A(e) = log(p_e/p⁻_e) = log(π_{s(e)} p_e/(π_{t(e)} p_{ē}))`. -/
theorem blockPetzReverse_affinity (πs πt pe peb : ℝ)
    (hπs : 0 < πs) (hπt : 0 < πt) (hpeb : 0 < peb) :
    Real.log (pe / (πt * peb / πs))
      = Real.log (πs * pe / (πt * peb)) := by
  congr 1
  field_simp

end BlockPetz

end NCG.Upstream
