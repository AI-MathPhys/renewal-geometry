/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.VolumeElement

/-!
# Oriented interference closure and the `d = 3` selection

* **Lemma `lem:interference-lorentz-pair`** — the bracket relations of
  the interference sector: `[ΓᵢΓⱼ, Γₖ] = 2δⱼₖΓᵢ − 2δᵢₖΓⱼ`
  (`NCG.bivector_vector_bracket`) and `[Kᵢ,Kⱼ] = ½ΓᵢΓⱼ = −Jᵢⱼ`
  (`NCG.boost_bracket`) — the Cartan-decomposition relations of
  `𝔰𝔬(d,1)` on `𝕀 ⊕ V_sp`.  (Linear independence of the bivector
  monomials and the global Lie-algebra isomorphism are not formalised.)

* **Theorem `thm:interference-independence`** (dimension dichotomy):
  at `d = 3` a closure isomorphism `⋀²V ≅ V` exists
  (`NCG.closure_iso_of_three`); for `d ≥ 4` none exists
  (`NCG.no_closure_iso`) — closure is satisfiable and falsifiable.
  (The bouquet/cross-polytope model realising the axiom package is the
  earlier proved material; the axiom bookkeeping is informal.)

* **Theorem `thm:interference-closure-selects-three`** — `⋀²V = 0` at
  `d = 1` (`NCG.wedge_two_dim_one`), and among `d ≥ 3` the volume-dual
  image has degree one iff `d = 3` (`NCG.closure_selects_three`).

* **Definition `def:volume-dual-response`** — the volume element is
  invertible (`NCG.volume_isUnit`, from `Vol² = ±1`), so
  `H = Vol⁻¹·b_ren` is defined; orientation reversal flips its sign.

* **Propositions `prop:hodge-interference-closure`,
  `prop:clifford-internal-interference`** (`d = 3`): `Vol² = −1`
  (`NCG.vol3_sq`), the `ε`-identities `ΓᵢΓⱼ = ε_{ijk}·Vol·Γₖ`
  (`NCG.vol3_gamma01` …), the Hodge bracket is the cross product and
  satisfies Jacobi (`NCG.hodge_bracket_jacobi`); the temporal
  anticommutation is `NCG.temporal_anticomm_volume`. -/

namespace NCG

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-! ### The Lorentz pair brackets (`lem:interference-lorentz-pair`) -/

section Brackets

variable {d : ℕ} (g : Fin d → A)

/-- Reversal rule from the Clifford relation. -/
theorem clifford_swap
    (hrel : ∀ i j, g i * g j + g j * g i
      = (if i = j then (2 : ℝ) else 0) • 1) (a b : Fin d) :
    g b * g a = (if a = b then (2 : ℝ) else 0) • 1 - g a * g b :=
  eq_sub_of_add_eq' (hrel a b)

/-- **Lemma `lem:interference-lorentz-pair`**, mixed bracket:
`[ΓᵢΓⱼ, Γₖ] = 2δⱼₖΓᵢ − 2δᵢₖΓⱼ` — the interference sector acts on the
revision sector by the standard `𝔰𝔬` rotation action. -/
theorem bivector_vector_bracket
    (hrel : ∀ i j, g i * g j + g j * g i
      = (if i = j then (2 : ℝ) else 0) • 1) (i j k : Fin d) :
    (g i * g j) * g k - g k * (g i * g j)
      = (if j = k then (2 : ℝ) else 0) • g i
        - (if i = k then (2 : ℝ) else 0) • g j := by
  have hexp : g k * (g i * g j)
      = (if i = k then (2 : ℝ) else 0) • g j
        - (if j = k then (2 : ℝ) else 0) • g i
        + (g i * g j) * g k := by
    calc g k * (g i * g j) = (g k * g i) * g j := (mul_assoc _ _ _).symm
      _ = ((if i = k then (2 : ℝ) else 0) • 1 - g i * g k) * g j := by
          rw [clifford_swap g hrel i k]
      _ = (if i = k then (2 : ℝ) else 0) • g j
          - g i * (g k * g j) := by
          rw [sub_mul, smul_mul_assoc, one_mul, mul_assoc]
      _ = (if i = k then (2 : ℝ) else 0) • g j
          - g i * ((if j = k then (2 : ℝ) else 0) • 1 - g j * g k) := by
          rw [clifford_swap g hrel j k]
      _ = (if i = k then (2 : ℝ) else 0) • g j
          - (if j = k then (2 : ℝ) else 0) • g i
          + (g i * g j) * g k := by
          rw [mul_sub, mul_smul_comm, mul_one, ← mul_assoc]
          abel
  rw [hexp]
  abel

/-- **Lemma `lem:interference-lorentz-pair`**, boost bracket:
`[Kᵢ, Kⱼ] = ½ΓᵢΓⱼ = −Jᵢⱼ` for `i ≠ j` — spatial generators close onto
the interference sector, the Cartan relation of `𝔰𝔬(d,1)`. -/
theorem boost_bracket
    (hrel : ∀ i j, g i * g j + g j * g i
      = (if i = j then (2 : ℝ) else 0) • 1) (i j : Fin d) (hij : i ≠ j) :
    ((1/2 : ℝ) • g i) * ((1/2 : ℝ) • g j)
      - ((1/2 : ℝ) • g j) * ((1/2 : ℝ) • g i)
      = (1/2 : ℝ) • (g i * g j) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm,
    clifford_swap g hrel i j, if_neg hij]
  rw [zero_smul, zero_sub, smul_neg, sub_neg_eq_add, ← add_smul]
  norm_num

end Brackets

/-! ### The dimension dichotomy (`thm:interference-independence`,
`thm:interference-closure-selects-three`) -/

section Dichotomy

open Module

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- **Theorem `thm:interference-independence` (i)**: at `d = 3` the
closure isomorphism `⋀²V ≅ V` exists. -/
theorem closure_iso_of_three (hd : finrank K V = 3) :
    Nonempty ((⋀[K]^2 V) ≃ₗ[K] V) := by
  refine ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩
  rw [exteriorPower.finrank_eq, hd]
  norm_num

/-- **Theorem `thm:interference-independence` (ii)**: for `d ≥ 4` no
closure isomorphism `⋀²V ≅ V` exists — `C(d,2) ≠ d`. -/
theorem no_closure_iso (hd : 4 ≤ finrank K V) :
    IsEmpty ((⋀[K]^2 V) ≃ₗ[K] V) := by
  constructor
  intro e
  have h1 := e.finrank_eq
  rw [exteriorPower.finrank_eq, Nat.choose_two_right] at h1
  set n := finrank K V with hn
  have heven : n * (n - 1) = 2 * (n * (n - 1) / 2) := by
    have hpar : Even ((n - 1) * n) := by
      have := Nat.even_mul_succ_self (n - 1)
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at this
    rw [mul_comm (n - 1) n] at hpar
    obtain ⟨k, hk⟩ := hpar
    set x := n * (n - 1) with hx
    omega
  have h2 : n * (n - 1) = n * 2 := by
    rw [heven, h1]
    ring
  have h3 : n - 1 = 2 :=
    Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) h2
  omega

/-- **Theorem `thm:interference-closure-selects-three`**, `d = 1`
degenerate case: the bivector domain vanishes, `⋀²V = 0`. -/
theorem wedge_two_dim_one (hd : finrank K V = 1) :
    finrank K (⋀[K]^2 V) = 0 := by
  rw [exteriorPower.finrank_eq, hd]
  norm_num

end Dichotomy

/-- **Theorem `thm:interference-closure-selects-three`**, degree
selection: among ranks `d ≥ 3` the volume-dual image (degree `d − 2` by
`prop:volume-dual-degree`) is elementary — degree one — iff `d = 3`. -/
theorem closure_selects_three {d : ℕ} (h3 : 3 ≤ d) :
    d - 2 = 1 ↔ d = 3 := by
  omega

/-! ### The volume-dual response is defined
(`def:volume-dual-response`) -/

section VolUnit

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
omit [Algebra ℝ A] in
/-- **Definition `def:volume-dual-response`** (well-posedness): the
volume element is invertible — `Vol² = ±1` — so the volume-dual map
`H = Vol⁻¹·b_ren : ⋀²V_sp → Cl(V_sp)` is defined. -/
theorem volume_isUnit (γ : ι → A)
    (hanti : ∀ i j, i ≠ j → γ i * γ j = -(γ j * γ i))
    (hsq : ∀ i, γ i * γ i = 1) (l : List ι) (hnodup : l.Nodup) :
    IsUnit ((l.map γ).prod) := by
  have hkey : ∀ (x : A),
      x * x = ((-1 : ℤ) ^ (l.length * (l.length - 1) / 2)) • (1 : A) →
      x * (((-1 : ℤ) ^ (l.length * (l.length - 1) / 2)) • x) = 1 := by
    intro x hx
    rw [mul_smul_comm, hx, smul_smul, ← pow_add,
      Even.neg_one_pow ⟨_, rfl⟩, one_smul]
  have hsq' := volume_element_sq γ hanti hsq l hnodup
  refine ⟨⟨(l.map γ).prod,
    ((-1 : ℤ) ^ (l.length * (l.length - 1) / 2)) • (l.map γ).prod,
    hkey _ hsq', ?_⟩, rfl⟩
  rw [smul_mul_assoc, hsq', smul_smul, ← pow_add,
    Even.neg_one_pow ⟨_, rfl⟩, one_smul]

end VolUnit

/-! ### The `d = 3` realisation (`prop:hodge-interference-closure`,
`prop:clifford-internal-interference`) -/

section CrossD3

/-- **Proposition `prop:hodge-interference-closure`** (induced
bracket): the Hodge bracket on `V_sp ≅ ℝ³` is the cross product, which
satisfies the Jacobi identity — `(V_sp, [·,·]_⋆) ≅ 𝔰𝔬(3)`. -/
theorem hodge_bracket_jacobi (u v w : Fin 3 → ℝ) :
    crossProduct u (crossProduct v w)
      + crossProduct v (crossProduct w u)
      + crossProduct w (crossProduct u v) = 0 :=
  jacobi_cross u v w

variable (g : Fin 3 → A)

/-- The spatial volume element at `d = 3`. -/
def vol3 : A := (([0, 1, 2] : List (Fin 3)).map g).prod

omit [Algebra ℝ A] in
theorem vol3_eq : vol3 g = g 0 * (g 1 * g 2) := by
  simp [vol3, List.prod_cons]

omit [Algebra ℝ A] in
/-- **Proposition `prop:clifford-internal-interference`**:
`Vol² = −1` at `d = 3`. -/
theorem vol3_sq
    (hanti : ∀ i j : Fin 3, i ≠ j → g i * g j = -(g j * g i))
    (hsq : ∀ i, g i * g i = 1) : vol3 g * vol3 g = -1 := by
  have h := volume_element_sq g hanti hsq [0, 1, 2] (by decide)
  simp only [List.length_cons, List.length_nil] at h
  norm_num at h
  rw [vol3_eq g]
  exact h

omit [Algebra ℝ A] in
/-- `Γ₀Γ₁ = Vol·Γ₂` (Propositions `prop:hodge-interference-closure` /
`prop:clifford-internal-interference`, `ε`-identity). -/
theorem vol3_gamma01 (hsq : ∀ i, g i * g i = 1) :
    g 0 * g 1 = vol3 g * g 2 := by
  rw [vol3_eq, mul_assoc, mul_assoc, hsq 2, mul_one]

omit [Algebra ℝ A] in
/-- The timelike-free volume commutes with `Γ₀`-conjugation pattern:
`Γ₀` anticommutes with `Γ₁` and `Γ₂` separately, hence commutes with
the bivector `Γ₁Γ₂`. -/
theorem g0_comm_bivec
    (hanti : ∀ i j : Fin 3, i ≠ j → g i * g j = -(g j * g i)) :
    g 0 * (g 1 * g 2) = (g 1 * g 2) * g 0 := by
  calc g 0 * (g 1 * g 2)
      = (g 0 * g 1) * g 2 := (mul_assoc _ _ _).symm
    _ = (-(g 1 * g 0)) * g 2 := by rw [hanti 0 1 (by decide)]
    _ = -(g 1 * (g 0 * g 2)) := by rw [neg_mul, mul_assoc]
    _ = -(g 1 * (-(g 2 * g 0))) := by rw [hanti 0 2 (by decide)]
    _ = (g 1 * g 2) * g 0 := by
        rw [mul_neg, neg_neg, ← mul_assoc]

omit [Algebra ℝ A] in
/-- `Γ₁Γ₂ = Vol·Γ₀` (`ε`-identity). -/
theorem vol3_gamma12
    (hanti : ∀ i j : Fin 3, i ≠ j → g i * g j = -(g j * g i))
    (hsq : ∀ i, g i * g i = 1) : g 1 * g 2 = vol3 g * g 0 := by
  rw [vol3_eq]
  calc g 1 * g 2
      = (g 0 * g 0) * (g 1 * g 2) := by rw [hsq 0, one_mul]
    _ = g 0 * (g 0 * (g 1 * g 2)) := mul_assoc _ _ _
    _ = g 0 * ((g 1 * g 2) * g 0) := by
        rw [g0_comm_bivec g hanti]
    _ = g 0 * (g 1 * g 2) * g 0 := (mul_assoc _ _ _).symm

omit [Algebra ℝ A] in
/-- `Γ₂Γ₀ = Vol·Γ₁` (`ε`-identity). -/
theorem vol3_gamma20
    (hanti : ∀ i j : Fin 3, i ≠ j → g i * g j = -(g j * g i))
    (hsq : ∀ i, g i * g i = 1) : g 2 * g 0 = vol3 g * g 1 := by
  rw [vol3_eq]
  have h : (g 0 * (g 1 * g 2)) * g 1 = g 2 * g 0 := by
    calc (g 0 * (g 1 * g 2)) * g 1
        = g 0 * ((g 1 * g 2) * g 1) := mul_assoc _ _ _
      _ = g 0 * (g 1 * (g 2 * g 1)) := by rw [mul_assoc]
      _ = g 0 * (g 1 * (-(g 1 * g 2))) := by
          rw [hanti 2 1 (by decide)]
      _ = -(g 0 * ((g 1 * g 1) * g 2)) := by
          rw [mul_neg, ← mul_assoc (g 1) (g 1) (g 2), mul_neg]
      _ = -(g 0 * g 2) := by rw [hsq 1, one_mul]
      _ = g 2 * g 0 := (hanti 2 0 (by decide)).symm
  exact h.symm

end CrossD3

end NCG
