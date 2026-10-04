/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.MatrixDetExp

/-!
# Flat periodic link fields are gauge equivalent to commuting constant links
  (`lem:flat-semisimple-normalization`, Einstein–SM action closure)

**Part A (any group `G`).**  On the periodic four-dimensional grid `(ℤ/n)^4` let `V` be a flat
link field (`V_μ(x) V_ν(x+μ) = V_ν(x) V_μ(x+ν)`, i.e. every plaquette is trivial).  With the
ordered line transports `line V μ p m = V_μ(p) V_μ(p+μ) ⋯ V_μ(p+(m-1)μ)` and the based
coordinate-cycle holonomies `w_μ = line V μ 0 n`:
* `ladder_line`, `ladder_stair`: plaquette moves (a link in direction `μ` slides along any
  staircase of transports in other directions);
* `cycle_commute`: flatness implies that the based cycle holonomies commute;
* `flat_gauge_eq_const`: **if `C_μ` are pairwise commuting with `C_μ^n = w_μ`, then
  `g_x V_μ(x) g_{x+μ}⁻¹ = C_μ` for the explicit site gauge `g_x = Q(x)⁻¹ P(x)`** (`P` the
  staircase transport from the root, `Q(x) = ∏_μ C_μ^{x_μ}`): comparison of the path transports
  of the two flat fields; plaquette moves preserve the comparison and the equal based cycle
  holonomies make it periodic.

**Part B (commuting logarithms).**  For a finite family of pairwise commuting unitary matrices with
determinant one (`SU(N)`), there are pairwise commuting, anti-Hermitian, traceless `b_μ` with
`e^{b_μ} = U_μ` and `‖b_μ‖ ≤ (N + 1) π` (operator norm), via the continuous functional
calculus `b = cfc (i arg) U` and a rank-one correction along a common eigenvector.

**Assembly** (`flat_semisimple_normalization`): a flat periodic `SU(3) × SU(2)` link field on
the box of side `L = n h` is gauge equivalent (by an `SU(3) × SU(2)` site gauge) to the constant
links `e^{h b_μ}` with commuting `b_μ ∈ 𝔰𝔲(3) ⊕ 𝔰𝔲(2)`, `‖b_μ‖ ≤ 4π/L`, whose cycle holonomies
are those of the field; for a sequence of such fields the bounded constant coordinates have a
convergent subsequence; constant commuting links have trivial plaquettes (zero curvature) and
zero first differences.  No smallness of the holonomies is assumed.
-/

open Filter Topology

namespace RenewalGeometry.FlatSemisimple

noncomputable section

/-! ### Part A: flat link fields on the periodic grid -/

section PartA

variable {G : Type*} [Group G] {n : ℕ}

/-- The unit step `e_μ`. -/
abbrev e (μ : Fin 4) : Fin 4 → ZMod n := Pi.single μ 1

/-- Flatness: every oriented plaquette is trivial, `V_μ(x) V_ν(x+μ) = V_ν(x) V_μ(x+ν)`. -/
def IsFlat (V : (Fin 4 → ZMod n) → Fin 4 → G) : Prop :=
  ∀ x μ ν, V x μ * V (x + e μ) ν = V x ν * V (x + e ν) μ

/-- The site gauge transform `V^g_μ(x) = g_x V_μ(x) g_{x+μ}⁻¹`. -/
def gaugeAct (g : (Fin 4 → ZMod n) → G) (V : (Fin 4 → ZMod n) → Fin 4 → G)
    (x : Fin 4 → ZMod n) (μ : Fin 4) : G :=
  g x * V x μ * (g (x + e μ))⁻¹

/-- The ordered line transport `V_μ(p) V_μ(p+μ) ⋯ V_μ(p+(m-1)μ)`. -/
def line (V : (Fin 4 → ZMod n) → Fin 4 → G) (μ : Fin 4) : (Fin 4 → ZMod n) → ℕ → G
  | _, 0 => 1
  | p, m + 1 => V p μ * line V μ (p + e μ) m

/-- The based coordinate-cycle holonomy `w_μ(p) = line V μ p n`. -/
def cyc (V : (Fin 4 → ZMod n) → Fin 4 → G) (μ : Fin 4) (p : Fin 4 → ZMod n) : G :=
  line V μ p n

theorem add_single_succ (p : Fin 4 → ZMod n) (μ : Fin 4) (m : ℕ) :
    p + e μ + Pi.single μ (m : ZMod n) = p + Pi.single μ ((m + 1 : ℕ) : ZMod n) := by
  rw [add_assoc, ← Pi.single_add]; push_cast; rw [add_comm (1 : ZMod n)]

/-- Tail recursion for line transports. -/
theorem line_succ' (V : (Fin 4 → ZMod n) → Fin 4 → G) (μ : Fin 4) (p : Fin 4 → ZMod n)
    (m : ℕ) : line V μ p (m + 1) = line V μ p m * V (p + Pi.single μ (m : ZMod n)) μ := by
  induction m generalizing p with
  | zero => simp [line]
  | succ m ih =>
      rw [line, ih (p + e μ), line, mul_assoc, add_single_succ]

/-- **Ladder lemma** (plaquette moves along a line): for `μ ≠ ν`,
`line_ν(p; m) V_μ(p + mν) = V_μ(p) line_ν(p + μ; m)`. -/
theorem ladder_line {V : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V) (μ ν : Fin 4)
    (p : Fin 4 → ZMod n) (m : ℕ) :
    line V ν p m * V (p + Pi.single ν (m : ZMod n)) μ = V p μ * line V ν (p + e μ) m := by
  induction m generalizing p with
  | zero => simp [line]
  | succ m ih =>
      have h1 := ih (p + e ν)
      rw [add_single_succ] at h1
      rw [line, line, mul_assoc, h1, ← mul_assoc, ← hV p μ ν, mul_assoc]
      congr 2
      abel_nf

theorem add_cast_n (p : Fin 4 → ZMod n) (ν : Fin 4) : p + Pi.single ν ((n : ℕ) : ZMod n) = p := by
  simp

/-- Cycle holonomies are transported by the links: `V_μ(p) w_ν(p+μ) = w_ν(p) V_μ(p)`. -/
theorem cyc_transport {V : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V) (μ ν : Fin 4)
    (p : Fin 4 → ZMod n) : V p μ * cyc V ν (p + e μ) = cyc V ν p * V p μ := by
  have := ladder_line hV μ ν p n
  rw [add_cast_n] at this
  exact this.symm

/-- Cycle holonomies are transported along lines:
`line_μ(p; m) w_ν(p + mμ) = w_ν(p) line_μ(p; m)`. -/
theorem cyc_line {V : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V) (μ ν : Fin 4)
    (p : Fin 4 → ZMod n) (m : ℕ) :
    line V μ p m * cyc V ν (p + Pi.single μ (m : ZMod n)) = cyc V ν p * line V μ p m := by
  induction m generalizing p with
  | zero => simp [line]
  | succ m ih =>
      have h1 := ih (p + e μ)
      rw [add_single_succ] at h1
      rw [line, mul_assoc, h1, ← mul_assoc, cyc_transport hV, mul_assoc]

/-- **Flatness implies that the based coordinate-cycle holonomies commute.** -/
theorem cycle_commute {V : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V) (μ ν : Fin 4)
    (p : Fin 4 → ZMod n) : Commute (cyc V μ p) (cyc V ν p) := by
  have := cyc_line hV μ ν p n
  rw [add_cast_n] at this
  exact this



/-- The staircase transport along the directions of `ds`, with `m d` steps in direction `d`. -/
def stair (V : (Fin 4 → ZMod n) → Fin 4 → G) : List (Fin 4) → (Fin 4 → ZMod n) → (Fin 4 → ℕ) → G
  | [], _, _ => 1
  | d :: ds, p, m => line V d p (m d) * stair V ds (p + Pi.single d (m d : ZMod n)) m

/-- The endpoint of the staircase. -/
def endp : List (Fin 4) → (Fin 4 → ZMod n) → (Fin 4 → ℕ) → (Fin 4 → ZMod n)
  | [], p, _ => p
  | d :: ds, p, m => endp ds (p + Pi.single d (m d : ZMod n)) m

theorem endp_add (ds : List (Fin 4)) (p q : Fin 4 → ZMod n) (m : Fin 4 → ℕ) :
    endp ds (p + q) m = endp ds p m + q := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp only [endp]; rw [← ih]; congr 1; abel

/-- **Ladder lemma along a staircase** avoiding the direction `μ`. -/
theorem ladder_stair {V : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V) (μ : Fin 4)
    (ds : List (Fin 4)) (hμ : μ ∉ ds) (p : Fin 4 → ZMod n) (m : Fin 4 → ℕ) :
    stair V ds p m * V (endp ds p m) μ = V p μ * stair V ds (p + e μ) m := by
  induction ds generalizing p with
  | nil => simp [stair, endp]
  | cons d ds ih =>
      have hμd : μ ∉ ds := fun h => hμ (List.mem_cons_of_mem d h)
      simp only [stair, endp]
      rw [mul_assoc, ih hμd, ← mul_assoc, ladder_line hV μ d p (m d), mul_assoc]
      congr 3
      abel

/-- Cycle holonomies are transported along staircases avoiding their direction. -/
theorem cyc_stair {V : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V) (μ : Fin 4)
    (ds : List (Fin 4)) (p : Fin 4 → ZMod n) (m : Fin 4 → ℕ) :
    stair V ds p m * cyc V μ (endp ds p m) = cyc V μ p * stair V ds p m := by
  induction ds generalizing p with
  | nil => simp [stair, endp]
  | cons d ds ih =>
      simp only [stair, endp]
      rw [mul_assoc, ih, ← mul_assoc, cyc_line hV d μ p (m d), mul_assoc]

theorem stair_append (V : (Fin 4 → ZMod n) → Fin 4 → G) (ds es : List (Fin 4))
    (p : Fin 4 → ZMod n) (m : Fin 4 → ℕ) :
    stair V (ds ++ es) p m = stair V ds p m * stair V es (endp ds p m) m := by
  induction ds generalizing p with
  | nil => simp [stair, endp]
  | cons d ds ih => simp only [List.cons_append, stair, endp]; rw [ih, mul_assoc]

theorem endp_append (ds es : List (Fin 4)) (p : Fin 4 → ZMod n) (m : Fin 4 → ℕ) :
    endp (ds ++ es) p m = endp es (endp ds p m) m := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp only [List.cons_append, endp]; rw [ih]

theorem stair_congr (V : (Fin 4 → ZMod n) → Fin 4 → G) (ds : List (Fin 4))
    (p : Fin 4 → ZMod n) (m m' : Fin 4 → ℕ) (h : ∀ d ∈ ds, m d = m' d) :
    stair V ds p m = stair V ds p m' ∧ endp ds p m = endp ds p m' := by
  induction ds generalizing p with
  | nil => exact ⟨rfl, rfl⟩
  | cons d ds ih =>
      have h' : ∀ d ∈ ds, m d = m' d := fun d hd => h d (List.mem_cons_of_mem _ hd)
      simp only [stair, endp]
      rw [h d List.mem_cons_self]
      exact ⟨by rw [(ih _ h').1], (ih _ h').2⟩

theorem stair_cons (V : (Fin 4 → ZMod n) → Fin 4 → G) (d : Fin 4) (ds : List (Fin 4))
    (p : Fin 4 → ZMod n) (m : Fin 4 → ℕ) :
    stair V (d :: ds) p m = line V d p (m d) * stair V ds (p + Pi.single d (m d : ZMod n)) m :=
  rfl

theorem endp_cons (d : Fin 4) (ds : List (Fin 4)) (p : Fin 4 → ZMod n) (m : Fin 4 → ℕ) :
    endp (d :: ds) p m = endp ds (p + Pi.single d (m d : ZMod n)) m :=
  rfl

theorem update_agree (m : Fin 4 → ℕ) (μ : Fin 4) (k : ℕ) (ds : List (Fin 4)) (hμ : μ ∉ ds) :
    ∀ d ∈ ds, m d = Function.update m μ k d := fun d hd => by
  rw [Function.update_of_ne (by rintro rfl; exact hμ hd)]

/-- The non-wrapping step: `P(m) V_μ(end) = P(m + δ_μ)`. -/
theorem stair_step {V : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V) (pre post : List (Fin 4))
    (μ : Fin 4) (hpre : μ ∉ pre) (hpost : μ ∉ post) (p : Fin 4 → ZMod n) (m : Fin 4 → ℕ) :
    stair V (pre ++ μ :: post) p m * V (endp (pre ++ μ :: post) p m) μ =
      stair V (pre ++ μ :: post) p (Function.update m μ (m μ + 1)) ∧
    endp (pre ++ μ :: post) p (Function.update m μ (m μ + 1)) =
      endp (pre ++ μ :: post) p m + e μ := by
  set m' := Function.update m μ (m μ + 1) with hm'
  have hμ : m' μ = m μ + 1 := by simp [m']
  obtain ⟨s1, e1⟩ := stair_congr V pre p m m' (update_agree m μ _ pre hpre)
  obtain ⟨s2, e2⟩ := stair_congr V post (endp pre p m + Pi.single μ ((m μ + 1 : ℕ) : ZMod n)) m m'
    (update_agree m μ _ post hpost)
  set q := endp pre p m
  have hr : q + Pi.single μ ((m μ : ℕ) : ZMod n) + e μ =
      q + Pi.single μ ((m μ + 1 : ℕ) : ZMod n) := by
    rw [add_assoc, ← Pi.single_add]; push_cast; rfl
  constructor
  · rw [stair_append, endp_append, stair_cons, endp_cons, stair_append, stair_cons, ← s1, ← e1,
      hμ, ← s2, mul_assoc, mul_assoc, ladder_stair hV μ post hpost, ← mul_assoc (line V μ q _),
      ← line_succ', hr]
  · rw [endp_append, endp_cons, endp_append, endp_cons, ← e1, hμ, ← e2, ← hr, endp_add]

/-- The wrapping step: if `m μ + 1 = n`, `P(m) V_μ(end) = w_μ(p) P(m with m μ := 0)`. -/
theorem stair_wrap {V : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V) (pre post : List (Fin 4))
    (μ : Fin 4) (hpre : μ ∉ pre) (hpost : μ ∉ post) (p : Fin 4 → ZMod n) (m : Fin 4 → ℕ)
    (hm : m μ + 1 = n) :
    stair V (pre ++ μ :: post) p m * V (endp (pre ++ μ :: post) p m) μ =
      cyc V μ p * stair V (pre ++ μ :: post) p (Function.update m μ 0) ∧
    endp (pre ++ μ :: post) p (Function.update m μ 0) =
      endp (pre ++ μ :: post) p m + e μ := by
  set m' := Function.update m μ 0 with hm'
  have hμ : m' μ = 0 := by simp [m']
  obtain ⟨s1, e1⟩ := stair_congr V pre p m m' (update_agree m μ _ pre hpre)
  obtain ⟨s2, e2⟩ := stair_congr V post (endp pre p m) m m' (update_agree m μ _ post hpost)
  set q := endp pre p m
  have hr : q + Pi.single μ ((m μ : ℕ) : ZMod n) + e μ = q := by
    rw [add_assoc, ← Pi.single_add]
    have : ((m μ : ℕ) : ZMod n) + 1 = 0 := by
      rw [show ((m μ : ℕ) : ZMod n) + 1 = ((m μ + 1 : ℕ) : ZMod n) by push_cast; rfl, hm,
        ZMod.natCast_self]
    rw [this, Pi.single_zero, add_zero]
  have hq0 : q + Pi.single μ (((0 : ℕ) : ℕ) : ZMod n) = q := by simp
  constructor
  · rw [stair_append, endp_append, stair_cons, endp_cons, stair_append, stair_cons, ← s1, ← e1,
      hμ, hq0, ← s2, mul_assoc, mul_assoc, ladder_stair hV μ post hpost, ← mul_assoc (line V μ q _),
      ← line_succ', hr, hm]
    simp only [line, one_mul]
    rw [← mul_assoc, ← mul_assoc, ← cyc, cyc_stair hV μ pre p m]
  · rw [endp_append, endp_cons, endp_append, endp_cons, ← e1, hμ, hq0, ← e2, ← hr, endp_add]


/-! ### Staircase transport from the root and the comparison gauge -/

/-- Lattice coordinates `x_μ ∈ {0, …, n-1}`. -/
def vals (x : Fin 4 → ZMod n) : Fin 4 → ℕ := fun i => (x i).val

/-- The coordinate order `0, 1, 2, 3` of the staircase. -/
def L4 : List (Fin 4) := [0, 1, 2, 3]

/-- The staircase transport from the root `0` to `x`. -/
def P (V : (Fin 4 → ZMod n) → Fin 4 → G) (x : Fin 4 → ZMod n) : G :=
  stair V L4 0 (vals x)

theorem L4_split (μ : Fin 4) : ∃ pre post : List (Fin 4), L4 = pre ++ μ :: post ∧ μ ∉ pre ∧ μ ∉ post := by
  fin_cases μ
  · exact ⟨[], [1, 2, 3], rfl, by decide, by decide⟩
  · exact ⟨[0], [2, 3], rfl, by decide, by decide⟩
  · exact ⟨[0, 1], [3], rfl, by decide, by decide⟩
  · exact ⟨[0, 1, 2], [], rfl, by decide, by decide⟩

variable [NeZero n]

theorem endp_vals (x : Fin 4 → ZMod n) : endp L4 0 (vals x) = x := by
  funext i
  fin_cases i <;> simp [L4, endp, vals, Pi.single_apply, ZMod.natCast_zmod_val]

theorem vals_succ (x : Fin 4 → ZMod n) (μ : Fin 4) (h : (x μ).val + 1 < n) :
    vals (x + e μ) = Function.update (vals x) μ ((x μ).val + 1) := by
  funext i
  by_cases hi : i = μ
  · subst hi
    simp only [vals, Pi.add_apply, Pi.single_eq_same, Function.update_self]
    rw [show x i + 1 = (((x i).val + 1 : ℕ) : ZMod n) by push_cast; rw [ZMod.natCast_zmod_val],
      ZMod.val_cast_of_lt h]
  · simp [vals, Pi.single_eq_of_ne hi, Function.update_of_ne hi]

theorem vals_wrap (x : Fin 4 → ZMod n) (μ : Fin 4) (h : (x μ).val + 1 = n) :
    vals (x + e μ) = Function.update (vals x) μ 0 := by
  funext i
  by_cases hi : i = μ
  · subst hi
    simp only [vals, Pi.add_apply, Pi.single_eq_same, Function.update_self]
    rw [show x i + 1 = (((x i).val + 1 : ℕ) : ZMod n) by push_cast; rw [ZMod.natCast_zmod_val],
      h, ZMod.natCast_self, ZMod.val_zero]
  · simp [vals, Pi.single_eq_of_ne hi, Function.update_of_ne hi]

/-- Non-wrapping link: `P(x) V_μ(x) = P(x + μ)`. -/
theorem P_succ {V : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V) (x : Fin 4 → ZMod n)
    (μ : Fin 4) (h : (x μ).val + 1 < n) : P V x * V x μ = P V (x + e μ) := by
  obtain ⟨pre, post, hL, hpre, hpost⟩ := L4_split μ
  have := (stair_step hV pre post μ hpre hpost 0 (vals x)).1
  rw [← hL, endp_vals] at this
  rw [P, P, vals_succ x μ h, this]
  rfl

/-- Wrapping link: `P(x) V_μ(x) = w_μ P(x + μ)` with the based cycle holonomy `w_μ`. -/
theorem P_wrap {V : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V) (x : Fin 4 → ZMod n)
    (μ : Fin 4) (h : (x μ).val + 1 = n) : P V x * V x μ = cyc V μ 0 * P V (x + e μ) := by
  obtain ⟨pre, post, hL, hpre, hpost⟩ := L4_split μ
  have := (stair_wrap hV pre post μ hpre hpost 0 (vals x) h).1
  rw [← hL, endp_vals] at this
  rw [P, P, vals_wrap x μ h, this]

/-- **Comparison of two flat fields** (`lem:flat-semisimple-normalization`, gauge step): two flat
periodic link fields with the same based coordinate-cycle holonomies are gauge equivalent, by the
site gauge `g_x = P_W(x)⁻¹ P_V(x)` comparing their staircase transports. -/
theorem flat_gauge_equiv {V W : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V) (hW : IsFlat W)
    (hcyc : ∀ μ, cyc V μ 0 = cyc W μ 0) :
    ∀ x μ, gaugeAct (fun x => (P W x)⁻¹ * P V x) V x μ = W x μ := by
  intro x μ
  simp only [gaugeAct]
  have hlt := (x μ).val_lt
  rcases Nat.lt_or_ge ((x μ).val + 1) n with h | h
  · rw [← P_succ hV x μ h, ← P_succ hW x μ h]
    group
  · have h' : (x μ).val + 1 = n := le_antisymm hlt h
    have hV' : P V (x + e μ) = (cyc V μ 0)⁻¹ * (P V x * V x μ) := by
      rw [P_wrap hV x μ h']; group
    have hW' : P W (x + e μ) = (cyc W μ 0)⁻¹ * (P W x * W x μ) := by
      rw [P_wrap hW x μ h']; group
    rw [hV', hW', hcyc]
    group

/-- Constant links with pairwise commuting values are flat. -/
theorem isFlat_const (C : Fin 4 → G) (hC : ∀ μ ν, Commute (C μ) (C ν)) :
    IsFlat (fun (_ : Fin 4 → ZMod n) μ => C μ) := fun _ μ ν => (hC μ ν).eq

theorem line_const (C : Fin 4 → G) (μ : Fin 4) (p : Fin 4 → ZMod n) (m : ℕ) :
    line (fun (_ : Fin 4 → ZMod n) μ => C μ) μ p m = C μ ^ m := by
  induction m generalizing p with
  | zero => simp [line]
  | succ m ih => rw [line, ih, pow_succ']

/-- **Flat fields are gauge equivalent to commuting constant links**: if `C_μ` pairwise commute
and `C_μ^n` is the based cycle holonomy `w_μ` of the flat field `V`, then
`g_x V_μ(x) g_{x+μ}⁻¹ = C_μ` for an explicit site gauge `g`. -/
theorem flat_gauge_eq_const {V : (Fin 4 → ZMod n) → Fin 4 → G} (hV : IsFlat V)
    (C : Fin 4 → G) (hC : ∀ μ ν, Commute (C μ) (C ν)) (hhol : ∀ μ, C μ ^ n = cyc V μ 0) :
    ∃ g : (Fin 4 → ZMod n) → G, ∀ x μ, gaugeAct g V x μ = C μ :=
  ⟨_, flat_gauge_equiv hV (isFlat_const C hC) fun μ => by
    rw [← hhol]; exact (line_const C μ 0 n).symm⟩

/-- The gauge transform of a field is flat iff the field is (plaquettes are conjugated). -/
theorem cyc_gaugeAct (g : (Fin 4 → ZMod n) → G) (V : (Fin 4 → ZMod n) → Fin 4 → G)
    (μ : Fin 4) (p : Fin 4 → ZMod n) (m : ℕ) :
    line (gaugeAct g V) μ p m = g p * line V μ p m * (g (p + Pi.single μ (m : ZMod n)))⁻¹ := by
  induction m generalizing p with
  | zero => simp [line]
  | succ m ih =>
      rw [line, line, ih, gaugeAct, add_single_succ]
      group

end PartA


/-! ### Part B: commuting logarithms of commuting special unitary matrices -/

section CommonEigen

/-- **Commuting operators have a common eigenspace**: for a finite set `s` of pairwise commuting
operators on a nontrivial finite-dimensional complex space there is a nonzero subspace invariant
under all of them on which every operator of `s` is scalar. -/
theorem exists_common_eigenspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] {ι : Type*} [DecidableEq ι] (f : ι → Module.End ℂ V)
    (hc : ∀ i j, Commute (f i) (f j)) (s : Finset ι) :
    ∃ W : Submodule ℂ V, W ≠ ⊥ ∧ (∀ i, ∀ w ∈ W, f i w ∈ W) ∧
      ∀ i ∈ s, ∃ c : ℂ, ∀ w ∈ W, f i w = c • w := by
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, top_ne_bot, fun _ _ _ => Submodule.mem_top, fun _ h => absurd h (by simp)⟩
  | insert j s hj ih =>
      obtain ⟨W, hW0, hWi, hWs⟩ := ih
      have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW0
      set g : Module.End ℂ W := (f j).restrict (hWi j)
      obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue g
      obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
      let W' : Submodule ℂ V :=
        { carrier := {w | w ∈ W ∧ f j w = c • w}
          add_mem' := fun ha hb => ⟨W.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, smul_add]⟩
          zero_mem' := ⟨W.zero_mem, by simp⟩
          smul_mem' := fun r w hw => ⟨W.smul_mem r hw.1, by rw [map_smul, hw.2, smul_comm]⟩ }
      have hv' : f j (v : V) = c • (v : V) := by
        have := Module.End.mem_eigenspace_iff.1 hv.1
        exact congrArg Subtype.val this
      refine ⟨W', ?_, fun i w hw => ⟨hWi i w hw.1, ?_⟩, fun i hi => ?_⟩
      · intro hbot
        have hmem : (v : V) ∈ W' := ⟨v.2, hv'⟩
        rw [hbot, Submodule.mem_bot] at hmem
        exact hv.2 (Subtype.ext hmem)
      · have := congrArg (fun F => F w) (hc j i).eq
        simp only [Module.End.mul_apply] at this
        rw [this, hw.2, map_smul]
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact ⟨c, fun w hw => hw.2⟩
        · obtain ⟨d, hd⟩ := hWs i hi
          exact ⟨d, fun w hw => hd w hw.1⟩

/-- **A finite family of pairwise commuting complex operators has a common eigenvector.** -/
theorem exists_common_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Module.End ℂ V) (hc : ∀ i j, Commute (f i) (f j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : ℂ, f i v = c • v := by
  obtain ⟨W, hW0, -, hWs⟩ := exists_common_eigenspace f hc Finset.univ
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  refine ⟨v, hv0, fun i => ?_⟩
  obtain ⟨c, hc⟩ := hWs i (Finset.mem_univ i)
  exact ⟨c, hc v hv⟩

end CommonEigen

section Projector

open Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The rank-one orthogonal projector onto `v`. -/
def rankOneProj (v : m → ℂ) : Matrix m m ℂ :=
  (star v ⬝ᵥ v)⁻¹ • vecMulVec v (star v)

omit [DecidableEq m] in
theorem dot_self_ne_zero (v : m → ℂ) (hv : v ≠ 0) : star v ⬝ᵥ v ≠ 0 := by
  intro h
  apply hv
  have h' : ∑ i, star (v i) * v i = 0 := h
  have hre : ∀ i, 0 ≤ (star (v i) * v i).re := fun i => by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.normSq_nonneg _
  have hsum : ∑ i, (star (v i) * v i).re = 0 := by rw [← Complex.re_sum, h', Complex.zero_re]
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hre i)).1 hsum i (Finset.mem_univ i)
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_zero] at hi
  exact hi

omit [DecidableEq m] in
theorem rankOneProj_mul_self (v : m → ℂ) (hv : v ≠ 0) :
    rankOneProj v * rankOneProj v = rankOneProj v := by
  have h0 := dot_self_ne_zero v hv
  have hsq : vecMulVec v (star v) * vecMulVec v (star v) =
      (star v ⬝ᵥ v) • vecMulVec v (star v) := by
    rw [vecMulVec_mul_vecMulVec]; ext i j; simp [vecMulVec_apply]; ring
  simp only [rankOneProj, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul]
  congr 1
  field_simp

omit [DecidableEq m] in
theorem trace_rankOneProj (v : m → ℂ) (hv : v ≠ 0) : trace (rankOneProj v) = 1 := by
  have h0 := dot_self_ne_zero v hv
  rw [rankOneProj, trace_smul, trace_vecMulVec, smul_eq_mul, dotProduct_comm v, inv_mul_cancel₀ h0]

omit [DecidableEq m] in
theorem star_rankOneProj (v : m → ℂ) : star (rankOneProj v) = rankOneProj v := by
  rw [rankOneProj, star_smul, star_eq_conjTranspose, conjTranspose_vecMulVec, star_star]
  congr 1
  rw [star_inv₀]
  congr 1
  simp only [dotProduct, star_sum, star_mul, star_star, Pi.star_apply]

/-- If `v` is an eigenvector of a unitary `U`, the projector onto `v` commutes with `U`. -/
theorem commute_rankOneProj (U : Matrix m m ℂ) (hU : U ∈ unitaryGroup m ℂ) (v : m → ℂ)
    (hv : v ≠ 0) (c : ℂ) (hc : U *ᵥ v = c • v) : Commute U (rankOneProj v) := by
  have h0 := dot_self_ne_zero v hv
  have hUU : star U * U = 1 := (mem_unitaryGroup_iff'.1 hU)
  have hUs : star U *ᵥ v = (star c) • v := by
    have h1 : star U *ᵥ (U *ᵥ v) = v := by rw [mulVec_mulVec, hUU, one_mulVec]
    rw [hc, mulVec_smul] at h1
    have hn : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
      rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose, hUU, vecMul_one]
    rw [hc, star_smul, smul_dotProduct, dotProduct_smul, smul_smul] at hn
    have hcc : star c * c = 1 := by
      have := hn
      rw [smul_eq_mul] at this
      exact (mul_left_eq_self₀.1 this).resolve_right h0
    have : star U *ᵥ v = (star c * c) • (star U *ᵥ v) := by rw [hcc, one_smul]
    rw [this, mul_smul, h1]
  simp only [Commute, SemiconjBy, rankOneProj, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec,
    vecMulVec_mul, hc]
  congr 1
  have : star v ᵥ* U = star (star U *ᵥ v) := by
    rw [star_mulVec, star_eq_conjTranspose U, conjTranspose_conjTranspose]
  rw [this, hUs, star_smul, star_star]
  ext i j
  simp [vecMulVec_apply, smul_eq_mul]
  ring

/-- `exp(t P) = 1 + (e^t - 1) P` for an idempotent matrix `P`. -/
theorem exp_smul_idempotent (P : Matrix m m ℂ) (hP : P * P = P) (t : ℂ) :
    NormedSpace.exp (t • P) = 1 + (Complex.exp t - 1) • P := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  have hpow : ∀ k : ℕ, (t • P) ^ (k + 1) = t ^ (k + 1) • P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, smul_mul_smul_comm, hP, ← pow_succ]
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (t • P)
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) t
  rw [← hasSum_nat_add_iff' 1] at h1 h2
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at h1 h2
  have h3 : HasSum (fun k : ℕ => ((((k + 1).factorial : ℂ)⁻¹) • t ^ (k + 1)) • P)
      ((NormedSpace.exp t - 1) • P) := h2.smul_const P
  simp only [hpow, smul_smul] at h1
  simp only [smul_eq_mul] at h3
  have := h1.unique h3
  rw [← Complex.exp_eq_exp_ℂ] at this
  rw [← this]
  abel

end Projector

section ArgLog

open Matrix
open scoped Matrix.Norms.L2Operator

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The principal-argument logarithm `i arg U` of a matrix, by the continuous functional
calculus. -/
def argLog (U : Matrix m m ℂ) : Matrix m m ℂ :=
  cfc (fun z : ℂ => Complex.I * (Complex.arg z : ℂ)) U

theorem continuousOn_spectrum (f : ℂ → ℂ) (U : Matrix m m ℂ) : ContinuousOn f (spectrum ℂ U) :=
  (Matrix.finite_spectrum U).continuousOn f

/-- `exp(i arg U) = U` for unitary `U`. -/
theorem exp_argLog (U : Matrix m m ℂ) (hU : U ∈ unitaryGroup m ℂ) :
    NormedSpace.exp (argLog U) = U := by
  have hN : IsStarNormal U := isStarNormal_of_mem_unitary hU
  rw [argLog, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) (a := cfc _ U)]
  rw [← cfc_comp' (hg := (Set.toFinite _).continuousOn _) (hf := continuousOn_spectrum _ U)]
  conv_rhs => rw [← cfc_id' ℂ U]
  refine cfc_congr fun z hz => ?_
  have h1 : ‖z‖ = 1 := by simpa using spectrum.subset_circle_of_unitary hU hz
  show NormedSpace.exp (Complex.I * (Complex.arg z : ℂ)) = id z
  rw [id, ← Complex.exp_eq_exp_ℂ, mul_comm]
  have := Complex.norm_mul_exp_arg_mul_I z
  rw [h1, Complex.ofReal_one, one_mul] at this
  exact this

theorem star_argLog (U : Matrix m m ℂ) : star (argLog U) = -argLog U := by
  rw [argLog, ← cfc_star, ← cfc_neg]
  refine cfc_congr fun z _ => ?_
  simp [Complex.conj_ofReal]

theorem norm_argLog_le (U : Matrix m m ℂ) : ‖argLog U‖ ≤ Real.pi := by
  refine norm_cfc_le Real.pi_pos.le fun z _ => ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact Complex.abs_arg_le_pi z

theorem commute_argLog (U W : Matrix m m ℂ) (h1 : Commute U W) (h2 : Commute (star U) W) :
    Commute (argLog U) W := h1.cfc h2 _

theorem matrix_entry_le (A : Matrix m m ℂ) (i j : m) : ‖A i j‖ ≤ ‖A‖ := by
  have h := A.l2_opNorm_mulVec (EuclideanSpace.single j 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le
    ((EuclideanSpace.equiv m ℂ).symm (A.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  refine le_trans (le_of_eq ?_) this
  congr 1
  simp

theorem norm_trace_le (A : Matrix m m ℂ) : ‖trace A‖ ≤ Fintype.card m * ‖A‖ := by
  unfold trace diag
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖A i i‖ ≤ ∑ _i : m, ‖A‖ := Finset.sum_le_sum fun i _ => matrix_entry_le A i i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem norm_proj_le_one (P : Matrix m m ℂ) (hP : P * P = P) (hs : star P = P) : ‖P‖ ≤ 1 := by
  have h := CStarRing.norm_star_mul_self (x := P)
  rw [hs, hP] at h
  rcases eq_or_ne ‖P‖ 0 with h0 | h0
  · rw [h0]; exact zero_le_one
  · have : ‖P‖ = 1 := by
      have := mul_left_cancel₀ h0 (h.symm.trans (mul_one ‖P‖).symm)
      exact this
    exact this.le

/-- **Commuting logarithms in `SU(N)`** (`lem:flat-semisimple-normalization`, second step).  A
finite family of pairwise commuting unitary matrices with determinant one admits pairwise
commuting, anti-Hermitian, traceless logarithms bounded by `(N + 1) π`, `N = card m`. -/
theorem exists_commuting_logs [Nonempty m] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι → Matrix m m ℂ) (hU : ∀ μ, U μ ∈ unitaryGroup m ℂ) (hdet : ∀ μ, (U μ).det = 1)
    (hc : ∀ μ ν, Commute (U μ) (U ν)) :
    ∃ b : ι → Matrix m m ℂ, (∀ μ, NormedSpace.exp (b μ) = U μ) ∧ (∀ μ, star (b μ) = -b μ) ∧
      (∀ μ, trace (b μ) = 0) ∧ (∀ μ ν, Commute (b μ) (b ν)) ∧
      ∀ μ, ‖b μ‖ ≤ (Fintype.card m + 1) * Real.pi := by
  -- a common eigenvector and its projector
  obtain ⟨v, hv0, hev⟩ := exists_common_eigenvector (fun μ => Matrix.toLin' (U μ)) fun μ ν => by
    have := (hc μ ν).eq
    show Matrix.toLin' (U μ) * Matrix.toLin' (U ν) = Matrix.toLin' (U ν) * Matrix.toLin' (U μ)
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      this]
  set P := rankOneProj v with hPdef
  have hPP := rankOneProj_mul_self v hv0
  have hPs := star_rankOneProj v
  have hUP : ∀ μ, Commute (U μ) P := fun μ => by
    obtain ⟨c, hc'⟩ := hev μ
    exact commute_rankOneProj (U μ) (hU μ) v hv0 c (by simpa using hc')
  have hsU : ∀ μ ν, Commute (star (U μ)) (U ν) := fun μ ν => by
    have h1 := (Matrix.mem_unitaryGroup_iff'.1 (hU μ))
    have h2 := (Matrix.mem_unitaryGroup_iff.1 (hU μ))
    have e := (hc μ ν).eq
    show star (U μ) * U ν = U ν * star (U μ)
    calc star (U μ) * U ν = star (U μ) * U ν * (U μ * star (U μ)) := by rw [h2, mul_one]
      _ = star (U μ) * (U ν * U μ) * star (U μ) := by simp only [mul_assoc]
      _ = star (U μ) * (U μ * U ν) * star (U μ) := by rw [e]
      _ = U ν * star (U μ) := by rw [← mul_assoc, h1, one_mul]
  have hsP : ∀ μ, Commute (star (U μ)) P := fun μ => by
    have := (hUP μ).star_star
    rwa [hPs] at this
  -- the principal logarithms
  set a : ι → Matrix m m ℂ := fun μ => argLog (U μ) with ha
  have haU : ∀ μ ν, Commute (a μ) (U ν) := fun μ ν => commute_argLog _ _ (hc μ ν) (hsU μ ν)
  have haUs : ∀ μ ν, Commute (a μ) (star (U ν)) := fun μ ν => by
    have := (haU μ ν).star_star
    rw [star_argLog] at this
    have h := this.neg_left
    rwa [neg_neg] at h
  have haa : ∀ μ ν, Commute (a μ) (a ν) := fun μ ν =>
    (commute_argLog (U ν) (a μ) (haU μ ν).symm (haUs μ ν).symm).symm
  have haP : ∀ μ, Commute (a μ) P := fun μ => commute_argLog _ _ (hUP μ) (hsP μ)
  -- integrality of the trace
  have htr : ∀ μ, ∃ k : ℤ, trace (a μ) = k * (2 * Real.pi * Complex.I) := fun μ => by
    have h := MatrixDetExp.det_exp_eq_complex_exp_trace (a μ)
    rw [exp_argLog _ (hU μ), hdet μ] at h
    exact Complex.exp_eq_one_iff.1 h.symm
  choose k hk using htr
  refine ⟨fun μ => a μ - ((k μ : ℂ) * (2 * Real.pi * Complex.I)) • P, fun μ => ?_, fun μ => ?_,
    fun μ => ?_, fun μ ν => ?_, fun μ => ?_⟩
  · -- exponential
    dsimp only
    have hcomm : Commute (a μ) (-(((k μ : ℂ) * (2 * Real.pi * Complex.I)) • P)) :=
      ((haP μ).smul_right _).neg_right
    rw [sub_eq_add_neg, Matrix.exp_add_of_commute _ _ hcomm, ← neg_smul,
      exp_smul_idempotent P hPP, exp_argLog _ (hU μ)]
    have : Complex.exp (-((k μ : ℂ) * (2 * Real.pi * Complex.I))) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨-k μ, by push_cast; ring⟩
    rw [this, sub_self, zero_smul, add_zero, mul_one]
  · -- anti-Hermitian
    dsimp only
    rw [star_sub, star_argLog, star_smul, hPs]
    have : star ((k μ : ℂ) * (2 * Real.pi * Complex.I)) = -((k μ : ℂ) * (2 * Real.pi * Complex.I)) := by
      simp [Complex.conj_ofReal]
    rw [this, neg_smul]; abel
  · -- traceless
    dsimp only
    rw [trace_sub, trace_smul, trace_rankOneProj v hv0, smul_eq_mul, mul_one, hk μ, sub_self]
  · -- commuting
    dsimp only
    exact ((haa μ ν).sub_right ((haP μ).smul_right _)).sub_left
      (((haP ν).symm.smul_left _).sub_right ((Commute.refl P).smul_left _ |>.smul_right _))
  · -- norm bound
    dsimp only
    have hP1 := norm_proj_le_one P hPP hPs
    have ha1 := norm_argLog_le (U μ)
    have hkb : |(k μ : ℝ)| * (2 * Real.pi) ≤ Fintype.card m * Real.pi := by
      have h1 := norm_trace_le (a μ)
      rw [hk μ, norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat] at h1
      calc |(k μ : ℝ)| * (2 * Real.pi) ≤ Fintype.card m * ‖a μ‖ := by linarith
        _ ≤ Fintype.card m * Real.pi := mul_le_mul_of_nonneg_left ha1 (by positivity)
    calc ‖a μ - ((k μ : ℂ) * (2 * Real.pi * Complex.I)) • P‖
        ≤ ‖a μ‖ + ‖(k μ : ℂ) * (2 * Real.pi * Complex.I)‖ * ‖P‖ :=
          (norm_sub_le _ _).trans (by rw [norm_smul])
      _ ≤ Real.pi + Fintype.card m * Real.pi * 1 := by
          gcongr
          rw [norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
          linarith
      _ = (Fintype.card m + 1) * Real.pi := by ring

end ArgLog


/-! ### Assembly for `SU(3) × SU(2)` -/

section Assembly

open Matrix

/-- The semisimple gauge group `G_ss = SU(3) × SU(2)`. -/
abbrev Gss : Type := Matrix.specialUnitaryGroup (Fin 3) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ

theorem exp_mem_specialUnitary {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ)
    (hs : star A = -A) (ht : trace A = 0) :
    NormedSpace.exp A ∈ Matrix.specialUnitaryGroup m ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      ← star_eq_conjTranspose, hs, ← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  · rw [MatrixDetExp.det_exp_eq_complex_exp_trace, ht, Complex.exp_zero]

theorem commute_coe_fst {a b : Gss} (h : Commute a b) :
    Commute (a.1 : Matrix (Fin 3) (Fin 3) ℂ) (b.1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have := congrArg (fun g : Gss => (g.1 : Matrix (Fin 3) (Fin 3) ℂ)) h.eq
  exact this

theorem commute_coe_snd {a b : Gss} (h : Commute a b) :
    Commute (a.2 : Matrix (Fin 2) (Fin 2) ℂ) (b.2 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have := congrArg (fun g : Gss => (g.2 : Matrix (Fin 2) (Fin 2) ℂ)) h.eq
  exact this

open scoped Matrix.Norms.L2Operator in
/-- Commuting logarithms of a commuting family of special unitary matrices, entrywise bounded. -/
theorem exists_commuting_logs_entry {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (U : Fin 4 → Matrix m m ℂ) (hU : ∀ μ, U μ ∈ Matrix.specialUnitaryGroup m ℂ)
    (hc : ∀ μ ν, Commute (U μ) (U ν)) :
    ∃ b : Fin 4 → Matrix m m ℂ, (∀ μ, NormedSpace.exp (b μ) = U μ) ∧ (∀ μ, star (b μ) = -b μ) ∧
      (∀ μ, trace (b μ) = 0) ∧ (∀ μ ν, Commute (b μ) (b ν)) ∧
      ∀ μ i j, ‖b μ i j‖ ≤ (Fintype.card m + 1) * Real.pi := by
  obtain ⟨b, h1, h2, h3, h4, h5⟩ := exists_commuting_logs U
    (fun μ => (Matrix.mem_specialUnitaryGroup_iff.1 (hU μ)).1)
    (fun μ => (Matrix.mem_specialUnitaryGroup_iff.1 (hU μ)).2) hc
  exact ⟨b, h1, h2, h3, h4, fun μ i j => (matrix_entry_le _ i j).trans (h5 μ)⟩

/-- **`lem:flat-semisimple-normalization`** (one grid).  A flat periodic `SU(3) × SU(2)` link
field `V` on `(ℤ/n)^4` with mesh `h > 0` (box side `L = n h`) is gauge equivalent, by an
`SU(3) × SU(2)` site gauge `g`, to constant links `e^{h b_μ}` with pairwise commuting
`b_μ = (b_μ³, b_μ²) ∈ 𝔰𝔲(3) ⊕ 𝔰𝔲(2)` (anti-Hermitian, traceless), uniformly bounded by
`|b_μ(i,j)| ≤ 4π / L`, whose cycle holonomies `e^{L b_μ}` are those of `V`.  No smallness of
the holonomies is assumed. -/
theorem flat_semisimple_normalization (n : ℕ) [NeZero n] {h : ℝ} (hh : 0 < h)
    (V : (Fin 4 → ZMod n) → Fin 4 → Gss) (hV : IsFlat V) :
    ∃ (b₃ : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (b₂ : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
      (g : (Fin 4 → ZMod n) → Gss),
      (∀ μ, star (b₃ μ) = -b₃ μ ∧ trace (b₃ μ) = 0 ∧ star (b₂ μ) = -b₂ μ ∧ trace (b₂ μ) = 0) ∧
      (∀ μ ν, Commute (b₃ μ) (b₃ ν) ∧ Commute (b₂ μ) (b₂ ν)) ∧
      (∀ μ, (∀ i j, ‖b₃ μ i j‖ ≤ 4 * Real.pi / (n * h)) ∧
        ∀ i j, ‖b₂ μ i j‖ ≤ 4 * Real.pi / (n * h)) ∧
      (∀ μ, ((cyc V μ 0).1 : Matrix (Fin 3) (Fin 3) ℂ) =
          NormedSpace.exp (((n * h : ℝ) : ℂ) • b₃ μ) ∧
        ((cyc V μ 0).2 : Matrix (Fin 2) (Fin 2) ℂ) =
          NormedSpace.exp (((n * h : ℝ) : ℂ) • b₂ μ)) ∧
      ∀ x μ, ((gaugeAct g V x μ).1 : Matrix (Fin 3) (Fin 3) ℂ) =
          NormedSpace.exp ((h : ℂ) • b₃ μ) ∧
        ((gaugeAct g V x μ).2 : Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp ((h : ℂ) • b₂ μ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hL : (0 : ℝ) < n * h := mul_pos hn hh
  set w : Fin 4 → Gss := fun μ => cyc V μ 0 with hw
  have hwc : ∀ μ ν, Commute (w μ) (w ν) := fun μ ν => cycle_commute hV μ ν 0
  obtain ⟨a₃, e₃, s₃, t₃, c₃, n₃⟩ := exists_commuting_logs_entry
    (fun μ => ((w μ).1 : Matrix (Fin 3) (Fin 3) ℂ)) (fun μ => (w μ).1.2)
    (fun μ ν => commute_coe_fst (hwc μ ν))
  obtain ⟨a₂, e₂, s₂, t₂, c₂, n₂⟩ := exists_commuting_logs_entry
    (fun μ => ((w μ).2 : Matrix (Fin 2) (Fin 2) ℂ)) (fun μ => (w μ).2.2)
    (fun μ ν => commute_coe_snd (hwc μ ν))
  set c : ℂ := ((((n : ℝ) * h)⁻¹ : ℝ) : ℂ) with hcdef
  refine ⟨fun μ => c • a₃ μ, fun μ => c • a₂ μ, ?_⟩
  -- the constant links
  have hmem₃ : ∀ μ, NormedSpace.exp ((h : ℂ) • (c • a₃ μ)) ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ :=
    fun μ => exp_mem_specialUnitary _ (by rw [star_smul, star_smul, s₃]; simp [hcdef]) (by
      rw [trace_smul, trace_smul, t₃]; simp)
  have hmem₂ : ∀ μ, NormedSpace.exp ((h : ℂ) • (c • a₂ μ)) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    fun μ => exp_mem_specialUnitary _ (by rw [star_smul, star_smul, s₂]; simp [hcdef]) (by
      rw [trace_smul, trace_smul, t₂]; simp)
  set C : Fin 4 → Gss := fun μ => (⟨_, hmem₃ μ⟩, ⟨_, hmem₂ μ⟩) with hC
  have hCc : ∀ μ ν, Commute (C μ) (C ν) := fun μ ν => by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact (((c₃ μ ν).smul_left c).smul_right c |>.smul_left (h : ℂ) |>.smul_right (h : ℂ)).exp.eq
    · exact (((c₂ μ ν).smul_left c).smul_right c |>.smul_left (h : ℂ) |>.smul_right (h : ℂ)).exp.eq
  have hnh1 : (((n : ℝ) * h : ℝ) : ℂ) * c = 1 := by
    rw [hcdef, ← Complex.ofReal_mul, mul_inv_cancel₀ hL.ne', Complex.ofReal_one]
  have hscal : (n : ℂ) * ((h : ℂ) * c) = 1 := by
    rw [← mul_assoc, ← hnh1]; push_cast; ring
  have hpow : ∀ μ, C μ ^ n = w μ := fun μ => by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [Prod.pow_fst, SubmonoidClass.coe_pow]
      change NormedSpace.exp ((h : ℂ) • (c • a₃ μ)) ^ n = _
      rw [← Matrix.exp_nsmul, smul_smul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hscal, one_smul]
      exact e₃ μ
    · rw [Prod.pow_snd, SubmonoidClass.coe_pow]
      change NormedSpace.exp ((h : ℂ) • (c • a₂ μ)) ^ n = _
      rw [← Matrix.exp_nsmul, smul_smul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hscal, one_smul]
      exact e₂ μ
  obtain ⟨g, hg⟩ := flat_gauge_eq_const hV C hCc hpow
  refine ⟨g, fun μ => ⟨?_, ?_, ?_, ?_⟩, fun μ ν => ⟨(c₃ μ ν).smul_left c |>.smul_right c,
    (c₂ μ ν).smul_left c |>.smul_right c⟩, fun μ => ⟨fun i j => ?_, fun i j => ?_⟩,
    fun μ => ⟨?_, ?_⟩, fun x μ => ⟨?_, ?_⟩⟩
  · rw [star_smul, s₃]; simp [hcdef]
  · rw [trace_smul, t₃, smul_zero]
  · rw [star_smul, s₂]; simp [hcdef]
  · rw [trace_smul, t₂, smul_zero]
  · dsimp only
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, hcdef, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hL), div_eq_inv_mul, mul_comm (4 : ℝ)]
    refine mul_le_mul_of_nonneg_left ((n₃ μ i j).trans (le_of_eq ?_)) (inv_pos.2 hL).le
    norm_num; ring
  · dsimp only
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, hcdef, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hL), div_eq_inv_mul, mul_comm (4 : ℝ)]
    refine mul_le_mul_of_nonneg_left ((n₂ μ i j).trans ?_) (inv_pos.2 hL).le
    norm_num; nlinarith [Real.pi_pos]
  · rw [smul_smul, hnh1, one_smul]; exact (e₃ μ).symm
  · rw [smul_smul, hnh1, one_smul]; exact (e₂ μ).symm
  · rw [hg x μ]
  · rw [hg x μ]

/-- Constant commuting links have trivial plaquettes (zero curvature). -/
theorem plaq_const_eq_one {G : Type*} [Group G] (C : Fin 4 → G) (hC : ∀ μ ν, Commute (C μ) (C ν))
    (μ ν : Fin 4) : C μ * C ν * (C μ)⁻¹ * (C ν)⁻¹ = 1 := by
  rw [(hC μ ν).eq]; group

/-- **Extraction** (`lem:flat-semisimple-normalization`, last clause): uniformly bounded constant
coordinates have a convergent subsequence. -/
theorem constant_coordinates_subseq (b₃ : ℕ → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
    (b₂ : ℕ → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (B : ℝ)
    (h₃ : ∀ k μ i j, ‖b₃ k μ i j‖ ≤ B) (h₂ : ∀ k μ i j, ‖b₂ k μ i j‖ ≤ B) :
    ∃ (φ : ℕ → ℕ) (B₃ : Fin 4 → Fin 3 → Fin 3 → ℂ) (B₂ : Fin 4 → Fin 2 → Fin 2 → ℂ),
      StrictMono φ ∧ ∀ μ, (∀ i j, Tendsto (fun k => b₃ (φ k) μ i j) atTop (𝓝 (B₃ μ i j))) ∧
        ∀ i j, Tendsto (fun k => b₂ (φ k) μ i j) atTop (𝓝 (B₂ μ i j)) := by
  set E := (Fin 4 → Fin 3 → Fin 3 → ℂ) × (Fin 4 → Fin 2 → Fin 2 → ℂ)
  set X : ℕ → E := fun k => (fun μ i j => b₃ k μ i j, fun μ i j => b₂ k μ i j)
  have hB : 0 ≤ B := (norm_nonneg _).trans (h₃ 0 0 0 0)
  have hbdd : Bornology.IsBounded (Metric.closedBall (0 : E) B) := Metric.isBounded_closedBall
  have hmem : ∀ k, X k ∈ Metric.closedBall (0 : E) B := fun k => by
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg hB).2 fun μ => (pi_norm_le_iff_of_nonneg hB).2 fun i =>
        (pi_norm_le_iff_of_nonneg hB).2 fun j => h₃ k μ i j
    · refine (pi_norm_le_iff_of_nonneg hB).2 fun μ => (pi_norm_le_iff_of_nonneg hB).2 fun i =>
        (pi_norm_le_iff_of_nonneg hB).2 fun j => h₂ k μ i j
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd hmem
  refine ⟨φ, a.1, a.2, hφ, fun μ => ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have hc : Continuous (fun a : (Fin 4 → Fin 3 → Fin 3 → ℂ) × (Fin 4 → Fin 2 → Fin 2 → ℂ) =>
        a.1 μ i j) := by fun_prop
    exact hc.continuousAt.tendsto.comp hlim
  · have hc : Continuous (fun a : (Fin 4 → Fin 3 → Fin 3 → ℂ) × (Fin 4 → Fin 2 → Fin 2 → ℂ) =>
        a.2 μ i j) := by fun_prop
    exact hc.continuousAt.tendsto.comp hlim

/-- **`lem:flat-semisimple-normalization`** for a sequence of grids `n_k` with fixed box side
`L = n_k h_k > 0`: every flat periodic `SU(3) × SU(2)` field `V_k` is gauge equivalent to constant
commuting links `e^{h_k b_{k,μ}}` with `b_{k,μ} ∈ 𝔰𝔲(3) ⊕ 𝔰𝔲(2)` bounded by `4π/L` uniformly in
`k`; after extraction the constant coordinates converge.  (Their first differences vanish
identically, being constant, and their plaquettes are trivial, `plaq_const_eq_one`.) -/
theorem flat_semisimple_normalization_seq (n : ℕ → ℕ) [∀ k, NeZero (n k)] {L : ℝ} (hL : 0 < L)
    (V : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → Gss) (hV : ∀ k, IsFlat (V k)) :
    ∃ (b₃ : ℕ → Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (b₂ : ℕ → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
      (g : ∀ k, (Fin 4 → ZMod (n k)) → Gss),
      (∀ k μ, star (b₃ k μ) = -b₃ k μ ∧ trace (b₃ k μ) = 0 ∧ star (b₂ k μ) = -b₂ k μ ∧
        trace (b₂ k μ) = 0) ∧
      (∀ k μ ν, Commute (b₃ k μ) (b₃ k ν) ∧ Commute (b₂ k μ) (b₂ k ν)) ∧
      (∀ k μ, (∀ i j, ‖b₃ k μ i j‖ ≤ 4 * Real.pi / L) ∧ ∀ i j, ‖b₂ k μ i j‖ ≤ 4 * Real.pi / L) ∧
      (∀ k x μ, ((gaugeAct (g k) (V k) x μ).1 : Matrix (Fin 3) (Fin 3) ℂ) =
          NormedSpace.exp (((L / n k : ℝ) : ℂ) • b₃ k μ) ∧
        ((gaugeAct (g k) (V k) x μ).2 : Matrix (Fin 2) (Fin 2) ℂ) =
          NormedSpace.exp (((L / n k : ℝ) : ℂ) • b₂ k μ)) ∧
      ∃ (φ : ℕ → ℕ) (B₃ : Fin 4 → Fin 3 → Fin 3 → ℂ) (B₂ : Fin 4 → Fin 2 → Fin 2 → ℂ),
        StrictMono φ ∧ ∀ μ, (∀ i j, Tendsto (fun k => b₃ (φ k) μ i j) atTop (𝓝 (B₃ μ i j))) ∧
          ∀ i j, Tendsto (fun k => b₂ (φ k) μ i j) atTop (𝓝 (B₂ μ i j)) := by
  have hh : ∀ k, 0 < L / n k := fun k => div_pos hL (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k)))
  have hnh : ∀ k, (n k : ℝ) * (L / n k) = L := fun k => by
    have : (n k : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (n k)
    field_simp
  choose b₃ b₂ g hs hc hb _ hg using fun k => flat_semisimple_normalization (n k) (hh k) (V k) (hV k)
  obtain ⟨φ, B₃, B₂, hφ, hlim⟩ := constant_coordinates_subseq b₃ b₂ (4 * Real.pi / L)
    (fun k μ i j => by have := (hb k μ).1 i j; rwa [hnh k] at this)
    (fun k μ i j => by have := (hb k μ).2 i j; rwa [hnh k] at this)
  refine ⟨b₃, b₂, g, hs, hc, fun k μ => ⟨fun i j => ?_, fun i j => ?_⟩, hg, φ, B₃, B₂, hφ, hlim⟩
  · have h1 := (hb k μ).1 i j
    rwa [hnh k] at h1
  · have h2 := (hb k μ).2 i j
    rwa [hnh k] at h2

end Assembly


/-- Non-vacuity: the trivial field is flat, and so is every constant field with commuting
values whose cycle holonomies need not be close to the identity (e.g. `C_μ = -1 ∈ SU(2)`). -/
theorem isFlat_one (n : ℕ) : IsFlat (fun (_ : Fin 4 → ZMod n) (_ : Fin 4) => (1 : Gss)) :=
  fun _ _ _ => rfl

end

end RenewalGeometry.FlatSemisimple
