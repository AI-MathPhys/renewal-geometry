/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.CohomologyZ4
import NCG.Upstream.AffinityCohomology

/-!
# Finite amplitude lifts and complex amplitude square roots

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex` (with `μ₄ ≅ ℤ/4`, `μ₂ ≅ ℤ/2` and the
squaring map as reduction of the exponent modulo two, as the notes
identify):

* `def:finite-amplitude-lift` — amplitude lifts
  `[u] ∈ H¹(G;ℤ/4)` of an orientation class with `q_*[u] = [χ]`;
* `thm:finite-amplitude-lifts` — `q_*` is surjective and each fibre
  has exactly `2^{b₁}` classes (a coset of the kernel — the torsor
  statement);
* `thm:order-four-forced-upstream` — a loop with signed holonomy
  `−1` forces an amplitude holonomy of exact (additive) order four:
  `μ₄` is the minimal finite coefficient group;
* `thm:no-canonical-z4-section` — the extension
  `μ₂ → μ₄ → μ₂` admits no group-theoretic section, so no additive
  coefficient-natural amplitude choice exists;
* `def:complex-amplitude-root` — complex cochains with
  `z(e)² = λ(e)`;
* `thm:amplitude-root-factorization` — `z(e) = e^{A(e)/2} i^{u(e)}`
  is an amplitude root for every finite phase lift `u`; conversely
  every root has modulus `e^{A/2}` and a fourth-root-of-unity phase
  whose square is the sign, and two roots differ by a `±1`
  cochain (the `μ₂` torsor);
* `cor:amplitude-conservative-upstream` — all roots of a fixed real
  class share modulus and squared phase: the signed cover and its
  Krein symmetry depend only on the square.
-/

namespace NCG.Multigraph

open NCG

variable (G : Multigraph)

/-! ## `def:finite-amplitude-lift` and `thm:finite-amplitude-lifts` -/

/-- **Definition `def:finite-amplitude-lift`**: a finite amplitude
lift of an orientation class `[χ] ∈ H¹(G;μ₂)` is a class
`[u] ∈ H¹(G;μ₄)` with `q_*[u] = [χ]`. -/
def IsAmplitudeLift (u : H1Z4 G) (χ : H1 G) : Prop :=
  H1Z4.reduce G u = χ

/-- **Theorem `thm:finite-amplitude-lifts` (existence)**: every
orientation class admits a finite amplitude lift. -/
theorem amplitudeLift_exists (χ : H1 G) :
    ∃ u : H1Z4 G, IsAmplitudeLift G u χ :=
  H1Z4.reduce_surjective G χ

/-- **Theorem `thm:finite-amplitude-lifts` (torsor / count)**: on a
finite connected graph, the lifts of a fixed orientation class form
a fibre of cardinality exactly `2^{b₁}` (a coset of the kernel of
the reduction — the `H¹(G;μ₂)`-torsor structure). -/
theorem amplitudeLift_card [Fintype G.V] [Fintype G.E] {v₀ : G.V}
    (hconn : G.ConnectedTo v₀) (χ : H1 G) :
    Nat.card {u : H1Z4 G // IsAmplitudeLift G u χ}
      = 2 ^ (Fintype.card G.E + 1 - Fintype.card G.V) :=
  card_fibre_reduce hconn χ

/-! ## Amplitude holonomy and `thm:order-four-forced-upstream` -/

namespace Walk

variable {G}

/-- Additive `ℤ/4` holonomy of a walk (phases multiply along the
path; backward traversal contributes the inverse phase). -/
def holonomy4 (u : G.E → ZMod 4) :
    ∀ {x y : G.V}, G.Walk x y → ZMod 4
  | _, _, .nil _ => 0
  | _, _, .fwd e p => u e + p.holonomy4 u
  | _, _, .bwd e p => -u e + p.holonomy4 u

@[simp] theorem holonomy4_nil (u : G.E → ZMod 4) (v : G.V) :
    (Walk.nil v).holonomy4 u = 0 := rfl

@[simp] theorem holonomy4_fwd (u : G.E → ZMod 4) (e : G.E)
    {w : G.V} (p : G.Walk (G.tgt e) w) :
    (Walk.fwd e p).holonomy4 u = u e + p.holonomy4 u := rfl

@[simp] theorem holonomy4_bwd (u : G.E → ZMod 4) (e : G.E)
    {w : G.V} (p : G.Walk (G.src e) w) :
    (Walk.bwd e p).holonomy4 u = -u e + p.holonomy4 u := rfl

/-- The `ℤ/4` holonomy reduces to the `ℤ/2` holonomy of the reduced
cochain. -/
theorem holonomy4_reduce (u : G.E → ZMod 4) :
    ∀ {x y : G.V} (p : G.Walk x y),
      z4ToZ2 (p.holonomy4 u) = p.holonomy (fun e => z4ToZ2 (u e)) := by
  intro x y p
  induction p with
  | nil _ => simp
  | fwd e p ih => simp [ih]
  | bwd e p ih => simp [ih]

end Walk

/-- **Theorem `thm:order-four-forced-upstream`**: if a loop has
nontrivial signed holonomy, any amplitude cochain lifting the sign
cochain has loop holonomy of exact additive order four
(`u(γ)² = −1`, i.e. `2·h = 2` in `ℤ/4`, and `h ∈ {1,3}`).  Hence
every finite phase group realizing the square root contains a cyclic
subgroup of order four — `μ₄` is minimal. -/
theorem order_four_forced (u : G.E → ZMod 4) (χ : G.E → ZMod 2)
    (hlift : ∀ e, z4ToZ2 (u e) = χ e) {v : G.V} (γ : G.Walk v v)
    (hχ : γ.holonomy χ = 1) :
    2 * γ.holonomy4 u = 2 ∧ 2 * γ.holonomy4 u ≠ 0
      ∧ 4 * γ.holonomy4 u = 0 := by
  have hred : z4ToZ2 (γ.holonomy4 u) = 1 := by
    rw [Walk.holonomy4_reduce]
    rw [show (fun e => z4ToZ2 (u e)) = χ from funext hlift]
    exact hχ
  have hcases : ∀ h : ZMod 4, z4ToZ2 h = 1 →
      2 * h = 2 ∧ 2 * h ≠ 0 ∧ 4 * h = 0 := by
    decide
  exact hcases _ hred

/-- **Theorem `thm:no-canonical-z4-section`**: the coefficient
extension `μ₂ → μ₄ → μ₂` does not split — there is no additive
homomorphism `s : ℤ/2 → ℤ/4` with `q ∘ s = id`.  The orientation
class alone supplies no coefficient-natural amplitude lift. -/
theorem no_canonical_z4_section (s : ZMod 2 →+ ZMod 4) :
    ¬∀ x : ZMod 2, z4ToZ2 (s x) = x := by
  intro hsec
  have h1 := hsec 1
  have h2 : s 1 + s 1 = 0 := by
    rw [← map_add]
    rw [show (1 : ZMod 2) + 1 = 0 from by decide]
    exact map_zero s
  have hno : ∀ y : ZMod 4, z4ToZ2 y = 1 → y + y = 0 → False := by
    decide
  exact hno (s 1) h1 h2

/-! ## `def:complex-amplitude-root`,
`thm:amplitude-root-factorization` -/

variable {G}

/-- **Definition `def:complex-amplitude-root`**: an edge-wise
complex amplitude square root of the real comparison cochain
`λ : E → ℝˣ` — a complex cochain with `z(e)² = λ(e)`. -/
def IsComplexAmplitudeRoot (z : G.E → ℂ) (lam : G.E → ℝˣ) : Prop :=
  ∀ e, (z e) ^ 2 = ((lam e : ℝ) : ℂ)

/-- The fourth root of unity attached to a `ℤ/4` phase exponent. -/
noncomputable def phaseOf (h : ZMod 4) : ℂ := Complex.I ^ h.val

theorem phaseOf_sq (h : ZMod 4) (χ : ZMod 2) (hred : z4ToZ2 h = χ) :
    phaseOf h ^ 2 = if χ = 0 then 1 else -1 := by
  have hall : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
    decide
  rcases hall h with h0 | h0 | h0 | h0 <;> subst h0
  · have hχ : χ = 0 := by rw [← hred]; decide
    subst hχ
    rw [if_pos rfl]
    show (Complex.I ^ (0 : ℕ)) ^ 2 = 1
    norm_num
  · have hχ : χ = 1 := by rw [← hred]; decide
    subst hχ
    rw [if_neg (by decide)]
    show (Complex.I ^ (1 : ℕ)) ^ 2 = -1
    rw [pow_one, Complex.I_sq]
  · have hχ : χ = 0 := by rw [← hred]; decide
    subst hχ
    rw [if_pos rfl]
    show (Complex.I ^ (2 : ℕ)) ^ 2 = 1
    rw [show Complex.I ^ (2 : ℕ) = Complex.I ^ 2 from rfl,
      Complex.I_sq]
    ring
  · have hχ : χ = 1 := by rw [← hred]; decide
    subst hχ
    rw [if_neg (by decide)]
    show (Complex.I ^ (3 : ℕ)) ^ 2 = -1
    rw [← pow_mul]
    show Complex.I ^ (6 : ℕ) = -1
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Complex.I_sq]
    ring

/-- **Theorem `thm:amplitude-root-factorization` (construction)**:
for any finite phase lift `u` of the sign cochain,
`z(e) = e^{A(e)/2} i^{u(e)}` is a complex amplitude root of `λ`. -/
theorem amplitude_root_construction (lam : G.E → ℝˣ)
    (u : G.E → ZMod 4)
    (hlift : ∀ e, z4ToZ2 (u e) = lineSign G lam e) :
    IsComplexAmplitudeRoot
      (fun e => (Real.exp (lineMagnitude G lam e / 2) : ℂ)
        * phaseOf (u e)) lam := by
  intro e
  show ((Real.exp (lineMagnitude G lam e / 2) : ℂ)
    * phaseOf (u e)) ^ 2 = _
  rw [mul_pow, phaseOf_sq (u e) (lineSign G lam e) (hlift e)]
  have hexp : ((Real.exp (lineMagnitude G lam e / 2) : ℝ) : ℂ) ^ 2
      = ((Real.exp (lineMagnitude G lam e) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow]
    congr 1
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have habs : Real.exp (lineMagnitude G lam e) = |(lam e : ℝ)| := by
    rw [lineMagnitude, Real.exp_log (abs_pos.mpr (Units.ne_zero _))]
  unfold lineSign
  rcases lt_or_gt_of_ne (Units.ne_zero (lam e)) with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), if_neg (by decide), habs,
      abs_of_neg hneg]
    push_cast
    ring
  · rw [if_pos hpos, if_pos rfl, habs, abs_of_pos hpos, mul_one]

/-- **Theorem `thm:amplitude-root-factorization` (modulus of any
root)**: every complex amplitude root has modulus `e^{A/2}`. -/
theorem amplitude_root_abs (z : G.E → ℂ) (lam : G.E → ℝˣ)
    (hz : IsComplexAmplitudeRoot z lam) (e : G.E) :
    ‖z e‖ = Real.exp (lineMagnitude G lam e / 2) := by
  have h1 : ‖z e‖ ^ 2 = |(lam e : ℝ)| := by
    rw [← norm_pow, hz e, Complex.norm_real, Real.norm_eq_abs]
  have h2 : Real.exp (lineMagnitude G lam e / 2) ^ 2
      = |(lam e : ℝ)| := by
    rw [sq, ← Real.exp_add]
    rw [show lineMagnitude G lam e / 2 + lineMagnitude G lam e / 2
        = lineMagnitude G lam e from by ring]
    rw [lineMagnitude, Real.exp_log (abs_pos.mpr (Units.ne_zero _))]
  have h3 : ‖z e‖ = Real.sqrt |(lam e : ℝ)| := by
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  have h4 : Real.exp (lineMagnitude G lam e / 2)
      = Real.sqrt |(lam e : ℝ)| := by
    rw [← h2, Real.sqrt_sq (Real.exp_pos _).le]
  rw [h3, h4]

/-- **Theorem `thm:amplitude-root-factorization` (squared phase)**:
the unit phase of any root squares to the sign of `λ` — the root has
the form `e^{A/2} · (fourth root of unity)` edgewise. -/
theorem amplitude_root_phase_sq (z : G.E → ℂ) (lam : G.E → ℝˣ)
    (hz : IsComplexAmplitudeRoot z lam) (e : G.E) :
    ((z e / (‖z e‖ : ℂ)) ^ 2
      = if lineSign G lam e = 0 then 1 else -1)
    ∧ (z e / (‖z e‖ : ℂ)) ^ 4 = 1 := by
  have hz0 : z e ≠ 0 := by
    intro h0
    have := hz e
    rw [h0] at this
    have h1 : ((lam e : ℝ) : ℂ) = 0 := by
      rw [← this]
      ring
    exact Units.ne_zero (lam e) (by exact_mod_cast h1)
  have hn0 : (‖z e‖ : ℂ) ≠ 0 := by
    simpa using norm_ne_zero_iff.mpr hz0
  have habs2 : (‖z e‖ : ℂ) ^ 2
      = Complex.ofReal |(lam e : ℝ)| := by
    rw [← Complex.ofReal_pow, ← norm_pow, hz e, Complex.norm_real, Real.norm_eq_abs]
  have hmain : (z e / (‖z e‖ : ℂ)) ^ 2
      = if lineSign G lam e = 0 then 1 else -1 := by
    rw [div_pow, hz e, habs2]
    unfold lineSign
    rcases lt_or_gt_of_ne (Units.ne_zero (lam e)) with hneg | hpos
    · rw [if_neg (not_lt.mpr hneg.le), if_neg (by decide),
        abs_of_neg hneg]
      rw [div_eq_iff (by
        intro h0
        rw [Complex.ofReal_eq_zero] at h0
        exact (Units.ne_zero (lam e)) (by linarith [h0]))]
      push_cast
      ring
    · rw [if_pos hpos, if_pos rfl, abs_of_pos hpos]
      exact div_self (by
        intro h0
        rw [Complex.ofReal_eq_zero] at h0
        exact (Units.ne_zero (lam e)) h0)
  refine ⟨hmain, ?_⟩
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hmain]
  rcases lt_or_gt_of_ne (Units.ne_zero (lam e)) with hneg | hpos
  · unfold lineSign
    rw [if_neg (not_lt.mpr hneg.le), if_neg (by decide)]
    ring
  · unfold lineSign
    rw [if_pos hpos, if_pos rfl]
    ring

/-- **Theorem `thm:amplitude-root-factorization` (torsor)**: two
amplitude roots of the same real class differ edgewise by `±1` — the
set of roots is a torsor for the `μ₂` cochains. -/
theorem amplitude_root_ratio (z z' : G.E → ℂ) (lam : G.E → ℝˣ)
    (hz : IsComplexAmplitudeRoot z lam)
    (hz' : IsComplexAmplitudeRoot z' lam) (e : G.E) :
    z e = z' e ∨ z e = -z' e := by
  have h1 : (z e) ^ 2 = (z' e) ^ 2 := by rw [hz e, hz' e]
  have h2 : (z e - z' e) * (z e + z' e) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- Multiplying a root by a `±1` cochain gives another root. -/
theorem amplitude_root_mul_sign (z : G.E → ℂ) (lam : G.E → ℝˣ)
    (hz : IsComplexAmplitudeRoot z lam) (ε : G.E → ℂ)
    (hε : ∀ e, ε e = 1 ∨ ε e = -1) :
    IsComplexAmplitudeRoot (fun e => ε e * z e) lam := by
  intro e
  show (ε e * z e) ^ 2 = _
  have hsq : (ε e) ^ 2 = 1 := by
    rcases hε e with h | h <;> rw [h] <;> ring
  rw [mul_pow, hsq, one_mul]
  exact hz e

/-- **Corollary `cor:amplitude-conservative-upstream`**: all
amplitude roots of a fixed real comparison class share their modulus
(`e^{A/2}`, hence the real affinity class) and their square (hence
the orientation class and the signed cover with its Krein
symmetry): changing the lift moves only the square-root phase
sector. -/
theorem amplitude_conservative (z z' : G.E → ℂ) (lam : G.E → ℝˣ)
    (hz : IsComplexAmplitudeRoot z lam)
    (hz' : IsComplexAmplitudeRoot z' lam) (e : G.E) :
    ‖z e‖ = ‖z' e‖ ∧ (z e) ^ 2 = (z' e) ^ 2 := by
  constructor
  · rw [amplitude_root_abs z lam hz e, amplitude_root_abs z' lam hz' e]
  · rw [hz e, hz' e]

end NCG.Multigraph
