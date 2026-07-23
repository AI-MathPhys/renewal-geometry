/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.SignedCover
import NCG.Graph.Cohomology

/-!
# Gauge covariance, the real affinity class, and the orientation cover

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `definition:local-normalization-gauge` — gauges `u : V → ℝ` acting
  by `A ↦ A + δu`;
* `thm:affinity-cohomology` — the gauge-invariant content of
  same-orientation mismatch is `[A] ∈ H¹(G;ℝ)`: path additivity,
  gauge transformation, cycle invariance, `[A] = 0` iff all cycle
  affinities vanish iff some gauge trivializes all relative weights;
* `def:relative-line-system` — rank-one real local systems in local
  frames: invertible edge coefficients `λ_e ∈ ℝˣ` (with the reverse
  transport `λ_e⁻¹`), magnitude `A_L = log|λ|` and sign
  `χ_L = sgn λ`;
* `lem:line-gauge-laws` — frame changes act by `A_L ↦ A_L − δu` and
  `χ_L ↦ χ_L + δ₂h`;
* `thm:two-invariant-line-classification` — gauge classes of line
  systems are classified by `H¹(G;ℝ) × H¹(G;ℤ/2)`, via
  `λ ↦ (log|λ|, sgn λ)` (gauge equivalence iff both classes agree,
  and every pair is realized);
* `thm:orientation-cover-upstream` — the orientation cover is the
  principal `ℤ/2` signed cover with class `w₁ = [χ_L]`: trivial iff
  a coherent orientation exists iff every cycle has positive sign
  holonomy, with the explicit trivialization, and connected whenever
  `w₁ ≠ 0`;
* `thm:upstream-signed-cover-bridge` — with calibrated magnitudes
  `|λ_e| = p⁺_e/p⁻_e`, the two classes are exactly the affinity
  class and the downstream signed-cover class;
* `prop:positive-comparison-trivial-sign` — positive transports give
  `w₁ = 0`;
* `thm:no-real-to-modtwo-reduction` — every additive map
  `ℝ → ℤ/2` vanishes;
* `thm:independence-one-loop` — on the one-loop graph the four
  holonomies `1, e^a, −1, −e^a` realize all four combinations of
  `([A] ≠ 0, w₁ ≠ 0)`;
* `cor:three-levels-distinct-v4` — affinity and orientation are
  logically independent (realized by the one-loop witnesses);
* `prop:no-canonical-section` — no automorphism-invariant selector
  exists when an automorphism exchanges two members of a class.
-/

namespace NCG.Multigraph

open NCG

variable (G : Multigraph)

/-! ## Real cochains and `H¹(G;ℝ)` -/

/-- The real coboundary `(δu)(e) = u(t(e)) − u(s(e))`. -/
def coboundR : (G.V → ℝ) →ₗ[ℝ] (G.E → ℝ) where
  toFun u := fun e => u (G.tgt e) - u (G.src e)
  map_add' u v := by
    funext e
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem coboundR_apply (u : G.V → ℝ) (e : G.E) :
    coboundR G u e = u (G.tgt e) - u (G.src e) := rfl

/-- Real first cohomology `H¹(G;ℝ) = C¹/δC⁰` (a graph has no
2-cells). -/
def H1R := (G.E → ℝ) ⧸ LinearMap.range (coboundR G)

instance : AddCommGroup (H1R G) :=
  inferInstanceAs (AddCommGroup
    ((G.E → ℝ) ⧸ LinearMap.range (coboundR G)))

instance : Module ℝ (H1R G) :=
  inferInstanceAs (Module ℝ
    ((G.E → ℝ) ⧸ LinearMap.range (coboundR G)))

/-- The class of a real one-cochain. -/
def H1R.mk : (G.E → ℝ) →ₗ[ℝ] H1R G := Submodule.mkQ _

variable {G}

theorem H1R.mk_eq_zero_iff {A : G.E → ℝ} :
    H1R.mk G A = 0 ↔ ∃ u : G.V → ℝ, A = coboundR G u := by
  have h1 : H1R.mk G A = 0 ↔ A ∈ LinearMap.range (coboundR G) :=
    Submodule.Quotient.mk_eq_zero _
  rw [h1]
  constructor
  · rintro ⟨u, hu⟩; exact ⟨u, hu.symm⟩
  · rintro ⟨u, hu⟩; exact ⟨u, hu.symm⟩

/-! ## Walk affinity: `thm:affinity-cohomology` -/

namespace Walk

/-- The affinity of a walk: sum of edge values, with sign reversed on
backward traversals (the antisymmetric one-cochain convention
`A(ē) = −A(e)` of `ass:reciprocal-relative-weights`). -/
def affinity (A : G.E → ℝ) : ∀ {u v : G.V}, G.Walk u v → ℝ
  | _, _, .nil _ => 0
  | _, _, .fwd e p => A e + p.affinity A
  | _, _, .bwd e p => -A e + p.affinity A

@[simp] theorem affinity_nil (A : G.E → ℝ) (v : G.V) :
    (Walk.nil v).affinity A = 0 := rfl

@[simp] theorem affinity_fwd (A : G.E → ℝ) (e : G.E) {w : G.V}
    (p : G.Walk (G.tgt e) w) :
    (Walk.fwd e p).affinity A = A e + p.affinity A := rfl

@[simp] theorem affinity_bwd (A : G.E → ℝ) (e : G.E) {w : G.V}
    (p : G.Walk (G.src e) w) :
    (Walk.bwd e p).affinity A = -A e + p.affinity A := rfl

/-- **Theorem `thm:affinity-cohomology` (i)**: affinity is additive
under concatenation. -/
theorem affinity_append (A : G.E → ℝ) :
    ∀ {u v w : G.V} (p : G.Walk u v) (q : G.Walk v w),
      (p.append q).affinity A = p.affinity A + q.affinity A := by
  intro u v w p q
  induction p with
  | nil _ => simp
  | fwd e p ih => simp [ih]; ring
  | bwd e p ih => simp [ih]; ring

/-- Affinity of the reversed walk is the negative. -/
theorem affinity_reverse (A : G.E → ℝ) :
    ∀ {u v : G.V} (p : G.Walk u v),
      p.reverse.affinity A = -(p.affinity A) := by
  intro u v p
  induction p with
  | nil _ => simp [Walk.reverse]
  | fwd e p ih =>
    change (p.reverse.append (singleRev e)).affinity A = _
    rw [affinity_append, ih]
    simp [Walk.singleRev]
  | bwd e p ih =>
    change (p.reverse.append (single e)).affinity A = _
    rw [affinity_append, ih]
    simp [Walk.single]

/-- **Theorem `thm:affinity-cohomology` (ii)**: under a local
normalization gauge (`definition:local-normalization-gauge`),
`𝒜^u(γ) = 𝒜(γ) + u(y) − u(x)` for a walk from `x` to `y`. -/
theorem affinity_gauge (A : G.E → ℝ) (u : G.V → ℝ) :
    ∀ {x y : G.V} (p : G.Walk x y),
      p.affinity (A + coboundR G u) = p.affinity A + (u y - u x) := by
  intro x y p
  induction p with
  | nil _ => simp
  | fwd e p ih => simp [ih]; ring
  | bwd e p ih => simp [ih]; ring

/-- Affinity is additive in the cochain. -/
theorem affinity_add_cochain (A B : G.E → ℝ) {u v : G.V}
    (p : G.Walk u v) :
    p.affinity (A + B) = p.affinity A + p.affinity B := by
  induction p with
  | nil _ => simp
  | fwd e p ih => simp [ih]; ring
  | bwd e p ih => simp [ih]; ring

/-- Affinity with respect to the zero cochain vanishes. -/
theorem affinity_zero {u v : G.V} (p : G.Walk u v) :
    p.affinity (0 : G.E → ℝ) = 0 := by
  induction p with
  | nil _ => simp
  | fwd e p ih => simp [ih]
  | bwd e p ih => simp [ih]

/-- **Theorem `thm:affinity-cohomology` (iii)**: cycle affinities are
gauge invariant and depend only on the class `[A]`. -/
theorem affinity_congr {A A' : G.E → ℝ}
    (h : H1R.mk G A = H1R.mk G A') {v : G.V} (p : G.Walk v v) :
    p.affinity A = p.affinity A' := by
  have hsub : A - A' ∈ LinearMap.range (coboundR G) := by
    rw [← Submodule.Quotient.eq]
    exact h
  obtain ⟨u, hu⟩ := hsub
  have hdecomp : A = A' + coboundR G u := by
    rw [hu]; abel
  rw [hdecomp, affinity_gauge]
  simp

end Walk

/-- **Theorem `thm:affinity-cohomology` (iv)**: on a connected graph,
`[A] = 0` iff every cycle affinity vanishes.  (The converse is the
potential construction: base every vertex by a chosen walk.) -/
theorem H1R.mk_eq_zero_iff_cycles {v₀ : G.V}
    (hconn : G.ConnectedTo v₀) (A : G.E → ℝ) :
    H1R.mk G A = 0 ↔
      ∀ (v : G.V) (p : G.Walk v v), p.affinity A = 0 := by
  constructor
  · intro h v p
    have h0 : p.affinity A = p.affinity (0 : G.E → ℝ) :=
      Walk.affinity_congr (by simpa using h) p
    rw [h0, Walk.affinity_zero]
  · intro hcyc
    rw [H1R.mk_eq_zero_iff]
    have hwalk : ∀ v : G.V, Nonempty (G.Walk v₀ v) := hconn
    refine ⟨fun v => (Classical.choice (hwalk v)).affinity A, ?_⟩
    funext e
    set γs := Classical.choice (hwalk (G.src e))
    set γt := Classical.choice (hwalk (G.tgt e))
    have hcycle := hcyc v₀
      ((γs.append (Walk.single e)).append γt.reverse)
    rw [Walk.affinity_append, Walk.affinity_append,
      Walk.affinity_reverse] at hcycle
    have hsingle : (Walk.single e).affinity A = A e := by
      simp [Walk.single]
    rw [hsingle] at hcycle
    simp only [coboundR_apply]
    linarith

/-- **Theorem `thm:affinity-cohomology` (v)**: `[A] = 0` iff some
gauge makes every relative weight equal to one (`A + δu = 0`). -/
theorem H1R.mk_eq_zero_iff_gauge (A : G.E → ℝ) :
    H1R.mk G A = 0 ↔ ∃ u : G.V → ℝ, A + coboundR G u = 0 := by
  rw [H1R.mk_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    rw [hu, map_neg]
    abel
  · rintro ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    rw [map_neg]
    have := congrArg (· - coboundR G u) hu
    simpa [sub_eq_add_neg] using this

/-! ## Rank-one real line systems: `def:relative-line-system`,
`lem:line-gauge-laws` -/

variable (G)

/-- **Definition `def:relative-line-system` (in local frames)**: a
rank-one real local system is presented by invertible edge
coefficients `λ_e ∈ ℝˣ` (`T_e b_{s(e)} = λ_e b_{t(e)}`; the reverse
transport is `λ_e⁻¹`, so one unit per geometric edge is the entire
datum).  Its magnitude cochain. -/
noncomputable def lineMagnitude (lam : G.E → ℝˣ) : G.E → ℝ :=
  fun e => Real.log |(lam e : ℝ)|

/-- **Definition `def:relative-line-system` (sign cochain)**:
`χ_L(e) = sgn λ_e`, written additively in `ℤ/2`. -/
noncomputable def lineSign (lam : G.E → ℝˣ) : G.E → ZMod 2 :=
  fun e => if 0 < (lam e : ℝ) then 0 else 1

/-- The frame-change (gauge) action on line coefficients:
`λ'_e = g_{s(e)} g_{t(e)}⁻¹ λ_e`. -/
def lineGauge (g : G.V → ℝˣ) (lam : G.E → ℝˣ) : G.E → ℝˣ :=
  fun e => g (G.src e) * (g (G.tgt e))⁻¹ * lam e

/-- **Lemma `lem:line-gauge-laws` (magnitude)**:
`A_L' = A_L − δu` with `u = log|g|`. -/
theorem lineMagnitude_gauge (g : G.V → ℝˣ) (lam : G.E → ℝˣ) :
    lineMagnitude G (lineGauge G g lam)
      = lineMagnitude G lam
        - coboundR G (fun x => Real.log |(g x : ℝ)|) := by
  funext e
  simp only [lineMagnitude, lineGauge, Pi.sub_apply, coboundR_apply,
    Units.val_mul]
  rw [abs_mul, abs_mul, Real.log_mul, Real.log_mul]
  · have hinv : |(((g (G.tgt e))⁻¹ : ℝˣ) : ℝ)|
        = |(g (G.tgt e) : ℝ)|⁻¹ := by
      rw [Units.val_inv_eq_inv_val, abs_inv]
    rw [hinv, Real.log_inv]
    ring
  · exact abs_ne_zero.mpr (Units.ne_zero _)
  · exact abs_ne_zero.mpr (Units.ne_zero _)
  · apply mul_ne_zero
    · exact abs_ne_zero.mpr (Units.ne_zero _)
    · rw [abs_ne_zero]
      exact Units.ne_zero _
  · exact abs_ne_zero.mpr (Units.ne_zero _)

/-- The additive `ℤ/2` sign of a unit. -/
noncomputable def unitSign (r : ℝˣ) : ZMod 2 :=
  if 0 < (r : ℝ) then 0 else 1

theorem unitSign_mul (r s : ℝˣ) :
    unitSign (r * s) = unitSign r + unitSign s := by
  unfold unitSign
  have hval : ((r * s : ℝˣ) : ℝ) = (r : ℝ) * s := Units.val_mul r s
  rcases lt_or_gt_of_ne (Units.ne_zero r) with hr | hr <;>
    rcases lt_or_gt_of_ne (Units.ne_zero s) with hs | hs
  · have hrs : 0 < ((r * s : ℝˣ) : ℝ) := by
      rw [hval]; exact mul_pos_of_neg_of_neg hr hs
    rw [if_pos hrs, if_neg (not_lt.mpr hr.le),
      if_neg (not_lt.mpr hs.le)]
    decide
  · have hrs : ((r * s : ℝˣ) : ℝ) < 0 := by
      rw [hval]; exact mul_neg_of_neg_of_pos hr hs
    rw [if_neg (not_lt.mpr hrs.le), if_neg (not_lt.mpr hr.le),
      if_pos hs]
    decide
  · have hrs : ((r * s : ℝˣ) : ℝ) < 0 := by
      rw [hval]; exact mul_neg_of_pos_of_neg hr hs
    rw [if_neg (not_lt.mpr hrs.le), if_pos hr,
      if_neg (not_lt.mpr hs.le)]
    decide
  · have hrs : 0 < ((r * s : ℝˣ) : ℝ) := by
      rw [hval]; exact mul_pos hr hs
    rw [if_pos hrs, if_pos hr, if_pos hs]
    decide

theorem unitSign_inv (r : ℝˣ) : unitSign r⁻¹ = unitSign r := by
  unfold unitSign
  have hcast : ((r⁻¹ : ℝˣ) : ℝ) = (r : ℝ)⁻¹ := Units.val_inv_eq_inv_val r
  rcases lt_or_gt_of_ne (Units.ne_zero r) with hr | hr
  · have h1 : (r : ℝ)⁻¹ < 0 := inv_lt_zero.mpr hr
    rw [if_neg (not_lt.mpr hr.le), if_neg (by rw [hcast]; exact not_lt.mpr h1.le)]
  · have h1 : 0 < (r : ℝ)⁻¹ := inv_pos.mpr hr
    rw [if_pos (by rw [hcast]; exact h1), if_pos hr]

theorem lineSign_eq_unitSign (lam : G.E → ℝˣ) (e : G.E) :
    lineSign G lam e = unitSign (lam e) := rfl

/-- **Lemma `lem:line-gauge-laws` (sign)**: `χ_L' = χ_L + δ₂h` with
`h = sgn g` — frame changes act by a `ℤ/2` coboundary. -/
theorem lineSign_gauge (g : G.V → ℝˣ) (lam : G.E → ℝˣ) :
    lineSign G (lineGauge G g lam)
      = lineSign G lam + coboundaryMap G (fun x => unitSign (g x)) := by
  funext e
  change unitSign (g (G.src e) * (g (G.tgt e))⁻¹ * lam e) = _
  rw [unitSign_mul, unitSign_mul, unitSign_inv]
  simp only [Pi.add_apply, coboundaryMap_apply, lineSign_eq_unitSign]
  ring

/-- Two units with equal magnitude and equal sign are equal. -/
theorem unit_eq_of_sign_mag (r s : ℝˣ)
    (hm : Real.log |(r : ℝ)| = Real.log |(s : ℝ)|)
    (hs : unitSign r = unitSign s) : r = s := by
  have habs : |(r : ℝ)| = |(s : ℝ)| := by
    have h1 : Real.exp (Real.log |(r : ℝ)|) = |(r : ℝ)| :=
      Real.exp_log (abs_pos.mpr (Units.ne_zero r))
    have h2 : Real.exp (Real.log |(s : ℝ)|) = |(s : ℝ)| :=
      Real.exp_log (abs_pos.mpr (Units.ne_zero s))
    rw [← h1, ← h2, hm]
  apply Units.ext
  unfold unitSign at hs
  rcases lt_or_gt_of_ne (Units.ne_zero r) with hr | hr
  · rcases lt_or_gt_of_ne (Units.ne_zero s) with hsn | hsn
    · have := congrArg (fun x => -x) habs
      rw [abs_of_neg hr, abs_of_neg hsn] at habs
      linarith
    · rw [if_neg (not_lt.mpr hr.le), if_pos hsn] at hs
      exact absurd hs (by decide)
  · rcases lt_or_gt_of_ne (Units.ne_zero s) with hsn | hsn
    · rw [if_pos hr, if_neg (not_lt.mpr hsn.le)] at hs
      exact absurd hs (by decide)
    · rw [abs_of_pos hr, abs_of_pos hsn] at habs
      exact habs

/-- A unit with prescribed magnitude and sign. -/
noncomputable def unitOf (a : ℝ) (ε : ZMod 2) : ℝˣ :=
  (if ε = 0 then 1 else -1) * Units.mk0 (Real.exp a) (Real.exp_ne_zero a)

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem unitOf_val (a : ℝ) (ε : ZMod 2) :
    (unitOf a ε : ℝ) = (if ε = 0 then 1 else -1) * Real.exp a := by
  unfold unitOf
  rcases zmod2_cases ε with h | h <;> subst h <;> simp

theorem unitOf_log_abs (a : ℝ) (ε : ZMod 2) :
    Real.log |(unitOf a ε : ℝ)| = a := by
  rw [unitOf_val]
  rcases zmod2_cases ε with h | h <;> subst h
  · simp [abs_of_pos (Real.exp_pos a), Real.log_exp]
  · rw [if_neg (by decide)]
    rw [show (-1 : ℝ) * Real.exp a = -(Real.exp a) by ring, abs_neg,
      abs_of_pos (Real.exp_pos a), Real.log_exp]

theorem unitOf_sign (a : ℝ) (ε : ZMod 2) :
    unitSign (unitOf a ε) = ε := by
  unfold unitSign
  rw [unitOf_val]
  rcases zmod2_cases ε with h | h <;> subst h
  · rw [if_pos]
    rw [if_pos rfl, one_mul]
    exact Real.exp_pos a
  · rw [if_neg]
    rw [if_neg (by decide)]
    have : (-1 : ℝ) * Real.exp a < 0 := by
      have := Real.exp_pos a
      nlinarith
    exact not_lt.mpr this.le

/-- **Theorem `thm:two-invariant-line-classification`
(realization)**: every pair `(A, χ)` of a real magnitude cochain and
a `ℤ/2` sign cochain is realized by a line system. -/
theorem line_realization (A : G.E → ℝ) (χ : G.E → ZMod 2) :
    ∃ lam : G.E → ℝˣ,
      lineMagnitude G lam = A ∧ lineSign G lam = χ := by
  refine ⟨fun e => unitOf (A e) (χ e), ?_, ?_⟩
  · funext e
    exact unitOf_log_abs (A e) (χ e)
  · funext e
    exact unitOf_sign (A e) (χ e)

/-- **Theorem `thm:two-invariant-line-classification`**: two line
systems are gauge equivalent iff their magnitude classes in
`H¹(G;ℝ)` and sign classes in `H¹(G;ℤ/2)` agree — with
`line_realization`, gauge classes of rank-one real local systems are
classified by `H¹(G;ℝ) × H¹(G;ℤ/2)`. -/
theorem line_classification (lam lam' : G.E → ℝˣ) :
    (∃ g : G.V → ℝˣ, lam' = lineGauge G g lam) ↔
      (H1R.mk G (lineMagnitude G lam)
          = H1R.mk G (lineMagnitude G lam')
        ∧ H1.mk G (lineSign G lam) = H1.mk G (lineSign G lam')) := by
  constructor
  · rintro ⟨g, rfl⟩
    constructor
    · rw [lineMagnitude_gauge]
      symm
      have heq : ∀ x y : G.E → ℝ,
          H1R.mk G x = H1R.mk G y ↔
            x - y ∈ LinearMap.range (coboundR G) := fun x y =>
        Submodule.Quotient.eq _
      rw [heq]
      refine ⟨fun x => -Real.log |(g x : ℝ)|, ?_⟩
      funext e
      simp only [Pi.sub_apply, coboundR_apply]
      ring
    · rw [lineSign_gauge]
      symm
      have heq : ∀ x y : G.E → ZMod 2,
          H1.mk G x = H1.mk G y ↔
            x - y ∈ LinearMap.range (coboundaryMap G) := fun x y =>
        Submodule.Quotient.eq _
      rw [heq]
      refine ⟨fun x => unitSign (g x), ?_⟩
      funext e
      simp only [Pi.sub_apply, coboundaryMap_apply, Pi.add_apply]
      ring
  · rintro ⟨hmag, hsign⟩
    have hm : lineMagnitude G lam - lineMagnitude G lam'
        ∈ LinearMap.range (coboundR G) := by
      rw [← Submodule.Quotient.eq]
      exact hmag
    have hsn : lineSign G lam - lineSign G lam'
        ∈ LinearMap.range (coboundaryMap G) := by
      rw [← Submodule.Quotient.eq]
      exact hsign
    obtain ⟨u, hu⟩ := hm
    obtain ⟨h, hh⟩ := hsn
    refine ⟨fun x => unitOf (u x) (h x), ?_⟩
    funext e
    apply unit_eq_of_sign_mag
    · have hgauge := congrFun
        (lineMagnitude_gauge G (fun x => unitOf (u x) (h x)) lam) e
      have hue := congrFun hu e
      simp only [Pi.sub_apply, coboundR_apply] at hue
      calc Real.log |(lam' e : ℝ)|
          = lineMagnitude G lam' e := rfl
        _ = lineMagnitude G lam e
            - (Real.log |((unitOf (u (G.tgt e)) (h (G.tgt e)) : ℝˣ) : ℝ)|
              - Real.log |((unitOf (u (G.src e)) (h (G.src e)) : ℝˣ) : ℝ)|) := by
            rw [unitOf_log_abs, unitOf_log_abs]
            linarith
        _ = lineMagnitude G
              (lineGauge G (fun x => unitOf (u x) (h x)) lam) e := by
            rw [hgauge]
            rfl
        _ = Real.log
              |((lineGauge G (fun x => unitOf (u x) (h x)) lam) e : ℝ)| :=
            rfl
    · have hgauge := congrFun
        (lineSign_gauge G (fun x => unitOf (u x) (h x)) lam) e
      have hhe := congrFun hh e
      simp only [Pi.sub_apply, coboundaryMap_apply] at hhe
      calc unitSign (lam' e)
          = lineSign G lam' e := rfl
        _ = lineSign G lam e
            + (unitSign (unitOf (u (G.src e)) (h (G.src e)))
              + unitSign (unitOf (u (G.tgt e)) (h (G.tgt e)))) := by
            rw [unitOf_sign, unitOf_sign]
            have hall : ∀ a b c : ZMod 2, c = a - b → b = a + c := by
              decide
            exact hall _ _ _ hhe
        _ = lineSign G
              (lineGauge G (fun x => unitOf (u x) (h x)) lam) e := by
            rw [hgauge]
            rfl
        _ = unitSign
              ((lineGauge G (fun x => unitOf (u x) (h x)) lam) e) := rfl

/-! ## `thm:orientation-cover-upstream` -/

/-- **Theorem `thm:orientation-cover-upstream` ((i) ↔ (ii))**: the
orientation class vanishes iff a coherent global orientation (a
vertex gauge trivializing every edge sign) exists. -/
theorem orientation_class_zero_iff_coherent (χ : G.E → ZMod 2) :
    H1.mk G χ = 0 ↔ IsCoboundary (G := G) χ :=
  H1.mk_eq_zero_iff

/-- **Theorem `thm:orientation-cover-upstream` ((i) ↔ (iii))**: the
orientation class vanishes iff every cycle has positive sign
holonomy. -/
theorem orientation_class_zero_iff_cycles {v₀ : G.V}
    (hconn : G.ConnectedTo v₀) (χ : G.E → ZMod 2) :
    H1.mk G χ = 0 ↔
      ∀ (v : G.V) (p : G.Walk v v), p.holonomy χ = 0 := by
  constructor
  · intro h v p
    exact holonomy_eq_zero_of_isCoboundary (H1.mk_eq_zero_iff.mp h) p
  · intro hcyc
    exact H1.mk_eq_zero_of_holonomy_eq_zero hconn (hcyc v₀)

/-- **Theorem `thm:orientation-cover-upstream` ((ii) → (iv))**: a
coherent orientation splits the orientation cover — the explicit
sheet-gauge morphism onto the trivial double cover `G ⊔ G`. -/
noncomputable def orientationCoverSplit (χ : G.E → ZMod 2)
    (h : IsCoboundary (G := G) χ) :
    Hom (G.signedCover χ) (G.signedCover fun _ => 0) := by
  refine trivializeHom χ (Classical.choose h) ?_
  exact Classical.choose_spec h

/-- **Theorem `thm:orientation-cover-upstream` (nontrivial case)**:
if `w₁ ≠ 0` the orientation cover is connected — it is exactly the
principal signed double cover of the downstream geometry. -/
theorem signedCover_connected_of_ne_zero {v₀ : G.V}
    (hconn : G.ConnectedTo v₀) {χ : G.E → ZMod 2}
    (hne : H1.mk G χ ≠ 0) :
    (G.signedCover χ).ConnectedTo (v₀, 0) := by
  have h2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hloop : ∃ p : G.Walk v₀ v₀, p.holonomy χ = 1 := by
    by_contra hno
    push Not at hno
    refine hne (H1.mk_eq_zero_of_holonomy_eq_zero hconn fun p => ?_)
    rcases h2 (p.holonomy χ) with h | h
    · exact h
    · exact absurd h (hno p)
  obtain ⟨ℓ, hℓ⟩ := hloop
  rintro ⟨y, η⟩
  obtain ⟨w⟩ := hconn y
  by_cases hcase : w.holonomy χ = η
  · refine ⟨?_⟩
    have hlift := liftWalk χ w 0
    rw [zero_add, hcase] at hlift
    exact hlift
  · refine ⟨?_⟩
    have hlift := liftWalk χ (ℓ.append w) 0
    rw [zero_add, Walk.holonomy_append, hℓ] at hlift
    have hη : 1 + w.holonomy χ = η := by
      rcases h2 (w.holonomy χ) with h | h <;> rcases h2 η with h' | h'
      · exact absurd (h.trans h'.symm) hcase
      · rw [h, h']
        decide
      · rw [h, h']
        decide
      · exact absurd (h.trans h'.symm) hcase
    rw [hη] at hlift
    exact hlift

/-! ## `thm:upstream-signed-cover-bridge`,
`prop:positive-comparison-trivial-sign` -/

/-- **Theorem `thm:upstream-signed-cover-bridge`**: when the
comparison line is calibrated by the operational relative weights
(`|λ_e| = p⁺_e/p⁻_e = r_e`), its magnitude cochain *is* the affinity
cochain `A = log r`, so `[A_L] = [A] ∈ H¹(G;ℝ)`; the sign part is
the downstream signed-cover class `w₁(L) = [χ_L] ∈ H¹(G;ℤ/2)`.
Both classes are the two coordinates of
`thm:two-invariant-line-classification`. -/
theorem signed_cover_bridge (lam : G.E → ℝˣ) (r : G.E → ℝ)
    (hcal : ∀ e, |(lam e : ℝ)| = r e) :
    lineMagnitude G lam = (fun e => Real.log (r e))
      ∧ H1R.mk G (lineMagnitude G lam)
          = H1R.mk G (fun e => Real.log (r e)) := by
  have h1 : lineMagnitude G lam = fun e => Real.log (r e) := by
    funext e
    rw [lineMagnitude, hcal]
  exact ⟨h1, by rw [h1]⟩

/-- **Proposition `prop:positive-comparison-trivial-sign`**: positive
comparison transports have trivial sign cocycle, hence `w₁ = 0` —
positivity alone cannot produce a nontrivial orientation class. -/
theorem positive_comparison_trivial_sign (lam : G.E → ℝˣ)
    (hpos : ∀ e, 0 < (lam e : ℝ)) :
    lineSign G lam = 0 ∧ H1.mk G (lineSign G lam) = 0 := by
  have h1 : lineSign G lam = 0 := by
    funext e
    change (if 0 < (lam e : ℝ) then (0 : ZMod 2) else 1) = 0
    rw [if_pos (hpos e)]
  exact ⟨h1, by rw [h1, map_zero]⟩

/-! ## `thm:no-real-to-modtwo-reduction` -/

/-- **Theorem `thm:no-real-to-modtwo-reduction`**: every additive
homomorphism `(ℝ,+) → ℤ/2` is zero, so no coefficient homomorphism
can canonically reduce the real affinity class to the orientation
class. -/
theorem addHom_real_zmod2_eq_zero (f : ℝ →+ ZMod 2) : f = 0 := by
  ext x
  have h : f x = f (x / 2) + f (x / 2) := by
    rw [← map_add]
    norm_num
  rw [h, CharTwo.add_self_eq_zero]
  rfl

/-! ## `thm:independence-one-loop`, `cor:three-levels-distinct-v4` -/

/-- On the one-loop graph every real coboundary vanishes. -/
theorem coboundR_bouquet_one :
    LinearMap.range (coboundR (bouquet 1)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro A ⟨u, rfl⟩
  funext e
  have h1 : (bouquet 1).tgt e = (bouquet 1).src e := rfl
  change u ((bouquet 1).tgt e) - u ((bouquet 1).src e) = 0
  rw [h1, sub_self]

theorem H1R_bouquet_mk_eq_zero_iff (A : (bouquet 1).E → ℝ) :
    H1R.mk (bouquet 1) A = 0 ↔ A = 0 := by
  have h1 : H1R.mk (bouquet 1) A = 0
      ↔ A ∈ LinearMap.range (coboundR (bouquet 1)) :=
    Submodule.Quotient.mk_eq_zero _
  rw [h1, coboundR_bouquet_one, Submodule.mem_bot]

theorem H1_bouquet_mk_eq_zero_iff (χ : (bouquet 1).E → ZMod 2) :
    H1.mk (bouquet 1) χ = 0 ↔ χ = 0 := by
  have h1 : H1.mk (bouquet 1) χ = 0
      ↔ χ ∈ LinearMap.range (coboundaryMap (bouquet 1)) :=
    Submodule.Quotient.mk_eq_zero _
  rw [h1, coboundaryMap_bouquet 1, Submodule.mem_bot]

/-- **Theorem `thm:independence-one-loop`**: on the one-loop graph
the four loop holonomies `1, e^a, −1, −e^a` (`a ≠ 0`) realize all
four combinations of vanishing/nonvanishing of the real affinity
class and the orientation class — the two invariants are logically
independent. -/
theorem independence_one_loop (a : ℝ) (ha : a ≠ 0) :
    (H1R.mk (bouquet 1) (lineMagnitude _ fun _ => (1 : ℝˣ)) = 0
      ∧ H1.mk (bouquet 1) (lineSign _ fun _ => (1 : ℝˣ)) = 0)
    ∧ (H1R.mk (bouquet 1) (lineMagnitude _ fun _ => unitOf a 0) ≠ 0
      ∧ H1.mk (bouquet 1) (lineSign _ fun _ => unitOf a 0) = 0)
    ∧ (H1R.mk (bouquet 1) (lineMagnitude _ fun _ => (-1 : ℝˣ)) = 0
      ∧ H1.mk (bouquet 1) (lineSign _ fun _ => (-1 : ℝˣ)) ≠ 0)
    ∧ (H1R.mk (bouquet 1) (lineMagnitude _ fun _ => unitOf a 1) ≠ 0
      ∧ H1.mk (bouquet 1) (lineSign _ fun _ => unitOf a 1) ≠ 0) := by
  have hmag1 : lineMagnitude (bouquet 1) (fun _ => (1 : ℝˣ)) = 0 := by
    funext e
    change Real.log |((1 : ℝˣ) : ℝ)| = 0
    rw [Units.val_one]
    simp
  have hmagneg1 : lineMagnitude (bouquet 1) (fun _ => (-1 : ℝˣ)) = 0 := by
    funext e
    change Real.log |((-1 : ℝˣ) : ℝ)| = 0
    rw [Units.val_neg, Units.val_one]
    simp
  have hsign1 : lineSign (bouquet 1) (fun _ => (1 : ℝˣ)) = 0 := by
    funext e
    change (if 0 < ((1 : ℝˣ) : ℝ) then (0 : ZMod 2) else 1) = 0
    rw [Units.val_one]
    norm_num
  have hsignneg1 : lineSign (bouquet 1) (fun _ => (-1 : ℝˣ)) ≠ 0 := by
    intro h
    have he := congrFun h (0 : Fin 1)
    revert he
    change ¬((if 0 < ((-1 : ℝˣ) : ℝ) then (0 : ZMod 2) else 1) = 0)
    rw [Units.val_neg, Units.val_one]
    norm_num
  have hmaga : ∀ ε : ZMod 2,
      lineMagnitude (bouquet 1) (fun _ => unitOf a ε) ≠ 0 := by
    intro ε h
    have he := congrFun h (0 : Fin 1)
    rw [show lineMagnitude (bouquet 1) (fun _ => unitOf a ε) (0 : Fin 1)
        = Real.log |((unitOf a ε : ℝˣ) : ℝ)| from rfl,
      unitOf_log_abs] at he
    exact ha he
  have hsigna : ∀ ε : ZMod 2,
      lineSign (bouquet 1) (fun _ => unitOf a ε) = fun _ => ε := by
    intro ε
    funext e
    exact unitOf_sign a ε
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hmag1, map_zero]
  · rw [hsign1, map_zero]
  · intro h
    exact hmaga 0 ((H1R_bouquet_mk_eq_zero_iff _).mp h)
  · rw [hsigna 0]
    rw [show (fun _ : (bouquet 1).E => (0 : ZMod 2)) = 0 from rfl,
      map_zero]
  · rw [hmagneg1, map_zero]
  · intro h
    exact hsignneg1 ((H1_bouquet_mk_eq_zero_iff _).mp h)
  · intro h
    exact hmaga 1 ((H1R_bouquet_mk_eq_zero_iff _).mp h)
  · intro h
    have h1 := (H1_bouquet_mk_eq_zero_iff _).mp h
    rw [hsigna 1] at h1
    have he := congrFun h1 (0 : Fin 1)
    exact absurd he (by decide)

/-- **Corollary `cor:three-levels-distinct-v4`**: nonequilibrium
affinity and signed orientation are logically independent — there
are line systems with `[A] ≠ 0, w₁ = 0` and with `[A] = 0, w₁ ≠ 0`
(and the constructions are kinematic: no state-level sheet selection
is implied, cf. `prop:no-canonical-section`). -/
theorem three_levels_distinct :
    (∃ lam : (bouquet 1).E → ℝˣ,
      H1R.mk (bouquet 1) (lineMagnitude _ lam) ≠ 0
        ∧ H1.mk (bouquet 1) (lineSign _ lam) = 0)
    ∧ ∃ lam : (bouquet 1).E → ℝˣ,
      H1R.mk (bouquet 1) (lineMagnitude _ lam) = 0
        ∧ H1.mk (bouquet 1) (lineSign _ lam) ≠ 0 := by
  obtain ⟨_, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩, _⟩ :=
    independence_one_loop 1 one_ne_zero
  exact ⟨⟨_, h2a, h2b⟩, ⟨_, h3a, h3b⟩⟩

/-! ## `prop:no-canonical-section` -/

/-- **Proposition `prop:no-canonical-section`**: if an automorphism
`α` preserves the quotient map and exchanges two distinct members
`h₁ ≠ h₂` of one predictive class (the class containing nothing
else), then no selector invariant under `α` exists. -/
theorem no_invariant_selector {H Q : Type*} (q : H → Q) (α : H → H)
    (_hq : ∀ h, q (α h) = q h) (h₁ h₂ : H) (hne : h₁ ≠ h₂)
    (hswap₁ : α h₁ = h₂) (hswap₂ : α h₂ = h₁)
    (hclass : ∀ h, q h = q h₁ → h = h₁ ∨ h = h₂) :
    ¬∃ s : Q → H, (∀ x, q (s x) = x) ∧ ∀ x, α (s x) = s x := by
  rintro ⟨s, hsec, hinv⟩
  have hmem := hclass (s (q h₁)) (hsec (q h₁))
  rcases hmem with h | h
  · have hfix := hinv (q h₁)
    rw [h, hswap₁] at hfix
    exact hne hfix.symm
  · have hfix := hinv (q h₁)
    rw [h, hswap₂] at hfix
    exact hne hfix

end NCG.Multigraph
