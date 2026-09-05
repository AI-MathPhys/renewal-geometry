/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Frobenius theorem: real division algebras have dimension 1, 2, or 4
  (missing Mathlib machinery; `thm:finite-algebra`, SM_emergence)

Mathlib has no Frobenius classification of finite-dimensional real
division algebras.  This file proves the dimension trichotomy by the
classical argument:

* `exists_quadratic` — every element satisfies a real quadratic
  (minimal polynomials over `ℝ` are linear or quadratic);
* `imaginarySet`/`imaginarySubmodule` — the set
  `V = {x | x² = c·1, c ≤ 0}` is an `ℝ`-subspace (the hard
  additivity step, via the quadratic trace extraction);
* `real_compl_imaginary` — `D = ℝ·1 ⊕ V`;
* `frobenius_dimension` — `dim_ℝ D ∈ {1, 2, 4}`: the imaginary part
  has dimension `0`, `1`, or `3`, by the quaternionic
  anticommutation argument.

This discharges the `DivType` dimension data used by the
Wedderburn–Artin block bookkeeping in `NCG/Matter/FiniteAlgebra.lean`.
-/

namespace NCG

open Polynomial Module

variable {D : Type*} [DivisionRing D] [Algebra ℝ D]
  [FiniteDimensional ℝ D]

omit [FiniteDimensional ℝ D] in
/-- Scalars embed injectively. -/
theorem real_smul_one_eq_zero {c : ℝ} (h : c • (1 : D) = 0) : c = 0 := by
  by_contra hc
  have := congrArg (fun y => c⁻¹ • y) h
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_zero] at this
  exact one_ne_zero this

/-- Every element of a finite-dimensional real division algebra
satisfies a real quadratic. -/
theorem exists_quadratic (x : D) :
    ∃ t n : ℝ, x * x = t • x + n • (1 : D) := by
  have hint : IsIntegral ℝ x := IsIntegral.of_finite ℝ x
  have hirr := minpoly.irreducible hint
  have hdeg : (minpoly ℝ x).natDegree ≤ 2 := hirr.natDegree_le_two
  have hpos : 0 < (minpoly ℝ x).natDegree := minpoly.natDegree_pos hint
  have hmonic := minpoly.monic hint
  have haev := minpoly.aeval ℝ x
  set p := minpoly ℝ x with hp
  have hexp : p = ∑ i ∈ Finset.range 3, (monomial i) (p.coeff i) :=
    p.as_sum_range' 3 (by omega)
  have haev2 : (p.coeff 0) • (1 : D) + (p.coeff 1) • x
      + (p.coeff 2) • (x * x) = 0 := by
    have h := haev
    rw [hexp] at h
    rw [map_sum] at h
    simp only [aeval_monomial] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one] at h
    simp only [pow_zero, pow_one, mul_one] at h
    rw [show x ^ 2 = x * x from sq x] at h
    calc (p.coeff 0) • (1 : D) + (p.coeff 1) • x
        + (p.coeff 2) • (x * x)
        = (algebraMap ℝ D) (p.coeff 0)
          + (algebraMap ℝ D) (p.coeff 1) * x
          + (algebraMap ℝ D) (p.coeff 2) * (x * x) := by
          rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def,
            mul_one]
    _ = 0 := h
  rcases Nat.lt_or_ge (p.natDegree) 2 with h2 | h2
  · -- degree one: `x` is a real scalar
    have hd1 : p.natDegree = 1 := by omega
    have hc1 : p.coeff 1 = 1 := by
      have := hmonic
      rw [Monic, leadingCoeff, hd1] at this
      exact this
    have hc2 : p.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hc1, hc2, one_smul, zero_smul, add_zero] at haev2
    have hx : x = (-(p.coeff 0)) • (1 : D) := by
      linear_combination (norm := module) haev2
    refine ⟨-(p.coeff 0), 0, ?_⟩
    rw [hx, smul_mul_assoc, one_mul, zero_smul, add_zero]
  · -- degree two: the quadratic relation
    have hd2 : p.natDegree = 2 := le_antisymm hdeg h2
    have hc2 : p.coeff 2 = 1 := by
      have := hmonic
      rw [Monic, leadingCoeff, hd2] at this
      exact this
    rw [hc2, one_smul] at haev2
    refine ⟨-(p.coeff 1), -(p.coeff 0), ?_⟩
    linear_combination (norm := module) haev2

/-- The imaginary set: elements squaring to a nonpositive real
scalar. -/
def imaginarySet (D : Type*) [DivisionRing D] [Algebra ℝ D] : Set D :=
  {x | ∃ c : ℝ, c ≤ 0 ∧ x * x = c • (1 : D)}

omit [FiniteDimensional ℝ D] in
theorem imaginary_zero_mem : (0 : D) ∈ imaginarySet D :=
  ⟨0, le_refl 0, by simp⟩

omit [FiniteDimensional ℝ D] in
theorem imaginary_smul_mem {x : D} (hx : x ∈ imaginarySet D) (r : ℝ) :
    r • x ∈ imaginarySet D := by
  obtain ⟨c, hc, hcc⟩ := hx
  refine ⟨r ^ 2 * c, by nlinarith [sq_nonneg r], ?_⟩
  rw [smul_mul_smul_comm, hcc, smul_smul]
  congr 1
  ring

omit [FiniteDimensional ℝ D] in
/-- Imaginary elements lying on the real line vanish. -/
theorem imaginary_not_real {x : D} (hx : x ∈ imaginarySet D)
    {lam : ℝ} (hlam : x = lam • (1 : D)) : x = 0 := by
  obtain ⟨c, hc, hcc⟩ := hx
  rw [hlam, smul_mul_smul_comm, one_mul] at hcc
  have hzero : (lam * lam - c) • (1 : D) = 0 := by
    rw [sub_smul, hcc, sub_self]
  have := real_smul_one_eq_zero hzero
  have hlam0 : lam = 0 := by nlinarith [sq_nonneg lam]
  rw [hlam, hlam0, zero_smul]

omit [FiniteDimensional ℝ D] in
/-- The positive-square dichotomy: `x² = c·1` with `c > 0` forces
`x = ±√c·1`. -/
theorem real_of_sq_pos {x : D} {c : ℝ} (hc : 0 < c)
    (hx : x * x = c • (1 : D)) :
    x = Real.sqrt c • (1 : D) ∨ x = -(Real.sqrt c • (1 : D)) := by
  set s : ℝ := Real.sqrt c with hs
  have hfact : (x - s • (1 : D)) * (x + s • (1 : D)) = 0 := by
    have hxc : x * (s • (1 : D)) = (s • (1 : D)) * x := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    have hss : (s • (1 : D)) * (s • (1 : D)) = c • (1 : D) := by
      rw [smul_mul_smul_comm, one_mul]
      congr 1
      exact Real.mul_self_sqrt hc.le
    rw [mul_add, sub_mul, sub_mul, hxc, hss, hx]
    abel
  rcases mul_eq_zero.mp hfact with h | h
  · left
    rw [sub_eq_zero] at h
    exact h
  · right
    rw [add_eq_zero_iff_eq_neg] at h
    exact h

omit [FiniteDimensional ℝ D] in
/-- From a real-line identity `(2s)·u = d·1` with `s ≠ 0`, an
imaginary `u` vanishes. -/
theorem imaginary_of_real_multiple {u : D} (hu : u ∈ imaginarySet D)
    {s d : ℝ} (hs : s ≠ 0) (h : (2 * s) • u = d • (1 : D)) :
    u = 0 := by
  have h2 := congrArg (fun y => (2 * s)⁻¹ • y) h
  simp only [smul_smul] at h2
  rw [inv_mul_cancel₀ (by positivity : (2 : ℝ) * s ≠ 0), one_smul] at h2
  exact imaginary_not_real hu h2

/-- The hard step: the imaginary set is closed under addition. -/
theorem imaginary_add_mem {u v : D} (hu : u ∈ imaginarySet D)
    (hv : v ∈ imaginarySet D) : u + v ∈ imaginarySet D := by
  classical
  by_cases hu0 : u = 0
  · rw [hu0, zero_add]
    exact hv
  by_cases hv0 : v = 0
  · rw [hv0, add_zero]
    exact hu
  by_cases hdep : ∃ r : ℝ, v = r • u
  · obtain ⟨r, rfl⟩ := hdep
    rw [show u + r • u = (1 + r) • u from by
      rw [add_smul, one_smul]]
    exact imaginary_smul_mem hu (1 + r)
  obtain ⟨cu, hcu, hcuu⟩ := hu
  obtain ⟨cv, hcv, hcvv⟩ := hv
  have indep3 : ∀ a b c : ℝ,
      a • (1 : D) + b • u + c • v = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c habc
    by_cases hcz : c = 0
    · rw [hcz, zero_smul, add_zero] at habc
      by_cases hbz : b = 0
      · rw [hbz, zero_smul, add_zero] at habc
        exact ⟨real_smul_one_eq_zero habc, hbz, hcz⟩
      · exfalso
        have h2 := congrArg (fun y => b⁻¹ • y) habc
        simp only [smul_add, smul_smul, smul_zero] at h2
        rw [inv_mul_cancel₀ hbz, one_smul] at h2
        have huR : u = (-(b⁻¹ * a)) • (1 : D) := by
          linear_combination (norm := module) h2
        exact hu0 (imaginary_not_real ⟨cu, hcu, hcuu⟩ huR)
    · exfalso
      have h2 := congrArg (fun y => c⁻¹ • y) habc
      simp only [smul_add, smul_smul, smul_zero] at h2
      rw [inv_mul_cancel₀ hcz, one_smul] at h2
      set al : ℝ := -(c⁻¹ * a) with hal
      set be : ℝ := -(c⁻¹ * b) with hbe
      have hvR : v = al • (1 : D) + be • u := by
        rw [hal, hbe]
        linear_combination (norm := module) h2
      have hsq : cv • (1 : D)
          = (al ^ 2 + be ^ 2 * cu) • (1 : D)
            + (2 * (al * be)) • u := by
        have hexp : (al • (1 : D) + be • u) * (al • (1 : D) + be • u)
            = (al * al) • (1 : D) + (2 * (al * be)) • u
              + (be * be) • (u * u) := by
          rw [mul_add, add_mul, add_mul, smul_mul_smul_comm,
            smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
            one_mul, one_mul, mul_one]
          module
        have hstep := hcvv
        rw [hvR, hexp, hcuu, smul_smul] at hstep
        linear_combination (norm := module) hstep.symm
      by_cases hab : al * be = 0
      · rcases mul_eq_zero.mp hab with h0 | h0
        · rw [h0, zero_smul, zero_add] at hvR
          exact hdep ⟨be, hvR⟩
        · rw [h0, zero_smul, add_zero] at hvR
          exact hv0 (imaginary_not_real ⟨cv, hcv, hcvv⟩ hvR)
      · have hlin : (2 * (al * be)) • u
            = (cv - (al ^ 2 + be ^ 2 * cu)) • (1 : D) := by
          linear_combination (norm := module) -hsq
        exact hu0 (imaginary_of_real_multiple ⟨cu, hcu, hcuu⟩ hab hlin)
  obtain ⟨t1, n1, h1⟩ := exists_quadratic (u + v)
  obtain ⟨t2, n2, h2⟩ := exists_quadratic (u - v)
  have hpar : (u + v) * (u + v) + (u - v) * (u - v)
      = (2 * cu + 2 * cv) • (1 : D) := by
    have hring : (u + v) * (u + v) + (u - v) * (u - v)
        = u * u + u * u + (v * v + v * v) := by
      noncomm_ring
    rw [hring, hcuu, hcvv]
    module
  have hcomb : (n1 + n2 - (2 * cu + 2 * cv)) • (1 : D)
      + (t1 + t2) • u + (t1 - t2) • v = 0 := by
    linear_combination (norm := module) hpar - h1 - h2
  obtain ⟨hA, hB, hC⟩ := indep3 _ _ _ hcomb
  have ht1 : t1 = 0 := by linarith
  rw [ht1, zero_smul, zero_add] at h1
  rcases le_or_gt n1 0 with hn | hn
  · exact ⟨n1, hn, h1⟩
  · exfalso
    have hsqrt : Real.sqrt n1 ≠ 0 :=
      (Real.sqrt_pos.mpr hn).ne'
    have key : ∀ s : ℝ, s ≠ 0 → u + v = s • (1 : D) → False := by
      intro s hs hx
      have hveq : v = s • (1 : D) - u := by
        linear_combination (norm := module) hx
      have hexp : (s • (1 : D) - u) * (s • (1 : D) - u)
          = (s * s) • (1 : D) - (2 * s) • u + u * u := by
        rw [sub_mul, mul_sub, mul_sub, smul_mul_smul_comm, one_mul,
          mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
        module
      have hstep := hcvv
      rw [hveq, hexp, hcuu] at hstep
      have hlin : (2 * s) • u
          = (s * s + cu - cv) • (1 : D) := by
        linear_combination (norm := module) -hstep
      exact hu0 (imaginary_of_real_multiple ⟨cu, hcu, hcuu⟩ hs hlin)
    rcases real_of_sq_pos hn h1 with hx | hx
    · exact key (Real.sqrt n1) hsqrt hx
    · exact key (-(Real.sqrt n1)) (neg_ne_zero.mpr hsqrt)
        (by rw [neg_smul]; exact hx)

/-- The imaginary subspace of a finite-dimensional real division
algebra. -/
def imaginarySubmodule (D : Type*) [DivisionRing D] [Algebra ℝ D]
    [FiniteDimensional ℝ D] : Submodule ℝ D where
  carrier := imaginarySet D
  zero_mem' := imaginary_zero_mem
  add_mem' := fun hu hv => imaginary_add_mem hu hv
  smul_mem' := fun r _x hx => imaginary_smul_mem hx r

/-- Every element splits into a real part and an imaginary part. -/
theorem exists_real_imaginary_decomp (x : D) :
    ∃ (a : ℝ) (w : D), w ∈ imaginarySet D ∧ x = a • (1 : D) + w := by
  obtain ⟨t, n, hq⟩ := exists_quadratic x
  set w : D := x - (t / 2) • (1 : D) with hw
  have hwsq : w * w = (n + t ^ 2 / 4) • (1 : D) := by
    have hexp : (x - (t / 2) • (1 : D)) * (x - (t / 2) • (1 : D))
        = x * x - t • x + (t ^ 2 / 4) • (1 : D) := by
      rw [sub_mul, mul_sub, mul_sub, mul_smul_comm, smul_mul_assoc,
        mul_one, one_mul, smul_mul_smul_comm, one_mul]
      module
    rw [hw, hexp, hq]
    module
  rcases le_or_gt (n + t ^ 2 / 4) 0 with hc | hc
  · refine ⟨t / 2, w, ⟨n + t ^ 2 / 4, hc, hwsq⟩, ?_⟩
    rw [hw]
    module
  · rcases real_of_sq_pos hc hwsq with hx | hx
    · refine ⟨t / 2 + Real.sqrt (n + t ^ 2 / 4), 0,
        imaginary_zero_mem, ?_⟩
      rw [hw] at hx
      rw [add_smul]
      linear_combination (norm := module) hx
    · refine ⟨t / 2 - Real.sqrt (n + t ^ 2 / 4), 0,
        imaginary_zero_mem, ?_⟩
      rw [hw] at hx
      rw [sub_smul]
      linear_combination (norm := module) hx

/-- The real line and the imaginary subspace are complementary, so
`dim D = 1 + dim V`. -/
theorem finrank_eq_one_add_imaginary :
    finrank ℝ D = 1 + finrank ℝ (imaginarySubmodule D) := by
  classical
  have hdisj : Disjoint (ℝ ∙ (1 : D)) (imaginarySubmodule D) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hxV
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hx1
    exact imaginary_not_real hxV (by rw [← hlam])
  have hsup : (ℝ ∙ (1 : D)) ⊔ imaginarySubmodule D = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, w, hwV, hxaw⟩ := exists_real_imaginary_decomp x
    rw [hxaw]
    exact Submodule.add_mem_sup
      (Submodule.mem_span_singleton.mpr ⟨a, rfl⟩) hwV
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq
    (ℝ ∙ (1 : D)) (imaginarySubmodule D)
  rw [hsup, hdisj.eq_bot, finrank_top, finrank_bot, add_zero,
    finrank_span_singleton (one_ne_zero : (1 : D) ≠ 0)] at hkey
  exact hkey

/-- Anticommutators of imaginary elements are real. -/
theorem imaginary_anticommutator {u w : D} (hu : u ∈ imaginarySet D)
    (hw : w ∈ imaginarySet D) :
    ∃ beta : ℝ, u * w + w * u = beta • (1 : D) := by
  obtain ⟨cs, _, hcs⟩ := imaginary_add_mem hu hw
  obtain ⟨cu, _, hcu⟩ := hu
  obtain ⟨cw, _, hcw⟩ := hw
  refine ⟨cs - cu - cw, ?_⟩
  have hexp : (u + w) * (u + w) = u * u + (u * w + w * u) + w * w := by
    noncomm_ring
  have h2 : cs • (1 : D)
      = cu • (1 : D) + (u * w + w * u) + cw • (1 : D) := by
    rw [← hcs, hexp, hcu, hcw]
  linear_combination (norm := module) -h2

omit [FiniteDimensional ℝ D] in
/-- Normalization: nonzero imaginary elements rescale to square
`-1`. -/
theorem imaginary_normalize {u : D} (hu : u ∈ imaginarySet D)
    (hu0 : u ≠ 0) :
    ∃ e : D, e ∈ imaginarySet D ∧ e * e = (-1 : ℝ) • (1 : D)
      ∧ ∃ r : ℝ, r ≠ 0 ∧ e = r • u := by
  obtain ⟨c, hc, hcc⟩ := hu
  have hcneg : c < 0 := by
    rcases lt_or_eq_of_le hc with h | h
    · exact h
    · exfalso
      rw [h, zero_smul] at hcc
      rcases mul_eq_zero.mp hcc with h0 | h0 <;> exact hu0 h0
  have hsqrt_pos : 0 < Real.sqrt (-c) := Real.sqrt_pos.mpr (by linarith)
  set r : ℝ := (Real.sqrt (-c))⁻¹ with hr
  have hrne : r ≠ 0 := inv_ne_zero hsqrt_pos.ne'
  refine ⟨r • u, imaginary_smul_mem ⟨c, hc, hcc⟩ r, ?_, r, hrne, rfl⟩
  rw [smul_mul_smul_comm, hcc, smul_smul]
  congr 1
  have hss : Real.sqrt (-c) * Real.sqrt (-c) = -c :=
    Real.mul_self_sqrt (by linarith)
  rw [hr, ← mul_inv, hss]
  field_simp [hcneg.ne]

/-- `dim V ≥ 2` forces the quaternionic triple and `dim V = 3`. -/
theorem imaginary_finrank_eq_three_of_two_le
    (hm2 : 2 ≤ finrank ℝ (imaginarySubmodule D)) :
    finrank ℝ (imaginarySubmodule D) = 3 := by
  classical
  set V := imaginarySubmodule D with hVdef
  have hVne : V ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hm2
    omega
  obtain ⟨u, huV, hu0⟩ := V.ne_bot_iff.mp hVne
  obtain ⟨e, heV, he2, r0, hr0, hre⟩ :=
    imaginary_normalize (huV : u ∈ imaginarySet D) hu0
  have he0 : e ≠ 0 := by
    rw [hre]
    exact smul_ne_zero hr0 hu0
  have hnotle : ¬(V ≤ ℝ ∙ e) := by
    intro hle
    have hmono := Submodule.finrank_mono hle
    rw [finrank_span_singleton he0] at hmono
    omega
  obtain ⟨w, hwV, hwns⟩ := SetLike.not_le_iff_exists.mp hnotle
  obtain ⟨be1, hbe1⟩ := imaginary_anticommutator heV
    (hwV : w ∈ imaginarySet D)
  set f0 : D := w + (be1 / 2) • e with hf0
  have hf0V : f0 ∈ imaginarySet D :=
    imaginary_add_mem hwV (imaginary_smul_mem heV (be1 / 2))
  have hf00 : f0 ≠ 0 := by
    intro h0
    apply hwns
    rw [hf0] at h0
    rw [Submodule.mem_span_singleton]
    refine ⟨-(be1 / 2), ?_⟩
    linear_combination (norm := module) -h0
  have hanti0 : e * f0 + f0 * e = 0 := by
    rw [hf0, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    have he2' : (be1 / 2) • (e * e) + (be1 / 2) • (e * e)
        = (-be1) • (1 : D) := by
      rw [he2]
      module
    linear_combination (norm := module) hbe1 + he2'
  obtain ⟨f, hfV, hf2, rf, hrf, hrfe⟩ := imaginary_normalize hf0V hf00
  have hantief : e * f + f * e = 0 := by
    rw [hrfe, mul_smul_comm, smul_mul_assoc, ← smul_add, hanti0,
      smul_zero]
  have hfe : f * e = -(e * f) := by
    linear_combination (norm := module) hantief
  set k : D := e * f with hk
  have hk2 : k * k = (-1 : ℝ) • (1 : D) := by
    have hassoc : k * k = e * (f * e) * f := by
      rw [hk]
      noncomm_ring
    rw [hassoc, hfe]
    have hneg : e * -(e * f) * f = -(e * e * (f * f)) := by
      noncomm_ring
    rw [hneg, he2, hf2, smul_mul_smul_comm, one_mul]
    module
  have hkV : k ∈ imaginarySet D := ⟨-1, by norm_num, hk2⟩
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hk2
    have := real_smul_one_eq_zero hk2.symm
    norm_num at this
  have hek : e * k = -f := by
    rw [hk, ← mul_assoc, he2, smul_mul_assoc, one_mul, neg_smul,
      one_smul]
  have hke : k * e = f := by
    rw [hk, mul_assoc, hfe, mul_neg, ← mul_assoc, he2,
      smul_mul_assoc, one_mul, neg_smul, one_smul, neg_neg]
  have hfk : f * k = e := by
    rw [hk, ← mul_assoc, hfe, neg_mul, mul_assoc, hf2,
      mul_smul_comm, mul_one, neg_smul, one_smul, neg_neg]
  have hkf : k * f = -e := by
    rw [hk, mul_assoc, hf2, mul_smul_comm, mul_one, neg_smul,
      one_smul]
  have hindep : ∀ a b c : ℝ, a • e + b • f + c • k = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c habc
    have hpe := congrArg (fun y => e * y + y * e) habc
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      mul_zero, zero_mul, add_zero] at hpe
    rw [he2, hek, hke, hfe] at hpe
    have ha : (-(2 * a)) • (1 : D) = 0 := by
      linear_combination (norm := module) hpe
    have ha0 : a = 0 := by
      have := real_smul_one_eq_zero ha
      linarith
    have hpf := congrArg (fun y => f * y + y * f) habc
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      mul_zero, zero_mul, add_zero] at hpf
    rw [hf2, hfk, hkf, hfe] at hpf
    have hb : (-(2 * b)) • (1 : D) = 0 := by
      linear_combination (norm := module) hpf
    have hb0 : b = 0 := by
      have := real_smul_one_eq_zero hb
      linarith
    rw [ha0, hb0, zero_smul, zero_smul, zero_add, zero_add] at habc
    rcases smul_eq_zero.mp habc with h | h
    · exact ⟨ha0, hb0, h⟩
    · exact absurd h hk0
  -- upper bound: every imaginary element lies in the quaternion span
  have hspan_le : V ≤ Submodule.span ℝ {e, f, k} := by
    intro x hxV
    obtain ⟨be2, hbe2⟩ := imaginary_anticommutator
      (hxV : x ∈ imaginarySet D) heV
    obtain ⟨bf2, hbf2⟩ := imaginary_anticommutator
      (hxV : x ∈ imaginarySet D) hfV
    set W : D := x + (be2 / 2) • e + (bf2 / 2) • f with hW
    have hWe : W * e + e * W = 0 := by
      rw [hW]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      rw [he2, hfe]
      linear_combination (norm := module) hbe2
    have hWf : W * f + f * W = 0 := by
      rw [hW]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      rw [hf2, hfe]
      linear_combination (norm := module) hbf2
    have hWk : W * k = k * W := by
      have h1 : W * e = -(e * W) := by
        linear_combination (norm := module) hWe
      have h2 : W * f = -(f * W) := by
        linear_combination (norm := module) hWf
      calc W * k = (W * e) * f := by
            rw [hk]
            noncomm_ring
      _ = -(e * W) * f := by rw [h1]
      _ = -(e * (W * f)) := by noncomm_ring
      _ = -(e * -(f * W)) := by rw [h2]
      _ = (e * f) * W := by noncomm_ring
      _ = k * W := by rw [hk]
    have hWV : W ∈ imaginarySet D := by
      rw [hW]
      exact imaginary_add_mem
        (imaginary_add_mem hxV (imaginary_smul_mem heV (be2 / 2)))
        (imaginary_smul_mem hfV (bf2 / 2))
    obtain ⟨gam, hgam⟩ := imaginary_anticommutator hWV hkV
    rw [← hWk] at hgam
    have hhalf := congrArg (fun y => (2 : ℝ)⁻¹ • y) hgam
    simp only [smul_add, smul_smul] at hhalf
    have hWk2 : W * k = (gam / 2) • (1 : D) := by
      linear_combination (norm := module) hhalf
    have h3 := congrArg (fun y => y * k) hWk2
    simp only [smul_mul_assoc, one_mul] at h3
    rw [mul_assoc, hk2, mul_smul_comm, mul_one] at h3
    have hWval : W = (-(gam / 2)) • k := by
      linear_combination (norm := module) -h3
    have hx : x = (-(be2 / 2)) • e + (-(bf2 / 2)) • f
        + (-(gam / 2)) • k := by
      linear_combination (norm := module) hWval - hW
    rw [hx]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (by simp))
  -- lower bound: the quaternion span sits inside `V` with rank 3
  have hLI : LinearIndependent ℝ ![e, f, k] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    obtain ⟨h0, h1, h2⟩ := hindep (g 0) (g 1) (g 2) hg
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hrange : Set.range ![e, f, k] = {e, f, k} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hspan_eq : finrank ℝ
      (Submodule.span ℝ ({e, f, k} : Set D)) = 3 := by
    rw [← hrange, finrank_span_eq_card hLI]
    simp
  have hle_span : Submodule.span ℝ ({e, f, k} : Set D) ≤ V := by
    rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact heV
    · exact hfV
    · exact hkV
  have hub := Submodule.finrank_mono hspan_le
  have hlb := Submodule.finrank_mono hle_span
  rw [hspan_eq] at hub hlb
  omega

/-- **The Frobenius theorem** (dimension form): a finite-dimensional
real division algebra has dimension 1, 2, or 4. -/
theorem frobenius_dimension :
    finrank ℝ D = 1 ∨ finrank ℝ D = 2 ∨ finrank ℝ D = 4 := by
  have hdecomp := finrank_eq_one_add_imaginary (D := D)
  by_cases h0 : finrank ℝ (imaginarySubmodule D) = 0
  · left
    omega
  by_cases h1 : finrank ℝ (imaginarySubmodule D) = 1
  · right
    left
    omega
  · right
    right
    have h3 := imaginary_finrank_eq_three_of_two_le (D := D) (by omega)
    omega

end NCG
