/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite reflected Weil criterion
  (`thm:finite-weil`, `corollary:ordinary-frames-do-not-locate-zeros`,
  arithmetic monograph)

For a finite multiset `Z` invariant (with multiplicity) under the
reflection `ℛρ = 1 − ρ̄`, the reflected Weil form
`𝒲_Z[u] = Σ_{ρ∈Z} u(ρ)·conj(u(ℛρ))` is nonnegative for every
polynomial `u` **iff** every point of `Z` lies on `Re s = 1/2`
(`finite_weil`).  The failure direction produces the interpolating
test polynomial equal to `1` at an off-line point, `−1` at its
reflection, and `0` elsewhere.

`ordinary_frames`: the unreflected energy `Σ_ρ |u(ρ)|²` is
nonnegative for *every* configuration (and positive as soon as `u`
does not vanish on all of `Z`) — horizontal information enters only
through the reflected cross-pairing (interpretive prose).
-/

open Polynomial ComplexConjugate
open scoped ComplexOrder

namespace NCG

/-- The reflection `ℛρ = 1 − ρ̄`. -/
noncomputable def weilReflect (ρ : ℂ) : ℂ := 1 - conj ρ

/-- The reflected Weil form `𝒲_Z[u]`. -/
noncomputable def weilForm (Z : Multiset ℂ) (u : Polynomial ℂ) : ℂ :=
  (Z.map fun ρ => u.eval ρ * conj (u.eval (weilReflect ρ))).sum

/-- The reflection is an involution. -/
lemma weilReflect_involutive (ρ : ℂ) :
    weilReflect (weilReflect ρ) = ρ := by
  rw [weilReflect, weilReflect, map_sub, map_one, Complex.conj_conj]
  ring

/-- A point is fixed by the reflection iff it lies on the critical
line. -/
lemma weilReflect_eq_self_iff (ρ : ℂ) :
    weilReflect ρ = ρ ↔ ρ.re = 1 / 2 := by
  rw [weilReflect, Complex.ext_iff]
  constructor
  · rintro ⟨h1, _⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h1
    linarith
  · intro h
    constructor
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, h]
      norm_num
    · simp [Complex.sub_im, Complex.conj_im]

/-- `thm:finite-weil`: for a reflection-invariant finite multiset,
every point lies on `Re s = 1/2` iff the reflected Weil form is
nonnegative on all polynomials. -/
theorem finite_weil (Z : Multiset ℂ)
    (hZ : Z.map weilReflect = Z) :
    (∀ ρ ∈ Z, ρ.re = 1 / 2) ↔
      ∀ u : Polynomial ℂ, 0 ≤ weilForm Z u := by
  classical
  constructor
  · -- on-line points give a sum of squared moduli
    intro hline u
    rw [weilForm]
    refine Multiset.sum_nonneg ?_
    intro z hz
    obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.mp hz
    rw [(weilReflect_eq_self_iff ρ).mpr (hline ρ hρ),
      Complex.mul_conj]
    exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)
  · -- an off-line point defeats the interpolating test polynomial
    intro hW ρ₀ hρ₀
    by_contra hre
    have hne : weilReflect ρ₀ ≠ ρ₀ := fun h =>
      hre ((weilReflect_eq_self_iff ρ₀).mp h)
    have hmemR : weilReflect ρ₀ ∈ Z := by
      rw [← hZ]
      exact Multiset.mem_map_of_mem _ hρ₀
    -- the interpolating polynomial
    set r : ℂ → ℂ := fun ρ =>
      if ρ = ρ₀ then 1 else if ρ = weilReflect ρ₀ then -1 else 0
      with hr
    set u : Polynomial ℂ := Lagrange.interpolate Z.toFinset id r
      with hu
    have hnode : ∀ ρ ∈ Z.toFinset, u.eval ρ = r ρ := by
      intro ρ hρ
      rw [hu]
      simpa using Lagrange.eval_interpolate_at_node
        (v := id) (r := r) (Set.injOn_id _) hρ
    have hval₀ : u.eval ρ₀ = 1 := by
      rw [hnode ρ₀ (Multiset.mem_toFinset.mpr hρ₀), hr]
      simp
    have hvalR : u.eval (weilReflect ρ₀) = -1 := by
      rw [hnode _ (Multiset.mem_toFinset.mpr hmemR), hr]
      simp [hne]
    -- compute the form
    have hcount : weilForm Z u
        = Z.count ρ₀ • (u.eval ρ₀ * conj (u.eval (weilReflect ρ₀)))
          + Z.count (weilReflect ρ₀)
            • (u.eval (weilReflect ρ₀)
              * conj (u.eval (weilReflect (weilReflect ρ₀)))) := by
      rw [weilForm, Finset.sum_multiset_map_count]
      have hsub : ({ρ₀, weilReflect ρ₀} : Finset ℂ) ⊆ Z.toFinset := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Multiset.mem_toFinset.mpr hρ₀
        · rw [Finset.mem_singleton] at hx
          subst hx
          exact Multiset.mem_toFinset.mpr hmemR
      have hzero : ∀ x ∈ Z.toFinset,
          x ∉ ({ρ₀, weilReflect ρ₀} : Finset ℂ) →
          Multiset.count x Z
            • (u.eval x * conj (u.eval (weilReflect x))) = 0 := by
        intro x hx hxP
        have hx₀ : x ≠ ρ₀ := by
          intro h
          refine hxP ?_
          rw [h]
          exact Finset.mem_insert_self _ _
        have hxR : x ≠ weilReflect ρ₀ := by
          intro h
          refine hxP ?_
          rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have hux : u.eval x = 0 := by
          rw [hnode x hx, hr]
          simp [hx₀, hxR]
        rw [hux, zero_mul, smul_zero]
      rw [← Finset.sum_subset hsub hzero,
        Finset.sum_insert (by simpa using hne.symm),
        Finset.sum_singleton]
    have hcpos : 1 ≤ Z.count ρ₀ := Multiset.count_pos.mpr hρ₀
    have hWval : weilForm Z u
        = -((Z.count ρ₀ : ℂ) + (Z.count (weilReflect ρ₀) : ℂ)) := by
      rw [hcount, weilReflect_involutive, hval₀, hvalR]
      simp only [map_neg, map_one, mul_neg, mul_one, smul_neg,
        nsmul_eq_mul, mul_one]
      ring
    have h0 := hW u
    rw [hWval, Complex.le_def] at h0
    obtain ⟨h1, _⟩ := h0
    simp only [Complex.zero_re, Complex.neg_re, Complex.add_re,
      Complex.natCast_re] at h1
    have : (1 : ℝ) ≤ (Z.count ρ₀ : ℝ) := by exact_mod_cast hcpos
    have hnn : (0 : ℝ) ≤ (Z.count (weilReflect ρ₀) : ℝ) := by
      positivity
    linarith

/-- `corollary:ordinary-frames-do-not-locate-zeros`: the ordinary
(unreflected) energy is nonnegative for every configuration, and
positive as soon as the frame does not annihilate `Z` — so it
carries no horizontal information. -/
theorem ordinary_frames (Z : Multiset ℂ) (u : Polynomial ℂ) :
    0 ≤ ((Z.map fun ρ => u.eval ρ * conj (u.eval ρ)).sum : ℂ)
      ∧ ((∃ ρ ∈ Z, u.eval ρ ≠ 0) →
        0 < ((Z.map fun ρ => u.eval ρ * conj (u.eval ρ)).sum : ℂ)) := by
  classical
  constructor
  · refine Multiset.sum_nonneg ?_
    intro z hz
    obtain ⟨ρ, _, rfl⟩ := Multiset.mem_map.mp hz
    rw [Complex.mul_conj]
    exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)
  · rintro ⟨ρ₁, hρ₁, hval⟩
    have hsplit := Multiset.cons_erase
      (Multiset.mem_map_of_mem
        (fun ρ => u.eval ρ * conj (u.eval ρ)) hρ₁)
    rw [← hsplit, Multiset.sum_cons]
    have h1 : 0 < u.eval ρ₁ * conj (u.eval ρ₁) := by
      rw [Complex.mul_conj]
      rw [Complex.zero_lt_real]
      exact Complex.normSq_pos.mpr hval
    have h2 : 0 ≤ ((Z.map fun ρ => u.eval ρ * conj (u.eval ρ)).erase
        (u.eval ρ₁ * conj (u.eval ρ₁))).sum := by
      refine Multiset.sum_nonneg ?_
      intro z hz
      have hz' := Multiset.mem_of_mem_erase hz
      obtain ⟨ρ, _, rfl⟩ := Multiset.mem_map.mp hz'
      rw [Complex.mul_conj]
      exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)
    calc (0 : ℂ) < u.eval ρ₁ * conj (u.eval ρ₁) := h1
      _ ≤ u.eval ρ₁ * conj (u.eval ρ₁)
          + ((Z.map fun ρ => u.eval ρ * conj (u.eval ρ)).erase
            (u.eval ρ₁ * conj (u.eval ρ₁))).sum := le_add_of_nonneg_right h2

end NCG
