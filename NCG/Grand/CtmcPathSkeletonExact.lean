/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite continuous-time path skeletons and their densities

Step (P1) of the path-space programme for `thm:accepted-path-likelihood`:
a finite-horizon trajectory of a finite continuous-time Markov model is
recorded by its **skeleton** — the initial state and the time-ordered
jump record.  The model `(p, L)` weights a skeleton by the density

`p(x₀) · Π_jumps L(x_{i-1}, x_i) · exp(− Σ_u Θ_u λ_L(u))`,

and the **boxed likelihood formula** is the pointwise identity

`log(dP/dQ) = log(p/q)(x₀) + Σ_{uv} N_{uv} log(L/M)(u,v)
             − Σ_u Θ_u (λ_L(u) − λ_M(u))`.

* `Skeleton`, `transitions`, `jumpCount`, `occupation`: the trajectory
  statistics;
* `pathDensity`: the model weight;
* `log_density_ratio`: **the boxed likelihood formula**.
-/

open Finset

namespace NCG
namespace Ctmc

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### Skeletons and statistics -/

/-- A finite-horizon path skeleton: the initial state and the
time-ordered jump record `(jump time, arrival state)`. -/
structure Skeleton (S : Type*) where
  init : S
  jumps : List (ℝ × S)

/-- The visited states, in order. -/
def states (w : Skeleton S) : List S :=
  w.init :: w.jumps.map Prod.snd

/-- The directed transitions `(departure, arrival)` along the skeleton. -/
def transitions (w : Skeleton S) : List (S × S) :=
  (states w).zip (w.jumps.map Prod.snd)

/-- The directed jump count `N_{uv}`. -/
def jumpCount (w : Skeleton S) (e : S × S) : ℕ :=
  (transitions w).count e

/-- The holding intervals: differences of consecutive jump times, with
the horizon appended. -/
def holdTimes (w : Skeleton S) (T : ℝ) : List ℝ :=
  List.zipWith (fun a b => a - b)
    ((w.jumps.map Prod.fst) ++ [T]) (0 :: w.jumps.map Prod.fst)

/-- The occupation time `Θ_u`. -/
def occupation (w : Skeleton S) (T : ℝ) (u : S) : ℝ :=
  (((states w).zip (holdTimes w T)).map
    (fun q => if q.1 = u then q.2 else 0)).sum

/-- The exit rate `λ_L(u) = Σ_{v ≠ u} L u v`. -/
def exitRate (L : Matrix S S ℝ) (u : S) : ℝ :=
  ∑ v, if v = u then 0 else L u v

/-! ### The path density -/

/-- The model weight of a skeleton: initial density, jump rates, and
exponential holding factors. -/
noncomputable def pathDensity (p : S → ℝ) (L : Matrix S S ℝ) (T : ℝ)
    (w : Skeleton S) : ℝ :=
  p w.init * ((transitions w).map (fun e => L e.1 e.2)).prod *
    Real.exp (- ∑ u, occupation w T u * exitRate L u)

/-! ### List counting identities -/

theorem log_list_prod (l : List ℝ) (h : ∀ x ∈ l, 0 < x) :
    Real.log l.prod = (l.map Real.log).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : 0 < a := h a (List.mem_cons_self)
      have ht : ∀ x ∈ t, 0 < x := fun x hx => h x (List.mem_cons_of_mem a hx)
      have htp : 0 < t.prod := List.prod_pos ht
      rw [List.prod_cons, Real.log_mul ha.ne' htp.ne', List.map_cons,
        List.sum_cons, ih ht]

/-- Summing a mapped list by counting values. -/
theorem list_map_sum_count {α : Type*} [Fintype α] [DecidableEq α]
    [BEq α] [LawfulBEq α] (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ a : α, (l.count a : ℝ) * f a := by
  induction l with
  | nil => simp
  | cons x t ih =>
      rw [List.map_cons, List.sum_cons, ih]
      have hstep : ∀ a : α, ((x :: t).count a : ℝ) * f a =
          (t.count a : ℝ) * f a + (if a = x then f a else 0) := by
        intro a
        rw [List.count_cons]
        rcases eq_or_ne a x with rfl | hax
        · have hb : (a == a) = true := beq_self_eq_true a
          rw [hb, if_pos rfl, if_pos rfl]
          push_cast
          ring
        · have hb : (x == a) = false :=
            beq_eq_false_iff_ne.mpr (Ne.symm hax)
          rw [hb, if_neg Bool.false_ne_true, if_neg hax]
          push_cast
          ring
      rw [Finset.sum_congr rfl fun a _ => hstep a,
        Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ x f]
      simp [add_comm]

/-- The transition sum grouped by directed pairs. -/
theorem transitions_map_sum (w : Skeleton S) (f : S × S → ℝ) :
    ((transitions w).map f).sum =
      ∑ e : S × S, (jumpCount w e : ℝ) * f e := by
  simp only [jumpCount]
  exact list_map_sum_count (transitions w) f

omit [Fintype S] [DecidableEq S] in
theorem transitions_prod_pos (w : Skeleton S) {L : Matrix S S ℝ}
    (hL : ∀ e ∈ transitions w, 0 < L e.1 e.2) :
    0 < ((transitions w).map (fun e => L e.1 e.2)).prod := by
  refine List.prod_pos fun x hx => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact hL e he

/-! ### The boxed likelihood formula -/

set_option maxHeartbeats 1600000 in -- likelihood bookkeeping
/-- **The boxed likelihood formula** of
`thm:accepted-path-likelihood`: the pointwise log-density ratio of two
absolutely continuous finite Markov models is a function of the initial
state, the directed jump counts, and the occupation times. -/
theorem log_density_ratio (p q : S → ℝ) (L M : Matrix S S ℝ) (T : ℝ)
    (w : Skeleton S) (hp : 0 < p w.init) (hq : 0 < q w.init)
    (hL : ∀ e ∈ transitions w, 0 < L e.1 e.2)
    (hM : ∀ e ∈ transitions w, 0 < M e.1 e.2) :
    Real.log (pathDensity p L T w / pathDensity q M T w) =
      Real.log (p w.init / q w.init) +
      (∑ e : S × S, (jumpCount w e : ℝ) *
        Real.log (L e.1 e.2 / M e.1 e.2)) -
      ∑ u, occupation w T u * (exitRate L u - exitRate M u) := by
  have hBL := transitions_prod_pos w hL
  have hBM := transitions_prod_pos w hM
  set BL := ((transitions w).map (fun e => L e.1 e.2)).prod with hBLdef
  set BM := ((transitions w).map (fun e => M e.1 e.2)).prod with hBMdef
  set CL := ∑ u, occupation w T u * exitRate L u with hCL
  set CM := ∑ u, occupation w T u * exitRate M u with hCM
  have hqne : q w.init ≠ 0 := hq.ne'
  have hBMne : BM ≠ 0 := hBM.ne'
  have hden : pathDensity p L T w / pathDensity q M T w =
      (p w.init / q w.init) * (BL / BM) * Real.exp (CM - CL) := by
    calc pathDensity p L T w / pathDensity q M T w
        = (p w.init / q w.init) * (BL / BM) *
          (Real.exp (-CL) / Real.exp (-CM)) := by
          unfold pathDensity
          rw [div_mul_div_comm, div_mul_div_comm]
          ring
      _ = (p w.init / q w.init) * (BL / BM) * Real.exp (CM - CL) := by
          rw [← Real.exp_sub, show -CL - -CM = CM - CL from by ring]
  rw [hden]
  have hpq : (0 : ℝ) < p w.init / q w.init := div_pos hp hq
  have hB : (0 : ℝ) < BL / BM := div_pos hBL hBM
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul hpq.ne' hB.ne', Real.log_exp]
  have hlogB : Real.log (BL / BM) =
      ∑ e : S × S, (jumpCount w e : ℝ) *
        Real.log (L e.1 e.2 / M e.1 e.2) := by
    rw [Real.log_div hBL.ne' hBM.ne', hBLdef, hBMdef]
    rw [log_list_prod _ (fun x hx => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact hL e he),
      log_list_prod _ (fun x hx => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        exact hM e he)]
    rw [List.map_map, List.map_map]
    rw [transitions_map_sum w (Real.log ∘ fun e => L e.1 e.2),
      transitions_map_sum w (Real.log ∘ fun e => M e.1 e.2)]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rcases Nat.eq_zero_or_pos (jumpCount w e) with h0 | hpos
    · rw [h0]
      simp
    · have he : e ∈ transitions w := List.count_pos_iff.mp hpos
      rw [Function.comp_apply, Function.comp_apply,
        Real.log_div (hL e he).ne' (hM e he).ne']
      ring
  rw [hlogB]
  have hC : CM - CL =
      - ∑ u, occupation w T u * (exitRate L u - exitRate M u) := by
    have h1 : ∑ u, occupation w T u * (exitRate L u - exitRate M u) =
        CL - CM := by
      rw [hCL, hCM, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [h1]
    ring
  rw [hC]
  ring

end Ctmc
end NCG
