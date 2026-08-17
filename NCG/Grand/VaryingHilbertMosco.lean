/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Mosco convergence on varying Hilbert spaces

This file supplies the common-carrier language missing from Mathlib for the analytic limit
statements in the Gran-Tensor manuscript.  A family of Hilbert spaces is compared with a limit
space by linear isometric embeddings into one ambient Hilbert space.  Strong convergence is
ordinary norm convergence after embedding; weak convergence is convergence of all ambient
inner products.

The definition `MoscoConverges` records the genuine weak-liminf and strong-recovery clauses for
extended nonnegative energies.  `StrongOperatorConverges` records the corresponding varying-space
strong convergence of resolvents, semigroups, or spectral multipliers.  The elementary calculus
proved here makes these notions usable without repeatedly unfolding dependent sequences.
-/

open scoped ENNReal

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]

/-- Isometric identifications of varying Hilbert spaces with subspaces of one common carrier. -/
structure System where

  /-- The stage-`n` isometric embedding into the common Hilbert carrier. -/
  embedding : ∀ n, Hn n →ₗᵢ[K] H

/-- A fixed Hilbert space viewed as a constant varying-space system. -/
def constantSystem (K : Type u) [RCLike K] (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace K H] :
    System (K := K) (H := H) (Hn := fun _ ↦ H) where
  embedding _ := LinearIsometry.id


variable (J : System (K := K) (H := H) (Hn := Hn))

namespace System
/-- Restrict a varying Hilbert system along a sequence of stage indices. -/
def reindex (φ : ℕ → ℕ) : System (K := K) (H := H) (Hn := fun n ↦ Hn (φ n)) where
  embedding n := J.embedding (φ n)

@[simp]
theorem reindex_embedding (φ : ℕ → ℕ) (n : ℕ) (x : Hn (φ n)) :
    (J.reindex φ).embedding n x = J.embedding (φ n) x :=
  rfl


/-- A dependent sequence converges strongly when its embedded representatives converge in norm
in the common carrier. -/
def StronglyConverges (x : ∀ n, Hn n) (xlim : H) : Prop :=
  Tendsto (fun n ↦ J.embedding n (x n)) atTop (𝓝 xlim)

/-- A dependent sequence converges weakly when every ambient inner product converges. -/
def WeaklyConverges (x : ∀ n, Hn n) (xlim : H) : Prop :=
  ∀ y : H,
    Tendsto (fun n ↦ inner K (J.embedding n (x n)) y) atTop
      (𝓝 (inner K xlim y))

@[simp]
theorem constantSystem_stronglyConverges_iff (x : ℕ → H) (xlim : H) :
    (constantSystem K H).StronglyConverges x xlim ↔
      Tendsto x atTop (𝓝 xlim) := by
  rfl

@[simp]
theorem constantSystem_weaklyConverges_iff (x : ℕ → H) (xlim : H) :
    (constantSystem K H).WeaklyConverges x xlim ↔
      ∀ y : H, Tendsto (fun n ↦ inner K (x n) y) atTop
        (𝓝 (inner K xlim y)) := by
  rfl

/-- Strong convergence on the common carrier implies weak convergence. -/
theorem StronglyConverges.weak {x : ∀ n, Hn n} {xlim : H}
    (hx : J.StronglyConverges x xlim) : J.WeaklyConverges x xlim := by
  intro y
  exact hx.inner tendsto_const_nhds

/-- Strong convergence passes to every cofinal reindexing. -/
theorem StronglyConverges.reindex {x : ∀ n, Hn n} {xlim : H}
    (hx : J.StronglyConverges x xlim) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) :
    (J.reindex φ).StronglyConverges (fun n ↦ x (φ n)) xlim := by
  exact hx.comp hφ

/-- Weak convergence passes to every cofinal reindexing. -/
theorem WeaklyConverges.reindex {x : ∀ n, Hn n} {xlim : H}
    (hx : J.WeaklyConverges x xlim) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) :
    (J.reindex φ).WeaklyConverges (fun n ↦ x (φ n)) xlim := by
  intro y
  exact (hx y).comp hφ


/-- Strong limits in the common carrier are unique. -/
theorem stronglyConverges_unique {x : ∀ n, Hn n} {a b : H}
    (ha : J.StronglyConverges x a) (hb : J.StronglyConverges x b) : a = b :=
  tendsto_nhds_unique ha hb

/-- Weak limits in the common carrier are unique. -/
theorem weaklyConverges_unique {x : ∀ n, Hn n} {a b : H}
    (ha : J.WeaklyConverges x a) (hb : J.WeaklyConverges x b) : a = b := by
  apply ext_inner_right K
  intro y
  exact tendsto_nhds_unique (ha y) (hb y)

/-- The zero sequence converges strongly to zero. -/
theorem stronglyConverges_zero :
    J.StronglyConverges (fun _ ↦ 0) 0 := by
  simp [StronglyConverges]

/-- Strong convergence is closed under addition of dependent sequences. -/
theorem StronglyConverges.add {x y : ∀ n, Hn n} {a b : H}
    (hx : J.StronglyConverges x a) (hy : J.StronglyConverges y b) :
    J.StronglyConverges (fun n ↦ x n + y n) (a + b) := by
  simpa only [StronglyConverges, map_add] using Filter.Tendsto.add hx hy
/-- Strong convergence is closed under scalar multiplication. -/
theorem StronglyConverges.smul (c : K) {x : ∀ n, Hn n} {a : H}
    (hx : J.StronglyConverges x a) :
    J.StronglyConverges (fun n ↦ c • x n) (c • a) := by
  simpa only [StronglyConverges, map_smul] using hx.const_smul c

/-- Weak convergence is closed under addition of dependent sequences. -/
theorem WeaklyConverges.add {x y : ∀ n, Hn n} {a b : H}
    (hx : J.WeaklyConverges x a) (hy : J.WeaklyConverges y b) :
    J.WeaklyConverges (fun n ↦ x n + y n) (a + b) := by
  intro z
  simpa only [map_add, inner_add_left] using (hx z).add (hy z)

/-- The stage images are asymptotically dense when every limit vector has a strongly convergent
dependent approximation. -/
def IsAsymptoticallyDense : Prop :=
  ∀ x : H, ∃ xn : ∀ n, Hn n, J.StronglyConverges xn x

/-- Genuine Mosco convergence for extended nonnegative forms on varying Hilbert spaces. -/
structure MoscoConverges (q : (n : ℕ) → Hn n → ℝ≥0∞) (qlim : H → ℝ≥0∞) : Prop where
  /-- Weakly convergent sequences satisfy the Mosco lower bound. -/
  liminf_le : ∀ (x : ∀ n, Hn n) (xlim : H), J.WeaklyConverges x xlim →
    qlim xlim ≤ liminf (fun n ↦ q n (x n)) atTop
  /-- Every limit vector admits a strongly convergent recovery sequence. -/
  recovery : ∀ xlim : H, ∃ x : ∀ n, Hn n,
    J.StronglyConverges x xlim ∧
      limsup (fun n ↦ q n (x n)) atTop ≤ qlim xlim

namespace MoscoConverges

variable {J}
variable {q : (n : ℕ) → Hn n → ℝ≥0∞} {qlim : H → ℝ≥0∞}

/-- Mosco convergence itself supplies asymptotic density of the comparison system. -/
theorem asymptoticallyDense (hq : J.MoscoConverges q qlim) :
    J.IsAsymptoticallyDense := by
  intro xlim
  obtain ⟨x, hx, -⟩ := hq.recovery xlim
  exact ⟨x, hx⟩

/-- A recovery sequence also converges weakly. -/
theorem exists_weakRecovery (hq : J.MoscoConverges q qlim) (xlim : H) :
    ∃ x : ∀ n, Hn n,
      J.WeaklyConverges x xlim ∧
        limsup (fun n ↦ q n (x n)) atTop ≤ qlim xlim := by
  obtain ⟨x, hx, henergy⟩ := hq.recovery xlim
  exact ⟨x, hx.weak, henergy⟩

end MoscoConverges

/-- Strong convergence of operator families between varying Hilbert systems.  This is the
notion used for resolvents and semigroups: every strongly convergent input family is taken to a
strongly convergent output family. -/
def StrongOperatorConverges
    {Gn : ℕ → Type*} {G : Type*}
    [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace K (Gn n)]
    [NormedAddCommGroup G] [InnerProductSpace K G]
    (L : System (K := K) (H := G) (Hn := Gn))
    (Tn : ∀ n, Hn n →L[K] Gn n) (T : H →L[K] G) : Prop :=
  ∀ (x : ∀ n, Hn n) (xlim : H), J.StronglyConverges x xlim →
    L.StronglyConverges (fun n ↦ Tn n (x n)) (T xlim)

/-- Identity operators converge strongly on every varying Hilbert system. -/
theorem strongOperatorConverges_id :
    J.StrongOperatorConverges J (fun _ ↦ ContinuousLinearMap.id K _)
      (ContinuousLinearMap.id K H) := by
  intro x xlim hx
  simpa [StronglyConverges] using hx

/-- Varying-space strong operator convergence is closed under composition. -/
theorem StrongOperatorConverges.comp
    {Gn : ℕ → Type*} {G : Type*}
    [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace K (Gn n)]
    [NormedAddCommGroup G] [InnerProductSpace K G]
    {Fn : ℕ → Type*} {F : Type*}
    [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]
    [NormedAddCommGroup F] [InnerProductSpace K F]
    {L : System (K := K) (H := G) (Hn := Gn)}
    {M : System (K := K) (H := F) (Hn := Fn)}
    {Sn : ∀ n, Hn n →L[K] Gn n} {S : H →L[K] G}
    {Tn : ∀ n, Gn n →L[K] Fn n} {T : G →L[K] F}
    (hT : L.StrongOperatorConverges M Tn T)
    (hS : J.StrongOperatorConverges L Sn S) :
    J.StrongOperatorConverges M (fun n ↦ (Tn n).comp (Sn n)) (T.comp S) := by
  intro x xlim hx
  exact hT _ _ (hS x xlim hx)

end System
/-- The zero operator family converges strongly to zero. -/
theorem strongOperatorConverges_zero :
    J.StrongOperatorConverges J (fun _ ↦ (0 : Hn _ →L[K] Hn _)) (0 : H →L[K] H) := by
  intro x xlim hx
  simpa using J.stronglyConverges_zero

/-- Varying-space strong operator convergence is closed under addition. -/
theorem StrongOperatorConverges.add
    {Sn Tn : ∀ n, Hn n →L[K] Hn n} {S T : H →L[K] H}
    (hS : J.StrongOperatorConverges J Sn S)
    (hT : J.StrongOperatorConverges J Tn T) :
    J.StrongOperatorConverges J (fun n ↦ Sn n + Tn n) (S + T) := by
  intro x xlim hx
  simpa only [add_apply] using
    System.StronglyConverges.add J (hS x xlim hx) (hT x xlim hx)

/-- Varying-space strong operator convergence is closed under scalar multiplication. -/
theorem StrongOperatorConverges.smul (c : K)
    {Tn : ∀ n, Hn n →L[K] Hn n} {T : H →L[K] H}
    (hT : J.StrongOperatorConverges J Tn T) :
    J.StrongOperatorConverges J (fun n ↦ c • Tn n) (c • T) := by
  intro x xlim hx
  simpa only [smul_apply] using System.StronglyConverges.smul J c (hT x xlim hx)

/-- Every fixed power of a strongly convergent endomorphism family converges strongly. -/
theorem StrongOperatorConverges.pow
    {Tn : ∀ n, Hn n →L[K] Hn n} {T : H →L[K] H}
    (hT : J.StrongOperatorConverges J Tn T) (m : ℕ) :
    J.StrongOperatorConverges J (fun n ↦ (Tn n) ^ m) (T ^ m) := by
  induction m with
  | zero =>
      change J.StrongOperatorConverges J (fun _ ↦ ContinuousLinearMap.id K _)
        (ContinuousLinearMap.id K H)
      exact J.strongOperatorConverges_id
  | succ m ih =>
      simpa [pow_succ, ContinuousLinearMap.mul_def] using
        System.StrongOperatorConverges.comp J ih hT

end NCG.VaryingHilbert
