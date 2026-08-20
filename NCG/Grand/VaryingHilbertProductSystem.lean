/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Product systems for graph embeddings

Two varying-Hilbert systems combine canonically on the Hilbert `L²` product.
The coordinate identities are definitional consequences of the product
isometry, so graph-system first-coordinate compatibility no longer needs to be
proved separately.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v w x y

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]
variable {Hn : ℕ → Type x} {Fn : ℕ → Type y}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]

/-- The canonical `L²` product of two varying-Hilbert systems. -/
def System.product
    (J : System (K := K) (H := H) (Hn := Hn))
    (M : System (K := K) (H := F) (Hn := Fn)) :
    System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)) where
  embedding n := (J.embedding n).withLpProdMap 2 (M.embedding n)

namespace System

variable (J : System (K := K) (H := H) (Hn := Hn))
variable (M : System (K := K) (H := F) (Hn := Fn))

/-- The product-system embedding acts coordinatewise. -/
@[simp] theorem product_embedding (n : ℕ) (z : WithLp 2 (Hn n × Fn n)) :
    (J.product M).embedding n z =
      WithLp.toLp 2 (J.embedding n z.fst, M.embedding n z.snd) := by
  rfl

/-- First-coordinate graph compatibility is automatic for the product system. -/
@[simp] theorem product_embedding_fst (n : ℕ)
    (z : WithLp 2 (Hn n × Fn n)) :
    ((J.product M).embedding n z).fst = J.embedding n z.fst := by
  rfl

/-- Second-coordinate graph compatibility is automatic for the product system. -/
@[simp] theorem product_embedding_snd (n : ℕ)
    (z : WithLp 2 (Hn n × Fn n)) :
    ((J.product M).embedding n z).snd = M.embedding n z.snd := by
  rfl


/-- Asymptotic density is preserved by the canonical `L²` product. -/
theorem IsAsymptoticallyDense.product
    (hJ : J.IsAsymptoticallyDense) (hM : M.IsAsymptoticallyDense) :
    (J.product M).IsAsymptoticallyDense := by
  intro z
  obtain ⟨xn, hxn⟩ := hJ z.fst
  obtain ⟨yn, hyn⟩ := hM z.snd
  refine ⟨fun n ↦ WithLp.toLp 2 (xn n, yn n), ?_⟩
  rw [StronglyConverges]
  simp only [product_embedding]
  have hpair : Tendsto
      (fun n ↦ (J.embedding n (xn n), M.embedding n (yn n)))
      atTop (nhds (z.fst, z.snd)) := by
    exact hxn.prodMk_nhds hyn
  exact (WithLp.prod_continuous_toLp 2 H F).continuousAt.tendsto.comp
    hpair
end System
end NCG.VaryingHilbert
