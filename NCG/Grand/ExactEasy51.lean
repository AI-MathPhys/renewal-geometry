/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Upstream.KalmanRealization

/-!
# Exact EASY 51: physical-source completeness and minimality

The upstream Kalman file supplies reduction of the Krylov span and existence
of a source-fixing unitary intertwiner from equal moments.  Here we encode the
remaining exact clauses: compression preserves every moment and every finite
functional-calculus block, the orthogonal complement is source-invisible, and
the intertwiner is unique on a source-minimal carrier.
-/

open Matrix

namespace NCG

/-- For a Hermitian response, invariance of the source-cyclic subspace also
makes its orthogonal complement invariant; hence the cyclic subspace reduces
the response in the full operator-theoretic sense. -/
theorem krylov_orthogonal_complement_invariant
    {u p : Type*} [Fintype u] [Fintype p] [DecidableEq u]
    (G : Matrix u u ℂ) (B : Matrix u p ℂ) (hG : Gᴴ = G)
    (x : u → ℂ)
    (hx : ∀ y ∈ Submodule.span ℂ
      (⋃ n : ℕ, Set.range fun v : p → ℂ => (G ^ n * B) *ᵥ v),
        star y ⬝ᵥ x = 0) :
    ∀ y ∈ Submodule.span ℂ
      (⋃ n : ℕ, Set.range fun v : p → ℂ => (G ^ n * B) *ᵥ v),
        star y ⬝ᵥ (G *ᵥ x) = 0 := by
  intro y hy
  have hGy := krylov_reduces G B y hy
  calc
    star y ⬝ᵥ (G *ᵥ x) = (star y ᵥ* G) ⬝ᵥ x :=
      Matrix.dotProduct_mulVec _ _ _
    _ = star (G *ᵥ y) ⬝ᵥ x := by rw [Matrix.star_mulVec, hG]
    _ = 0 := hx (G *ᵥ y) hGy

/-- A commuting source projection reduces the response and makes its
orthogonal complement invisible to every source moment.  Compression preserves
both individual moments and arbitrary finite linear combinations of them. -/
theorem source_compression_invisibility
    {u p : Type*} [Fintype u] [Fintype p] [DecidableEq u]
    (G P : Matrix u u ℂ) (B : Matrix u p ℂ)
    (_hP2 : P * P = P) (hPG : P * G = G * P) (hPB : P * B = B) :
    ((1 - P) * G = G * (1 - P))
    ∧ (∀ n : ℕ, P * (G ^ n * B) = G ^ n * B)
    ∧ (∀ n : ℕ, (1 - P) * (G ^ n * B) = 0)
    ∧ (∀ n : ℕ,
        Bᴴ * G ^ n * B = Bᴴ * (P * G * P) ^ n * B)
    ∧ (∀ (s : Finset ℕ) (c : ℕ → ℂ),
        Bᴴ * (∑ n ∈ s, c n • G ^ n) * B
          = Bᴴ * (∑ n ∈ s, c n • (P * G * P) ^ n) * B) := by
  have hreduce : (1 - P) * G = G * (1 - P) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPG]
  have hcyc : ∀ n : ℕ, P * (G ^ n * B) = G ^ n * B := by
    intro n
    induction n with
    | zero => simpa using hPB
    | succ n ih =>
        calc
          P * (G ^ (n + 1) * B)
              = (P * G) * (G ^ n * B) := by
                  rw [pow_succ']
                  simp only [Matrix.mul_assoc]
          _ = G * (P * (G ^ n * B)) := by rw [hPG]; simp only [Matrix.mul_assoc]
          _ = G * (G ^ n * B) := by rw [ih]
          _ = G ^ (n + 1) * B := by rw [pow_succ']; simp only [Matrix.mul_assoc]
  have hinvis : ∀ n : ℕ, (1 - P) * (G ^ n * B) = 0 := by
    intro n
    rw [Matrix.sub_mul, Matrix.one_mul, hcyc n, sub_self]
  have hcompressed : ∀ n : ℕ, (P * G * P) ^ n * B = G ^ n * B := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          (P * G * P) ^ (n + 1) * B
              = (P * G * P) * ((P * G * P) ^ n * B) := by
                  rw [pow_succ']
                  simp only [Matrix.mul_assoc]
          _ = P * G * P * (G ^ n * B) := by rw [ih]
          _ = P * G * (P * (G ^ n * B)) := by
                simp only [Matrix.mul_assoc]
          _ = P * (G * (G ^ n * B)) := by
                rw [hcyc n]
                exact Matrix.mul_assoc _ _ _
          _ = (P * G) * (G ^ n * B) := (Matrix.mul_assoc _ _ _).symm
          _ = P * (G ^ (n + 1) * B) := by
                rw [pow_succ']
                simp only [Matrix.mul_assoc]
          _ = G ^ (n + 1) * B := hcyc (n + 1)
  have hmom : ∀ n : ℕ,
      Bᴴ * G ^ n * B = Bᴴ * (P * G * P) ^ n * B := by
    intro n
    calc
      Bᴴ * G ^ n * B = Bᴴ * (G ^ n * B) := Matrix.mul_assoc _ _ _
      _ = Bᴴ * ((P * G * P) ^ n * B) := by rw [hcompressed n]
      _ = Bᴴ * (P * G * P) ^ n * B := (Matrix.mul_assoc _ _ _).symm
  refine ⟨hreduce, hcyc, hinvis, hmom, ?_⟩
  · intro s c
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hmom n]

/-- Source-minimality makes a source-fixing transfer intertwiner unique.  No
unitarity hypothesis is needed for uniqueness: agreement on the finite Krylov
generators and surjectivity of their synthesis already force equality. -/
theorem source_fixing_intertwiner_unique
    {u p : Type*} [Fintype u] [Fintype p]
    [DecidableEq u] [DecidableEq p]
    (G G' : Matrix u u ℂ) (B B' : Matrix u p ℂ)
    (d : ℕ) (hmin : Function.Surjective (krylovMat G B d).mulVec)
    (W V : Matrix u u ℂ)
    (hWB : W * B = B') (hVB : V * B = B')
    (hWG : W * G = G' * W) (hVG : V * G = G' * V) :
    W = V := by
  have hWpow : ∀ n : ℕ, W * G ^ n = G' ^ n * W := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          W * G ^ (n + 1) = (W * G ^ n) * G := by
            rw [pow_succ]
            simp only [Matrix.mul_assoc]
          _ = (G' ^ n * W) * G := by rw [ih]
          _ = G' ^ n * (W * G) := by simp only [Matrix.mul_assoc]
          _ = G' ^ n * (G' * W) := by rw [hWG]
          _ = G' ^ (n + 1) * W := by
            rw [pow_succ]
            simp only [Matrix.mul_assoc]
  have hVpow : ∀ n : ℕ, V * G ^ n = G' ^ n * V := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          V * G ^ (n + 1) = (V * G ^ n) * G := by
            rw [pow_succ]
            simp only [Matrix.mul_assoc]
          _ = (G' ^ n * V) * G := by rw [ih]
          _ = G' ^ n * (V * G) := by simp only [Matrix.mul_assoc]
          _ = G' ^ n * (G' * V) := by rw [hVG]
          _ = G' ^ (n + 1) * V := by
            rw [pow_succ]
            simp only [Matrix.mul_assoc]
  have hWK : W * krylovMat G B d = krylovMat G' B' d := by
    ext i nq
    change (W * (G ^ (nq.1 : ℕ) * B)) i nq.2
      = (G' ^ (nq.1 : ℕ) * B') i nq.2
    rw [← Matrix.mul_assoc, hWpow, Matrix.mul_assoc, hWB]
  have hVK : V * krylovMat G B d = krylovMat G' B' d := by
    ext i nq
    change (V * (G ^ (nq.1 : ℕ) * B)) i nq.2
      = (G' ^ (nq.1 : ℕ) * B') i nq.2
    rw [← Matrix.mul_assoc, hVpow, Matrix.mul_assoc, hVB]
  have hmulVec : ∀ x : u → ℂ, W *ᵥ x = V *ᵥ x := by
    intro x
    obtain ⟨y, rfl⟩ := hmin x
    rw [Matrix.mulVec_mulVec, hWK, Matrix.mulVec_mulVec, hVK]
  ext i j
  have h := congrFun (hmulVec (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

end NCG
