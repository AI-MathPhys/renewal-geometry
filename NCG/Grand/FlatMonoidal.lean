/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.KalmanRealization

/-!
# Flat monoidal moment reconstruction
  (`thm:flat-monoidal-reconstruction`, Gran-Tensor manuscript)

* `flat_monoidal_reconstruction`: two source-generated history
  realizations with matching flat moment hierarchies are
  identified by a unitary `W` with `W·W₁,r = W₂,r` on the
  observability (Krylov) syntheses — existence via the proved
  Kalman construction, and uniqueness by source-cyclicity
  (surjectivity of the synthesis).

Rendering disclosed: the realizations enter through their
transfer/source pairs `(G, B)`, `(G', B')`; the flat shared
hierarchy `𝕂_{1,r+1} = 𝕂_{2,r+1}` is the all-order moment
equality (flatness `rank 𝕂_r = rank 𝕂_{r+1}` enters as the
source-cyclicity/minimality hypothesis of the cited Kalman
record); that unitary conjugation is a unital `*`-isomorphism
of the generated algebras is the manuscript's bookkeeping over
`WᴴW = 1`.
-/

open Matrix

namespace NCG

/-- `thm:flat-monoidal-reconstruction`: unique unitary
identification of flat moment-matched realizations on the
Krylov syntheses. -/
theorem flat_monoidal_reconstruction {u p : Type*} [Fintype u]
    [Fintype p] [DecidableEq u]
    (G G' : Matrix u u ℂ) (B B' : Matrix u p ℂ)
    (hG : Gᴴ = G) (hG' : G'ᴴ = G')
    (d : ℕ) (hd : 0 < d)
    (hmin : Function.Surjective (krylovMat G B d).mulVec)
    (hmom : ∀ n : ℕ, Bᴴ * G ^ n * B = B'ᴴ * G' ^ n * B') :
    (∃ W : Matrix u u ℂ, Wᴴ * W = 1
      ∧ (∀ e : ℕ, W * krylovMat G B e = krylovMat G' B' e)
      ∧ W * B = B' ∧ W * G = G' * W)
    ∧ (∀ W₁ W₂ : Matrix u u ℂ,
        W₁ * krylovMat G B d = krylovMat G' B' d →
        W₂ * krylovMat G B d = krylovMat G' B' d →
        W₁ = W₂) := by
  constructor
  · obtain ⟨W, hWu, hWB, hWG⟩ :=
      physical_source_uniqueness G G' B B' hG hG' d hd
        hmin hmom
    have hWpow : ∀ k : ℕ, W * (G ^ k * B) = G' ^ k * B' := by
      intro k
      have hcomm : W * G ^ k = G' ^ k * W := by
        induction k with
        | zero => simp
        | succ n ih =>
            rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih,
              Matrix.mul_assoc, hWG, ← Matrix.mul_assoc]
      rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, hWB]
    refine ⟨W, hWu, ?_, hWB, hWG⟩
    intro e
    ext i kq
    calc (W * krylovMat G B e) i kq
        = (W * (G ^ (kq.1 : ℕ) * B)) i kq.2 := by
          rw [Matrix.mul_apply, Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro j _
          rfl
      _ = (G' ^ (kq.1 : ℕ) * B') i kq.2 := by
          rw [hWpow]
      _ = krylovMat G' B' e i kq := rfl
  · intro W₁ W₂ hW₁ hW₂
    have hdiff : (W₁ - W₂) * krylovMat G B d = 0 := by
      rw [Matrix.sub_mul, hW₁, hW₂, sub_self]
    have hv : ∀ v : u → ℂ, (W₁ - W₂) *ᵥ v = 0 := by
      intro v
      obtain ⟨a, ha⟩ := hmin v
      rw [← ha, Matrix.mulVec_mulVec, hdiff,
        Matrix.zero_mulVec]
    have hzero : W₁ - W₂ = 0 := by
      ext i j
      have h := congrFun (hv (Pi.single j 1)) i
      have hval : ((W₁ - W₂) *ᵥ Pi.single j (1 : ℂ)) i
          = (W₁ - W₂) i j := by
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply]
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk
          rw [if_neg hk, mul_zero]
        · intro hk
          exact absurd (Finset.mem_univ _) hk
      rw [hval] at h
      simpa using h
    exact sub_eq_zero.mp hzero

end NCG
