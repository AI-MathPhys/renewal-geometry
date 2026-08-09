import NCG.Grand.RecordCutoff

/-! # forward corner compression is an algebra map -/

open Matrix

namespace NCG

/-- `thm:ar-record-cutoff`, abstract homomorphism core.  The displayed
condition is exactly the vanishing upper-right block of a forward operator.
For an isometric corner inclusion, compression preserves the unit, addition,
scalars, and products of forward operators. -/
theorem forward_corner_compression_hom
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (J : Matrix Y X ℂ) (hJ : Jᴴ * J = 1) :
    (Jᴴ * (1 : Matrix Y Y ℂ) * J = 1)
      ∧ (∀ A B : Matrix Y Y ℂ,
        Jᴴ * A = Jᴴ * A * (J * Jᴴ) →
        Jᴴ * (A * B) * J = (Jᴴ * A * J) * (Jᴴ * B * J))
      ∧ (∀ A B : Matrix Y Y ℂ,
        Jᴴ * (A + B) * J = Jᴴ * A * J + Jᴴ * B * J)
      ∧ (∀ (c : ℂ) (A : Matrix Y Y ℂ),
        Jᴴ * (c • A) * J = c • (Jᴴ * A * J)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hJ
  · intro A B hforward
    have h := congrArg (fun M : Matrix X Y ℂ => M * B * J) hforward
    simpa only [Matrix.mul_assoc] using h
  · intro A B
    simp only [Matrix.mul_add, Matrix.add_mul]
  · intro c A
    simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- The canonical record inclusion is an isometry, so the preceding abstract
homomorphism theorem applies to the manuscript corner `cornerJ X Y`. -/
theorem cornerJ_isometry {X Y : ℕ} (hXY : X ≤ Y) :
    (cornerJ X Y)ᴴ * cornerJ X Y = 1 := by
  have hIY : Matrix.of (fun (j i : Fin Y) =>
      if (j : ℕ) = (i : ℕ) then (1 : ℂ) else 0) = 1 := by
    ext j i
    simp [Matrix.one_apply, Fin.ext_iff]
  have hIX : Matrix.of (fun (j i : Fin X) =>
      if (j : ℕ) = (i : ℕ) then (1 : ℂ) else 0) = 1 := by
    ext j i
    simp [Matrix.one_apply, Fin.ext_iff]
  have h := corner_compress hXY
    (fun j i : ℕ => if j = i then (1 : ℂ) else 0)
  rw [hIY, hIX, Matrix.mul_one] at h
  exact h

end NCG
