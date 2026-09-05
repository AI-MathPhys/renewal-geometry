import NCG.Grand.AbsorbingCutoff

/-! # absorbing words -/

open Matrix

namespace NCG

private def absorbingCore {Y : Type*} [Fintype Y]
    (P A : Matrix Y Y ℂ) : List (Matrix Y Y ℂ) → Matrix Y Y ℂ
  | [] => A
  | B :: rest => A * P * absorbingCore P B rest

/-- Letterwise corner compression, multiplied in the displayed word order. -/
def compressedWord {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] (J : Matrix Y X ℂ)
    (word : List (Matrix Y Y ℂ)) : Matrix X X ℂ :=
  (word.map fun A => Jᴴ * A * J).prod

/-- The manuscript absorbing-corner expression with `JJ*` inserted between
every two consecutive letters. -/
def absorbingWord {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] (J : Matrix Y X ℂ)
    (word : List (Matrix Y Y ℂ)) : Matrix X X ℂ :=
  match word with
  | [] => 1
  | A :: rest => Jᴴ * absorbingCore (J * Jᴴ) A rest * J

/-- `thm:ar-absorbing-cutoff`, boxed arbitrary-word identity. -/
theorem absorbingWord_eq_compressedWord
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] (J : Matrix Y X ℂ) (hJ : Jᴴ * J = 1)
    (word : List (Matrix Y Y ℂ)) :
    absorbingWord J word = compressedWord J word := by
  have hcore : ∀ (A : Matrix Y Y ℂ) (rest : List (Matrix Y Y ℂ)),
      Jᴴ * absorbingCore (J * Jᴴ) A rest * J
        = (Jᴴ * A * J) * compressedWord J rest := by
    intro A rest
    induction rest generalizing A with
    | nil => simp [absorbingCore, compressedWord]
    | cons B rest ih =>
        rw [absorbingCore]
        calc
          Jᴴ * (A * (J * Jᴴ) * absorbingCore (J * Jᴴ) B rest) * J
              = (Jᴴ * A * J) *
                  (Jᴴ * absorbingCore (J * Jᴴ) B rest * J) := by
                    simp only [Matrix.mul_assoc]
          _ = (Jᴴ * A * J) *
                ((Jᴴ * B * J) * compressedWord J rest) := by rw [ih B]
          _ = (Jᴴ * A * J) * compressedWord J (B :: rest) := by
                simp [compressedWord, Matrix.mul_assoc]
  cases word with
  | nil => simp [absorbingWord, compressedWord]
  | cons A rest =>
      simpa [absorbingWord, compressedWord] using hcore A rest

/-- The absorbing evaluation is the unique concatenation-multiplicative rule
that agrees with corner compression on single letters. -/
theorem compressedWord_unique
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] (J : Matrix Y X ℂ)
    (F : List (Matrix Y Y ℂ) → Matrix X X ℂ)
    (h0 : F [] = 1)
    (hletter : ∀ A, F [A] = Jᴴ * A * J)
    (happend : ∀ u v, F (u ++ v) = F u * F v) :
    ∀ word, F word = compressedWord J word := by
  intro word
  induction word with
  | nil => simpa [compressedWord] using h0
  | cons A rest ih =>
      rw [show A :: rest = [A] ++ rest from rfl, happend,
        hletter, ih]
      simp [compressedWord]

/-- Word-level transitivity of record cutoff. -/
theorem compressedWord_transitive {X Y Z : ℕ}
    (hXY : X ≤ Y) (hYZ : Y ≤ Z)
    (word : List (Matrix (Fin Z) (Fin Z) ℂ)) :
    compressedWord (cornerJ X Z) word
      = compressedWord (cornerJ X Y)
          (word.map fun A =>
            (cornerJ Y Z)ᴴ * A * cornerJ Y Z) := by
  induction word with
  | nil => simp [compressedWord]
  | cons A rest ih =>
      simp only [compressedWord, List.map_cons, List.prod_cons]
      have ih' := ih
      simp only [compressedWord] at ih'
      rw [(absorbing_cutoff hXY hYZ A).2, ih']

end NCG
