/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NSScaleCurrent
import NCG.Grand.PsdBlockSchurExact

/-!
# Singular Moore--Penrose scale current

This is the pseudoinverse completion of `NSScaleCurrent`.  The action may be
positive semidefinite and singular.  The boundary map is supported on its
energy support, and the source is assumed only to lie in the range of the
induced scale Laplacian.  Under exactly those harmonic-obstruction conditions
the Moore--Penrose current is feasible, has the advertised energy, and every
competitor satisfies the exact Pythagoras identity.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace SingularScaleCurrent

open GeometricThresholdBank SourceCoercivityInfluence PsdBlockSchur

variable {n s m : Type*} [Fintype n] [Fintype s] [Fintype m]
  [DecidableEq n] [DecidableEq s]

/-- Scale Laplacian induced by a possibly singular positive action. -/
noncomputable def scaleLaplacian (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (D : Matrix s n ℂ) : Matrix s s ℂ :=
  D * pinv hA.1 * Dᴴ

theorem scaleLaplacian_posSemidef
    (A : Matrix n n ℂ) (hA : A.PosSemidef) (D : Matrix s n ℂ) :
    (scaleLaplacian A hA D).PosSemidef := by
  simpa [scaleLaplacian] using
    (pinv_posSemidef hA.1).conjTranspose_mul_mul_same Dᴴ

/-- Canonical Moore--Penrose current. -/
noncomputable def canonicalCurrent
    (A : Matrix n n ℂ) (hA : A.PosSemidef) (D : Matrix s n ℂ)
    (src : Matrix s m ℂ) : Matrix n m ℂ :=
  let L := scaleLaplacian A hA D
  pinv hA.1 * (Dᴴ * (pinv (scaleLaplacian_posSemidef A hA D).1 * src))

/-- **`thm:NS-effective-scale-current`, singular exact form.** -/
theorem singular_effective_scale_current
    (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (D : Matrix s n ℂ) (src : Matrix s m ℂ)
    (hDsupport : D * supportProj hA.1 = D)
    (hsrc : scaleLaplacian A hA D *
      pinv (scaleLaplacian_posSemidef A hA D).1 * src = src) :
    D * canonicalCurrent A hA D src = src ∧
    (canonicalCurrent A hA D src)ᴴ * A *
        canonicalCurrent A hA D src =
      srcᴴ * (pinv (scaleLaplacian_posSemidef A hA D).1 * src) ∧
    ∀ j : Matrix n m ℂ, D * j = src →
      jᴴ * A * j =
        srcᴴ * (pinv (scaleLaplacian_posSemidef A hA D).1 * src) +
        (j - canonicalCurrent A hA D src)ᴴ * A *
          (j - canonicalCurrent A hA D src) := by
  let G := pinv hA.1
  let L := scaleLaplacian A hA D
  let hL : L.PosSemidef := scaleLaplacian_posSemidef A hA D
  let H := pinv hL.1
  let js := G * (Dᴴ * (H * src))
  have hsrc' : L * H * src = src := by
    simpa [L, H, hL] using hsrc
  have hsrc'' : L * (H * src) = src := by
    rw [← Matrix.mul_assoc]
    exact hsrc'
  have hGH : Gᴴ = G := (pinv_isHermitian hA.1).eq
  have hHH : Hᴴ = H := (pinv_isHermitian hL.1).eq
  have hPD : supportProj hA.1 * Dᴴ = Dᴴ := by
    have h := congrArg Matrix.conjTranspose hDsupport
    simpa [Matrix.conjTranspose_mul,
      (supportProj_posSemidef hA.1).1.eq] using h
  have hAG : A * G = supportProj hA.1 :=
    mul_pinv_eq_supportProj hA.1
  have hfeas : D * js = src := by
    change D * (G * (Dᴴ * (H * src))) = src
    calc
      D * (G * (Dᴴ * (H * src))) = L * H * src := by
        simp only [L, G, scaleLaplacian, Matrix.mul_assoc]
      _ = src := hsrc'
  have hAjs : A * js = Dᴴ * (H * src) := by
    change A * (G * (Dᴴ * (H * src))) = Dᴴ * (H * src)
    calc
      A * (G * (Dᴴ * (H * src))) =
          supportProj hA.1 * (Dᴴ * (H * src)) := by
            rw [← Matrix.mul_assoc, hAG]
      _ = (supportProj hA.1 * Dᴴ) * (H * src) := by
            rw [Matrix.mul_assoc]
      _ = Dᴴ * (H * src) := by rw [hPD]
  have hvalue : jsᴴ * A * js = srcᴴ * (H * src) := by
    rw [Matrix.mul_assoc jsᴴ A js, hAjs]
    change (G * (Dᴴ * (H * src)))ᴴ * (Dᴴ * (H * src)) =
      srcᴴ * (H * src)
    calc
      (G * (Dᴴ * (H * src)))ᴴ * (Dᴴ * (H * src))
          = (H * src)ᴴ * (L * (H * src)) := by
              rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
                hGH, Matrix.conjTranspose_conjTranspose]
              simp only [L, G, scaleLaplacian, Matrix.mul_assoc]
      _ = (H * src)ᴴ * src := by
              rw [hsrc'']
      _ = srcᴴ * (H * src) := by
              rw [Matrix.conjTranspose_mul, hHH, Matrix.mul_assoc]
  change D * js = src ∧ jsᴴ * A * js = srcᴴ * (H * src) ∧
    ∀ j, D * j = src →
      jᴴ * A * j = srcᴴ * (H * src) + (j - js)ᴴ * A * (j - js)
  refine ⟨hfeas, hvalue, ?_⟩
  intro j hj
  have hw : D * (j - js) = 0 := by
    rw [Matrix.mul_sub, hj, hfeas, sub_self]
  have hcross1 : (j - js)ᴴ * (A * js) = 0 := by
    rw [hAjs, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      hw, Matrix.conjTranspose_zero, Matrix.zero_mul]
  have hcross2 : jsᴴ * (A * (j - js)) = 0 := by
    have h1 : (A * js)ᴴ = jsᴴ * A := by
      rw [Matrix.conjTranspose_mul, hA.1.eq]
    rw [← Matrix.mul_assoc, ← h1, hAjs, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hw,
      Matrix.mul_zero]
  have hdecomp : j = js + (j - js) := by abel
  calc
    jᴴ * A * j = (js + (j - js))ᴴ * A * (js + (j - js)) := by
      rw [← hdecomp]
    _ = jsᴴ * (A * js) + jsᴴ * (A * (j - js)) +
        ((j - js)ᴴ * (A * js) + (j - js)ᴴ * (A * (j - js))) := by
      rw [Matrix.conjTranspose_add]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    _ = srcᴴ * (H * src) + (j - js)ᴴ * A * (j - js) := by
      rw [hcross1, hcross2, ← Matrix.mul_assoc jsᴴ A js, hvalue,
        add_zero, zero_add, Matrix.mul_assoc]

end SingularScaleCurrent
end NCG
