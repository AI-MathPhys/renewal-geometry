/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Operator.Diagonal

/-!
# The canonical signed modular Dirac

**Theorem `thm:signed-dirac`** (algebraic core): with a fundamental
symmetry `J` commuting with the self-adjoint modular weight `Δ = e^{βN}`
and a `J`-self-adjoint perturbation `B`,

* `D = JΔ + B` is **Krein-self-adjoint**, `J D* J = D`
  (`NCG.signed_dirac_krein_selfadjoint`);
* the twisted commutator of the modular part **collapses**:
  `[JΔ, a]_ρ = 0` for the modular twist `ρ(a) = JΔ a Δ⁻¹ J`, so
  `[D, a]_ρ = [B, a]_ρ` (`NCG.twisted_commutator_collapse`,
  `NCG.twisted_commutator_reduction`) — boundedness of the twisted
  commutators reduces to the bounded perturbation.

**Lemma `lem:bounded-twisted`** (multiplier core): on the finsupp model
the modular conjugation of a lifted shift is again a weighted shift,

`Δ S Δ⁻¹ e_x = e^{β(Λ(sx) − Λ(x))} e_{sx}`

(`NCG.modular_conj_shift_single`), and under bounded increments
`|Λ(sx) − Λ(x)| ≤ L` the multiplier obeys `|e^{β(...)}| ≤ e^{βL}`
(`NCG.modular_multiplier_bound`).  (The Schur-test boundedness of
general propagation-`r` elements on `ℓ²` and the compact
resolvent/summability claims are not formalised.) -/

namespace NCG

/-! ### Krein-self-adjointness and the twisted-commutator reduction -/

section Algebraic

variable {A : Type*} [Ring A] [StarRing A]

/-- **Theorem `thm:signed-dirac`** (Krein-self-adjointness): with
`J* = J`, `J² = 1`, `Δ* = Δ`, `JΔ = ΔJ`, and `JB*J = B`, the signed
modular Dirac `D = JΔ + B` satisfies `J D* J = D`. -/
theorem signed_dirac_krein_selfadjoint (J Δ B : A)
    (hJstar : star J = J) (hJsq : J * J = 1)
    (hΔstar : star Δ = Δ) (_hcomm : J * Δ = Δ * J)
    (hB : J * star B * J = B) :
    J * star (J * Δ + B) * J = J * Δ + B := by
  rw [star_add, star_mul, hΔstar, hJstar, mul_add, add_mul]
  congr 1
  calc J * (Δ * J) * J = J * Δ * (J * J) := by
        rw [← mul_assoc J Δ J, mul_assoc (J * Δ) J J]
    _ = J * Δ := by rw [hJsq, mul_one]

omit [StarRing A] in
/-- **Theorem `thm:signed-dirac`** (modular collapse): the twisted
commutator of the modular part vanishes for the canonical twist
`ρ(a) = JΔ a Δ⁻¹ J`:  `JΔ·a − ρ(a)·JΔ = 0`. -/
theorem twisted_commutator_collapse (J : A) (u : Aˣ) (a : A)
    (hJsq : J * J = 1) :
    J * (u : A) * a
      - (J * (u : A) * a * (↑u⁻¹ : A) * J) * (J * (u : A)) = 0 := by
  have hkey : (J * (u : A) * a * (↑u⁻¹ : A) * J) * (J * (u : A))
      = J * (u : A) * a := by
    calc (J * (u : A) * a * (↑u⁻¹ : A) * J) * (J * (u : A))
        = J * (u : A) * a * (↑u⁻¹ : A) * (J * J) * (u : A) := by
          rw [mul_assoc (J * (u : A) * a * (↑u⁻¹ : A)) J _,
            ← mul_assoc J J (u : A), ← mul_assoc]
      _ = J * (u : A) * a * ((↑u⁻¹ : A) * (u : A)) := by
          rw [hJsq, mul_one, mul_assoc]
      _ = J * (u : A) * a := by
          rw [Units.inv_mul, mul_one]
  rw [hkey, sub_self]

omit [StarRing A] in
/-- **Theorem `thm:signed-dirac` / Lemma `lem:bounded-twisted`**
(reduction): the twisted commutator of `D = JΔ + B` equals that of the
bounded part alone, `[D, a]_ρ = [B, a]_ρ`. -/
theorem twisted_commutator_reduction (J : A) (u : Aˣ) (a B : A)
    (hJsq : J * J = 1) :
    (J * (u : A) + B) * a
        - (J * (u : A) * a * (↑u⁻¹ : A) * J) * (J * (u : A) + B)
      = B * a - (J * (u : A) * a * (↑u⁻¹ : A) * J) * B := by
  have h := twisted_commutator_collapse J u a hJsq
  rw [add_mul, mul_add]
  calc J * (u : A) * a + B * a
      - ((J * (u : A) * a * (↑u⁻¹ : A) * J) * (J * (u : A))
        + (J * (u : A) * a * (↑u⁻¹ : A) * J) * B)
      = (J * (u : A) * a
          - (J * (u : A) * a * (↑u⁻¹ : A) * J) * (J * (u : A)))
        + (B * a - (J * (u : A) * a * (↑u⁻¹ : A) * J) * B) := by
        abel
    _ = B * a - (J * (u : A) * a * (↑u⁻¹ : A) * J) * B := by
        rw [h, zero_add]

end Algebraic

/-! ### The modular conjugation multiplier (`lem:bounded-twisted`) -/

section Multiplier

variable {ι : Type*}

/-- **Lemma `lem:bounded-twisted`** (exchange identity): the modular
conjugation of a lifted shift is the shift weighted by the length
increment, `ΔSΔ⁻¹ e_x = e^{β(Λ(sx) − Λ(x))}·e_{sx}`. -/
theorem modular_conj_shift_single (Λ : ι → ℝ) (β : ℝ) (s : ι → ι)
    (x : ι) (c : ℂ) :
    (diagOp (fun i => Complex.exp ((β * Λ i : ℝ) : ℂ)) ∘ₗ shiftOp s ∘ₗ
        diagOp (fun i => Complex.exp ((-(β * Λ i) : ℝ) : ℂ)))
      (Finsupp.single x c)
      = Complex.exp ((β * (Λ (s x) - Λ x) : ℝ) : ℂ) •
          Finsupp.single (s x) c := by
  simp only [LinearMap.comp_apply, diagOp_single, shiftOp_single,
    Finsupp.smul_single]
  congr 1
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- **Lemma `lem:bounded-twisted`** (multiplier bound): under bounded
length increments `|Λ(sx) − Λ(x)| ≤ L`, the conjugation multiplier is
bounded by `e^{βL}` — the σ_β-boundedness of lifted generators. -/
theorem modular_multiplier_bound {Λ : ι → ℝ} {β L : ℝ} (hβ : 0 ≤ β)
    {s : ι → ι} {x : ι} (h : |Λ (s x) - Λ x| ≤ L) :
    ‖Complex.exp ((β * (Λ (s x) - Λ x) : ℝ) : ℂ)‖
      ≤ Real.exp (β * L) := by
  rw [Complex.norm_exp, Complex.ofReal_re]
  apply Real.exp_le_exp.mpr
  have := abs_le.mp h
  nlinarith

end Multiplier

end NCG
