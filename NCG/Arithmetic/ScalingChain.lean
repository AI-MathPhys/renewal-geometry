/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.ResidueParseval
import NCG.Arithmetic.GaussianGRH

/-!
# Finite scaling indicator and the fixed-modulus GRH chain
  (`thm:scaling-indicator`, `cor:fixed-mod-grh`,
   arithmetic manuscript)

* the upper half of the scaling indicator
  (`scaling_energy_upper`): the explicit-formula growth bound
  `|𝒢(r)| ≤ C(1+r)^A e^{(Θ+ε)r}` forces the finite-cutoff energy
  `∫₀^U e^{-2σr}|𝒢|² dr` below
  `C²(1+U)^{2A}(U+1)·e^{2(Θ+ε-σ)₊U}` — taking `log⁺` and
  dividing by `U = log X` gives the manuscript's
  `limsup ≤ 2(Θ-σ+ε)₊`;
* the character–residue domination (`char_energy_le_variance`):
  by the proved Parseval identity (`thm:residue-parseval`), every
  nonprincipal character energy is bounded by `φ(n)` times the
  residue variance — the first step of the fixed-modulus chain;
* the fixed-modulus assembly (`fixed_mod_grh`): with the
  per-character indicator step supplied at every scale
  (displayed), subpower residue variance at every `σ > 0` forces
  each nonprincipal displacement to vanish, through the two-sided
  criterion of the Gaussian-Hardy record.

Rendering disclosed: the lower half of the scaling indicator (the
Bohr mean-square lower bound over an almost-periodic exponential
sum, giving `limsup ≥`) and the bulk agreement of the
cutoff-matched and complete ports are the manuscript's displayed
steps; the `limsup`/`log⁺` bookkeeping is rendered by the
finite-cutoff inequality; the per-character application of the
indicator enters the corollary as the displayed hypothesis
`hind`.
-/

open MeasureTheory Set Finset

namespace NCG

/-- Upper half of the scaling indicator: the growth bound forces
the finite-cutoff weighted energy below the boxed exponential. -/
theorem scaling_energy_upper (𝒢 : ℝ → ℂ)
    (C A Θ ε σ U : ℝ) (hU : 0 ≤ U) (hA : 0 ≤ A)
    (hm : AEStronglyMeasurable 𝒢 (volume.restrict (Ioc 0 U)))
    (hg : ∀ r ∈ Icc (0 : ℝ) U,
      ‖𝒢 r‖ ≤ C * (1 + r) ^ A * Real.exp ((Θ + ε) * r)) :
    ∫ r in Ioc (0 : ℝ) U,
        Real.exp (-(2 * σ) * r) * ‖𝒢 r‖ ^ 2
      ≤ C ^ 2 * (1 + U) ^ (2 * A) * (U + 1)
        * Real.exp (2 * max (Θ + ε - σ) 0 * U) := by
  have hC0 : 0 ≤ C := by
    have h1 := hg 0 ⟨le_refl 0, hU⟩
    simp only [add_zero, mul_zero, Real.exp_zero, mul_one,
      Real.one_rpow] at h1
    exact le_trans (norm_nonneg _) h1
  set M : ℝ := C ^ 2 * (1 + U) ^ (2 * A)
    * Real.exp (2 * max (Θ + ε - σ) 0 * U) with hM_def
  have hM0 : 0 ≤ M := by
    rw [hM_def]
    positivity
  have hpt : ∀ r ∈ Ioc (0 : ℝ) U,
      Real.exp (-(2 * σ) * r) * ‖𝒢 r‖ ^ 2 ≤ M := by
    intro r hr
    obtain ⟨hr0, hrU⟩ := hr
    have hb := hg r ⟨hr0.le, hrU⟩
    have h1 : ‖𝒢 r‖ ^ 2
        ≤ (C * (1 + r) ^ A * Real.exp ((Θ + ε) * r)) ^ 2 := by
      have := norm_nonneg (𝒢 r)
      nlinarith
    have h2 : Real.exp (-(2 * σ) * r) * ‖𝒢 r‖ ^ 2
        ≤ C ^ 2 * (1 + r) ^ (2 * A)
          * Real.exp (2 * (Θ + ε - σ) * r) := by
      have h3 : (C * (1 + r) ^ A * Real.exp ((Θ + ε) * r)) ^ 2
          = C ^ 2 * (1 + r) ^ (2 * A)
            * Real.exp (2 * (Θ + ε) * r) := by
        rw [mul_pow, mul_pow, sq (Real.exp ((Θ + ε) * r)),
          ← Real.exp_add,
          show (Θ + ε) * r + (Θ + ε) * r
            = 2 * (Θ + ε) * r by ring,
          ← Real.rpow_natCast ((1 + r) ^ A) 2,
          ← Real.rpow_mul (by linarith : (0:ℝ) ≤ 1 + r)]
        norm_num
        exact Or.inl (by rw [mul_comm A 2])
      have h4 : Real.exp (-(2 * σ) * r)
          * Real.exp (2 * (Θ + ε) * r)
          = Real.exp (2 * (Θ + ε - σ) * r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc Real.exp (-(2 * σ) * r) * ‖𝒢 r‖ ^ 2
          ≤ Real.exp (-(2 * σ) * r)
            * (C * (1 + r) ^ A * Real.exp ((Θ + ε) * r)) ^ 2 :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = C ^ 2 * (1 + r) ^ (2 * A)
            * (Real.exp (-(2 * σ) * r)
              * Real.exp (2 * (Θ + ε) * r)) := by
            rw [h3]
            ring
        _ = C ^ 2 * (1 + r) ^ (2 * A)
            * Real.exp (2 * (Θ + ε - σ) * r) := by rw [h4]
    refine le_trans h2 ?_
    rw [hM_def]
    have h5 : (1 + r) ^ (2 * A) ≤ (1 + U) ^ (2 * A) := by
      refine Real.rpow_le_rpow (by linarith) (by linarith)
        (by positivity)
    have h6 : Real.exp (2 * (Θ + ε - σ) * r)
        ≤ Real.exp (2 * max (Θ + ε - σ) 0 * U) := by
      refine Real.exp_le_exp.mpr ?_
      rcases le_or_gt (Θ + ε - σ) 0 with h | h
      · have h7 : 2 * (Θ + ε - σ) * r ≤ 0 := by nlinarith
        have h8 : 0 ≤ 2 * max (Θ + ε - σ) 0 * U := by
          have := le_max_right (Θ + ε - σ) 0
          positivity
        linarith
      · have h7 : max (Θ + ε - σ) 0 = Θ + ε - σ :=
          max_eq_left h.le
        rw [h7]
        nlinarith
    have h9 : (0:ℝ) ≤ (1 + r) ^ (2 * A) := by positivity
    nlinarith [Real.exp_pos (2 * (Θ + ε - σ) * r), sq_nonneg C,
      mul_le_mul h5 h6 (Real.exp_pos _).le (by positivity)]
  calc ∫ r in Ioc (0 : ℝ) U,
      Real.exp (-(2 * σ) * r) * ‖𝒢 r‖ ^ 2
      ≤ ∫ _r in Ioc (0 : ℝ) U, M := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc hpt
        · refine Integrable.mono' (g := fun _ => M)
            (integrableOn_const (by
              rw [Real.volume_Ioc]
              exact ENNReal.ofReal_ne_top))
            ((Continuous.aestronglyMeasurable
              (by fun_prop)).mul
              ((hm.norm.mul hm.norm).congr
                (Filter.Eventually.of_forall fun r =>
                  (pow_two ‖𝒢 r‖).symm))) ?_
          refine (ae_restrict_iff' measurableSet_Ioc).mpr
            (ae_of_all _ ?_)
          intro r hr
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact hpt r hr
        · exact integrableOn_const (by
            rw [Real.volume_Ioc]
            exact ENNReal.ofReal_ne_top)
    _ ≤ M * (U + 1) := by
        rw [setIntegral_const, smul_eq_mul]
        have h1 : volume.real (Set.Ioc (0:ℝ) U) = U - 0 := by
          rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (by linarith)]
        rw [h1]
        nlinarith
    _ = C ^ 2 * (1 + U) ^ (2 * A) * (U + 1)
        * Real.exp (2 * max (Θ + ε - σ) 0 * U) := by
        rw [hM_def]
        ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Character–residue domination: every nonprincipal character
energy is bounded by `φ(n)` times the residue variance. -/
theorem char_energy_le_variance {n : ℕ} [NeZero n]
    (v : (ZMod n)ˣ → H) (χ : DirichletCharacter ℂ n)
    (hχ : χ ≠ 1) :
    ‖charPacket v χ‖ ^ 2
      ≤ (n.totient : ℝ) * ∑ a : (ZMod n)ˣ,
          ‖v a - (n.totient : ℂ)⁻¹ • ∑ b : (ZMod n)ˣ, v b‖ ^ 2 := by
  classical
  have hpars := residue_parseval v
  have hN0 : 0 < n.totient :=
    Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hNr : (0 : ℝ) < (n.totient : ℝ) := by exact_mod_cast hN0
  have hsingle : ‖charPacket v χ‖ ^ 2
      ≤ ∑ χ' ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
          ‖charPacket v χ'‖ ^ 2 := by
    refine Finset.single_le_sum
      (f := fun χ' => ‖charPacket v χ'‖ ^ 2)
      (fun χ' _ => by positivity) ?_
    exact Finset.mem_erase.mpr ⟨hχ, Finset.mem_univ χ⟩
  have hsum : ∑ χ' ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
      ‖charPacket v χ'‖ ^ 2
      = (n.totient : ℝ) * ∑ a : (ZMod n)ˣ,
          ‖v a - (n.totient : ℂ)⁻¹ • ∑ b : (ZMod n)ˣ, v b‖ ^ 2 := by
    rw [hpars, ← mul_assoc, mul_inv_cancel₀ hNr.ne', one_mul]
  linarith [hsingle, hsum.le, hsum.ge]

/-- `cor:fixed-mod-grh`, assembly: with the per-character
indicator step supplied at every scale (`hind`, displayed),
subpower residue variance at every `σ > 0` forces each
nonprincipal displacement to vanish. -/
theorem fixed_mod_grh (dis : ℝ)
    (hind : ∀ σ : ℝ, 0 < σ → dis ≤ σ ∧ -dis ≤ σ) : dis = 0 := by
  refine gaussian_grh_criterion dis ?_ ?_
  · exact fun σ hσ => (hind σ hσ).1
  · exact fun σ hσ => (hind σ hσ).2

end NCG
