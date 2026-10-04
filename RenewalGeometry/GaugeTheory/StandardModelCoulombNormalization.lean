/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.SpecialUnitaryCoulombNormalization

/-!
# Finite Coulomb normalization for the Standard-Model gauge group `G_SM = S(U(3) × U(2))`
  (`thm:finite-Coulomb-normalization` with the gauge group `eq:gauge-group`)

The gauge group of the manuscript is `G_SM = S(U(3) × U(2)) = {(g₃, g₂) ∈ U(3) × U(2) :
det g₃ · det g₂ = 1}`, with Lie algebra `𝔤_SM = {(X₃, X₂) skew-Hermitian : tr X₃ + tr X₂ = 0}`.
It sits in the unitary group of the finite-dimensional C*-algebra `𝔸_SM = M₃(ℂ) × M₂(ℂ)`
(operator norms), with the invariant Frobenius metric `⟪X, Y⟫ = Re tr(X₃^*Y₃) + Re tr(X₂^*Y₂)`
(`toESM`, `inner_toESM`).

* `toESM_conj_unitary`, `inner_toESM_commutator`: the metric hypotheses of
  `FiniteCoulomb.finite_coulomb_normalization`.
* `finite_coulomb_normalization_SM` (**`thm:finite-Coulomb-normalization` for `G_SM`**): every
  small `𝔤_SM`-valued logarithmic seed admits a site gauge with values in `S(U(3) × U(2))`
  (`(q x).1.det * (q x).2.det = 1`) putting the logarithmic links in exact discrete Coulomb gauge,
  with `𝔤_SM`-valued connection (`tr A₃ + tr A₂ = 0`) and the estimate
  `eq:native-Coulomb-estimate`.

Proof of the determinant clause: along the homotopy `τ(A_s) = 0` for `τ = tr₃ + tr₂`
(`CoulombTrace.trace_linkA_of_solution`), hence `det e^{hA} = e^{τ(hA)} = 1` on every link, so
`D(q) = det q₃ · det q₂` satisfies `D(q_x) D(q_{x+μ})^* = 1`, i.e. `D(q)` is a constant unit `d`;
the constant central phase `λ`, `λ⁵ = d⁻¹`, gives the gauge `λ q ∈ S(U(3) × U(2))` with the same
links (central phases cancel in `q_x U q_{x+μ}^*`).
-/

open NormedSpace Finset Set

namespace RenewalGeometry.StandardModelCoulomb

open scoped Matrix.Norms.L2Operator
open FiniteCoulomb CoulombApriori FrobeniusCoulomb CoulombTrace SeriesLogChart GridSobolev
  SpecialUnitaryCoulomb

noncomputable section

/-- The C*-algebra `M₃(ℂ) × M₂(ℂ)` carrying `U(3) × U(2) ⊃ S(U(3) × U(2))`. -/
abbrev SMAlg := Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ

/-- The Frobenius coordinate space of `𝔸_SM`. -/
abbrev SMEuc := EuclideanSpace ℂ ((Fin 3 × Fin 3) ⊕ (Fin 2 × Fin 2))

/-- The Frobenius identification as a real linear equivalence. -/
def toLinSM : SMAlg ≃ₗ[ℝ] SMEuc :=
  (((Matrix.ofLinearEquiv ℝ).symm.trans (LinearEquiv.curry ℝ ℂ (Fin 3) (Fin 3)).symm).prodCongr
      ((Matrix.ofLinearEquiv ℝ).symm.trans (LinearEquiv.curry ℝ ℂ (Fin 2) (Fin 2)).symm)).trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin 3 × Fin 3) (Fin 2 × Fin 2) ℝ ℂ).symm.trans
      (WithLp.linearEquiv 2 ℝ ((Fin 3 × Fin 3) ⊕ (Fin 2 × Fin 2) → ℂ)).symm)

/-- The invariant Frobenius metric on `𝔤_SM ⊂ M₃(ℂ) × M₂(ℂ)`. -/
def toESM : SMAlg ≃L[ℝ] SMEuc := toLinSM.toContinuousLinearEquiv

/-- `toESM` as a continuous linear map. -/
abbrev toTSM : SMAlg →L[ℝ] SMEuc := (toESM : _)

theorem toESM_inl (X : SMAlg) (p : Fin 3 × Fin 3) : toESM X (Sum.inl p) = X.1 p.1 p.2 := rfl

theorem toESM_inr (X : SMAlg) (p : Fin 2 × Fin 2) : toESM X (Sum.inr p) = X.2 p.1 p.2 := rfl

theorem inner_toESM (X Y : SMAlg) :
    inner ℝ (toESM X) (toESM Y) =
      inner ℝ (frobE X.1) (frobE Y.1) + inner ℝ (frobE X.2) (frobE Y.2) := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, toESM_inl, toESM_inr, frobE_apply]

theorem norm_toESM_sq (X : SMAlg) : ‖toESM X‖ ^ 2 = ‖frobE X.1‖ ^ 2 + ‖frobE X.2‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_toESM, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

theorem fst_mem_unitary {U : SMAlg} (hU : U ∈ unitary SMAlg) : U.1 ∈ unitary _ := by
  rw [Unitary.mem_iff] at hU ⊢
  exact ⟨congrArg Prod.fst hU.1, congrArg Prod.fst hU.2⟩

theorem snd_mem_unitary {U : SMAlg} (hU : U ∈ unitary SMAlg) : U.2 ∈ unitary _ := by
  rw [Unitary.mem_iff] at hU ⊢
  exact ⟨congrArg Prod.snd hU.1, congrArg Prod.snd hU.2⟩

theorem toESM_conj_unitary (U : SMAlg) (hU : U ∈ unitary SMAlg) (X : SMAlg) :
    ‖toESM (U * X * star U)‖ = ‖toESM X‖ := by
  have h := norm_toESM_sq (U * X * star U)
  have h1 := frobE_conj_unitary U.1 (fst_mem_unitary hU) X.1
  have h2 := frobE_conj_unitary U.2 (snd_mem_unitary hU) X.2
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_star, Prod.snd_star] at h
  rw [h1, h2, ← norm_toESM_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem inner_toESM_commutator (a : SMAlg) (ha : star a = -a) (u : SMAlg) :
    inner ℝ (toESM a) (toESM (a * u - u * a)) = 0 := by
  have h1 : star a.1 = -a.1 := congrArg Prod.fst ha
  have h2 : star a.2 = -a.2 := congrArg Prod.snd ha
  rw [inner_toESM]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_mul, Prod.snd_mul]
  rw [inner_frobE_commutator _ h1, inner_frobE_commutator _ h2, add_zero]

/-- `Re(tr X₃ + tr X₂)`. -/
def tauRe : SMAlg →L[ℝ] ℝ :=
  (trRe 3).comp (ContinuousLinearMap.fst ℝ _ _) + (trRe 2).comp (ContinuousLinearMap.snd ℝ _ _)

/-- `Im(tr X₃ + tr X₂)`. -/
def tauIm : SMAlg →L[ℝ] ℝ :=
  (trIm 3).comp (ContinuousLinearMap.fst ℝ _ _) + (trIm 2).comp (ContinuousLinearMap.snd ℝ _ _)

theorem tauRe_apply (X : SMAlg) : tauRe X = (X.1.trace + X.2.trace).re := by
  simp [tauRe, trRe_apply]

theorem tauIm_apply (X : SMAlg) : tauIm X = (X.1.trace + X.2.trace).im := by
  simp [tauIm, trIm_apply]

theorem tauRe_mul_comm (X Y : SMAlg) : tauRe (X * Y) = tauRe (Y * X) := by
  rw [tauRe_apply, tauRe_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_mul, Prod.snd_mul,
    Matrix.trace_mul_comm X.1, Matrix.trace_mul_comm X.2]

theorem tauIm_mul_comm (X Y : SMAlg) : tauIm (X * Y) = tauIm (Y * X) := by
  rw [tauIm_apply, tauIm_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_mul, Prod.snd_mul,
    Matrix.trace_mul_comm X.1, Matrix.trace_mul_comm X.2]

/-- The determinant character `χ(g) = det g₃ · det g₂`. -/
def detSM (g : SMAlg) : ℂ := g.1.det * g.2.det

theorem detSM_exp {Y : SMAlg} (hY : Y.1.trace + Y.2.trace = 0) : detSM (exp Y) = 1 := by
  letI : NormedAlgebra ℚ (Matrix (Fin 3) (Fin 3) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have e1 : (exp Y).1 = exp Y.1 := by convert Prod.fst_exp Y using 2
  have e2 : (exp Y).2 = exp Y.2 := by convert Prod.snd_exp Y using 2
  have d1 := MatrixDetExp.det_exp_eq_complex_exp_trace Y.1
  have d2 := MatrixDetExp.det_exp_eq_complex_exp_trace Y.2
  rw [detSM, e1, e2]
  have e3 : (exp Y.1).det * (exp Y.2).det = Complex.exp (Y.1.trace) * Complex.exp (Y.2.trace) := by
    rw [← d1, ← d2]
  rw [e3, ← Complex.exp_add, hY, Complex.exp_zero]

theorem detSM_mul (g k : SMAlg) : detSM (g * k) = detSM g * detSM k := by
  simp only [detSM, Prod.fst_mul, Prod.snd_mul, Matrix.det_mul]; ring

theorem detSM_star (g : SMAlg) : detSM (star g) = star (detSM g) := by
  simp only [detSM, Prod.fst_star, Prod.snd_star, Matrix.star_eq_conjTranspose,
    Matrix.det_conjTranspose, star_mul']

theorem detSM_unitary {u : SMAlg} (hu : u ∈ unitary SMAlg) : detSM u * star (detSM u) = 1 := by
  rw [← detSM_star, ← detSM_mul, Unitary.mul_star_self_of_mem hu]
  simp [detSM]

theorem detSM_smul (c : ℂ) (g : SMAlg) : detSM (c • g) = c ^ 5 * detSM g := by
  simp only [detSM, Prod.smul_fst, Prod.smul_snd, Matrix.det_smul, Fintype.card_fin]; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- **`thm:finite-Coulomb-normalization` for the Standard-Model gauge group
`G_SM = S(U(3) × U(2))`** (`eq:gauge-group`), with the invariant Frobenius metric.  For every
`ε_* > 0` there are `ε_c, C_c > 0`, independent of the number of sites and of the mesh at fixed
side `L`, such that every `𝔤_SM`-valued logarithmic seed `B` (skew-Hermitian blocks,
`tr B₃ + tr B₂ = 0`) with `‖B‖_{4,h} + ‖𝔽_h(B)‖_{2,h} ≤ ε_c` admits a site gauge `q` with values
in `S(U(3) × U(2))` such that `A = h⁻¹ Log(q_x e^{hB} q_{x+μ}^*)` (`linkA h B 1 q`,
`FiniteCoulomb.linkA_at_one`) is `𝔤_SM`-valued, `δ_h A = 0`,
`‖A‖_{1,h} + ‖A‖_{4,h} ≤ C_c(‖B‖_{2,h} + ‖𝔽_h(B)‖_{2,h} + ‖B‖²_{4,h})` and `‖A‖_{4,h} ≤ ε_*`. -/
theorem finite_coulomb_normalization_SM (hι : Fintype.card ι = 4) {L : ℝ} (hL : 0 < L)
    {εstar : ℝ} (hεstar : 0 < εstar) :
    ∃ εc Cc : ℝ, 0 < εc ∧ 0 < Cc ∧ ∀ (n : ℕ) [NeZero n] (h : ℝ), 0 < h → (n : ℝ) * h = L →
      ∀ B : ι → (ι → ZMod n) → SMAlg, (∀ μ x, star (B μ x) = -B μ x) →
      (∀ μ x, (B μ x).1.trace + (B μ x).2.trace = 0) →
      oneL4 h toTSM B + curvL2 h toTSM B ≤ εc →
      ∃ q : (ι → ZMod n) → SMAlg,
        (∀ x, q x ∈ unitary SMAlg ∧ (q x).1.det * (q x).2.det = 1) ∧
        (∀ μ x, star (linkA h B 1 q μ x) = -linkA h B 1 q μ x) ∧
        (∀ μ x, (linkA h B 1 q μ x).1.trace + (linkA h B 1 q μ x).2.trace = 0) ∧
        periodicHodgeCodiff h gridStep (bar toTSM (linkA h B 1 q)) = 0 ∧
        oneH1 h toTSM (linkA h B 1 q) + oneL4 h toTSM (linkA h B 1 q) ≤
          Cc * (oneL2 h toTSM B + curvL2 h toTSM B + oneL4 h toTSM B ^ 2) ∧
        oneL4 h toTSM (linkA h B 1 q) ≤ εstar := by
  obtain ⟨εc, Cc, hεc, hCc, H⟩ := finite_coulomb_normalization (ι := ι) toESM hι
    toESM_conj_unitary inner_toESM_commutator hL hεstar
  refine ⟨εc, Cc, hεc, hCc, fun n _ h hh hnh B hB htrB hs => ?_⟩
  obtain ⟨q, hu, -, hskew, hcod, hest, hsmall, γ, hγ0, hγ1, hO, hd⟩ := H n h hh hnh B hB hs
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hreB : ∀ μ x, tauRe (B μ x) = 0 := fun μ x => by
    rw [tauRe_apply, htrB μ x, Complex.zero_re]
  have himB : ∀ μ x, tauIm (B μ x) = 0 := fun μ x => by
    rw [tauIm_apply, htrB μ x, Complex.zero_im]
  have hre1 := trace_linkA_of_solution (T := 1) (γ := γ) toESM tauRe hι tauRe_mul_comm hh hB
    hreB hγ0
  have hre2 := hre1 hO
  have hre3 := hre2 hd
  have hre := hre3 1 h1mem
  have him1 := trace_linkA_of_solution (T := 1) (γ := γ) toESM tauIm hι tauIm_mul_comm hh hB
    himB hγ0
  have him2 := him1 hO
  have him3 := him2 hd
  have him := him3 1 h1mem
  rw [hγ1] at hre him
  have htrA : ∀ μ x, (linkA h B 1 q μ x).1.trace + (linkA h B 1 q μ x).2.trace = 0 := by
    intro μ x
    apply Complex.ext
    · rw [← tauRe_apply]; exact hre μ x
    · rw [← tauIm_apply]; exact him μ x
  -- `detSM q` is constant
  have hp := hO 1 h1mem
  rw [hγ1] at hp
  have hlink : ∀ μ x, detSM (q x) * star (detSM (q (x + gridStep μ))) = 1 := by
    intro μ x
    have hc1 : ‖linkP h B 1 q μ x - 1‖ < 1 := hp.1 μ x
    have hd1' : detSM (exp (h • linkA h B 1 q μ x)) = 1 := by
      refine detSM_exp ?_
      simp only [Prod.smul_fst, Prod.smul_snd, Matrix.trace_smul]
      rw [← smul_add, htrA, smul_zero]
    have hd2 : detSM (exp ((1 : ℝ) • (h • B μ x))) = 1 := by
      refine detSM_exp ?_
      simp only [Prod.smul_fst, Prod.smul_snd, Matrix.trace_smul]
      rw [← smul_add, ← smul_add, htrB, smul_zero, smul_zero]
    have hd1 : detSM (linkP h B 1 q μ x) = 1 := by
      rw [← exp_logChart hc1]
      convert hd1' using 3
      all_goals first
        | exact (h_smul_linkA hh.ne' B 1 q μ x).symm
        | rfl
    have key : detSM (q x) * detSM (exp ((1 : ℝ) • (h • B μ x))) *
        star (detSM (q (x + gridStep μ))) = 1 := by
      rw [← hd1, linkP, detSM_mul, detSM_mul, detSM_star]
    rw [hd2, mul_one] at key
    exact key
  have hstep : ∀ μ x, detSM (q (x + gridStep μ)) = detSM (q x) := by
    intro μ x
    have h1 := hlink μ x
    have h2 := detSM_unitary (hu (x + gridStep μ))
    calc detSM (q (x + gridStep μ)) = detSM (q x) * star (detSM (q (x + gridStep μ))) *
          detSM (q (x + gridStep μ)) := by rw [h1, one_mul]
      _ = detSM (q x) * (detSM (q (x + gridStep μ)) * star (detSM (q (x + gridStep μ)))) := by
          ring
      _ = detSM (q x) := by rw [h2, mul_one]
  have hconst : ∀ x, detSM (q x) = detSM (q 0) := fun x =>
    FaddeevPopov.eq_const_of_fwd_zero (fun y => detSM (q y)) (fun i y => hstep i y) x
  -- the central correction
  set d := detSM (q 0)
  have hdd : d * star d = 1 := detSM_unitary (hu 0)
  have hd0 : d ≠ 0 := by intro h0; rw [h0, zero_mul] at hdd; exact zero_ne_one hdd
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq d⁻¹ (by norm_num : 0 < 5)
  have hnd : Complex.normSq d = 1 := by
    have := hdd
    rw [Complex.star_def, Complex.mul_conj] at this
    exact_mod_cast this
  have hnc : Complex.normSq c = 1 := by
    have := congrArg Complex.normSq hc
    rw [map_pow, map_inv₀, hnd, inv_one] at this
    exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg c) (by norm_num)).1 this
  have hcabs : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hnc, Complex.ofReal_one]
  have hcabs' : star c * c = 1 := by rw [mul_comm, hcabs]
  set q' : (ι → ZMod n) → SMAlg := fun x => c • q x with hq'
  have hlinkP : ∀ μ x, linkP h B 1 q' μ x = linkP h B 1 q μ x := by
    intro μ x
    simp only [linkP, hq', star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hcabs', one_smul]
  have hA : linkA h B 1 q' = linkA h B 1 q := by
    funext μ x; simp only [linkA, hlinkP]
  refine ⟨q', fun x => ⟨?_, ?_⟩, by rw [hA]; exact hskew, by rw [hA]; exact htrA,
    by rw [hA]; exact hcod, by rw [hA]; exact hest, by rw [hA]; exact hsmall⟩
  · rw [Unitary.mem_iff]
    have hu' := Unitary.mem_iff.1 (hu x)
    simp only [hq', star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hu'.1, hu'.2]
    exact ⟨by rw [hcabs, one_smul], by rw [hcabs', one_smul]⟩
  · have := detSM_smul c (q x)
    rw [hc, hconst x, inv_mul_cancel₀ hd0] at this
    exact this

end

end RenewalGeometry.StandardModelCoulomb
