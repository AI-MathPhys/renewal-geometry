/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.NativeRecordNormalization
import RenewalGeometry.GaugeTheory.StandardModelCoulombNormalization
import RenewalGeometry.GaugeTheory.RootedCertificateInvariance

/-!
# The rooted Coulomb normalization for `G_SM = S(U(3) × U(2))`, with its logarithm chart
  (`prop:rooted-gauge-certificate` and `thm:finite-Wilson-zero-defect`, gauge group
  `eq:gauge-group`; Einstein–SM action closure)

For links with values in `G_SM = {u ∈ U(3) × U(2) : det u₃ · det u₂ = 1}`:

* `holonomy_mem`: holonomies of links in a subgroup stay in it (so the tree paths `C_x` and the
  rooted words `W^𝔗` are in `G_SM`);
* `trace_logChart_eq_zero`: the logarithm of a word of `G_SM` in the admissible chart
  (`‖W - 1‖ ≤ 1/64`) is `𝔤_SM`-valued, `tr Y₃ + tr Y₂ = 0` (`det e^Y = e^{tr Y}` and smallness);
* **`rooted_coulomb_normalization_chart_SM`**: if the rooted certificate is `≤ ε_c`, a site gauge
  `g` **with values in `G_SM`** (the exact tree gauge, then the Coulomb gauge of
  `thm:finite-Coulomb-normalization` corrected by a constant central phase) puts the original
  links in exact small discrete Coulomb gauge, the normalized links lying in the logarithm chart.
-/

open NormedSpace Finset Set Filter

namespace RenewalGeometry.NativeRecordNormSM

open scoped Matrix.Norms.L2Operator
open SeriesLogChart GridSobolev CoulombApriori CurvatureSplit FiniteCoulomb RootedWilson
  CoulombHomotopy RootedCoulomb StandardModelCoulomb CoulombTrace

noncomputable section

/-! ### Holonomies in a subgroup -/

theorem holonomy_mem {V E : Type*} {src tgt : E → V} {G : Type*} [Group G] (K : Subgroup G)
    {U : E → G} (hU : ∀ e, U e ∈ K) {a b : V} (w : LatticeWalk src tgt a b) :
    w.holonomy U ∈ K := by
  induction w with
  | nil v => exact K.one_mem
  | cons s w ih =>
    rw [LatticeWalk.holonomy_cons]
    refine K.mul_mem ih ?_
    rcases s with ⟨e, b⟩
    cases b
    · exact K.inv_mem (hU e)
    · exact hU e

/-- The determinant character on the unitary group of `M₃(ℂ) × M₂(ℂ)`. -/
def detHom : unitary SMAlg →* ℂ where
  toFun u := detSM (u : SMAlg)
  map_one' := by simp [detSM]
  map_mul' u v := by
    change detSM ((u : SMAlg) * (v : SMAlg)) = _
    exact detSM_mul _ _

/-- `G_SM = S(U(3) × U(2))` as a subgroup of the unitary group. -/
def GSM : Subgroup (unitary SMAlg) := detHom.ker

theorem mem_GSM {u : unitary SMAlg} : u ∈ GSM ↔ detSM (u : SMAlg) = 1 := Iff.rfl

/-! ### `𝔤_SM`-valued logarithms -/

theorem norm_trace_le {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : ‖A.trace‖ ≤ m * ‖A‖ := by
  unfold Matrix.trace
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖Matrix.diag A i‖ ≤ ∑ _i : Fin m, ‖A‖ :=
        Finset.sum_le_sum fun i _ => RootedCertificate.entry_le_opNorm A i i
    _ = m * ‖A‖ := by simp

theorem det_exp_SM (Y : SMAlg) :
    detSM (exp Y) = Complex.exp (Y.1.trace + Y.2.trace) := by
  let _ : NormedAlgebra ℚ (Matrix (Fin 3) (Fin 3) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  let _ : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have e1 : (exp Y).1 = exp Y.1 := by convert Prod.fst_exp Y using 2
  have e2 : (exp Y).2 = exp Y.2 := by convert Prod.snd_exp Y using 2
  rw [detSM, e1, e2, MatrixDetExp.det_exp_eq_complex_exp_trace,
    MatrixDetExp.det_exp_eq_complex_exp_trace, ← Complex.exp_add]

/-- **The logarithm of a small `G_SM` word is `𝔤_SM`-valued.** -/
theorem trace_logChart_eq_zero {W : SMAlg} (hW : ‖W - 1‖ ≤ 1 / 64) (hd : detSM W = 1) :
    (logChart W).1.trace + (logChart W).2.trace = 0 := by
  set Y := logChart W
  have hY : ‖Y‖ ≤ 1 / 32 := (norm_logChart_le (hW.trans (by norm_num))).trans (by linarith)
  have hexp : exp Y = W := exp_logChart (hW.trans_lt (by norm_num))
  have h1 : Complex.exp (Y.1.trace + Y.2.trace) = 1 := by rw [← det_exp_SM, hexp, hd]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h1
  have hb : ‖Y.1.trace + Y.2.trace‖ ≤ 5 / 32 := by
    have a1 := norm_trace_le Y.1
    have a2 := norm_trace_le Y.2
    have b1 : ‖Y.1‖ ≤ ‖Y‖ := norm_fst_le Y
    have b2 : ‖Y.2‖ ≤ ‖Y‖ := norm_snd_le Y
    push_cast at a1 a2
    calc ‖Y.1.trace + Y.2.trace‖ ≤ ‖Y.1.trace‖ + ‖Y.2.trace‖ := norm_add_le _ _
      _ ≤ 3 * ‖Y‖ + 2 * ‖Y‖ := by nlinarith [norm_nonneg Y.1, norm_nonneg Y.2]
      _ ≤ 5 / 32 := by linarith
  rw [hk] at hb ⊢
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  · exfalso
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    have hn : ‖(k : ℂ) * (2 * Real.pi * Complex.I)‖ = |(k : ℝ)| * (2 * Real.pi) := by
      rw [norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [hn] at hb
    nlinarith [Real.pi_gt_three]

/-! ### The rooted normalization in `G_SM` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

theorem trace_treeSeed {m : ℕ} [NeZero m] {h : ℝ} {o : ι → ZMod m}
    (w : ∀ v, LatticeWalk (latSrc (ι := ι) (n := m)) latTgt v o)
    (U : (ι → ZMod m) × ι → unitary SMAlg) (hU : ∀ e, U e ∈ GSM)
    (hadm : ∀ μ x, ‖((rootedWord w U (x, μ) : unitary SMAlg) : SMAlg) - 1‖ ≤ 1 / 64) (μ : ι)
    (x : ι → ZMod m) : (treeSeed h w U μ x).1.trace + (treeSeed h w U μ x).2.trace = 0 := by
  have hW : rootedWord w U (x, μ) ∈ GSM := by
    unfold rootedWord rootedPath
    exact GSM.mul_mem (GSM.mul_mem (holonomy_mem GSM hU _) (hU _))
      (GSM.inv_mem (holonomy_mem GSM hU _))
  have h0 := trace_logChart_eq_zero (hadm μ x) (mem_GSM.1 hW)
  simp only [treeSeed, Prod.smul_fst, Prod.smul_snd, Matrix.trace_smul]
  rw [← smul_add]
  exact (congrArg (fun t : ℂ => h⁻¹ • t) h0).trans (smul_zero _)

/-- **The rooted Coulomb normalization in `G_SM`, with its chart** (`prop:rooted-gauge-certificate`,
Coulomb clause, for the gauge group `eq:gauge-group`): for links with values in `G_SM`, a small
rooted certificate yields a site gauge with values in `G_SM` putting the original links in exact
small discrete Coulomb gauge, with the normalized links in the logarithm chart. -/
theorem rooted_coulomb_normalization_chart_SM (hι : Fintype.card ι = 4) {L : ℝ} (hL : 0 < L)
    {εstar : ℝ} (hεstar : 0 < εstar) :
    ∃ εc Cc : ℝ, 0 < εc ∧ 0 < Cc ∧ ∀ (m : ℕ) [NeZero m] (h : ℝ), 0 < h → (m : ℝ) * h = L →
      ∀ (o : ι → ZMod m) (w : ∀ v, LatticeWalk (latSrc (ι := ι) (n := m)) latTgt v o)
        (U : (ι → ZMod m) × ι → unitary SMAlg), (∀ e, U e ∈ GSM) →
      (∀ μ x, ‖((rootedWord w U (x, μ) : unitary SMAlg) : SMAlg) - 1‖ ≤ 1 / 64) →
      (∀ μ ν x, ‖litPlaq U μ ν x - 1‖ < 1) →
      oneL4 h toTSM (treeSeed h w U) + litCurvL2 toESM h U ≤ εc →
      ∃ g : (ι → ZMod m) → unitary SMAlg, (∀ x, g x ∈ GSM) ∧
        let A : ι → (ι → ZMod m) → SMAlg := fun μ x =>
          h⁻¹ • logChart ((gaugeLinks latSrc latTgt g U (x, μ) : unitary SMAlg) : SMAlg)
        (∀ μ x, ‖((gaugeLinks latSrc latTgt g U (x, μ) : unitary SMAlg) : SMAlg) - 1‖ < 1) ∧
        (∀ μ x, star (A μ x) = -A μ x) ∧
        periodicHodgeCodiff h gridStep (bar toTSM A) = 0 ∧
        oneH1 h toTSM A + oneL4 h toTSM A ≤
          Cc * (oneL2 h toTSM (treeSeed h w U) + litCurvL2 toESM h U +
            oneL4 h toTSM (treeSeed h w U) ^ 2) ∧
        oneL4 h toTSM A ≤ εstar := by
  obtain ⟨εc, Cc, hεc, hCc, H⟩ := finite_coulomb_normalization (ι := ι) toESM hι
    toESM_conj_unitary inner_toESM_commutator hL hεstar
  refine ⟨εc, Cc, hεc, hCc, fun m _ h hh hmh o w U hUK hadm hplaq hcert => ?_⟩
  have hcurv := curvL2_treeSeed toESM toESM_conj_unitary hh.ne' w U hadm hplaq
  rw [← hcurv] at hcert ⊢
  set B := treeSeed h w U with hBdef
  have hB : ∀ μ x, star (B μ x) = -B μ x := treeSeed_skew w U hadm
  have htrB : ∀ μ x, (B μ x).1.trace + (B μ x).2.trace = 0 := trace_treeSeed w U hUK hadm
  obtain ⟨q, hu, -, hskew, hcod, hest, hsmall, γ, hγ0, hγ1, hO, hd⟩ := H m h hh hmh B hB hcert
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hreB : ∀ μ x, tauRe (B μ x) = 0 := fun μ x => by
    rw [tauRe_apply, htrB μ x, Complex.zero_re]
  have himB : ∀ μ x, tauIm (B μ x) = 0 := fun μ x => by
    rw [tauIm_apply, htrB μ x, Complex.zero_im]
  have hre := trace_linkA_of_solution (T := 1) (γ := γ) toESM tauRe hι tauRe_mul_comm hh hB
    hreB hγ0 hO hd 1 h1mem
  have him := trace_linkA_of_solution (T := 1) (γ := γ) toESM tauIm hι tauIm_mul_comm hh hB
    himB hγ0 hO hd 1 h1mem
  rw [hγ1] at hre him
  have htrA : ∀ μ x, (linkA h B 1 q μ x).1.trace + (linkA h B 1 q μ x).2.trace = 0 := by
    intro μ x
    apply Complex.ext
    · rw [← tauRe_apply]; exact hre μ x
    · rw [← tauIm_apply]; exact him μ x
  have hp := hO 1 h1mem
  rw [hγ1] at hp
  -- `detSM q` is constant
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
  set q' : (ι → ZMod m) → SMAlg := fun x => c • q x with hq'
  have hlinkP : ∀ μ x, linkP h B 1 q' μ x = linkP h B 1 q μ x := by
    intro μ x
    simp only [linkP, hq', star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hcabs', one_smul]
  have hA : linkA h B 1 q' = linkA h B 1 q := by
    funext μ x; simp only [linkA, hlinkP]
  have hq'u : ∀ x, q' x ∈ unitary SMAlg := by
    intro x
    rw [Unitary.mem_iff]
    have hu' := Unitary.mem_iff.1 (hu x)
    simp only [hq', star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hu'.1, hu'.2]
    exact ⟨by rw [hcabs, one_smul], by rw [hcabs', one_smul]⟩
  have hq'd : ∀ x, detSM (q' x) = 1 := by
    intro x
    have := detSM_smul c (q x)
    rw [hc, hconst x, inv_mul_cancel₀ hd0] at this
    exact this
  -- the total gauge
  set C := rootedPath w U
  refine ⟨fun x => ⟨q' x, hq'u x⟩ * C x, fun x => ?_, ?_⟩
  · refine GSM.mul_mem (mem_GSM.2 (hq'd x)) ?_
    exact holonomy_mem GSM hUK _
  have hP : ∀ μ x, ((gaugeLinks latSrc latTgt
      (fun x => (⟨q' x, hq'u x⟩ : unitary SMAlg) * C x) U (x, μ) : unitary SMAlg) : SMAlg) =
      linkP h B 1 q' μ x := by
    intro μ x
    simp only [linkP, one_smul]
    rw [hBdef, exp_treeSeed hh.ne' w U hadm]
    simp only [gaugeLinks_apply, latTgt, latSrc, Submonoid.coe_mul, coe_inv_unitary, star_mul,
      rootedWord, rootedPath, mul_assoc]
    rfl
  have hAeq : ∀ μ x, h⁻¹ • logChart ((gaugeLinks latSrc latTgt
      (fun x => (⟨q' x, hq'u x⟩ : unitary SMAlg) * C x) U (x, μ) : unitary SMAlg) : SMAlg) =
      linkA h B 1 q μ x := by
    intro μ x
    rw [hP, ← hA]
    rfl
  simp only [hAeq]
  exact ⟨fun μ x => by rw [hP, hlinkP]; exact hp.1 μ x, hskew, hcod, hest, hsmall⟩

end

end RenewalGeometry.NativeRecordNormSM
