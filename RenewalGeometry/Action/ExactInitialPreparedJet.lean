/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialPreparedSeed
import RenewalGeometry.Action.ExactInitialBalanceMeanJet
import RenewalGeometry.Analysis.RangeReductionUniformBounds
import RenewalGeometry.Analysis.HessianRayIdentification

/-!
# The quadratic jet of the reduced mean map on the balancing seed
  (`thm:supp-action-prepared-chart`, `lem:supp-initial-balance`; emergent-spacetime manuscript)

For a range-reduction packet `D` of the actual constraint map (`ExactInitialRangeUniform.lean`),
free records are parametrized on the ambient phase space `𝒫^r_h` through the kernel projection
`P_K = I - R_h L_h` (scaled so that `‖ι‖ ≤ 1`), and the reduced mean map is
`Θ(z) = P₀ 𝒞_h(ι z + R_h y_h(ι z))`.

* `PK`, `iotaC`, `iotaK`: the kernel projection and the parametrization `ι = c_ι P_K`.
* `derivBound_ThX`: uniform order-three bounds for `Θ` on the uniform ball of
  `RangeUniform.derivBound_meanMap`.
* `hasFDerivAt_ThX_zero`, `ThX_zero`: zero constant and linear jets.
* **`hessian_ThX_seed`** (`½ D²Θ_h = Q_h` on the seed): for the actual action, for every
  `ϑ = (κ, b)`, `½ D²Θ(0)(Z'(ϑ), Z'(ϑ)) = Q_h(ϑ)` (as a vector of `ℝ⁴`), where
  `Z'(ϑ) = c_ι⁻¹ (u_*, p(ϑ))`, i.e. `ι Z'(ϑ) = (u_*, p(ϑ))` is the seed of
  `eq:supp-initial-seed`.  The proof compares `Θ(s Z')` with `P₀𝒞_h(s Z)` to `O(s³)` (the range
  correction is `O(s²)` and `P₀ L_h = 0`), identifies `P₀𝒞_h` near `0` with the spatial means of
  the original lapse–shift rows (`Cmap`), and uses `InitialMeanJet.quadratic_mean_jet_seed`.
-/

open Filter Finset Metric Set
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.PreparedChart

set_option linter.unusedSectionVars false

open QuadJet PeriodicGridSobolev GridLocalOps InitialCalculus InitialRange PreparedSeed
open LyapunovSchmidt HessianRay IteratedDerivBounds UniformDerivBounds LapseHomogeneity
open InitialMeanJet OddPhaseDerivativeReal

variable {N : ℕ} [NeZero N] {r : ℕ}

/-- The range-reduction packets on the grid Sobolev spaces. -/
abbrev RD (N r : ℕ) [NeZero N] := RangeData (XH N r) (YH N r) (Fin 4 → ℝ)

/-! ### The kernel parametrization -/

/-- The kernel projection `P_K = I - R L`. -/
def PK (D : RD N r) : XH N r →L[ℝ] XH N r := ContinuousLinearMap.id ℝ _ - D.R.comp D.L

theorem PK_apply (D : RD N r) (z : XH N r) : PK D z = z - D.R (D.L z) := rfl

theorem L_PK (D : RD N r) (z : XH N r) : D.L (PK D z) = 0 := by
  rw [PK_apply, map_sub, D.hLR _ (D.hPL z), sub_self]

theorem PK_of_ker (D : RD N r) {z : XH N r} (hz : D.L z = 0) : PK D z = z := by
  rw [PK_apply, hz, map_zero, sub_zero]

/-- The parametrization `ι = c_ι P_K` of free records. -/
def iotaC (D : RD N r) (cι : ℝ) : XH N r →L[ℝ] XH N r := cι • PK D

theorem iotaC_apply (D : RD N r) (cι : ℝ) (z : XH N r) : iotaC D cι z = cι • PK D z := rfl

theorem L_iotaC (D : RD N r) (cι : ℝ) (z : XH N r) : D.L (iotaC D cι z) = 0 := by
  rw [iotaC_apply, map_smul, L_PK, smul_zero]

theorem norm_iotaC_le (D : RD N r) {Mk : ℝ} (hMk : 0 ≤ Mk) (hL : ‖D.L‖ ≤ Mk) (z : XH N r) :
    ‖iotaC D (1 + D.a * Mk)⁻¹ z‖ ≤ ‖z‖ := by
  have ha := D.a_nonneg
  have h1 : 0 < 1 + D.a * Mk := by positivity
  rw [iotaC_apply, norm_smul, PK_apply, Real.norm_eq_abs, abs_inv, abs_of_pos h1]
  have h2 : ‖z - D.R (D.L z)‖ ≤ (1 + D.a * Mk) * ‖z‖ := by
    calc ‖z - D.R (D.L z)‖ ≤ ‖z‖ + ‖D.R‖ * (‖D.L‖ * ‖z‖) :=
          (norm_sub_le _ _).trans (add_le_add le_rfl ((D.R.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (D.L.le_opNorm z) (norm_nonneg _))))
      _ ≤ ‖z‖ + D.a * (Mk * ‖z‖) := by gcongr; exact D.ha
      _ = (1 + D.a * Mk) * ‖z‖ := by ring
  calc (1 + D.a * Mk)⁻¹ * ‖z - D.R (D.L z)‖ ≤ (1 + D.a * Mk)⁻¹ * ((1 + D.a * Mk) * ‖z‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ‖z‖ := by field_simp

/-- `ι` as a map into `ker L`. -/
def iotaK (D : RD N r) (cι : ℝ) : XH N r →L[ℝ] D.K :=
  (iotaC D cι).codRestrict D.K fun z => LinearMap.mem_ker.mpr (L_iotaC D cι z)

@[simp] theorem coe_iotaK (D : RD N r) (cι : ℝ) (z : XH N r) :
    ((iotaK D cι z : D.K) : XH N r) = iotaC D cι z := rfl

/-- The reduced mean map on free records, `Θ(z) = P₀𝒞(ιz + R y(ιz))`. -/
def ThX (D : RD N r) (σ δ cι : ℝ) (z : XH N r) : Fin 4 → ℝ := D.meanMap σ δ (iotaC D cι z)

theorem ThX_zero (D : RD N r) {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) (cι : ℝ) :
    ThX D σ δ cι 0 = 0 := by
  simpa [ThX] using D.meanMap_zero hr

theorem hasFDerivAt_ThX_zero (D : RD N r) {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ)
    (hδ : 0 < δ) (cι : ℝ) : HasFDerivAt (ThX D σ δ cι) (0 : XH N r →L[ℝ] (Fin 4 → ℝ)) 0 := by
  have h0 := D.hasFDerivAt_meanMap_zero hr hδ
  have h1 : HasFDerivAt (fun k : D.K => D.meanMap σ δ (k : XH N r)) (0 : D.K →L[ℝ] (Fin 4 → ℝ))
      (iotaK D cι 0) := by simpa using h0
  have := h1.comp (0 : XH N r) (iotaK D cι).hasFDerivAt
  simpa [ThX, Function.comp_def] using this

theorem norm_iotaK_le (D : RD N r) {cι : ℝ} (hι : ∀ z, ‖iotaC D cι z‖ ≤ ‖z‖) :
    ‖iotaK D cι‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [one_mul]; exact hι z

theorem delta0_pos (D : RD N r) (hρ : 0 < D.ρ) {MN : ℝ} (hNb : DerivBound D.N (ball 0 D.ρ) 3 MN)
    {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ) (hδ : 0 < δ) :
    0 < RangeUniform.delta0 D MN σ δ := by
  have h1 := (RangeUniform.hyp D hρ hNb).del_pos
  have h2 := hr.1
  have h3 := UniformImplicit.Mp_pos (RangeUniform.Mf D MN)
  exact lt_min h1 (lt_min hδ (by positivity))

/-- **Uniform order-three bounds for `Θ`** on the uniform ball. -/
theorem derivBound_ThX (D : RD N r) (hρ : 0 < D.ρ) {MN : ℝ}
    (hNb : DerivBound D.N (ball 0 D.ρ) 3 MN) {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ)
    {cι : ℝ} (hι : ∀ z, ‖iotaC D cι z‖ ≤ ‖z‖) :
    DerivBound (ThX D σ δ cι) (ball 0 (RangeUniform.delta0 D MN σ δ)) 3
      (RangeUniform.C3 D MN σ δ) := by
  have hmaps : MapsTo (iotaK D cι) (ball 0 (RangeUniform.delta0 D MN σ δ))
      (ball 0 (RangeUniform.delta0 D MN σ δ)) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    exact (hι z).trans_lt hz
  have h := (RangeUniform.derivBound_meanMap D hρ hNb hr).comp_clm isOpen_ball (iotaK D cι) hmaps
  have hm : max 1 ‖iotaK D cι‖ = 1 := max_eq_left (norm_iotaK_le D hι)
  rw [hm, one_pow, mul_one] at h
  exact h

/-! ### The quadratic jet on the seed -/

/-- The four components `(lapse, shift₁, shift₂, shift₃)` of `Q_h` as a vector of `ℝ⁴`. -/
def eQ (q : ℝ × (Fin 3 → ℝ)) : Fin 4 → ℝ := Fin.cons q.1 q.2

/-- The four spatial means of the encoded original rows. -/
theorem P0L_encY_zero (C : (Site N → ℝ) × (Site N → Fin 3 → ℝ)) :
    P0L r (encY r C) 0 = hN N ^ 3 * ∑ x, C.1 x := by
  rw [P0L_apply]
  simp only [meanG, encY, Fin.cases_zero, GridH.val_mk]
  rw [show hN N = ((N : ℝ))⁻¹ from rfl, inv_pow]

theorem P0L_encY_succ (C : (Site N → ℝ) × (Site N → Fin 3 → ℝ)) (a : Fin 3) :
    P0L r (encY r C) a.succ = hN N ^ 3 * ∑ x, C.2 x a := by
  rw [P0L_apply]
  simp only [meanG, encY, Fin.cases_succ, GridH.val_mk]
  rw [show hN N = ((N : ℝ))⁻¹ from rfl, inv_pow]

/-- The original means, as functions of the decoded data. -/
def mRow (r : ℕ) (R : ℝ) (c : Fin 4) (v : MetF N × MetF N) : ℝ := P0L r (encY r (Cmap 1 R v)) c

theorem mRow_zero (r : ℕ) (R : ℝ) : mRow (N := N) r R 0 = meanLapse 1 R := by
  funext v; rw [mRow, P0L_encY_zero]; rfl

theorem mRow_succ (r : ℕ) (R : ℝ) (a : Fin 3) : mRow (N := N) r R a.succ = meanShift 1 R a := by
  funext v; rw [mRow, P0L_encY_succ]; rfl

/-- `P₀𝒞` has vanishing constant and linear jets at `0`. -/
theorem P0_full_jets (D : RD N r) (hρ : 0 < D.ρ) :
    D.P0 (D.full 0) = 0 ∧ fderiv ℝ (fun X => D.P0 (D.full X)) 0 = 0 := by
  have hfull0 : D.full 0 = 0 := by simp [LyapunovSchmidt.RangeData.full, D.hN0]
  have hDN0 : D.DN 0 = 0 := by
    have := D.hDN 0 (mem_ball_self hρ)
    rw [norm_zero, mul_zero] at this
    exact norm_le_zero_iff.mp this
  have hd : HasFDerivAt D.full D.L 0 := by
    have := D.L.hasFDerivAt.add (D.hN 0 (mem_ball_self hρ))
    rw [hDN0, add_zero] at this
    exact this
  have hd' : HasFDerivAt (fun X => D.P0 (D.full X)) (D.P0.comp D.L) 0 :=
    D.P0.hasFDerivAt.comp 0 hd
  refine ⟨by rw [hfull0, map_zero], ?_⟩
  rw [hd'.fderiv]
  exact ContinuousLinearMap.ext fun x => D.hP0L x

/-- **Closeness of the reduced mean map and `P₀𝒞` on kernel rays**:
`‖Θ(z) - P₀𝒞(z)‖ = O(‖z‖³)` along `z = s Z ∈ ker L`. -/
theorem meanMap_sub_P0_full_le (D : RD N r) {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ)
    (hδ : 0 < δ) {Z : XH N r} (hZ : D.L Z = 0) :
    ∃ s0 > 0, ∃ K3 ≥ 0, ∀ s, 0 < s → s < s0 →
      ‖D.meanMap σ δ (s • Z) - D.P0 (D.full (s • Z))‖ ≤ K3 * s ^ 3 := by
  have ha := D.a_nonneg; have hp := D.p_nonneg; have hC := D.hC
  have hρ : 0 < D.ρ := by
    obtain ⟨h1, h2, h3, -, -⟩ := hr
    nlinarith [mul_nonneg ha h1.le]
  set n := ‖Z‖ with hn
  set q := 2 * D.p * D.C with hq
  have hq0 : 0 ≤ q := by positivity
  have hn0 : 0 ≤ n := norm_nonneg _
  set B := n + D.a * q * n ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨min 1 (min (δ / (n + 1)) (D.ρ / (B + 1))),
    lt_min one_pos (lt_min (by positivity) (by positivity)), ‖D.P0‖ * D.C * B * (D.a * q * n ^ 2),
    by positivity, fun s hs hss => ?_⟩
  have hs1 : s ≤ 1 := (hss.trans_le (min_le_left _ _)).le
  have hsδ : s * n ≤ δ := by
    have h := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mp h
    nlinarith
  have hsρ : s * B < D.ρ := by
    have h := hss.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < B + 1)).mp h
    nlinarith
  set z := s • Z with hzdef
  have hz : D.L z = 0 := by rw [hzdef, map_smul, hZ, smul_zero]
  have hzn : ‖z‖ = s * n := by rw [hzdef, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hzδ : ‖z‖ ≤ δ := hzn ▸ hsδ
  set y := D.sol σ δ z with hydef
  have hy : ‖y‖ ≤ q * (s * n) ^ 2 := by
    have := D.norm_sol_le hr hz hzδ
    rwa [hzn] at this
  have hRy : ‖D.R y‖ ≤ D.a * (q * (s * n) ^ 2) :=
    (D.R.le_opNorm y).trans (mul_le_mul D.ha hy (norm_nonneg _) ha)
  have hss2 : s ^ 2 ≤ s := by nlinarith
  have hRy' : ‖D.R y‖ ≤ s * (D.a * q * n ^ 2) := by
    calc ‖D.R y‖ ≤ D.a * (q * (s * n) ^ 2) := hRy
      _ = s ^ 2 * (D.a * q * n ^ 2) := by ring
      _ ≤ s * (D.a * q * n ^ 2) := mul_le_mul_of_nonneg_right hss2 (by positivity)
  have hx1 : ‖z + D.R y‖ ≤ s * B := by
    calc ‖z + D.R y‖ ≤ ‖z‖ + ‖D.R y‖ := norm_add_le _ _
      _ ≤ s * n + s * (D.a * q * n ^ 2) := add_le_add hzn.le hRy'
      _ = s * B := by rw [hB]; ring
  have hx2 : ‖z‖ ≤ s * B := by
    rw [hzn]; exact mul_le_mul_of_nonneg_left (by rw [hB]; nlinarith [mul_nonneg ha hq0]) hs.le
  have hN := norm_sub_le_of_fderiv_bound D.hN D.hDN D.hC hsρ hx1 hx2
  rw [add_sub_cancel_left] at hN
  have e : D.meanMap σ δ z - D.P0 (D.full z) = D.P0 (D.N (z + D.R y) - D.N z) := by
    rw [D.meanMap_eq, map_sub]
    simp only [LyapunovSchmidt.RangeData.full, hz, zero_add]
    rfl
  rw [e]
  calc ‖D.P0 (D.N (z + D.R y) - D.N z)‖ ≤ ‖D.P0‖ * ‖D.N (z + D.R y) - D.N z‖ :=
        D.P0.le_opNorm _
    _ ≤ ‖D.P0‖ * (D.C * (s * B) * (D.a * (q * (s * n) ^ 2))) :=
        mul_le_mul_of_nonneg_left (hN.trans (mul_le_mul_of_nonneg_left hRy
          (mul_nonneg hC (mul_nonneg hs.le hB0))))
          (norm_nonneg _)
    _ = ‖D.P0‖ * D.C * B * (D.a * q * n ^ 2) * s ^ 3 := by ring

/-- **`½ D²Θ_h(0) = Q_h` on the seed** (`thm:supp-action-prepared-chart`, proof, first step;
`lem:supp-initial-balance`).  Let `D` be a range-reduction packet for the actual constraint map
(`D.L = L_h`, `D.P₀ = P₀`), whose full map agrees near `0` with the encoded original rows
`Cmap 1 R` and has order-three bounds, and let `ι = c_ι P_K` with `‖ι‖ ≤ 1`.  If the quadratic
mean jet of the original rows on the seed is `Q_h` (`InitialMeanJet.quadratic_mean_jet_seed`),
then for every `ϑ` the reduced mean map `Θ = Θ_h ∘ ι` satisfies
`½ D²Θ(0)(c_ι⁻¹ Z(ϑ), c_ι⁻¹ Z(ϑ)) = Q_h(ϑ)` (`ι (c_ι⁻¹ Z(ϑ)) = Z(ϑ) = (u_*, p(ϑ))`). -/
theorem hessian_ThX_seed (D : RD N r) {σ δ cι MN MF R : ℝ}
    (hr : radiiOK D.a D.p D.C D.ρ σ δ) (hδ : 0 < δ) (hρ : 0 < D.ρ)
    (hDL : ∀ X, D.L X = LHfun r X) (hP0 : D.P0 = P0L r)
    (hNb : DerivBound D.N (ball 0 D.ρ) 3 MN) (hFb : DerivBound D.full (ball 0 D.ρ) 3 MF)
    (hι : ∀ z, ‖iotaC D cι z‖ ≤ ‖z‖) (hcι : cι ≠ 0)
    (hfull : ∀ᶠ X in 𝓝 (0 : XH N r), D.full X = encY r (Cmap 1 R (decX X)))
    (hjet : ∀ (κ : ℝ) (b : Fin 3 → ℝ),
      (1 / 2 * fderiv ℝ (fderiv ℝ (meanLapse (N := N) 1 R)) 0 (uSeed N, pSeedF N κ b)
          (uSeed N, pSeedF N κ b) = (InitialBalance.Qh (omega N) (κ, b)).1) ∧
        ∀ a : Fin 3, 1 / 2 * fderiv ℝ (fderiv ℝ (meanShift (N := N) 1 R a)) 0
          (uSeed N, pSeedF N κ b) (uSeed N, pSeedF N κ b) =
            (InitialBalance.Qh (omega N) (κ, b)).2 a)
    (ϑ : ℝ × (Fin 3 → ℝ)) :
    (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (ThX D σ δ cι)) 0 (cι⁻¹ • (Zs0 r + ZsL r ϑ))
      (cι⁻¹ • (Zs0 r + ZsL r ϑ)) = eQ (InitialBalance.Qh (omega N) ϑ) := by
  set Z : XH N r := Zs0 r + ZsL r ϑ with hZdef
  set v : XH N r := cι⁻¹ • Z with hvdef
  have hLZ : D.L Z = 0 := by rw [hDL]; exact LHfun_seed r ϑ
  have hιv : ∀ s : ℝ, iotaC D cι (s • v) = s • Z := by
    intro s
    rw [map_smul, iotaC_apply, hvdef, map_smul, PK_of_ker D hLZ, smul_smul, smul_smul,
      mul_assoc, mul_inv_cancel₀ hcι, mul_one]
  set G : XH N r → (Fin 4 → ℝ) := fun X => D.P0 (D.full X) with hGdef
  have hGb : DerivBound G (ball 0 D.ρ) 3 (‖D.P0‖ * MF) := hFb.clm_comp isOpen_ball D.P0
  obtain ⟨hG0, hdG0⟩ := P0_full_jets D hρ
  -- the two Taylor expansions
  have hTb := derivBound_ThX D hρ hNb hr hι
  have hδ0 := delta0_pos D hρ hNb hr hδ
  have hC3 : 0 ≤ RangeUniform.C3 D MN σ δ := hTb.nonneg (mem_ball_self hδ0)
  have hMF : 0 ≤ ‖D.P0‖ * MF := hGb.nonneg (mem_ball_self hρ)
  have hT := taylor_bound_of_derivBound hTb hC3 (ThX_zero D hr cι)
    (hasFDerivAt_ThX_zero D hr hδ cι).fderiv
  have hG := taylor_bound_of_derivBound hGb hMF hG0 hdG0
  have hT' := ray_of_ball hT v
  have hG' := ray_of_ball hG Z
  obtain ⟨s3, hs3, K3, hK3, h3⟩ := meanMap_sub_P0_full_le D hr hδ hLZ
  set K := RangeUniform.C3 D MN σ δ * ‖v‖ ^ 3 + ‖D.P0‖ * MF * ‖Z‖ ^ 3 + K3 with hKdef
  have hK1 : 0 ≤ RangeUniform.C3 D MN σ δ * ‖v‖ ^ 3 := by positivity
  have hK2 : 0 ≤ ‖D.P0‖ * MF * ‖Z‖ ^ 3 := by positivity
  set s0 := min (RangeUniform.delta0 D MN σ δ / (‖v‖ + 1)) (min (D.ρ / (‖Z‖ + 1)) s3)
  have hs0 : 0 < s0 := lt_min (by positivity) (lt_min (by positivity) hs3)
  have hjetG : (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (ThX D σ δ cι)) 0 v v =
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ G) 0 Z Z := by
    refine eq_of_ray_bounds (φ := fun s => ThX D σ δ cι (s • v)) (ψ := fun s => G (s • Z))
      (K := K) hs0 (fun s hs hss => ?_) (fun s hs hss => ?_) (fun s hs hss => ?_)
    · have h := hT' s hs (hss.trans_le (min_le_left _ _))
      refine h.trans ?_
      have : 0 ≤ s ^ 3 := by positivity
      nlinarith
    · have h := hG' s hs (hss.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      refine h.trans ?_
      have : 0 ≤ s ^ 3 := by positivity
      nlinarith
    · have h := h3 s hs (hss.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
      show ‖D.meanMap σ δ (iotaC D cι (s • v)) - D.P0 (D.full (s • Z))‖ ≤ K * s ^ 3
      rw [hιv]
      refine h.trans ?_
      have : 0 ≤ s ^ 3 := by positivity
      nlinarith
  rw [hjetG]
  -- the components of `D²(P₀𝒞)(0)(Z, Z)` are the original quadratic mean jets
  have hGc : ContDiffAt ℝ 2 G 0 :=
    (hGb.contDiffAt isOpen_ball (mem_ball_self hρ)).of_le (by
      exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hcomp : ∀ c : Fin 4, fderiv ℝ (fderiv ℝ G) 0 Z Z c =
      fderiv ℝ (fderiv ℝ (mRow (N := N) r R c)) 0 (uSeed N, pSeedF N ϑ.1 ϑ.2)
        (uSeed N, pSeedF N ϑ.1 ϑ.2) := by
    intro c
    have heq : (fun X => G X c) =ᶠ[𝓝 0] fun X => mRow r R c (decE r X) := by
      filter_upwards [hfull] with X hX
      simp only [hGdef, hX, hP0, mRow, decE_apply]
    have h := fderiv_fderiv_apply_eq_of_eventuallyEq (decE r) c hGc heq Z Z
    rw [h, map_zero, decE_apply, decX_seed]
  funext c
  rw [Pi.smul_apply, hcomp c, smul_eq_mul]
  cases c using Fin.cases with
  | zero => rw [mRow_zero, (hjet ϑ.1 ϑ.2).1]; rfl
  | succ a => rw [mRow_succ, (hjet ϑ.1 ϑ.2).2 a]; rfl

end RenewalGeometry.ExactPhaseAction.PreparedChart
