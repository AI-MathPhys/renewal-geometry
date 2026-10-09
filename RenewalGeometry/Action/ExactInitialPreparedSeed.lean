/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialRangeUniform

/-!
# The balancing seed in the grid Sobolev phase space
  (`eq:supp-initial-seed`, `thm:supp-action-prepared-chart`; emergent-spacetime manuscript)

The four balancing directions `Z_h(ϑ) = (u_*, p(ϑ))`, `ϑ = (κ, b)`, of `eq:supp-initial-seed`
(`u_* = Σ_i T_i cos(2πx_i)`, `p(ϑ) = -(2/3)κ I + Σ_i b_i T_i sin(2πx_i)`) as elements of the phase
space `𝒫^r_h = (H^{r+2}_h)^6 × (H^{r+1}_h)^6`:

* `norm_cosA_le`, `norm_sinA_le`: the unit Fourier modes `cos(2πx_i)`, `sin(2πx_i)` have grid
  Sobolev norms bounded independently of the cutoff (odd `N ≥ 3`; the difference symbols of the
  unit frequency are bounded by `2π`).
* `Zs0`, `ZsL`: the affine seed `Z(ϑ) = Z₀ + Z_l ϑ` with `‖Z₀‖, ‖Z_l‖ ≤ ζ_r` uniformly in `N`
  (`norm_Zs0_le`, `norm_ZsL_le`).
* `LHfun_Zs0`, `LHfun_ZsL`: the seed lies in `ker L_h` (`R¹(u_*) = 0`, `div p(ϑ) = 0`, exactly, for
  the odd phase derivative).
* `decE`: the decoding `𝒫^r_h ≃ MetF × MetF` as a continuous linear equivalence;
  `decX (Z(ϑ)) = (u_*, p(ϑ))`.
-/

open Filter Finset Metric Set
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.PreparedSeed

set_option linter.unusedSectionVars false

open QuadJet PeriodicGridSobolev PeriodicGridSobolev.Sampling GridLocalOps InitialCalculus
open InitialConstraintLinearRange LatticeTorusPlancherel InitialRange OddPhaseDerivativeReal
open LapseHomogeneity InitialBalancePhase

variable {N : ℕ} [NeZero N]

/-! ### The unit Fourier modes -/

theorem valMinAbs_one' (h3 : 3 ≤ N) : (1 : ZMod N).valMinAbs = 1 := by
  have : Fact (1 < N) := ⟨by omega⟩
  rw [ZMod.valMinAbs_def_pos, ZMod.val_one, ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
  rfl

theorem latticeChar_axis (k : Fin 3) (z : Grid N) :
    latticeChar (Pi.single k 1 : Grid N) z = ZMod.stdAddChar (z k) := by
  rw [latticeChar_comm, latticeChar_single_apply, mul_one]

theorem sobSq_axis (s : ℕ) (k : Fin 3) :
    sobSq s (fun z : Grid N => latticeChar (Pi.single k 1 : Grid N) z) =
      gridWeight s (Pi.single k 1 : Grid N) := by
  rw [sobSq_eq_weight]
  simp only [dft_latticeChar]
  rw [Finset.sum_eq_single (Pi.single k 1 : Grid N)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem abs_freq_axis_le (h3 : 3 ≤ N) (k i : Fin 3) :
    |(freq i (Pi.single k 1 : Grid N) : ℝ)| ≤ 1 := by
  unfold freq
  by_cases hik : i = k
  · subst hik
    rw [Pi.single_eq_same, valMinAbs_one' h3]
    simp
  · rw [Pi.single_eq_of_ne hik]
    simp

theorem gbr_axis_le (h3 : 3 ≤ N) (k : Fin 3) : gbr (Pi.single k 1 : Grid N) ≤ 121 := by
  have hk : ∀ i, kap i (Pi.single k 1 : Grid N) ^ 2 ≤ 40 := fun i => by
    rw [kap_sq_eq]
    have h1 := norm_sym_le i (Pi.single k 1 : Grid N)
    have h2 := abs_freq_axis_le h3 k i
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have h0 : 0 ≤ ‖sym i (Pi.single k 1 : Grid N)‖ := norm_nonneg _
    have h3' : ‖sym i (Pi.single k 1 : Grid N)‖ ≤ 2 * Real.pi := by
      refine h1.trans ?_
      nlinarith [abs_nonneg (freq i (Pi.single k 1 : Grid N) : ℝ)]
    nlinarith
  unfold gbr kapSq
  have hs : ∑ i, kap i (Pi.single k 1 : Grid N) ^ 2 ≤ ∑ _i : Fin 3, (40 : ℝ) :=
    sum_le_sum fun i _ => hk i
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  norm_num at hs
  linarith

/-- The cutoff-independent bound for the `H^s_h` norms of the unit modes. -/
def Bm (s : ℕ) : ℝ := Real.sqrt (((multiIndices s).card : ℝ) * 121 ^ s)

theorem Bm_nonneg (s : ℕ) : 0 ≤ Bm s := Real.sqrt_nonneg _

theorem sobNorm_axis_le (h3 : 3 ≤ N) (s : ℕ) (k : Fin 3) :
    sobNorm s (fun z : Grid N => latticeChar (Pi.single k 1 : Grid N) z) ≤ Bm s := by
  unfold sobNorm Bm
  refine Real.sqrt_le_sqrt ?_
  rw [sobSq_axis]
  refine (gridWeight_le_gbr s _).trans ?_
  have h0 : 0 ≤ gbr (Pi.single k 1 : Grid N) := (zero_le_one.trans (one_le_gbr _))
  gcongr
  exact gbr_axis_le h3 k

theorem sobNorm_reArr_le (s : ℕ) (w : Grid N → ℂ) : sobNorm s (reArr w) ≤ sobNorm s w :=
  Real.sqrt_le_sqrt (sobSq_re_le s w)

/-- The cosine mode `cos(2π x_k)` as an `H^s_h` array. -/
def cosA (s : ℕ) (k : Fin 3) : GridH N s := GridH.mk fun z => Real.cos (2 * Real.pi * (z k).val / N)

/-- The sine mode `sin(2π x_k)` as an `H^s_h` array. -/
def sinA (s : ℕ) (k : Fin 3) : GridH N s := GridH.mk fun z => Real.sin (2 * Real.pi * (z k).val / N)

theorem norm_cosA_le (h3 : 3 ≤ N) (s : ℕ) (k : Fin 3) : ‖cosA (N := N) s k‖ ≤ Bm s := by
  rw [GridH.norm_def]
  have e : GridH.cxv (cosA (N := N) s k) =
      reArr (fun z : Grid N => latticeChar (Pi.single k 1 : Grid N) z) := by
    funext z
    simp only [GridH.cxv, cosA, GridH.val_mk, reArr, latticeChar_axis, re_stdAddChar]
  rw [e]
  exact (sobNorm_reArr_le s _).trans (sobNorm_axis_le h3 s k)

theorem norm_sinA_le (h3 : 3 ≤ N) (s : ℕ) (k : Fin 3) : ‖sinA (N := N) s k‖ ≤ Bm s := by
  rw [GridH.norm_def]
  have e : GridH.cxv (sinA (N := N) s k) =
      reArr ((-Complex.I) • fun z : Grid N => latticeChar (Pi.single k 1 : Grid N) z) := by
    funext z
    simp only [GridH.cxv, sinA, GridH.val_mk, reArr, latticeChar_axis, Pi.smul_apply,
      smul_eq_mul]
    rw [← im_stdAddChar]
    simp [Complex.mul_re]
  rw [e]
  refine (sobNorm_reArr_le s _).trans ?_
  rw [Moser.sobNorm_smul, norm_neg, Complex.norm_I, one_mul]
  exact sobNorm_axis_le h3 s k

/-! ### The seed fields are in `ker L_h` -/

theorem cosMode_toF (k : Fin 3) (z : Site N) :
    InitialBalance.cosMode N k (toF z) = Real.cos (2 * Real.pi * (z k).val / N) := by
  simp [InitialBalance.cosMode, toF, coe_finEquiv_symm]

theorem sinMode_toF (k : Fin 3) (z : Site N) :
    InitialBalance.sinMode N k (toF z) = Real.sin (2 * Real.pi * (z k).val / N) := by
  simp [InitialBalance.sinMode, toF, coe_finEquiv_symm]

theorem T_col (k a : Fin 3) : InitialBalance.T k a k = 0 := by
  rw [isSym3_T k a k]; exact T_diag_row k a

theorem symMat_uSeed (z : Site N) : symMat (uSeed N z) = InitialBalance.uStar N (toF z) :=
  symMat_matToSym (isSym3_uStar _)

theorem symMat_pSeedF (κ : ℝ) (b : Fin 3 → ℝ) (z : Site N) :
    symMat (pSeedF N κ b z) = InitialBalance.pSeed N κ b (toF z) :=
  symMat_matToSym (isSym3_pSeed κ b _)

/-- A field `y ↦ f(y_k) · c` with `c = 0` whenever `k = j` is annihilated by `δ_j`. -/
theorem pd_mode_eq_zero {j k : Fin 3} (f : ZMod N → ℝ) {c : ℝ} (hc : k = j → c = 0) :
    pd j (fun y : Grid N => f (y k) * c) = 0 := by
  by_cases hjk : j = k
  · subst hjk
    have e : (fun y : Grid N => f (y j) * c) = fun _ => (0 : ℝ) := by
      funext y; rw [hc rfl, mul_zero]
    rw [e]; exact pd_const j 0
  · exact pd_of_ne (E := ℝ) hjk (fun a => f a * c)

/-- `R¹(u_*) = 0`: the configuration seed is transverse and trace free for the odd phase
derivative. -/
theorem R1F_uSeed : R1F (uSeed N) = 0 := by
  have hA : ∀ i j, pd j (fun y : Site N => symMat (uSeed N y) i j) = 0 := by
    intro i j
    have e : (fun y : Site N => symMat (uSeed N y) i j) =
        ∑ k, fun y : Grid N => Real.cos (2 * Real.pi * (y k).val / N) * InitialBalance.T k i j := by
      funext y
      rw [symMat_uSeed]
      simp [InitialBalance.uStar, Matrix.sum_apply, Finset.sum_apply, cosMode_toF]
    rw [e, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    exact pd_mode_eq_zero (fun a : ZMod N => Real.cos (2 * Real.pi * a.val / N))
      (fun h => by subst h; exact T_col k i)
  have hB : (fun y : Site N => trS (uSeed N y)) = 0 := by
    funext y
    simp only [uSeed, trS_matToSym, InitialBalance.uStar, Matrix.trace_sum, Matrix.trace_smul,
      InitialBalance.trace_T, smul_zero, Finset.sum_const_zero, Pi.zero_apply]
  funext x
  simp only [R1F, hA, hB, map_zero, Pi.zero_apply, Finset.sum_const_zero, sub_zero]

/-- `div p(ϑ) = 0`: the momentum seed is divergence free for the odd phase derivative. -/
theorem divF_pSeedF (κ : ℝ) (b : Fin 3 → ℝ) : divF (pSeedF N κ b) = 0 := by
  have hA : ∀ j a, pd j (fun y : Site N => symMat (pSeedF N κ b y) j a) = 0 := by
    intro j a
    have e : (fun y : Site N => symMat (pSeedF N κ b y) j a) =
        (fun _ : Grid N => (-(2 / 3) * κ) * (1 : Matrix (Fin 3) (Fin 3) ℝ) j a) +
        ∑ k, fun y : Grid N =>
          Real.sin (2 * Real.pi * (y k).val / N) * (b k * InitialBalance.T k j a) := by
      funext y
      rw [symMat_pSeedF]
      simp [InitialBalance.pSeed, Matrix.sum_apply, Finset.sum_apply, sinMode_toF, mul_comm,
        mul_left_comm, mul_assoc]
    rw [e, map_add, map_sum, pd_const, zero_add]
    refine Finset.sum_eq_zero fun k _ => ?_
    exact pd_mode_eq_zero (fun a : ZMod N => Real.sin (2 * Real.pi * a.val / N))
      (fun h => by subst h; rw [T_diag_row, mul_zero])
  funext x a
  simp only [divF, hA, Pi.zero_apply, Finset.sum_const_zero, mul_zero]

/-! ### The seed in the phase space `𝒫^r_h` -/

/-- A metric field as an `(H^s_h)^6` array. -/
def metH (s : ℕ) (m : MetF N) : MetH N s := fun c => GridH.mk fun y => m y c

@[simp] theorem metOf_metH (s : ℕ) (m : MetF N) : metOf (metH s m) = m := rfl

/-- The decoding `𝒫^r_h ≃ MetF × MetF` as a linear equivalence. -/
def decLE (r : ℕ) : XH N r ≃ₗ[ℝ] MetF N × MetF N where
  toFun := decX
  invFun m := (metH (r + 2) m.1, metH (r + 1) m.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The decoding `𝒫^r_h ≃ MetF × MetF` as a continuous linear equivalence. -/
def decE (r : ℕ) : XH N r ≃L[ℝ] MetF N × MetF N := (decLE r).toContinuousLinearEquiv

@[simp] theorem decE_apply (r : ℕ) (X : XH N r) : decE r X = decX X := rfl

@[simp] theorem decE_symm_apply (r : ℕ) (m : MetF N × MetF N) :
    (decE r).symm m = (metH (r + 2) m.1, metH (r + 1) m.2) := rfl

/-- The coefficients of `T_k` in `Sym₃` coordinates. -/
def tC (k : Fin 3) (c : Fin 6) : ℝ := matToSymLin (InitialBalance.T k) c

/-- The coefficients of the identity in `Sym₃` coordinates. -/
def oC (c : Fin 6) : ℝ := matToSymLin (1 : Matrix (Fin 3) (Fin 3) ℝ) c

/-- `Σ_k Σ_c |T_k,c|` (a fixed number). -/
def cT : ℝ := ∑ k : Fin 3, ∑ c : Fin 6, |tC k c|

/-- `Σ_c |I_c|` (a fixed number). -/
def c1 : ℝ := ∑ c : Fin 6, |oC c|

theorem abs_oC_le (c : Fin 6) : |oC c| ≤ c1 :=
  single_le_sum (f := fun c => |oC c|) (fun _ _ => abs_nonneg _) (mem_univ c)

theorem cT_nonneg : 0 ≤ cT := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

theorem c1_nonneg : 0 ≤ c1 := sum_nonneg fun _ _ => abs_nonneg _

theorem sum_abs_tC_le (c : Fin 6) : ∑ k : Fin 3, |tC k c| ≤ cT :=
  sum_le_sum fun k _ => (single_le_sum (f := fun c => |tC k c|)
    (fun _ _ => abs_nonneg _) (mem_univ c))

theorem metH_uSeed (s : ℕ) (c : Fin 6) :
    metH s (uSeed N) c = ∑ k, tC k c • cosA s k := by
  refine GridH.ext fun z => ?_
  simp [metH, uSeed, InitialBalance.uStar, cosA, tC, cosMode_toF, GridH.val_sum,
    Finset.sum_apply, mul_comm]

theorem metH_pSeedF (s : ℕ) (κ : ℝ) (b : Fin 3 → ℝ) (c : Fin 6) :
    metH s (pSeedF N κ b) c =
      (-(2 / 3) * κ * oC c) • GridH.constArr s 1 + ∑ k, (b k * tC k c) • sinA s k := by
  refine GridH.ext fun z => ?_
  simp [metH, pSeedF, InitialBalance.pSeed, sinA, tC, oC, sinMode_toF, GridH.val_sum,
    Finset.sum_apply, mul_comm, mul_left_comm, mul_assoc]

/-- The fixed part `Z₀ = (u_*, 0)` of the seed. -/
def Zs0 (r : ℕ) : XH N r := (metH (r + 2) (uSeed N), 0)

/-- One component of the balancing part of the seed. -/
def ZsLc (r : ℕ) (c : Fin 6) : (ℝ × (Fin 3 → ℝ)) →L[ℝ] GridH N (r + 1) :=
  ((-(2 / 3) * oC c) • ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)).smulRight
      (GridH.constArr (r + 1) 1) +
    ∑ k, (tC k c • (ContinuousLinearMap.proj k).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))).smulRight (sinA (r + 1) k)

/-- The balancing part `Z_l ϑ = (0, p(ϑ))` of the seed. -/
def ZsL (r : ℕ) : (ℝ × (Fin 3 → ℝ)) →L[ℝ] XH N r :=
  (ContinuousLinearMap.inr ℝ (MetH N (r + 2)) (MetH N (r + 1))).comp
    (ContinuousLinearMap.pi fun c => ZsLc r c)

theorem ZsL_apply (r : ℕ) (ϑ : ℝ × (Fin 3 → ℝ)) :
    ZsL (N := N) r ϑ = (0, metH (r + 1) (pSeedF N ϑ.1 ϑ.2)) := by
  refine Prod.ext rfl (funext fun c => ?_)
  show ZsLc r c ϑ = metH (r + 1) (pSeedF N ϑ.1 ϑ.2) c
  rw [metH_pSeedF]
  simp only [ZsLc, ContinuousLinearMap.coe_comp, Function.comp_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.coe_fst', _root_.sum_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  congr 1
  · congr 1; ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 1; ring

/-- The seed `Z(ϑ) = Z₀ + Z_l ϑ = (u_*, p(ϑ))`. -/
theorem decX_seed (r : ℕ) (ϑ : ℝ × (Fin 3 → ℝ)) :
    decX (Zs0 (N := N) r + ZsL r ϑ) = (uSeed N, pSeedF N ϑ.1 ϑ.2) := by
  rw [ZsL_apply]
  refine Prod.ext ?_ ?_
  · funext z c; simp [decX, Zs0]
  · funext z c; simp [decX, Zs0]

/-- **The seed lies in `ker L_h`** (odd phase derivative). -/
theorem LHfun_seed (r : ℕ) (ϑ : ℝ × (Fin 3 → ℝ)) : LHfun r (Zs0 (N := N) r + ZsL r ϑ) = 0 := by
  have e1 : metOf (Zs0 (N := N) r + ZsL r ϑ).1 = uSeed N := congrArg Prod.fst (decX_seed r ϑ)
  have e2 : metOf (Zs0 (N := N) r + ZsL r ϑ).2 = pSeedF N ϑ.1 ϑ.2 :=
    congrArg Prod.snd (decX_seed r ϑ)
  funext c
  refine GridH.ext fun x => ?_
  cases c using Fin.cases with
  | zero =>
    simp only [LHfun, encY, Fin.cases_zero, GridH.val_mk, e1, R1F_uSeed, Pi.zero_apply,
      mul_zero]
    rfl
  | succ a =>
    simp only [LHfun, encY, Fin.cases_succ, GridH.val_mk, e2, divF_pSeedF, Pi.zero_apply]
    rfl

/-- The cutoff-independent seed bound `ζ_r`. -/
def zetaS (r : ℕ) : ℝ := c1 + cT * (Bm (r + 1) + Bm (r + 2))

theorem zetaS_nonneg (r : ℕ) : 0 ≤ zetaS r := by
  have hB1 := Bm_nonneg (r + 1); have hB2 := Bm_nonneg (r + 2)
  have hc1 := c1_nonneg; have hcT := cT_nonneg
  unfold zetaS; positivity

theorem norm_Zs0_le (h3 : 3 ≤ N) (r : ℕ) : ‖Zs0 (N := N) r‖ ≤ zetaS r := by
  have hB1 := Bm_nonneg (r + 1); have hB2 := Bm_nonneg (r + 2)
  have hc1 := c1_nonneg; have hcT := cT_nonneg
  have hz := zetaS_nonneg r
  refine norm_prod_le_iff.mpr ⟨?_, by rw [show (Zs0 (N := N) r).2 = 0 from rfl, norm_zero]; exact hz⟩
  refine (pi_norm_le_iff_of_nonneg hz).mpr fun c => ?_
  show ‖metH (r + 2) (uSeed N) c‖ ≤ _
  rw [metH_uSeed]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖tC k c • cosA (N := N) (r + 2) k‖ ≤ ∑ k : Fin 3, |tC k c| * Bm (r + 2) := by
        refine sum_le_sum fun k _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_cosA_le h3 _ k) (abs_nonneg _)
    _ = (∑ k : Fin 3, |tC k c|) * Bm (r + 2) := by rw [sum_mul]
    _ ≤ cT * Bm (r + 2) := mul_le_mul_of_nonneg_right (sum_abs_tC_le c) hB2
    _ ≤ zetaS r := by unfold zetaS; nlinarith

theorem norm_ZsL_le (h3 : 3 ≤ N) (r : ℕ) : ‖ZsL (N := N) r‖ ≤ zetaS r := by
  have hB1 := Bm_nonneg (r + 1); have hB2 := Bm_nonneg (r + 2)
  have hc1 := c1_nonneg; have hcT := cT_nonneg
  have hz := zetaS_nonneg r
  refine ContinuousLinearMap.opNorm_le_bound _ hz fun ϑ => ?_
  have hκ : |ϑ.1| ≤ ‖ϑ‖ := by
    have := norm_fst_le ϑ; rwa [Real.norm_eq_abs] at this
  have hb : ∀ k, |ϑ.2 k| ≤ ‖ϑ‖ := fun k => by
    have h1 := norm_le_pi_norm ϑ.2 k
    have h2 := norm_snd_le ϑ
    rw [Real.norm_eq_abs] at h1
    linarith
  have hn : 0 ≤ ‖ϑ‖ := norm_nonneg _
  rw [ZsL_apply]
  refine norm_prod_le_iff.mpr ⟨by simpa using mul_nonneg hz hn, ?_⟩
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hz hn)).mpr fun c => ?_
  show ‖metH (r + 1) (pSeedF N ϑ.1 ϑ.2) c‖ ≤ _
  rw [metH_pSeedF]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(-(2 / 3) * ϑ.1 * oC c) • GridH.constArr (N := N) (r + 1) 1‖ ≤ c1 * ‖ϑ‖ := by
    rw [norm_smul, GridH.norm_constArr, abs_one, mul_one, Real.norm_eq_abs, abs_mul, abs_mul]
    have := abs_oC_le c
    have h23 : |(-(2 / 3) : ℝ)| ≤ 1 := by norm_num [abs_div]
    calc |(-(2 / 3) : ℝ)| * |ϑ.1| * |oC c| ≤ 1 * ‖ϑ‖ * c1 := by
          gcongr
      _ = c1 * ‖ϑ‖ := by ring
  have h2 : ‖∑ k, (ϑ.2 k * tC k c) • sinA (N := N) (r + 1) k‖ ≤ cT * Bm (r + 1) * ‖ϑ‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖(ϑ.2 k * tC k c) • sinA (N := N) (r + 1) k‖
        ≤ ∑ k : Fin 3, |tC k c| * (Bm (r + 1) * ‖ϑ‖) := by
          refine sum_le_sum fun k _ => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_mul]
          have := norm_sinA_le (N := N) h3 (r + 1) k
          calc |ϑ.2 k| * |tC k c| * ‖sinA (N := N) (r + 1) k‖
              ≤ ‖ϑ‖ * |tC k c| * Bm (r + 1) := by gcongr; exact hb k
            _ = |tC k c| * (Bm (r + 1) * ‖ϑ‖) := by ring
      _ = (∑ k : Fin 3, |tC k c|) * (Bm (r + 1) * ‖ϑ‖) := by rw [sum_mul]
      _ ≤ cT * (Bm (r + 1) * ‖ϑ‖) :=
          mul_le_mul_of_nonneg_right (sum_abs_tC_le c) (by positivity)
      _ = cT * Bm (r + 1) * ‖ϑ‖ := by ring
  calc _ ≤ c1 * ‖ϑ‖ + cT * Bm (r + 1) * ‖ϑ‖ := add_le_add h1 h2
    _ ≤ zetaS r * ‖ϑ‖ := by
        unfold zetaS
        nlinarith [mul_nonneg hcT hB2, mul_nonneg (mul_nonneg hcT hB2) hn]

end RenewalGeometry.ExactPhaseAction.PreparedSeed
