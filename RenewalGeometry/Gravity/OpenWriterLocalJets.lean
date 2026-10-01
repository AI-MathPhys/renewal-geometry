/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterTimeJets
import RenewalGeometry.DiscreteAnalysis.PeriodicGridSobolevSpace

/-!
# Inverse-mesh vector-field bounds and time jets of the local finite writer
  (`lem:supp-open-local-jets`, `eq:supp-open-local-vector-bounds`,
  `eq:supp-open-inverse-time-jets`; emergent-spacetime manuscript)

The phase space is `𝒳^s_h = (H^{s+1}_h)^{10} × (H^s_h)^{10}` (`XS N s`: ten upper components
`μ ≤ ν` of the position `q` and the velocity `v`, each a `GridH` normed space; the norm is the
maximum of the component norms, equivalent to `‖X‖_{𝒳^s_h}` of `eq:supp-open-norms` with
mesh-independent constants: `XS.norm_le_Xnorm`, `XS.Xnorm_le_norm`).

* `lawField s B X = (v, V_{B,h}(q, v))`: **the differential writer** `𝓕_{B,h}` of the law family
  `eq:supp-law-family` (the open writer is `B = 0`) on symmetric ten-component records
  (`recOf`), with `V_{B,h} = lawAccel B`.
* `fieldF`: the same map written as a composition of mesh-uniform building blocks (pointwise
  analytic coefficient maps `a⁻¹, c^{ij}, b^i, 𝖦`, the product of `H^s_h`, the differences
  `D_i^±` from `H^{s+1}_h`, and the inverse-mesh operators `D_i⁻, D_i⁰ : H^s_h → H^s_h`,
  `h²Λ_h² : H^{s+1}_h → H^s_h`, `v ↦ v : H^s_h → H^{s+1}_h` of norm `O(h^{-1})`);
  `fieldF_eq : fieldF = lawField`.
* `local_vector_bounds` (**`eq:supp-open-local-vector-bounds`**): for `s ≥ 2`, every order
  `K` and every mark bound `b`, there are `δ > 0` and `C`, independent of the mesh and of the
  mark `B` (`|B_{kl}| ≤ b`), such that on the ball `‖X‖ < δ` the field is `C^∞` with
  `‖D^j 𝓕_{B,h}(X)‖ ≤ C h^{-1}` for all `j ≤ K` (in particular `1 ≤ j ≤ 9`) and
  `‖𝓕_{B,h}(X)‖ ≤ C h^{-1} ‖X‖`.
* `inverse_time_jets` (**`eq:supp-open-inverse-time-jets`**): along an exact solution
  `X' = 𝓕_{B,h}(X)` whose source `X(t)` lies in the ball with `‖X(t)‖ ≤ ε`,
  `‖∂_t^j q(t)‖_{H^s_h} ≤ C ε h^{1-j}` for `1 ≤ j ≤ K`; the jets are `J_j(X(t))` with
  `J_1 = 𝓕`, `J_{j+1} = DJ_j 𝓕` (`IteratedDerivBounds.vfJet`).
* `jets_local` (**locality**): `J_j(X)` agrees with `J_j(X')` on the box of radius `ρ` around
  any site as soon as `X` and `X'` agree on the box of radius `ρ + 2j`: the jet of order `j` is a
  function of a fixed-radius neighbourhood of the source, independent of `h`.
-/

open Set Metric Filter Topology Finset
open scoped NNReal BigOperators ContDiff

namespace RenewalGeometry.OpenWriterLocalJets

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterEnergyEstimate OpenWriterLifespan PeriodicGridSobolev.GridH IteratedDerivBounds
open PeriodicGridSobolev (GridH sobNorm invConst invConst_nonneg sobNorm_succ_le_inverse)

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### Difference operators between grid Sobolev spaces -/

/-- `D_i⁺` as a linear map of real arrays. -/
def DpLin (i : Fin 3) : (Grid N → ℝ) →ₗ[ℝ] (Grid N → ℝ) where
  toFun := OpenWriterEnergy.Dp i
  map_add' u w := by funext x; simp only [Dp_apply, Pi.add_apply]; ring
  map_smul' c u := by funext x; simp only [Dp_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- `D_i⁻` as a linear map of real arrays. -/
def DmLin (i : Fin 3) : (Grid N → ℝ) →ₗ[ℝ] (Grid N → ℝ) where
  toFun := OpenWriterEnergy.Dm i
  map_add' u w := by funext x; simp only [Dm_apply, Pi.add_apply]; ring
  map_smul' c u := by funext x; simp only [Dm_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- `D_i⁰` as a linear map of real arrays. -/
def D0Lin (i : Fin 3) : (Grid N → ℝ) →ₗ[ℝ] (Grid N → ℝ) where
  toFun := OpenWriterEnergy.D0 i
  map_add' u w := by
    funext x; simp only [D0_apply, Dp_apply, Dm_apply, Pi.add_apply]; ring
  map_smul' c u := by
    funext x; simp only [D0_apply, Dp_apply, Dm_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- `h² Λ_h²` as a linear map of real arrays. -/
def lap2Lin : (Grid N → ℝ) →ₗ[ℝ] (Grid N → ℝ) where
  toFun u := ((N : ℝ) ^ 2)⁻¹ • lapR (lapR u)
  map_add' u w := by rw [lapR_add, lapR_add, smul_add]
  map_smul' c u := by rw [lapR_smul, lapR_smul, smul_comm]; rfl

theorem cxv_mk (r : ℕ) (f : Grid N → ℝ) : cxv (mk (r := r) f) = cx f := rfl

/-- `D_i⁺ : H^{r+1}_h → H^r_h`, norm `≤ 1`. -/
def DpL (r : ℕ) (i : Fin 3) : GridH N (r + 1) →L[ℝ] GridH N r :=
  ofBound (DpLin i) 1 fun u => by
    rw [one_mul, norm_def, norm_def, cxv_mk]
    show sobNorm r (cx (OpenWriterEnergy.Dp i (val u))) ≤ _
    rw [cx_Dp]
    exact PeriodicGridSobolev.CommutedRow.sobNorm_Dp_le r i _

/-- `D_i⁻ : H^r_h → H^r_h`, norm `≤ 2 h^{-1}`. -/
def DmM (r : ℕ) (i : Fin 3) : GridH N r →L[ℝ] GridH N r :=
  ofBound (DmLin i) (2 * N) fun u => by
    rw [norm_def, norm_def, cxv_mk]
    show sobNorm r (cx (OpenWriterEnergy.Dm i (val u))) ≤ _
    rw [cx_Dm]
    exact sobNorm_Dm_mesh r i _

/-- `D_i⁰ : H^r_h → H^r_h`, norm `≤ 2 h^{-1}`. -/
def D0M (r : ℕ) (i : Fin 3) : GridH N r →L[ℝ] GridH N r :=
  ofBound (D0Lin i) (2 * N) fun u => by
    rw [norm_def, norm_def, cxv_mk]
    show sobNorm r (cx (OpenWriterEnergy.D0 i (val u))) ≤ _
    rw [cx_D0]
    exact sobNorm_mesh_of_comm r (fun α w => PeriodicGridSobolev.CommutedRow.Dα_D0 α i w)
      (fun w => (PeriodicGridSobolev.gridNorm_D0_le i w).trans (gridNorm_Dp_le i w)) _

/-- `h² Λ_h² : H^{r+1}_h → H^r_h`, norm `≤ 36 C_{r+1} h^{-1}`. -/
def lap2L (r : ℕ) : GridH N (r + 1) →L[ℝ] GridH N r :=
  ofBound lap2Lin (36 * invConst (r + 1) * N) fun u => by
    rw [norm_def, norm_def, cxv_mk]
    show sobNorm r (cx (((N : ℝ) ^ 2)⁻¹ • lapR (lapR (val u)))) ≤ _
    rw [cx_smul, cx_lapR, cx_lapR, PeriodicGridSobolev.Moser.sobNorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have h1 := sobNorm_lap2_le r (cx (val u))
    have h2 := sobNorm_succ_le_inverse (r + 1) (cx (val u))
    calc ((N : ℝ) ^ 2)⁻¹ * sobNorm r (lapC (lapC (cx (val u)))) ≤
          36 * sobNorm (r + 2) (cx (val u)) := h1
      _ ≤ 36 * (invConst (r + 1) * N * sobNorm (r + 1) (cx (val u))) := by gcongr
      _ = invConst (r + 1) * N * sobNorm (r + 1) (cxv u) * 36 := by rw [← cxv_mk (r := r + 1), mk_val]; ring
      _ = _ := by ring

theorem norm_DpL_le (r : ℕ) (i : Fin 3) : ‖DpL (N := N) r i‖ ≤ 1 := norm_ofBound_le _ zero_le_one _
theorem norm_DmM_le (r : ℕ) (i : Fin 3) : ‖DmM (N := N) r i‖ ≤ 2 * N :=
  norm_ofBound_le _ (by positivity) _
theorem norm_D0M_le (r : ℕ) (i : Fin 3) : ‖D0M (N := N) r i‖ ≤ 2 * N :=
  norm_ofBound_le _ (by positivity) _
theorem norm_lap2L_le (r : ℕ) : ‖lap2L (N := N) r‖ ≤ 36 * invConst (r + 1) * N :=
  norm_ofBound_le _ (by have := invConst_nonneg (r + 1); positivity) _

@[simp] theorem DpL_val (r : ℕ) (i : Fin 3) (u : GridH N (r + 1)) :
    val (DpL r i u) = OpenWriterEnergy.Dp i (val u) := rfl
@[simp] theorem DmM_val (r : ℕ) (i : Fin 3) (u : GridH N r) :
    val (DmM r i u) = OpenWriterEnergy.Dm i (val u) := rfl
@[simp] theorem D0M_val (r : ℕ) (i : Fin 3) (u : GridH N r) :
    val (D0M r i u) = OpenWriterEnergy.D0 i (val u) := rfl
@[simp] theorem lap2L_val (r : ℕ) (u : GridH N (r + 1)) :
    val (lap2L r u) = ((N : ℝ) ^ 2)⁻¹ • lapR (lapR (val u)) := rfl

/-! ### The phase space and the differential writer -/

/-- **The phase space** `𝒳^s_h = (H^{s+1}_h)^{10} × (H^s_h)^{10}` of ten-component records. -/
abbrev XS (N s : ℕ) := (Upper → GridH N (s + 1)) × (Upper → GridH N s)

/-- The symmetric record array of ten upper components. -/
def recOf {r : ℕ} (Q : Upper → GridH N r) : Grid N → MetricRec :=
  fun x μ ν => val (Q (upperOf μ ν)) x

theorem isSymRec_recOf {r : ℕ} (Q : Upper → GridH N r) : IsSymRec (recOf Q) := by
  intro x μ ν; simp only [recOf, upperOf_comm μ ν]

theorem comp_recOf {r : ℕ} (Q : Upper → GridH N r) (κ : Upper) :
    comp (recOf Q) κ.1.1 κ.1.2 = val (Q κ) := by
  funext x; simp only [comp, recOf, upperOf_upper]

/-- **The differential writer** `𝓕_{B,h}(q, v) = (v, V_{B,h}(q, v))` on `𝒳^s_h`
(`eq:supp-law-family`; the open writer is the mark `B = 0`). -/
def lawField (s : ℕ) (B : Upper → Upper → ℝ) (X : XS N s) : XS N s :=
  (fun κ => up s (X.2 κ), fun κ => mk (comp (lawAccel B (recOf X.1) (recOf X.2)) κ.1.1 κ.1.2))

/-! ### The writer as a composition of mesh-uniform blocks -/

/-- Rebuild a record from its ten upper components. -/
def recW : (Upper → ℝ) →L[ℝ] MetricRec :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w μ ν => w (upperOf μ ν)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem recW_apply (w : Upper → ℝ) (μ ν : Fin 4) : recW w μ ν = w (upperOf μ ν) := rfl

/-- Index set of the site-jet coordinates `(q, v, D⁺q)`. -/
abbrev JIdx := Upper ⊕ Upper ⊕ (Fin 3 × Upper)

/-- The site jet from its coordinates. -/
def jetW : (JIdx → ℝ) →L[ℝ] JetSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (recW (fun κ => w (Sum.inl κ)), recW (fun κ => w (Sum.inr (Sum.inl κ))),
        fun i => recW (fun κ => w (Sum.inr (Sum.inr (i, κ)))))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Pointwise coefficient functions of the chart. -/
def aInvA (w : Upper → ℝ) : ℝ := (harmA (minkowski + recW w))⁻¹
def cA (i j : Fin 3) (w : Upper → ℝ) : ℝ := harmC i j (minkowski + recW w)
def bA (i : Fin 3) (w : Upper → ℝ) : ℝ := harmB i (minkowski + recW w)
def GA (κ : Upper) (w : JIdx → ℝ) : ℝ := compensatorMap (jetW w) κ.1.1 κ.1.2

theorem analyticAt_recW_chart : AnalyticAt ℝ (fun w : Upper → ℝ => minkowski + recW w) 0 :=
  analyticAt_const.add (recW.analyticAt 0)

theorem analyticAt_aInvA : AnalyticAt ℝ aInvA 0 :=
  analyticAt_harmA_inv.comp_of_eq analyticAt_recW_chart (by simp)

theorem analyticAt_cA (i j : Fin 3) : AnalyticAt ℝ (cA i j) 0 :=
  (analyticAt_harmC i j).comp_of_eq analyticAt_recW_chart (by simp)

theorem analyticAt_bA (i : Fin 3) : AnalyticAt ℝ (bA i) 0 :=
  (analyticAt_harmB i).comp_of_eq analyticAt_recW_chart (by simp)

theorem analyticAt_GA (κ : Upper) : AnalyticAt ℝ (GA κ) 0 := by
  have h := analyticAt_compensatorMap κ.1.1 κ.1.2 0
  have h0 : jetW (0 : JIdx → ℝ) = ((0 : MetricRec), (0 : MetricRec × (Fin 3 → MetricRec))) := by
    rw [map_zero]; rfl
  exact h.comp_of_eq (jetW.analyticAt 0) h0

/-- The position components in `H^s_h`. -/
def Lq (s : ℕ) : XS N s →L[ℝ] (Upper → GridH N s) :=
  ContinuousLinearMap.pi fun κ => (incl (Nat.le_succ s)).comp
    ((ContinuousLinearMap.proj κ).comp (ContinuousLinearMap.fst ℝ _ _))

/-- The site-jet components `(q, v, D⁺q)` in `H^s_h`. -/
def LJ (s : ℕ) : XS N s →L[ℝ] (JIdx → GridH N s) :=
  ContinuousLinearMap.pi fun j => match j with
    | Sum.inl κ => (incl (Nat.le_succ s)).comp
        ((ContinuousLinearMap.proj κ).comp (ContinuousLinearMap.fst ℝ _ _))
    | Sum.inr (Sum.inl κ) => (ContinuousLinearMap.proj κ).comp (ContinuousLinearMap.snd ℝ _ _)
    | Sum.inr (Sum.inr (i, κ)) => (DpL s i).comp
        ((ContinuousLinearMap.proj κ).comp (ContinuousLinearMap.fst ℝ _ _))

theorem norm_Lq_apply_le (s : ℕ) (X : XS N s) : ‖Lq s X‖ ≤ ‖X‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun κ => ?_
  show ‖incl (Nat.le_succ s) (X.1 κ)‖ ≤ ‖X‖
  refine ((incl (N := N) (Nat.le_succ s)).le_opNorm _).trans ?_
  calc ‖incl (N := N) (Nat.le_succ s)‖ * ‖X.1 κ‖ ≤ 1 * ‖X.1 κ‖ :=
        mul_le_mul_of_nonneg_right (norm_incl_le _) (norm_nonneg _)
    _ ≤ ‖X‖ := by rw [one_mul]; exact (norm_le_pi_norm X.1 κ).trans (norm_fst_le X)

theorem norm_LJ_apply_le (s : ℕ) (X : XS N s) : ‖LJ s X‖ ≤ ‖X‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
  rcases j with κ | κ | ⟨i, κ⟩
  · show ‖incl (Nat.le_succ s) (X.1 κ)‖ ≤ ‖X‖
    refine ((incl (N := N) (Nat.le_succ s)).le_opNorm _).trans ?_
    calc ‖incl (N := N) (Nat.le_succ s)‖ * ‖X.1 κ‖ ≤ 1 * ‖X.1 κ‖ :=
          mul_le_mul_of_nonneg_right (norm_incl_le _) (norm_nonneg _)
      _ ≤ ‖X‖ := by rw [one_mul]; exact (norm_le_pi_norm X.1 κ).trans (norm_fst_le X)
  · show ‖X.2 κ‖ ≤ ‖X‖
    exact (norm_le_pi_norm X.2 κ).trans (norm_snd_le X)
  · show ‖DpL s i (X.1 κ)‖ ≤ ‖X‖
    refine ((DpL (N := N) s i).le_opNorm _).trans ?_
    calc ‖DpL (N := N) s i‖ * ‖X.1 κ‖ ≤ 1 * ‖X.1 κ‖ :=
          mul_le_mul_of_nonneg_right (norm_DpL_le _ _) (norm_nonneg _)
      _ ≤ ‖X‖ := by rw [one_mul]; exact (norm_le_pi_norm X.1 κ).trans (norm_fst_le X)

theorem norm_Lq_le (s : ℕ) : ‖Lq (N := N) s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun X => by rw [one_mul]; exact norm_Lq_apply_le s X

theorem norm_LJ_le (s : ℕ) : ‖LJ (N := N) s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun X => by rw [one_mul]; exact norm_LJ_apply_le s X

variable (s : ℕ) (hs : 2 ≤ s)

/-- `a⁻¹(q)` as an element of `H^s_h`. -/
def ainvF (X : XS N s) : GridH N s := pointwise aInvA 0 (Lq s X)
def cF (i j : Fin 3) (X : XS N s) : GridH N s := pointwise (cA i j) 0 (Lq s X)
def bF (i : Fin 3) (X : XS N s) : GridH N s := pointwise (bA i) 0 (Lq s X)
def GF (κ : Upper) (X : XS N s) : GridH N s := pointwise (GA κ) 0 (LJ s X)

/-- The divergence flux `Σ_{ij} D_i⁻(c^{ij} D_j⁺ q_κ)`. -/
def divF (κ : Upper) (X : XS N s) : GridH N s :=
  ∑ i, ∑ j, DmM s i (mulL hs (cF s i j X) (DpL s j (X.1 κ)))

/-- The skew transport `Σ_i (b^i D_i⁰ v_κ + D_i⁰(b^i v_κ))`. -/
def skewF (κ : Upper) (X : XS N s) : GridH N s :=
  ∑ i, (mulL hs (bF s i X) (D0M s i (X.2 κ)) + D0M s i (mulL hs (bF s i X) (X.2 κ)))

/-- The law stencil `h² Σ_l B_{κl} Λ_h² q_l`. -/
def bTF (B : Upper → Upper → ℝ) (κ : Upper) (X : XS N s) : GridH N s :=
  ∑ l, B κ l • lap2L s (X.1 l)

/-- The acceleration component `κ`. -/
def accF (B : Upper → Upper → ℝ) (κ : Upper) (X : XS N s) : GridH N s :=
  mulL hs (ainvF s X) (divF s hs κ X - skewF s hs κ X + GF s κ X - bTF s B κ X)

/-- The writer as a composition of the blocks. -/
def fieldF (B : Upper → Upper → ℝ) (X : XS N s) : XS N s :=
  (fun κ => up s (X.2 κ), fun κ => accF s hs B κ X)

theorem val_pointwise {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (A : (ι → ℝ) → ℝ)
    (u : ι → GridH N r) (x : Grid N) :
    val (pointwise A 0 u) x = A (evalAt x u) := by
  simp [pointwise]

theorem recW_evalAt_Lq (X : XS N s) (x : Grid N) : recW (evalAt x (Lq s X)) = recOf X.1 x := by
  funext μ ν; rfl

theorem jetW_evalAt_LJ (X : XS N s) (x : Grid N) :
    jetW (evalAt x (LJ s X)) = jetArr (recOf X.1) (recOf X.2) x := by
  refine Prod.ext (funext fun μ => funext fun ν => rfl) (Prod.ext (funext fun μ => funext fun ν => rfl) ?_)
  funext i μ ν
  show OpenWriterEnergy.Dp i (val (X.1 (upperOf μ ν))) x = fwd (N : ℝ)⁻¹ (e N) i (recOf X.1) x μ ν
  have := congrFun (comp_fwd (recOf X.1) i μ ν) x
  simp only [comp] at this
  rw [this]
  rfl

/-- **The decomposition is the writer**: `fieldF = lawField`. -/
theorem fieldF_eq (B : Upper → Upper → ℝ) (X : XS N s) : fieldF s hs B X = lawField s B X := by
  refine Prod.ext rfl (funext fun κ => GridH.ext fun x => ?_)
  show val (accF s hs B κ X) x = lawAccel B (recOf X.1) (recOf X.2) x κ.1.1 κ.1.2
  rw [lawAccel_apply]
  set q := recOf X.1
  set v := recOf X.2
  have hq : comp q κ.1.1 κ.1.2 = val (X.1 κ) := comp_recOf X.1 κ
  have hv : comp v κ.1.1 κ.1.2 = val (X.2 κ) := comp_recOf X.2 κ
  have ha : val (ainvF s X) x = (aArr q x)⁻¹ := by
    rw [ainvF, val_pointwise]; simp only [aInvA, aArr]; rw [recW_evalAt_Lq]
  have hc : ∀ i j, val (cF s i j X) = cArr q i j := by
    intro i j; funext y; rw [cF, val_pointwise]; simp only [cA, cArr]; rw [recW_evalAt_Lq]
  have hb : ∀ i, val (bF s i X) = bArr q i := by
    intro i; funext y; rw [bF, val_pointwise]; simp only [bA, bArr]; rw [recW_evalAt_Lq]
  have hG : val (GF s κ X) x = compensatorMap (jetArr q v x) κ.1.1 κ.1.2 := by
    rw [GF, val_pointwise]; simp only [GA]; rw [jetW_evalAt_LJ]
  have hdiv : val (divF s hs κ X) x = divArr (cArr q) (comp q κ.1.1 κ.1.2) x := by
    simp only [divF, divArr, val_sum, Finset.sum_apply, DmM_val, mulL_val, DpL_val, hc, hq]
    rfl
  have hskew : val (skewF s hs κ X) x = skewArr (bArr q) (comp v κ.1.1 κ.1.2) x := by
    simp only [skewF, skewArr, val_sum, Finset.sum_apply, val_add, Pi.add_apply, D0M_val,
      mulL_val, hb, hv]
    rfl
  have hbT : val (bTF s B κ X) x = bTerm B q x κ.1.1 κ.1.2 := by
    simp only [bTF, bTerm, val_sum, Finset.sum_apply, val_smul, Pi.smul_apply, lap2L_val,
      smul_eq_mul, upperOf_upper]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [comp_recOf X.1 l]
    ring
  simp only [accF, mulL_val, Pi.mul_apply, val_add, val_sub, Pi.add_apply, Pi.sub_apply]
  rw [ha, hdiv, hskew, hG, hbT]

/-! ### Uniform derivative bounds for the writer -/

omit [NeZero N] in
theorem derivBound_clm_unit {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU1 : U ⊆ closedBall 0 1) (K : ℕ)
    (L : E →L[ℝ] F) {c : ℝ} (hL : ‖L‖ ≤ c) : DerivBound (fun x => L x) U K c :=
  (DerivBound.clm L zero_le_one hU1 K).mono le_rfl (by rw [max_self, mul_one]; exact hL)

theorem norm_fst_comp_le (X : XS N s) (κ : Upper) : ‖X.1 κ‖ ≤ ‖X‖ :=
  (norm_le_pi_norm X.1 κ).trans (norm_fst_le X)

theorem norm_snd_comp_le (X : XS N s) (κ : Upper) : ‖X.2 κ‖ ≤ ‖X‖ :=
  (norm_le_pi_norm X.2 κ).trans (norm_snd_le X)

include hs in
/-- Uniform chart constants for the four families of pointwise coefficient maps. -/
theorem coef_bounds (K : ℕ) : ∃ δ > 0, ∃ P ≥ 0, ∀ (N : ℕ) [NeZero N],
    DerivBound (pointwise (N := N) (r := s) aInvA 0) (ball 0 δ) K P ∧
    (∀ i j, DerivBound (pointwise (N := N) (r := s) (cA i j) 0) (ball 0 δ) K P) ∧
    (∀ i, DerivBound (pointwise (N := N) (r := s) (bA i) 0) (ball 0 δ) K P) ∧
    (∀ κ, DerivBound (pointwise (N := N) (r := s) (GA κ) 0) (ball 0 δ) K P) := by
  obtain ⟨δa, hδa, Pa, hPa, ha⟩ := pointwise_derivBound (r := s) hs analyticAt_aInvA K
  have hc' : ∀ ij : Fin 3 × Fin 3, ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N],
      DerivBound (pointwise (N := N) (r := s) (cA ij.1 ij.2) 0) (ball 0 δ) K C :=
    fun ij => pointwise_derivBound hs (analyticAt_cA ij.1 ij.2) K
  obtain ⟨δc, hδc, Pc, hPc, hc⟩ := uniformize' (fun (ij : Fin 3 × Fin 3) δ C =>
      ∀ (N : ℕ) [NeZero N], DerivBound (pointwise (N := N) (r := s) (cA ij.1 ij.2) 0)
        (ball 0 δ) K C)
    (fun _ _ _ _ _ _ hδ hC h N _ => ((h N).subset (ball_subset_ball hδ)).mono le_rfl hC) hc'
  have hb' : ∀ i : Fin 3, ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N],
      DerivBound (pointwise (N := N) (r := s) (bA i) 0) (ball 0 δ) K C :=
    fun i => pointwise_derivBound hs (analyticAt_bA i) K
  obtain ⟨δb, hδb, Pb, hPb, hb⟩ := uniformize' (fun (i : Fin 3) δ C =>
      ∀ (N : ℕ) [NeZero N], DerivBound (pointwise (N := N) (r := s) (bA i) 0) (ball 0 δ) K C)
    (fun _ _ _ _ _ _ hδ hC h N _ => ((h N).subset (ball_subset_ball hδ)).mono le_rfl hC) hb'
  have hG' : ∀ κ : Upper, ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N],
      DerivBound (pointwise (N := N) (r := s) (GA κ) 0) (ball 0 δ) K C :=
    fun κ => pointwise_derivBound hs (analyticAt_GA κ) K
  obtain ⟨δG, hδG, PG, hPG, hG⟩ := uniformize' (fun (κ : Upper) δ C =>
      ∀ (N : ℕ) [NeZero N], DerivBound (pointwise (N := N) (r := s) (GA κ) 0) (ball 0 δ) K C)
    (fun _ _ _ _ _ _ hδ hC h N _ => ((h N).subset (ball_subset_ball hδ)).mono le_rfl hC) hG'
  set δ := min (min δa δc) (min δb δG)
  have h1 : δ ≤ δa := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : δ ≤ δc := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : δ ≤ δb := (min_le_right _ _).trans (min_le_left _ _)
  have h4 : δ ≤ δG := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, lt_min (lt_min hδa hδc) (lt_min hδb hδG), Pa + Pc + Pb + PG, by positivity,
    fun N _ => ⟨?_, fun i j => ?_, fun i => ?_, fun κ => ?_⟩⟩
  · exact ((ha N).subset (ball_subset_ball h1)).mono le_rfl (by linarith)
  · exact ((hc (i, j) N).subset (ball_subset_ball h2)).mono le_rfl (by linarith)
  · exact ((hb i N).subset (ball_subset_ball h3)).mono le_rfl (by linarith)
  · exact ((hG κ N).subset (ball_subset_ball h4)).mono le_rfl (by linarith)

include hs in
set_option maxHeartbeats 4000000 in
/-- **Inverse-mesh vector-field bounds** (`eq:supp-open-local-vector-bounds`, derivative part).
For `s ≥ 2`, every order `K` and every bound `b` on the mark entries there are `δ > 0` and `C`,
independent of the mesh `h = 1/N` and of the mark, such that the differential writer
`𝓕_{B,h}` is `C^∞` on the ball `‖X‖_{𝒳^s_h} < δ` with `‖D^j 𝓕_{B,h}(X)‖ ≤ C h^{-1}` for every
`j ≤ K`. -/
theorem local_vector_bounds (K : ℕ) (b : ℝ) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ), (∀ k l, |B k l| ≤ b) →
      DerivBound (lawField (N := N) s B) (ball 0 δ) K (C * N) := by
  obtain ⟨δP, hδP, P, hP, hcoef⟩ := coef_bounds s hs K
  set A := PeriodicGridSobolev.Moser.algConst s with hAdef
  have hA0 : 0 < A := PeriodicGridSobolev.Moser.algConst_pos s
  set T : ℝ := 2 ^ K with hTdef
  have hT0 : 0 < T := by positivity
  set b' := max b 0 with hb'def
  have hb'0 : 0 ≤ b' := le_max_right _ _
  set IC := invConst (s + 1) with hICdef
  have hIC : 0 ≤ IC := invConst_nonneg _
  have hIC0 : 0 ≤ invConst s := invConst_nonneg _
  set cU : ℝ := (Fintype.card Upper : ℝ)
  have hcU : 0 ≤ cU := Nat.cast_nonneg _
  set CT := 18 * (A * T * P) + 12 * (A * T * P) + P + cU * (b' * (36 * IC)) with hCTdef
  have hCT : 0 ≤ CT := by positivity
  refine ⟨min δP 1, lt_min hδP one_pos, invConst s + A * T * P * CT, by positivity,
    fun N _ B hB => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN0 : (0 : ℝ) ≤ N := by linarith
  set U : Set (XS N s) := ball 0 (min δP 1)
  have hU : IsOpen U := isOpen_ball
  have hU1 : U ⊆ closedBall 0 1 := fun X hX => by
    have h := mem_ball_zero_iff.mp hX
    exact mem_closedBall_zero_iff.mpr (h.le.trans (min_le_right _ _))
  obtain ⟨hcA, hcC, hcB, hcG⟩ := hcoef N
  have hmapq : MapsTo (Lq (N := N) s) U (ball 0 δP) := fun X hX => by
    have h := mem_ball_zero_iff.mp hX
    exact mem_ball_zero_iff.mpr ((norm_Lq_apply_le s X).trans_lt (h.trans_le (min_le_left _ _)))
  have hmapJ : MapsTo (LJ (N := N) s) U (ball 0 δP) := fun X hX => by
    have h := mem_ball_zero_iff.mp hX
    exact mem_ball_zero_iff.mpr ((norm_LJ_apply_le s X).trans_lt (h.trans_le (min_le_left _ _)))
  have hmq : P * max 1 ‖Lq (N := N) s‖ ^ K ≤ P := by
    rw [max_eq_left (norm_Lq_le s), one_pow, mul_one]
  have hmJ : P * max 1 ‖LJ (N := N) s‖ ^ K ≤ P := by
    rw [max_eq_left (norm_LJ_le s), one_pow, mul_one]
  -- coefficient blocks
  have dA : DerivBound (fun X : XS N s => ainvF s X) U K P :=
    (hcA.comp_clm isOpen_ball (Lq s) hmapq).mono le_rfl hmq
  have dC : ∀ i j, DerivBound (fun X : XS N s => cF s i j X) U K P := fun i j =>
    ((hcC i j).comp_clm isOpen_ball (Lq s) hmapq).mono le_rfl hmq
  have dB : ∀ i, DerivBound (fun X : XS N s => bF s i X) U K P := fun i =>
    ((hcB i).comp_clm isOpen_ball (Lq s) hmapq).mono le_rfl hmq
  have dG : ∀ κ, DerivBound (fun X : XS N s => GF s κ X) U K P := fun κ =>
    ((hcG κ).comp_clm isOpen_ball (LJ s) hmapJ).mono le_rfl hmJ
  -- linear blocks
  have dDp : ∀ j κ, DerivBound (fun X : XS N s => DpL s j (X.1 κ)) U K 1 := fun j κ =>
    derivBound_clm_unit hU1 K ((DpL s j).comp ((ContinuousLinearMap.proj κ).comp
      (ContinuousLinearMap.fst ℝ _ _)))
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun X => by
        rw [one_mul]
        show ‖DpL s j (X.1 κ)‖ ≤ ‖X‖
        refine ((DpL (N := N) s j).le_opNorm _).trans ?_
        exact (mul_le_mul_of_nonneg_right (norm_DpL_le s j) (norm_nonneg _)).trans
          (by rw [one_mul]; exact norm_fst_comp_le s X κ))
  have dV : ∀ κ, DerivBound (fun X : XS N s => X.2 κ) U K 1 := fun κ =>
    derivBound_clm_unit hU1 K ((ContinuousLinearMap.proj κ).comp (ContinuousLinearMap.snd ℝ _ _))
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun X => by
        rw [one_mul]; exact norm_snd_comp_le s X κ)
  have dD0 : ∀ i κ, DerivBound (fun X : XS N s => D0M s i (X.2 κ)) U K (2 * N) := fun i κ =>
    derivBound_clm_unit hU1 K ((D0M s i).comp ((ContinuousLinearMap.proj κ).comp
      (ContinuousLinearMap.snd ℝ _ _)))
      (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun X => by
        show ‖D0M s i (X.2 κ)‖ ≤ 2 * N * ‖X‖
        refine ((D0M (N := N) s i).le_opNorm _).trans ?_
        exact mul_le_mul (norm_D0M_le s i) (norm_snd_comp_le s X κ) (norm_nonneg _)
          (by positivity))
  have hmul : ‖mulL (N := N) hs‖ ≤ A := norm_mulL_le hs
  have hmulP : ‖mulL (N := N) hs‖ * 2 ^ K * P ≤ A * T * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmul (le_of_lt hT0)) hP
  have hATP : 0 ≤ A * T * P := by positivity
  -- the divergence flux
  have dDiv : ∀ κ, DerivBound (fun X : XS N s => divF s hs κ X) U K (18 * (A * T * P) * N) := by
    intro κ
    have hij : ∀ i j, DerivBound (fun X : XS N s => DmM s i (mulL hs (cF s i j X)
        (DpL s j (X.1 κ)))) U K (2 * N * (A * T * P)) := by
      intro i j
      have h := ((dC i j).bilinear (dDp j κ) hU (mulL hs) hP zero_le_one).clm_comp hU (DmM s i)
      refine h.mono le_rfl ?_
      rw [mul_one]
      exact mul_le_mul (norm_DmM_le s i) hmulP (by positivity) (by positivity)
    have h := DerivBound.sum Finset.univ (fun i _ => DerivBound.sum Finset.univ
      (fun j _ => hij i j) hU) hU
    refine (h.mono le_rfl ?_).congr fun X => rfl
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    exact le_of_eq (by ring)
  -- the skew transport
  have dSkew : ∀ κ, DerivBound (fun X : XS N s => skewF s hs κ X) U K
      (12 * (A * T * P) * N) := by
    intro κ
    have hi : ∀ i, DerivBound (fun X : XS N s => mulL hs (bF s i X) (D0M s i (X.2 κ)) +
        D0M s i (mulL hs (bF s i X) (X.2 κ))) U K (4 * (A * T * P) * N) := by
      intro i
      have h1 := (dB i).bilinear (dD0 i κ) hU (mulL hs) hP (by positivity)
      have h2 := ((dB i).bilinear (dV κ) hU (mulL hs) hP zero_le_one).clm_comp hU (D0M s i)
      refine (h1.add h2 hU).mono le_rfl ?_
      have k1 : ‖mulL (N := N) hs‖ * 2 ^ K * P * (2 * N) ≤ 2 * (A * T * P) * N := by
        nlinarith
      have k2 : ‖D0M (N := N) s i‖ * (‖mulL (N := N) hs‖ * 2 ^ K * P * 1) ≤
          2 * (A * T * P) * N := by
        rw [mul_one]
        calc ‖D0M (N := N) s i‖ * (‖mulL (N := N) hs‖ * 2 ^ K * P) ≤ (2 * N) * (A * T * P) :=
              mul_le_mul (norm_D0M_le s i) hmulP (by positivity) (by positivity)
          _ = 2 * (A * T * P) * N := by ring
      linarith
    have h := DerivBound.sum Finset.univ (fun i _ => hi i) hU
    refine (h.mono le_rfl ?_).congr fun X => rfl
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    exact le_of_eq (by ring)
  -- the law stencil
  have dBT : ∀ κ, DerivBound (fun X : XS N s => bTF s B κ X) U K (cU * (b' * (36 * IC)) * N) := by
    intro κ
    have hl : ∀ l, (∀ X : XS N s, ‖B κ l • lap2L s (X.1 l)‖ ≤ b' * (36 * IC) * N * ‖X‖) →
        DerivBound (fun X : XS N s => B κ l • lap2L s (X.1 l)) U K
        (b' * (36 * IC) * N) := by
      intro l hpt
      set L : XS N s →L[ℝ] GridH N s := (lap2L s).comp ((ContinuousLinearMap.proj l).comp
        (ContinuousLinearMap.fst ℝ _ _)) with hLdef
      have hLX : ∀ X : XS N s, L X = lap2L s (X.1 l) := fun X => rfl
      have hbound : ‖B κ l • L‖ ≤ b' * (36 * IC) * N := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun X => ?_
        rw [ContinuousLinearMap.smul_apply, hLX]
        exact hpt X
      exact (derivBound_clm_unit hU1 K (B κ l • L) hbound).congr fun X => by
        rw [ContinuousLinearMap.smul_apply, hLX]
    have hl' : ∀ l (X : XS N s), ‖B κ l • lap2L s (X.1 l)‖ ≤ b' * (36 * IC) * N * ‖X‖ := by
      intro l X
      rw [norm_smul, Real.norm_eq_abs]
      have e1 := ((lap2L (N := N) s).le_opNorm (X.1 l)).trans
        (mul_le_mul (norm_lap2L_le s) (norm_fst_comp_le s X l) (norm_nonneg _) (by positivity))
      have e2 : |B κ l| ≤ b' := (hB κ l).trans (le_max_left _ _)
      calc |B κ l| * ‖lap2L s (X.1 l)‖ ≤ b' * (36 * invConst (s + 1) * N * ‖X‖) :=
            mul_le_mul e2 e1 (norm_nonneg _) hb'0
        _ = b' * (36 * IC) * N * ‖X‖ := by ring
    have h := DerivBound.sum Finset.univ (fun l _ => hl l (hl' l)) hU
    refine (h.mono le_rfl ?_).congr fun X => rfl
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact le_of_eq (by ring)
  -- the bracket and the acceleration
  have dAcc : ∀ κ, DerivBound (fun X : XS N s => accF s hs B κ X) U K (A * T * P * CT * N) := by
    intro κ
    have hT' := (((dDiv κ).sub (dSkew κ) hU).add (dG κ) hU).sub (dBT κ) hU
    have hT'' : DerivBound (fun X : XS N s => divF s hs κ X - skewF s hs κ X + GF s κ X -
        bTF s B κ X) U K (CT * N) := by
      refine hT'.mono le_rfl ?_
      rw [hCTdef]
      have : P ≤ P * N := le_mul_of_one_le_right hP hN1
      nlinarith
    have h := dA.bilinear hT'' hU (mulL hs) hP (by positivity)
    refine (h.mono le_rfl ?_).congr fun X => rfl
    have h2 : 0 ≤ CT * N := by positivity
    calc ‖mulL (N := N) hs‖ * 2 ^ K * P * (CT * N) ≤ A * T * P * (CT * N) :=
          mul_le_mul_of_nonneg_right hmulP h2
      _ = A * T * P * CT * N := by ring
  -- the field
  have dVel : DerivBound (fun X : XS N s => fun κ => up s (X.2 κ)) U K (invConst s * N) := by
    refine DerivBound.pi (fun κ => ?_) hU (by positivity)
    refine derivBound_clm_unit hU1 K ((up s).comp ((ContinuousLinearMap.proj κ).comp
      (ContinuousLinearMap.snd ℝ _ _))) ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun X => ?_
    show ‖up s (X.2 κ)‖ ≤ invConst s * N * ‖X‖
    exact ((up (N := N) s).le_opNorm _).trans
      (mul_le_mul (norm_up_le s) (norm_snd_comp_le s X κ) (norm_nonneg _) (by positivity))
  have dAccs : DerivBound (fun X : XS N s => fun κ => accF s hs B κ X) U K (A * T * P * CT * N) :=
    DerivBound.pi dAcc hU (by positivity)
  have dF := dVel.prod dAccs hU (by positivity) (by positivity)
  refine (dF.mono le_rfl (le_of_eq (by ring))).congr fun X => ?_
  exact fieldF_eq s hs B X


/-! ### The zeroth-order bound -/

omit [NeZero N] in
theorem recOf_zero {r : ℕ} [NeZero N] : recOf (0 : Upper → GridH N r) = 0 := by
  funext x μ ν; rfl

theorem lawField_zero (B : Upper → Upper → ℝ) : lawField s B (0 : XS N s) = 0 := by
  refine Prod.ext (funext fun κ => GridH.ext fun x => rfl) (funext fun κ => GridH.ext fun x => ?_)
  show lawAccel B (recOf (0 : Upper → GridH N (s + 1))) (recOf (0 : Upper → GridH N s)) x
    κ.1.1 κ.1.2 = 0
  rw [recOf_zero, recOf_zero, lawAccel_zero_state]
  rfl

/-- Mean-value form of the zeroth-order bound: on a ball where `‖D𝓕‖ ≤ M`,
`‖𝓕(X)‖ ≤ M ‖X‖` (since `𝓕(0) = 0`). -/
theorem norm_lawField_le {B : Upper → Upper → ℝ} {δ M : ℝ} {K : ℕ} (hK : 1 ≤ K)
    (h : DerivBound (lawField (N := N) s B) (ball 0 δ) K M) {X : XS N s} (hX : X ∈ ball 0 δ) :
    ‖lawField s B X‖ ≤ M * ‖X‖ := by
  have h0 : (0 : XS N s) ∈ ball 0 δ := by
    have := mem_ball_zero_iff.mp hX
    exact mem_ball_self ((norm_nonneg _).trans_lt this)
  have hd : ∀ Y ∈ ball (0 : XS N s) δ, DifferentiableAt ℝ (lawField s B) Y := fun Y hY =>
    (h.contDiffAt isOpen_ball hY).differentiableAt (by simp)
  have := (convex_ball (0 : XS N s) δ).norm_image_sub_le_of_norm_fderiv_le hd
    (fun Y hY => h.norm_fderiv_le hK hY) h0 hX
  rwa [lawField_zero, sub_zero, sub_zero] at this

/-! ### The phase norm and the `𝒳^s_h` norm of the manuscript -/

theorem Xsq_recOf (X : XS N s) :
    Xsq s (recOf X.1) (recOf X.2) = ∑ κ : Upper, (‖X.1 κ‖ ^ 2 + ‖X.2 κ‖ ^ 2) := by
  unfold Xsq
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [comp_recOf, comp_recOf, norm_def, norm_def, PeriodicGridSobolev.sobNorm_sq,
    PeriodicGridSobolev.sobNorm_sq]
  rfl

/-- The phase norm is dominated by the norm `‖X‖_{𝒳^s_h}` of `eq:supp-open-norms`. -/
theorem norm_le_Xnorm (X : XS N s) : ‖X‖ ≤ Xnorm s (recOf X.1) (recOf X.2) := by
  rw [Xnorm, Xsq_recOf]
  have hle : ∀ κ, ‖X.1 κ‖ ≤ Real.sqrt (∑ κ : Upper, (‖X.1 κ‖ ^ 2 + ‖X.2 κ‖ ^ 2)) ∧
      ‖X.2 κ‖ ≤ Real.sqrt (∑ κ : Upper, (‖X.1 κ‖ ^ 2 + ‖X.2 κ‖ ^ 2)) := by
    intro κ
    have hs : ‖X.1 κ‖ ^ 2 + ‖X.2 κ‖ ^ 2 ≤ ∑ κ : Upper, (‖X.1 κ‖ ^ 2 + ‖X.2 κ‖ ^ 2) :=
      Finset.single_le_sum (f := fun κ => ‖X.1 κ‖ ^ 2 + ‖X.2 κ‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ κ)
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖X.2 κ‖])
    · exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖X.1 κ‖])
  refine max_le ?_ ?_
  · exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun κ => (hle κ).1
  · exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun κ => (hle κ).2

/-- Conversely `‖X‖_{𝒳^s_h} ≤ √(2·10) ‖X‖`: the two norms are equivalent uniformly in the mesh. -/
theorem Xnorm_le_norm (X : XS N s) :
    Xnorm s (recOf X.1) (recOf X.2) ≤ Real.sqrt (2 * Fintype.card Upper) * ‖X‖ := by
  rw [Xnorm, Xsq_recOf, ← Real.sqrt_sq (norm_nonneg X), ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have hκ : ∀ κ : Upper, ‖X.1 κ‖ ^ 2 + ‖X.2 κ‖ ^ 2 ≤ 2 * ‖X‖ ^ 2 := by
    intro κ
    have h1 := norm_fst_comp_le s X κ
    have h2 := norm_snd_comp_le s X κ
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    linarith
  calc ∑ κ : Upper, (‖X.1 κ‖ ^ 2 + ‖X.2 κ‖ ^ 2) ≤ ∑ _κ : Upper, 2 * ‖X‖ ^ 2 :=
        Finset.sum_le_sum fun κ _ => hκ κ
    _ = 2 * Fintype.card Upper * ‖X‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-! ### Time jets -/

/-- The velocity components (in `H^s_h`). -/
def Lv (s : ℕ) : XS N s →L[ℝ] (Upper → GridH N s) := ContinuousLinearMap.snd ℝ _ _

theorem Lq_lawField (B : Upper → Upper → ℝ) (X : XS N s) : Lq s (lawField s B X) = Lv s X := by
  funext κ; exact GridH.ext fun x => rfl

theorem norm_Lv_apply_le (X : XS N s) : ‖Lv s X‖ ≤ ‖X‖ := norm_snd_le X

/-- **Intrinsic inverse-mesh jet bound.**  If `DerivBound 𝓕 (ball 0 δ) K (C h^{-1})` and
`‖X‖ ≤ ε` in the ball, the position part of the jet satisfies
`‖(J_j X)_q‖_{H^s_h} ≤ (2^K (C + 1))^K ε h^{1-j}` for `1 ≤ j ≤ K`. -/
theorem jet_q_bound {B : Upper → Upper → ℝ} {δ C : ℝ} {K : ℕ} (hC : 0 ≤ C)
    (h : DerivBound (lawField (N := N) s B) (ball 0 δ) K (C * N)) {X : XS N s}
    (hXU : X ∈ ball 0 δ) {ε : ℝ} (hε : ‖X‖ ≤ ε) (j : ℕ) (hj1 : 1 ≤ j) (hjK : j ≤ K) :
    ‖Lq s (vfJet (lawField s B) j X)‖ ≤ (2 ^ K * (C + 1)) ^ K * ε * (N : ℝ) ^ (j - 1) := by
  have hU : IsOpen (ball (0 : XS N s) δ) := isOpen_ball
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hM : 0 ≤ C * N := by positivity
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [vfJet_proj h.contDiffOn hU (Lq s) (Lv s) (fun Y _ => Lq_lawField s B Y) i X hXU]
  refine (norm_Lv_apply_le s _).trans ?_
  simp only [Nat.add_sub_cancel]
  have hbase : (1 : ℝ) ≤ 2 ^ K * (C + 1) := by
    have : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
    nlinarith
  have hbig : (2 ^ K * (C + 1)) ^ i ≤ (2 ^ K * (C + 1)) ^ K :=
    pow_le_pow_right₀ hbase (by omega)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [vfJet_zero, id, pow_zero, mul_one]
    calc ‖X‖ ≤ 1 * ε := by rw [one_mul]; exact hε
      _ ≤ (2 ^ K * (C + 1)) ^ K * ε := by
          refine mul_le_mul_of_nonneg_right ?_ hε0
          exact one_le_pow₀ hbase
  · have hn := vfJet_norm_le h hU hM hXU i hi (by omega)
    have hF := norm_lawField_le s (by omega) h hXU
    have hF' : ‖lawField s B X‖ ≤ C * N * ε :=
      hF.trans (mul_le_mul_of_nonneg_left hε hM)
    have h2 : (2 : ℝ) ^ K * (C * N) ≤ 2 ^ K * (C + 1) * N := by
      have : (0 : ℝ) ≤ 2 ^ K := by positivity
      nlinarith
    calc ‖vfJet (lawField s B) i X‖ ≤ (2 ^ K * (C * N)) ^ (i - 1) * ‖lawField s B X‖ := hn
      _ ≤ (2 ^ K * (C + 1) * N) ^ (i - 1) * ((C + 1) * N * ε) := by
          refine mul_le_mul (pow_le_pow_left₀ (by positivity) h2 _) (hF'.trans ?_) (norm_nonneg _)
            (by positivity)
          have : C * N * ε ≤ (C + 1) * N * ε := by
            have := mul_nonneg (by positivity : (0 : ℝ) ≤ N) hε0
            nlinarith
          exact this
      _ ≤ (2 ^ K * (C + 1) * N) ^ (i - 1) * (2 ^ K * (C + 1) * N * ε) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : (0 : ℝ) ≤ (C + 1) * N * ε := by positivity
          have h3 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
          have : (C + 1) * N * ε ≤ 2 ^ K * ((C + 1) * N * ε) := le_mul_of_one_le_left this h3
          linarith [show 2 ^ K * (C + 1) * N * ε = 2 ^ K * ((C + 1) * N * ε) by ring]
      _ = (2 ^ K * (C + 1)) ^ i * ε * (N : ℝ) ^ i := by
          obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          rw [mul_pow (2 ^ K * (C + 1)) (N : ℝ) m]
          ring
      _ ≤ (2 ^ K * (C + 1)) ^ K * ε * (N : ℝ) ^ i := by
          gcongr

/-- **`lem:supp-open-local-jets`, time-jet clause** (`eq:supp-open-inverse-time-jets`).
Let `𝓕` satisfy `DerivBound 𝓕 (ball 0 δ) K (C h^{-1})` (as given by `local_vector_bounds`).
For an exact solution `X' = 𝓕(X)` on an open time set `S` staying in the ball, at every time
`t ∈ S` with `‖X(t)‖ ≤ ε`: `‖∂_t^j q(t)‖_{H^s_h} ≤ (2^K (C + 1))^K ε h^{1-j}` for
`1 ≤ j ≤ K`. -/
theorem inverse_time_jets {B : Upper → Upper → ℝ} {δ C : ℝ} {K : ℕ} (hC : 0 ≤ C)
    (h : DerivBound (lawField (N := N) s B) (ball 0 δ) K (C * N)) {S : Set ℝ} (hS : IsOpen S)
    {X : ℝ → XS N s} (hXU : ∀ t ∈ S, X t ∈ ball 0 δ)
    (hX : ∀ t ∈ S, HasDerivAt X (lawField s B (X t)) t) {t : ℝ} (ht : t ∈ S) {ε : ℝ}
    (hε : ‖X t‖ ≤ ε) (j : ℕ) (hj1 : 1 ≤ j) (hjK : j ≤ K) :
    ‖iteratedDeriv j (fun τ => Lq s (X τ)) t‖ ≤ (2 ^ K * (C + 1)) ^ K * ε * (N : ℝ) ^ (j - 1) := by
  rw [iteratedDeriv_clm_eq_vfJet h.contDiffOn isOpen_ball hS hXU hX (Lq s) j t ht]
  exact jet_q_bound s hC h (hXU t ht) hε j hj1 hjK

/-! ### Locality of the jets -/

/-- The box of radius `ρ` (in lattice steps, `ℓ^∞`) around a site. -/
def box (x : Grid N) (ρ : ℕ) : Set (Grid N) :=
  {y | ∃ d : Fin 3 → ℤ, (∀ i, |d i| ≤ ρ) ∧ y = x + fun i => (d i : ZMod N)}

theorem mem_box_self (x : Grid N) (ρ : ℕ) : x ∈ box x ρ :=
  ⟨0, fun i => by simp, by funext i; simp⟩

theorem box_mono {x : Grid N} {ρ ρ' : ℕ} (h : ρ ≤ ρ') : box x ρ ⊆ box x ρ' := by
  rintro y ⟨d, hd, rfl⟩
  exact ⟨d, fun i => (hd i).trans (by exact_mod_cast h), rfl⟩

theorem box_trans {x y z : Grid N} {ρ k : ℕ} (hy : y ∈ box x ρ) (hz : z ∈ box y k) :
    z ∈ box x (ρ + k) := by
  obtain ⟨d, hd, rfl⟩ := hy
  obtain ⟨d', hd', rfl⟩ := hz
  refine ⟨d + d', fun i => ?_, ?_⟩
  · have := abs_add_le (d i) (d' i)
    have h1 := hd i
    have h2 := hd' i
    simp only [Pi.add_apply]
    push_cast
    linarith
  · funext i; simp [add_assoc]

theorem add_e_mem_box (y : Grid N) (i : Fin 3) : y + e N i ∈ box y 1 := by
  refine ⟨Pi.single i 1, fun j => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  · funext j
    by_cases h : j = i
    · subst h; simp [e]
    · simp [e, Pi.single_apply, h]

theorem sub_e_mem_box (y : Grid N) (i : Fin 3) : y - e N i ∈ box y 1 := by
  refine ⟨-Pi.single i 1, fun j => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  · funext j
    by_cases h : j = i
    · subst h; simp [e, sub_eq_add_neg]
    · simp [e, Pi.single_apply, h]

theorem stencil_mem_box {y z : Grid N} (h : InStencil (e N) y z) : z ∈ box y 2 := by
  rcases h with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · exact mem_box_self _ _
  · exact box_mono (by norm_num) (add_e_mem_box y i)
  · exact box_mono (by norm_num) (sub_e_mem_box y i)
  · exact box_trans (sub_e_mem_box y i) (add_e_mem_box _ j)

/-- `Λ_h` loses one lattice step of locality. -/
theorem lapR_congr {u u' : Grid N → ℝ} {y : Grid N} {ρ : ℕ}
    (h : ∀ z ∈ box y (ρ + 1), u z = u' z) : ∀ z ∈ box y ρ, lapR u z = lapR u' z := by
  intro z hz
  have h1 : ∀ i, u (z + e N i) = u' (z + e N i) := fun i => h _ (box_trans hz (add_e_mem_box z i))
  have h2 : ∀ i, u (z - e N i) = u' (z - e N i) := fun i => h _ (box_trans hz (sub_e_mem_box z i))
  have h0 : u z = u' z := h _ (box_mono (Nat.le_succ ρ) hz)
  simp only [lapR_apply, OpenWriterEnergy.Dm_apply, OpenWriterEnergy.Dp_apply, sub_add_cancel,
    h0, h1, h2]

/-- Two states agree (all components) on a set of sites. -/
def AgreeOn (S : Set (Grid N)) (X X' : XS N s) : Prop :=
  ∀ y ∈ S, ∀ κ, val (X.1 κ) y = val (X'.1 κ) y ∧ val (X.2 κ) y = val (X'.2 κ) y

/-- Restriction of a state to a set of sites (zero outside), a continuous linear map. -/
def restr (S : Set (Grid N)) : XS N s →L[ℝ] XS N s :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (fun κ => mk (S.indicator (val (X.1 κ))),
        fun κ => mk (S.indicator (val (X.2 κ))))
      map_add' := fun X Y => by
        refine Prod.ext (funext fun κ => GridH.ext fun x => ?_) (funext fun κ => GridH.ext fun x => ?_)
        · show S.indicator (val (X.1 κ) + val (Y.1 κ)) x =
            S.indicator (val (X.1 κ)) x + S.indicator (val (Y.1 κ)) x
          by_cases hx : x ∈ S
          · simp only [Set.indicator_of_mem hx]; rfl
          · simp only [Set.indicator_of_notMem hx]; simp
        · show S.indicator (val (X.2 κ) + val (Y.2 κ)) x =
            S.indicator (val (X.2 κ)) x + S.indicator (val (Y.2 κ)) x
          by_cases hx : x ∈ S
          · simp only [Set.indicator_of_mem hx]; rfl
          · simp only [Set.indicator_of_notMem hx]; simp
      map_smul' := fun c X => by
        refine Prod.ext (funext fun κ => GridH.ext fun x => ?_) (funext fun κ => GridH.ext fun x => ?_)
        · show S.indicator (c • val (X.1 κ)) x = c * S.indicator (val (X.1 κ)) x
          by_cases hx : x ∈ S
          · simp only [Set.indicator_of_mem hx]; rfl
          · simp only [Set.indicator_of_notMem hx]; simp
        · show S.indicator (c • val (X.2 κ)) x = c * S.indicator (val (X.2 κ)) x
          by_cases hx : x ∈ S
          · simp only [Set.indicator_of_mem hx]; rfl
          · simp only [Set.indicator_of_notMem hx]; simp }

theorem restr_apply_fst (S : Set (Grid N)) (X : XS N s) (κ : Upper) (y : Grid N) :
    val ((restr s S X).1 κ) y = S.indicator (val (X.1 κ)) y := rfl

theorem restr_apply_snd (S : Set (Grid N)) (X : XS N s) (κ : Upper) (y : Grid N) :
    val ((restr s S X).2 κ) y = S.indicator (val (X.2 κ)) y := rfl

theorem restr_fst (S : Set (Grid N)) (X : XS N s) (κ : Upper) :
    val ((restr s S X).1 κ) = S.indicator (val (X.1 κ)) := rfl

theorem restr_snd (S : Set (Grid N)) (X : XS N s) (κ : Upper) :
    val ((restr s S X).2 κ) = S.indicator (val (X.2 κ)) := rfl

theorem restr_eq_iff (S : Set (Grid N)) (X X' : XS N s) :
    restr s S X = restr s S X' ↔ AgreeOn s S X X' := by
  constructor
  · intro h y hy κ
    have h1 := congrArg (fun Z : XS N s => val (Z.1 κ) y) h
    have h2 := congrArg (fun Z : XS N s => val (Z.2 κ) y) h
    simp only [restr_apply_fst, restr_apply_snd, Set.indicator_of_mem hy] at h1 h2
    exact ⟨h1, h2⟩
  · intro h
    refine Prod.ext (funext fun κ => GridH.ext fun y => ?_) (funext fun κ => GridH.ext fun y => ?_)
    · rw [restr_apply_fst, restr_apply_fst]
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact (h y hy κ).1
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    · rw [restr_apply_snd, restr_apply_snd]
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact (h y hy κ).2
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

theorem restr_restr {S S' : Set (Grid N)} (h : S' ⊆ S) (X : XS N s) :
    restr s S' (restr s S X) = restr s S' X := by
  refine Prod.ext (funext fun κ => GridH.ext fun y => ?_) (funext fun κ => GridH.ext fun y => ?_)
  · rw [restr_apply_fst, restr_fst, Set.indicator_indicator, Set.inter_eq_left.mpr h]
    rfl
  · rw [restr_apply_snd, restr_snd, Set.indicator_indicator, Set.inter_eq_left.mpr h]
    rfl

/-- **Locality of the writer** (radius two): the field on the box of radius `ρ` depends only on
the state on the box of radius `ρ + 2`. -/
theorem lawField_local (B : Upper → Upper → ℝ) (x : Grid N) (ρ : ℕ) (X X' : XS N s)
    (h : AgreeOn s (box x (ρ + 2)) X X') :
    AgreeOn s (box x ρ) (lawField s B X) (lawField s B X') := by
  intro y hy κ
  have hyb : ∀ z ∈ box y 2, z ∈ box x (ρ + 2) := fun z hz => box_trans hy hz
  refine ⟨(h y (box_mono (by omega) hy) κ).2, ?_⟩
  show lawAccel B (recOf X.1) (recOf X.2) y κ.1.1 κ.1.2 =
    lawAccel B (recOf X'.1) (recOf X'.2) y κ.1.1 κ.1.2
  have hq : ∀ z ∈ box y 2, recOf X.1 z = recOf X'.1 z := fun z hz => by
    funext μ ν; exact (h z (hyb z hz) _).1
  have hv : ∀ z ∈ box y 2, recOf X.2 z = recOf X'.2 z := fun z hz => by
    funext μ ν; exact (h z (hyb z hz) _).2
  have hW : harmonicWriterAcceleration (recOf X.1) (recOf X.2) y =
      harmonicWriterAcceleration (recOf X'.1) (recOf X'.2) y := by
    unfold harmonicWriterAcceleration openWriterAcceleration
    exact writerAcceleration_local _ _ _ _ _ _ _ _ _ _ _ _ _ y
      (fun z hz => hq z (stencil_mem_box hz)) (fun z hz => hv z (stencil_mem_box hz))
  have hl : ∀ l : Upper, lapR (lapR (comp (recOf X.1) l.1.1 l.1.2)) y =
      lapR (lapR (comp (recOf X'.1) l.1.1 l.1.2)) y := by
    intro l
    have hc : ∀ z ∈ box y (1 + 1), comp (recOf X.1) l.1.1 l.1.2 z =
        comp (recOf X'.1) l.1.1 l.1.2 z := fun z hz => by simp only [comp]; rw [hq z hz]
    have h1 := lapR_congr (ρ := 1) hc
    exact lapR_congr (ρ := 0) h1 y (mem_box_self y 0)
  have hF : lawForce B (recOf X.1) y = lawForce B (recOf X'.1) y := by
    funext μ ν
    simp only [lawForce, bTerm, aArr, hl, hq y (mem_box_self y 2)]
  simp only [lawAccel, Pi.add_apply]
  rw [hW, hF]

/-- **`lem:supp-open-local-jets`, locality clause.**  On the ball where the field is smooth, the
jet `J_j(X)` on the box of radius `ρ` around any site depends only on `X` on the box of radius
`ρ + 2j`: each initial jet is a function of a fixed-radius neighbourhood of the source,
independent of the mesh. -/
theorem jets_local {B : Upper → Upper → ℝ} {U : Set (XS N s)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ (lawField s B) U) (x : Grid N) (j ρ : ℕ) {X X' : XS N s}
    (hX : X ∈ U) (hX' : X' ∈ U) (h : AgreeOn s (box x (ρ + 2 * j)) X X') :
    AgreeOn s (box x ρ) (vfJet (lawField s B) j X) (vfJet (lawField s B) j X') := by
  have key := vfJet_local hF hU (fun ρ => restr s (box x ρ))
    (fun ρ ρ' hρ X => restr_restr s (box_mono hρ) X) 2
    (fun ρ Y hY Y' hY' hYY' => (restr_eq_iff s _ _ _).mpr
      (lawField_local s B x ρ Y Y' ((restr_eq_iff s _ _ _).mp hYY'))) j ρ X hX X' hX'
    ((restr_eq_iff s _ _ _).mpr h)
  exact (restr_eq_iff s _ _ _).mp key


/-! ### `lem:supp-open-local-jets` -/

include hs in
/-- **`lem:supp-open-local-jets`** (inverse-mesh time jets for a local finite writer).  Fix
`s ≥ 2` (the manuscript takes `s ≥ 11`), an order `K ≥ 1` (the manuscript uses `K = 9` for the
field and `K = 8` for the jets) and a bound `b` on the mark entries.  There are `δ > 0` and `C`,
independent of the mesh `h = 1/N` and of the mark `B` (`|B_{kl}| ≤ b`; `B = 0` is the open
writer), such that on the common ball `‖X‖ < δ` of `𝒳^s_h`:
1. `𝓕_{B,h}` is `C^∞`, `‖D^j 𝓕_{B,h}(X)‖ ≤ C h^{-1}` for `1 ≤ j ≤ K` and
   `‖𝓕_{B,h}(X)‖ ≤ C h^{-1} ‖X‖` (`eq:supp-open-local-vector-bounds`);
2. the jets `J_1 = 𝓕`, `J_{j+1} = DJ_j 𝓕` satisfy `‖(J_j X)_q‖_{H^s_h} ≤ C ε h^{1-j}` when
   `‖X‖ ≤ ε`, and along every exact solution through a source of size `≤ ε`,
   `‖∂_t^j q‖_{H^s_h} ≤ C ε h^{1-j}` for `1 ≤ j ≤ K` (`eq:supp-open-inverse-time-jets`);
3. `J_j(X)` on the box of radius `ρ` around any site depends only on `X` on the box of radius
   `ρ + 2j` (fixed-radius neighbourhood, independent of `h`). -/
theorem supp_open_local_jets (K : ℕ) (hK : 1 ≤ K) (b : ℝ) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ), (∀ k l, |B k l| ≤ b) →
      ContDiffOn ℝ ∞ (lawField (N := N) s B) (ball 0 δ) ∧
      (∀ X ∈ ball (0 : XS N s) δ, ∀ j, 1 ≤ j → j ≤ K →
        ‖iteratedFDeriv ℝ j (lawField s B) X‖ ≤ C * N) ∧
      (∀ X ∈ ball (0 : XS N s) δ, ‖lawField s B X‖ ≤ C * N * ‖X‖) ∧
      (∀ X ∈ ball (0 : XS N s) δ, ∀ ε, ‖X‖ ≤ ε → ∀ j, 1 ≤ j → j ≤ K →
        ‖Lq s (vfJet (lawField s B) j X)‖ ≤ C * ε * (N : ℝ) ^ (j - 1)) ∧
      (∀ (S : Set ℝ) (X : ℝ → XS N s), IsOpen S → (∀ t ∈ S, X t ∈ ball 0 δ) →
        (∀ t ∈ S, HasDerivAt X (lawField s B (X t)) t) → ∀ t ∈ S, ∀ ε, ‖X t‖ ≤ ε →
        ∀ j, 1 ≤ j → j ≤ K →
          ‖iteratedDeriv j (fun τ => Lq s (X τ)) t‖ ≤ C * ε * (N : ℝ) ^ (j - 1)) ∧
      (∀ (x : Grid N) (j ρ : ℕ) (X X' : XS N s), X ∈ ball 0 δ → X' ∈ ball 0 δ →
        AgreeOn s (box x (ρ + 2 * j)) X X' →
        AgreeOn s (box x ρ) (vfJet (lawField s B) j X) (vfJet (lawField s B) j X')) := by
  obtain ⟨δ, hδ, C0, hC0, hb⟩ := local_vector_bounds s hs K b
  set CJ := (2 ^ K * (C0 + 1)) ^ K
  have hCJ : 0 ≤ CJ := by positivity
  refine ⟨δ, hδ, C0 + CJ, by positivity, fun N _ B hB => ?_⟩
  have h := hb N B hB
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hle : C0 * N ≤ (C0 + CJ) * N := by nlinarith
  refine ⟨h.contDiffOn, fun X hX j hj1 hjK => ?_, fun X hX => ?_, fun X hX ε hε j hj1 hjK => ?_,
    fun S X hS hXU hX t ht ε hε j hj1 hjK => ?_, fun x j ρ X X' hX hX' hXX' => ?_⟩
  · exact (h.bound X hX j hjK).trans hle
  · exact (norm_lawField_le s hK h hX).trans
      (mul_le_mul_of_nonneg_right hle (norm_nonneg _))
  · have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
    refine (jet_q_bound s hC0 h hX hε j hj1 hjK).trans ?_
    have : 0 ≤ ε * (N : ℝ) ^ (j - 1) := by positivity
    nlinarith
  · have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
    refine (inverse_time_jets s hC0 h hS hXU hX ht hε j hj1 hjK).trans ?_
    have : 0 ≤ ε * (N : ℝ) ^ (j - 1) := by positivity
    nlinarith
  · exact jets_local s isOpen_ball h.contDiffOn x j ρ hX hX' hXX'

/-- Non-vacuity: the flat history `X ≡ 0` is an exact solution of every law-family writer and
lies in every ball, so the solution clause of `supp_open_local_jets` applies to it. -/
example (B : Upper → Upper → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    (∀ t ∈ (Set.univ : Set ℝ), (fun _ : ℝ => (0 : XS N s)) t ∈ ball 0 δ) ∧
    ∀ t ∈ (Set.univ : Set ℝ), HasDerivAt (fun _ : ℝ => (0 : XS N s))
      (lawField s B ((fun _ : ℝ => (0 : XS N s)) t)) t :=
  ⟨fun _ _ => mem_ball_self hδ, fun t _ => by rw [lawField_zero]; exact hasDerivAt_const t _⟩

end

end RenewalGeometry.OpenWriterLocalJets
