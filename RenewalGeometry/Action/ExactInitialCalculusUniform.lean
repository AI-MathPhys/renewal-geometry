/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialCalculusFlatBlock
import RenewalGeometry.DiscreteAnalysis.PeriodicGridLocalAnalytic
import RenewalGeometry.DiscreteAnalysis.PeriodicGridPhaseDerivativeSobolev
import RenewalGeometry.Analysis.UniformImplicitFunction

/-!
# The joint stationary/Legendre residual on the grid Sobolev spaces, with mesh-uniform bounds
  (`lem:supp-initial-calculus`: "stationary connection and Legendre elimination are analytic on the
  retained small chart … the output loses at most the declared Sobolev orders";
  emergent-spacetime manuscript)

Fix `r ≥ 2`, odd `N`, `h = 1/N`.  The data `X = (u, π) ∈ (H^{r+2}_h)^6 × (H^{r+1}_h)^6` (`XH`) and
the unknowns `z = (A, V) ∈ (H^{r+1}_h)^{30}` (`ZH`, local index `J30`) enter the **joint residual**

  `F_h(X, z) = (γ°_h(e(I + u), ∂_tΠ(I + u, V); A), legLoc(u, π, A))`

(the explicit stationary row and the Legendre row, `FH`), built from
* `dPart`: the phase derivatives of the entries of `Π_i(e)`, `Σ_ji(e)` (pointwise analytic maps of
  `u` on `H^{r+2}_h` followed by the odd phase derivative `H^{r+2}_h → H^{r+1}_h`, norm `≤ 1`),
* `locPart`: ONE spacing-dependent local analytic operator (`GridLocalOps.localOp`) with stencil
  `κF` (metric at `x - o_ℓ`, velocity and momentum at `x`, connection at `x - o_ℓ + o_ν`) and
  coefficient function `Gst` (load velocity part + Cartan operator + link-remainder gradient
  `NhLoc`, and the Legendre row), analytic at `(h, ξ) = (0, 0)` (`analyticAt_Gst`).

* **`exists_derivBound_FH`**: for every `K` there are `ρ, M, h₀ > 0`, independent of `N`, with
  `DerivBound (FH N) (B(0, ρ)) K M` for all odd `N` with `h < h₀`.
-/

open Filter Finset Metric Set
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.InitialCalculus

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open QuadJet PeriodicGridSobolev GridLocalOps IteratedDerivBounds UniformDerivBounds
open LocalSumGradient

/-! ### Spaces and decoders -/

/-- Metric-type arrays in `H^s_h`. -/
abbrev MetH (N s : ℕ) := Fin 6 → GridH N s

/-- The data space `P^r_h = (H^{r+2}_h)^6 × (H^{r+1}_h)^6` of `(u, π)`. -/
abbrev XH (N r : ℕ) := MetH N (r + 2) × MetH N (r + 1)

/-- The unknowns `(A, V) ∈ (H^{r+1}_h)^{30}`. -/
abbrev ZH (N r : ℕ) := J30 → GridH N (r + 1)

variable {N : ℕ} [NeZero N]

/-- The metric field of a metric-type array. -/
def metOf {s : ℕ} (u : MetH N s) : MetF N := fun y c => GridH.val (u c) y

/-- The connection of an unknown. -/
def connOfZ {s : ℕ} (z : J30 → GridH N s) : Conn N := fun y μ k => GridH.val (z (Sum.inl (μ, k))) y

/-- The velocity of an unknown. -/
def velOfZ {s : ℕ} (z : J30 → GridH N s) : MetF N := fun y c => GridH.val (z (Sum.inr c)) y

/-! ### Packing the fields -/

/-- Field index of the local operator: metric, momentum, unknowns. -/
abbrev FI := Fin 6 ⊕ Fin 6 ⊕ J30

/-- The component maps of the packing. -/
def packComp (r : ℕ) : FI → (XH N r × ZH N r →L[ℝ] GridH N (r + 1)) :=
  Sum.elim (fun c => (GridH.incl (N := N) (r := r + 1) (r' := r + 2) (by omega)).comp
      ((ContinuousLinearMap.proj c).comp ((ContinuousLinearMap.fst ℝ _ _).comp
        (ContinuousLinearMap.fst ℝ _ _))))
    (Sum.elim (fun c => (ContinuousLinearMap.proj c).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        (ContinuousLinearMap.fst ℝ _ _)))
      (fun m => (ContinuousLinearMap.proj m).comp (ContinuousLinearMap.snd ℝ _ _)))

/-- The packing `(X, z) ↦ (u, π, z)` at level `r + 1`. -/
def packL (r : ℕ) : XH N r × ZH N r →L[ℝ] (FI → GridH N (r + 1)) :=
  ContinuousLinearMap.pi (packComp r)

theorem norm_packComp_le (r : ℕ) (i : FI) : ‖packComp (N := N) r i‖ ≤ 1 := by
  have hf : ‖ContinuousLinearMap.fst ℝ (XH N r) (ZH N r)‖ ≤ 1 := ContinuousLinearMap.norm_fst_le _ _ _
  have hs : ‖ContinuousLinearMap.snd ℝ (XH N r) (ZH N r)‖ ≤ 1 := ContinuousLinearMap.norm_snd_le _ _ _
  have hf' : ‖ContinuousLinearMap.fst ℝ (MetH N (r + 2)) (MetH N (r + 1))‖ ≤ 1 :=
    ContinuousLinearMap.norm_fst_le _ _ _
  have hs' : ‖ContinuousLinearMap.snd ℝ (MetH N (r + 2)) (MetH N (r + 1))‖ ≤ 1 :=
    ContinuousLinearMap.norm_snd_le _ _ _
  have hp : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (c : ι),
      ‖(ContinuousLinearMap.proj c : (ι → GridH N s) →L[ℝ] GridH N s)‖ ≤ 1 := fun c =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      rw [one_mul]; exact norm_le_pi_norm v c
  have hc : ∀ {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
      [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (g : F →L[ℝ] G) (f : E →L[ℝ] F),
      ‖g‖ ≤ 1 → ‖f‖ ≤ 1 → ‖g.comp f‖ ≤ 1 := fun g f hg hf =>
    (ContinuousLinearMap.opNorm_comp_le g f).trans (by nlinarith [norm_nonneg g, norm_nonneg f])
  rcases i with c | c | m
  · exact hc _ _ (GridH.norm_incl_le _) (hc _ _ (hp c) (hc _ _ hf' hf))
  · exact hc _ _ (hp c) (hc _ _ hs' hf)
  · exact hc _ _ (hp m) hs

theorem norm_packL_le (r : ℕ) : ‖packL (N := N) r‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  calc ‖packComp (N := N) r i q‖ ≤ ‖packComp (N := N) r i‖ * ‖q‖ := (packComp r i).le_opNorm q
    _ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right (norm_packComp_le r i) (norm_nonneg _)

/-! ### The stencil of the local operator -/

/-- The stencil: metric at `x - o_ℓ`, velocity at `x`, connection at `x - o_ℓ + o_ν`, momentum
at `x`. -/
abbrev KF := (Fin 4 × Fin 6) ⊕ Fin 6 ⊕ (Fin 4 × Fin 4 × (Fin 4 × Fin 6)) ⊕ Fin 6

/-- The input slot of each stencil entry. -/
def jF : KF → FI
  | Sum.inl (_, c) => Sum.inl c
  | Sum.inr (Sum.inl c) => Sum.inr (Sum.inr (Sum.inr c))
  | Sum.inr (Sum.inr (Sum.inl (_, _, m))) => Sum.inr (Sum.inr (Sum.inl m))
  | Sum.inr (Sum.inr (Sum.inr c)) => Sum.inr (Sum.inl c)

/-- The offset of each stencil entry. -/
def oF (N : ℕ) [NeZero N] : KF → Grid N
  | Sum.inl (ℓ, _) => -(offs ℓ : Site N)
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl (ℓ, ν, _))) => -(offs ℓ : Site N) + offs ν
  | Sum.inr (Sum.inr (Sum.inr _)) => 0

/-- Metric values in the stencil. -/
def uL (ξ : KF → ℝ) (ℓ : Fin 4) : Fin 6 → ℝ := fun c => ξ (Sum.inl (ℓ, c))
/-- Velocity value in the stencil. -/
def vL (ξ : KF → ℝ) : Fin 6 → ℝ := fun c => ξ (Sum.inr (Sum.inl c))
/-- Connection values in the stencil. -/
def aL (ξ : KF → ℝ) (ℓ ν : Fin 4) : LocVal := fun μ k => ξ (Sum.inr (Sum.inr (Sum.inl (ℓ, ν, (μ, k)))))
/-- Momentum value in the stencil. -/
def pL (ξ : KF → ℝ) : Fin 6 → ℝ := fun c => ξ (Sum.inr (Sum.inr (Sum.inr c)))

/-- The stationary-row coefficient (without the load phase derivatives). -/
def GstA (χ : ℝ) (μ : Fin 4) (k : Fin 6) (q : ℝ × (KF → ℝ)) : ℝ :=
  fLocP (fun i => PdLoc χ (uL q.2 0) (vL q.2) i) μ k +
    cartLoc χ (eU (uL q.2 0)) (aL q.2 0 0) μ k +
    NhLoc χ (q.1, fun ℓ => eU (uL q.2 ℓ), fun ℓ ν => aL q.2 ℓ ν) μ k

/-- The Legendre-row coefficient. -/
def GstB (χ : ℝ) (c : Fin 6) (q : ℝ × (KF → ℝ)) : ℝ :=
  legLoc χ (uL q.2 0) (pL q.2) (aL q.2 0 0) c

/-- **The coefficient function of the joint residual** (without the load phase derivatives). -/
def Gst (χ : ℝ) (m : J30) : ℝ × (KF → ℝ) → ℝ :=
  Sum.elim (fun mk : Fin 4 × Fin 6 => GstA χ mk.1 mk.2) (fun c => GstB χ c) m

/-! ### Analyticity of the coefficient function -/

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}

theorem analyticAt_eval_comp {ι : Type*} [Fintype ι] {f : E → ι → ℝ} (hf : AnalyticAt ℝ f p₀)
    (i : ι) : AnalyticAt ℝ (fun q => f q i) p₀ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).analyticAt _).comp hf

theorem analyticAt_PdLoc_fixed (χ : ℝ) (V : Fin 6 → ℝ) (i : Fin 3) (K L : Fin 4) :
    AnalyticAt ℝ (fun v : Fin 6 → ℝ => PdLoc χ v V i K L) 0 := by
  have hE : AnalyticAt ℝ (piEntry χ sqrtTriad i K L) (flatSym + 0) := by
    refine analyticAt_piEntry χ ?_ i K L
    rw [add_zero, symMat_flatSym]; exact analyticAt_sqrtTriad
  have hf : AnalyticAt ℝ (fun v : Fin 6 → ℝ => fderiv ℝ (piEntry χ sqrtTriad i K L) (flatSym + v)) 0 :=
    hE.fderiv.comp_of_eq (analyticAt_const.add analyticAt_id) rfl
  exact ((ContinuousLinearMap.apply ℝ ℝ V).analyticAt _).comp hf

theorem analyticAt_fLocP_comp {P : E → Fin 3 → M4} (hP : ∀ i K L, AnalyticAt ℝ (fun q => P q i K L) p₀)
    (μ : Fin 4) (k : Fin 6) : AnalyticAt ℝ (fun q => fLocP (P q) μ k) p₀ := by
  cases μ using Fin.cases with
  | zero => exact analyticAt_const
  | succ i =>
    simp only [fLocP, Fin.cases_succ]
    exact analyticAt_coordM (analyticAt_of_entries fun K L => (hP i K L).neg) k

end Analytic

theorem analyticAt_uL_comp (ℓ : Fin 4) :
    AnalyticAt ℝ (fun q : ℝ × (KF → ℝ) => uL q.2 ℓ) (0, 0) :=
  AnalyticAt.pi fun c => analyticAt_eval_comp analyticAt_snd _

theorem analyticAt_vL_comp : AnalyticAt ℝ (fun q : ℝ × (KF → ℝ) => vL q.2) (0, 0) :=
  AnalyticAt.pi fun c => analyticAt_eval_comp analyticAt_snd _

theorem analyticAt_pL_comp : AnalyticAt ℝ (fun q : ℝ × (KF → ℝ) => pL q.2) (0, 0) :=
  AnalyticAt.pi fun c => analyticAt_eval_comp analyticAt_snd _

theorem analyticAt_aL_comp (ℓ ν : Fin 4) :
    AnalyticAt ℝ (fun q : ℝ × (KF → ℝ) => aL q.2 ℓ ν) (0, 0) :=
  AnalyticAt.pi fun μ => AnalyticAt.pi fun k => analyticAt_eval_comp analyticAt_snd _

theorem uL_zero (ℓ : Fin 4) : uL (0 : KF → ℝ) ℓ = 0 := rfl

theorem aL_zero (ℓ ν : Fin 4) : aL (0 : KF → ℝ) ℓ ν = 0 := rfl

theorem analyticAt_GstA (χ : ℝ) (μ : Fin 4) (k : Fin 6) : AnalyticAt ℝ (GstA χ μ k) (0, 0) := by
  have he : ∀ ℓ, AnalyticAt ℝ (fun q : ℝ × (KF → ℝ) => eU (uL q.2 ℓ)) (0, 0) := fun ℓ =>
    analyticAt_eU_comp (analyticAt_uL_comp ℓ) rfl
  have hP : ∀ i K L, AnalyticAt ℝ (fun q : ℝ × (KF → ℝ) => PdLoc χ (uL q.2 0) (vL q.2) i K L)
      (0, 0) := fun i K L =>
    (analyticAt_PdLoc χ i K L).comp_of_eq ((analyticAt_uL_comp 0).prod analyticAt_vL_comp) rfl
  have h1 : AnalyticAt ℝ (fun q : ℝ × (KF → ℝ) => ((q.1, fun ℓ => eU (uL q.2 ℓ),
      fun ℓ ν => aL q.2 ℓ ν) : ℝ × (Fin 4 → M4) × (Fin 4 → Cfg))) (0, 0) :=
    analyticAt_fst.prod ((AnalyticAt.pi he).prod
      (AnalyticAt.pi fun ℓ => AnalyticAt.pi fun ν => analyticAt_aL_comp ℓ ν))
  have h0 : (fun q : ℝ × (KF → ℝ) => ((q.1, fun ℓ => eU (uL q.2 ℓ),
      fun ℓ ν => aL q.2 ℓ ν) : ℝ × (Fin 4 → M4) × (Fin 4 → Cfg))) (0, 0) =
      ((0 : ℝ), (fun _ => (1 : M4)), (0 : Fin 4 → Cfg)) := by
    simp only [uL_zero, eU_zero]
    rfl
  have hN : AnalyticAt ℝ (fun q : ℝ × (KF → ℝ) => NhLoc χ (q.1, fun ℓ => eU (uL q.2 ℓ),
      fun ℓ ν => aL q.2 ℓ ν)) (0, 0) := (analyticAt_NhLoc χ (fun _ => 1)).comp_of_eq h1 h0
  unfold GstA
  exact ((analyticAt_fLocP_comp hP μ k).add (analyticAt_cartLoc_comp χ (he 0)
    (analyticAt_aL_comp 0 0) μ k)).add (analyticAt_pi_apply (analyticAt_pi_apply hN μ) k)

theorem analyticAt_GstB (χ : ℝ) (c : Fin 6) : AnalyticAt ℝ (GstB χ c) (0, 0) := by
  unfold GstB legLoc
  refine AnalyticAt.add ?_ (Finset.analyticAt_fun_sum _ fun i _ => ?_)
  · have : (fun q : ℝ × (KF → ℝ) => frob (pL q.2) (Pi.single c 1)) =
        fun q => ∑ p, ∑ s, symMat (pL q.2) p s * symMat (Pi.single c (1 : ℝ)) p s := rfl
    rw [this]
    exact Finset.analyticAt_fun_sum _ fun p _ => Finset.analyticAt_fun_sum _ fun s _ =>
      (analyticAt_eval_comp analyticAt_pL_comp _).mul analyticAt_const
  · have hP : AnalyticAt ℝ (fun q : ℝ × (KF → ℝ) => PdLoc χ (uL q.2 0) (Pi.single c 1) i) (0, 0) :=
      analyticAt_of_entries fun K L =>
        (analyticAt_PdLoc_fixed χ (Pi.single c 1) i K L).comp_of_eq (analyticAt_uL_comp 0) rfl
    exact analyticAt_pairing_comp hP (analyticAt_iota_comp' (analyticAt_pi_apply
      (analyticAt_aL_comp 0 0) i.succ))

/-- **The coefficient function is analytic at `(0, 0)`.** -/
theorem analyticAt_Gst (χ : ℝ) (m : J30) : AnalyticAt ℝ (Gst χ m) (0, 0) := by
  rcases m with ⟨μ, k⟩ | c
  · exact analyticAt_GstA χ μ k
  · exact analyticAt_GstB χ c

/-! ### The load phase derivatives -/

/-- Indices of the entries of `Π_i(e)` and `Σ_ji(e)` that are differentiated. -/
abbrev Pidx := (Fin 3 × Fin 4 × Fin 4) ⊕ (Fin 3 × Fin 3 × Fin 4 × Fin 4)

/-- The pointwise coefficient functions `v ↦ Π_i(e(I + v))_{KL}`, `v ↦ Σ_ji(e(I + v))_{KL}`. -/
def pfun (χ : ℝ) : Pidx → (Fin 6 → ℝ) → ℝ
  | Sum.inl (i, K, L) => fun v => piArr χ (eU v) i K L
  | Sum.inr (j, i, K, L) => fun v => sigmaArr χ (eU v) j i K L

/-- The direction of the phase derivative applied to each entry. -/
def dirP : Pidx → Fin 3
  | Sum.inl (i, _, _) => i
  | Sum.inr (j, _, _, _) => j

theorem analyticAt_pfun (χ : ℝ) (p : Pidx) : AnalyticAt ℝ (pfun χ p) 0 := by
  have he : AnalyticAt ℝ eU 0 := analyticAt_eU
  rcases p with ⟨i, K, L⟩ | ⟨j, i, K, L⟩
  · exact analyticAt_entry_comp (analyticAt_piArr_comp χ i he) K L
  · exact analyticAt_entry_comp (analyticAt_sigmaArr_comp χ j i he) K L

/-- The pointwise compositions on `H^{r+2}_h`. -/
def PW (χ : ℝ) (r : ℕ) (u : MetH N (r + 2)) : Pidx → GridH N (r + 2) :=
  fun p => GridH.pointwise (pfun χ p) 0 u

/-- The phase derivatives `H^{r+2}_h → H^{r+1}_h` of all entries (odd `N`). -/
def pdAll (hNo : Odd N) (r : ℕ) : (Pidx → GridH N (r + 2)) →L[ℝ] (Pidx → GridH N (r + 1)) :=
  ContinuousLinearMap.pi fun p =>
    (PhaseDerivSobolev.GridH.pdL hNo (r + 1) (dirP p)).comp (ContinuousLinearMap.proj p)

theorem norm_pdAll_le (hNo : Odd N) (r : ℕ) : ‖pdAll hNo r‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  calc ‖(PhaseDerivSobolev.GridH.pdL hNo (r + 1) (dirP p)) (v p)‖
      ≤ ‖PhaseDerivSobolev.GridH.pdL hNo (r + 1) (dirP p)‖ * ‖v p‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖v‖ := mul_le_mul (PhaseDerivSobolev.GridH.norm_pdL_le hNo _ _) (norm_le_pi_norm v p)
        (norm_nonneg _) zero_le_one

/-- The load (phase-derivative part) from the differentiated entries, at one site. -/
def LcoordFun (d : Pidx → ℝ) : J30 → ℝ :=
  Sum.elim (fun mk : Fin 4 × Fin 6 => fLoc (fun i K L => d (Sum.inl (i, K, L)))
    (fun j i K L => d (Sum.inr (j, i, K, L))) 0 mk.1 mk.2) (fun _ => 0)

/-- `coord` in matrix entries. -/
theorem coord_eq_sum (X : M4) (k : Fin 6) :
    coord X k = ∑ K, ∑ L, (lorBasis k L K / gram k) * X K L := by
  unfold coord pairing
  rw [Matrix.trace, Finset.sum_div]
  simp only [Matrix.diag, Matrix.mul_apply, Finset.sum_div]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => by ring

theorem LcoordFun_eq (d : Pidx → ℝ) : LcoordFun d = Sum.elim
    (fun mk : Fin 4 × Fin 6 => Fin.cases (motive := fun _ => ℝ)
      (∑ i, ∑ K, ∑ L, (lorBasis mk.2 L K / gram mk.2) * d (Sum.inl (i, K, L)))
      (fun i => -∑ j, ∑ K, ∑ L, (lorBasis mk.2 L K / gram mk.2) * d (Sum.inr (j, i, K, L))) mk.1)
    (fun _ => 0) := by
  funext m
  rcases m with ⟨μ, k⟩ | c
  · cases μ using Fin.cases with
    | zero =>
      simp only [LcoordFun, Sum.elim_inl, fLoc, Fin.cases_zero, coord_eq_sum, Matrix.sum_apply,
        Matrix.of_apply, Finset.mul_sum]
      simp only [Fin.sum_univ_four, Fin.sum_univ_three]
      ring
    | succ i =>
      simp only [LcoordFun, Sum.elim_inl, fLoc, Fin.cases_succ, coord_eq_sum, Pi.zero_apply,
        neg_zero, zero_add, Matrix.neg_apply, Matrix.sum_apply, Matrix.of_apply, mul_neg,
        Finset.sum_neg_distrib, Finset.mul_sum]
      simp only [Fin.sum_univ_four, Fin.sum_univ_three]
      ring
  · rfl

/-- The load as a linear map of the differentiated entries. -/
def Lcoord : (Pidx → ℝ) →ₗ[ℝ] (J30 → ℝ) where
  toFun := LcoordFun
  map_add' d d' := by
    rw [LcoordFun_eq, LcoordFun_eq, LcoordFun_eq]
    funext m
    rcases m with ⟨μ, k⟩ | c
    · cases μ using Fin.cases with
      | zero =>
        simp only [Sum.elim_inl, Fin.cases_zero, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      | succ i =>
        simp only [Sum.elim_inl, Fin.cases_succ, Pi.add_apply, mul_add, Finset.sum_add_distrib,
          neg_add]
    · simp
  map_smul' t d := by
    rw [LcoordFun_eq, LcoordFun_eq]
    funext m
    rcases m with ⟨μ, k⟩ | c
    · cases μ using Fin.cases with
      | zero =>
        simp only [Sum.elim_inl, Fin.cases_zero, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring
      | succ i =>
        simp only [Sum.elim_inl, Fin.cases_succ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
        congr 1
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring
    · simp

theorem Lcoord_apply (d : Pidx → ℝ) : Lcoord d = LcoordFun d := rfl

/-! ### The joint residual -/

/-- **The joint stationary/Legendre residual** on `P^r_h × (H^{r+1}_h)^{30}`. -/
def FH (hNo : Odd N) (χ : ℝ) (r : ℕ) (q : XH N r × ZH N r) : ZH N r :=
  applyLinH (r + 1) Lcoord (pdAll hNo r (PW χ r q.1.1)) +
    fun m => localOp (r + 1) (Gst χ m) 0 (hN N) jF (oF N) (packL r q)

theorem norm_fst_fst_le (r : ℕ) :
    ‖(ContinuousLinearMap.fst ℝ (MetH N (r + 2)) (MetH N (r + 1))).comp
      (ContinuousLinearMap.fst ℝ (XH N r) (ZH N r))‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    have h1 := ContinuousLinearMap.norm_fst_le ℝ (MetH N (r + 2)) (MetH N (r + 1))
    have h2 := ContinuousLinearMap.norm_fst_le ℝ (XH N r) (ZH N r)
    nlinarith [norm_nonneg (ContinuousLinearMap.fst ℝ (MetH N (r + 2)) (MetH N (r + 1))),
      norm_nonneg (ContinuousLinearMap.fst ℝ (XH N r) (ZH N r))])

/-- **Mesh-uniform derivative bounds for the joint residual.** -/
theorem exists_derivBound_FH (χ : ℝ) (r : ℕ) (hr : 2 ≤ r) (K : ℕ) :
    ∃ ρ > 0, ∃ M ≥ 0, ∃ h₀ > 0, ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
      DerivBound (FH hNo χ r) (ball 0 ρ) K M := by
  obtain ⟨δP, hδP, CP, hCP, hPW⟩ := GridH.uniformize'
    (fun p δ C => ∀ (N : ℕ) [NeZero N], DerivBound (GridH.pointwise (N := N) (r := r + 2)
      (pfun χ p) 0) (ball 0 δ) K C)
    (fun p δ δ' C C' _ hδ' hCC' hP N _ =>
      ((hP N).subset (ball_subset_ball hδ')).mono le_rfl hCC')
    (fun p => GridH.pointwise_derivBound (r := r + 2) (by omega) (analyticAt_pfun χ p) K)
  obtain ⟨δL, hδL, CL, hCL, hLoc⟩ := localOp_derivBound_pi (r := r + 1) (ι := FI) (by omega)
    (c := (0 : KF → ℝ)) (fun m => analyticAt_Gst χ m) K
  set ρ := min δP δL
  have hρ : 0 < ρ := lt_min hδP hδL
  refine ⟨ρ, hρ, coefNorm Lcoord * CP + CL, by
    have := coefNorm_nonneg Lcoord; positivity, δL, hδL, fun N _ hNo hh => ?_⟩
  set L1 := (ContinuousLinearMap.fst ℝ (MetH N (r + 2)) (MetH N (r + 1))).comp
    (ContinuousLinearMap.fst ℝ (XH N r) (ZH N r))
  have hPWN : DerivBound (PW (N := N) χ r) (ball 0 δP) K CP :=
    DerivBound.pi (fun p => hPW p N) isOpen_ball hCP
  have h1a := hPWN.comp_clm isOpen_ball L1 (U := ball (0 : XH N r × ZH N r) ρ) fun q hq => by
    rw [mem_ball_zero_iff] at hq ⊢
    calc ‖L1 q‖ ≤ ‖L1‖ * ‖q‖ := L1.le_opNorm q
      _ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right (norm_fst_fst_le r) (norm_nonneg _)
      _ < δP := by rw [one_mul]; exact hq.trans_le (min_le_left _ _)
  have hL1 : max 1 ‖L1‖ = 1 := max_eq_left (norm_fst_fst_le r)
  rw [hL1, one_pow, mul_one] at h1a
  set T1 := (applyLinH (N := N) (r + 1) Lcoord).comp (pdAll hNo r)
  have h1 := h1a.clm_comp isOpen_ball T1
  have hT1 : ‖T1‖ ≤ coefNorm Lcoord := (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    have a1 := norm_applyLinH_le (N := N) (r := r + 1) Lcoord
    have a2 := norm_pdAll_le hNo r
    have := coefNorm_nonneg Lcoord
    nlinarith [norm_nonneg (applyLinH (N := N) (r + 1) Lcoord), norm_nonneg (pdAll hNo r)])
  have habs : |hN N| < δL := by rw [abs_of_pos hN_pos]; exact hh
  have h2a := (hLoc N (hN N) habs jF (oF N)).comp_clm isOpen_ball (packL r)
    (U := ball (0 : XH N r × ZH N r) ρ) fun q hq => by
      rw [mem_ball_zero_iff] at hq ⊢
      calc ‖packL r q‖ ≤ ‖packL (N := N) r‖ * ‖q‖ := (packL r).le_opNorm q
        _ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right (norm_packL_le r) (norm_nonneg _)
        _ < δL := by rw [one_mul]; exact hq.trans_le (min_le_right _ _)
  have hP1 : max 1 ‖packL (N := N) r‖ = 1 := max_eq_left (norm_packL_le r)
  rw [hP1, one_pow, mul_one] at h2a
  have hsum := (h1.mono le_rfl (mul_le_mul_of_nonneg_right hT1 hCP)).add h2a isOpen_ball
  refine hsum.congr fun q => ?_
  simp only [T1, L1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', FH]

end RenewalGeometry.ExactPhaseAction.InitialCalculus
