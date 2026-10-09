/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialCalculusUniform

/-!
# The uniform joint stationary/Legendre solve on one mesh-independent ball
  (`lem:supp-initial-calculus`; emergent-spacetime manuscript)

* `FH_inl_val`, `FH_inr_val` (exact, `h` and the sup norm of `A` below an `N`-independent radius):
  the joint residual `FH` is the explicit stationary row `γ°_h(e(I + u), ∂_tΠ(I + u, V); A)` and the
  site-wise Legendre row `legLoc(u, π, A)`.
* `FH_zero`: `F_h(0) = 0`; `hasFDerivAt_FH_zero_right`: `D_zF_h(0) = M` site-wise (the flat block
  of `ExactInitialCalculusFlatBlock.lean`).
* **`exists_uniform_solve`**: there are `N`-independent `a, M, ρ, h₀` such that for every odd `N` with
  `h < h₀` the hypotheses of the uniform implicit function theorem (`UniformImplicit.Hyp`) hold for
  `F_h` with `T = M` (site-wise) and `‖T⁻¹‖ ≤ a`; hence (`UniformImplicit.Hyp.derivBound_imp`) the
  joint solution `z_h(X) = (A_h(X), V_h(X))` exists, is unique in a fixed ball, and has
  `N`-independent derivative bounds of every order on the fixed ball `B(0, del M a ρ)`.
-/

open Filter Finset Metric Set
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.InitialCalculus

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open QuadJet PeriodicGridSobolev GridLocalOps IteratedDerivBounds UniformDerivBounds
open LocalSumGradient OddPhaseDerivativeReal

variable {N : ℕ} [NeZero N]

/-! ### Values of the joint residual -/

theorem val_incl_eq {s s' : ℕ} (h : s ≤ s') (u : GridH N s') (x : Grid N) :
    GridH.val (GridH.incl (r := s) h u) x = GridH.val u x := rfl

theorem pointwise_val (A : (Fin 6 → ℝ) → ℝ) {s : ℕ} (u : MetH N s) (y : Grid N) :
    GridH.val (GridH.pointwise A 0 u) y = A (metOf u y) := by
  simp only [GridH.pointwise, GridH.val_mk, zero_add]
  rfl

theorem val_dPart (hNo : Odd N) (χ : ℝ) (r : ℕ) (u : MetH N (r + 2)) (μ : Fin 4) (k : Fin 6)
    (x : Grid N) :
    GridH.val (applyLinH (r + 1) Lcoord (pdAll hNo r (PW χ r u)) (Sum.inl (μ, k))) x =
      fLoc (fun i K L => pd i (fun y => piArr χ (eU (metOf u y)) i K L) x)
        (fun j i K L => pd j (fun y => sigmaArr χ (eU (metOf u y)) j i K L) x) 0 μ k := by
  have hv : ∀ p : Pidx, GridH.val (pdAll hNo r (PW χ r u) p) x =
      pd (dirP p) (fun y => pfun χ p (metOf u y)) x := by
    intro p
    simp only [pdAll, ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.proj_apply, PhaseDerivSobolev.GridH.pdL_val]
    have : GridH.val (PW χ r u p) = fun y => pfun χ p (metOf u y) := funext fun y => pointwise_val _ u y
    rw [this]
  rw [applyLinH_val, Lcoord_apply]
  simp only [LcoordFun, Sum.elim_inl, hv]
  rfl

/-- The stencil values of the packed fields. -/
theorem stencil_eq (r : ℕ) (q : XH N r × ZH N r) (x : Grid N) :
    (0 + fun k : KF => GridH.val (packL r q (jF k)) (x + oF N k)) =
      fun k => match k with
        | Sum.inl (ℓ, c) => metOf q.1.1 (x - offs ℓ) c
        | Sum.inr (Sum.inl c) => velOfZ q.2 x c
        | Sum.inr (Sum.inr (Sum.inl (ℓ, ν, (μ, k)))) => connOfZ q.2 (x - offs ℓ + offs ν) μ k
        | Sum.inr (Sum.inr (Sum.inr c)) => metOf q.1.2 x c := by
  funext k
  rw [zero_add]
  rcases k with ⟨ℓ, c⟩ | c | ⟨ℓ, ν, μ, k⟩ | c
  · simp only [jF, oF, packL, ContinuousLinearMap.pi_apply, packComp, Sum.elim_inl,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_fst', val_incl_eq, metOf, sub_eq_add_neg]
  · simp only [jF, oF, packL, ContinuousLinearMap.pi_apply, packComp, Sum.elim_inr,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_snd', velOfZ, add_zero]
  · simp only [jF, oF, packL, ContinuousLinearMap.pi_apply, packComp, Sum.elim_inr, Sum.elim_inl,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_snd', connOfZ, sub_eq_add_neg, add_assoc]
  · simp only [jF, oF, packL, ContinuousLinearMap.pi_apply, packComp, Sum.elim_inr, Sum.elim_inl,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', metOf, add_zero]

/-- The stencil values. -/
def stencilVal (r : ℕ) (q : XH N r × ZH N r) (x : Grid N) : KF → ℝ :=
  fun k => match k with
    | Sum.inl (ℓ, c) => metOf q.1.1 (x - offs ℓ) c
    | Sum.inr (Sum.inl c) => velOfZ q.2 x c
    | Sum.inr (Sum.inr (Sum.inl (ℓ, ν, (μ, k)))) => connOfZ q.2 (x - offs ℓ + offs ν) μ k
    | Sum.inr (Sum.inr (Sum.inr c)) => metOf q.1.2 x c

theorem val_localOp_FH (χ : ℝ) (r : ℕ) (q : XH N r × ZH N r) (m : J30) (x : Grid N) :
    GridH.val (localOp (r + 1) (Gst χ m) 0 (hN N) jF (oF N) (packL r q)) x =
      Gst χ m (hN N, stencilVal r q x) := by
  have := stencil_eq r q x
  simp only [localOp, GridH.val_mk]
  rw [this]
  rfl

theorem FH_val (hNo : Odd N) (χ : ℝ) (r : ℕ) (q : XH N r × ZH N r) (m : J30) (x : Grid N) :
    GridH.val (FH hNo χ r q m) x =
      GridH.val (applyLinH (r + 1) Lcoord (pdAll hNo r (PW χ r q.1.1)) m) x +
        Gst χ m (hN N, stencilVal r q x) := by
  rw [← val_localOp_FH]
  rfl

/-- **The Legendre components of the joint residual are the Legendre row** (exact). -/
theorem FH_inr_val (hNo : Odd N) (χ : ℝ) (r : ℕ) (q : XH N r × ZH N r) (c : Fin 6) (x : Grid N) :
    GridH.val (FH hNo χ r q (Sum.inr c)) x =
      legLoc χ (metOf q.1.1 x) (metOf q.1.2 x) (connOfZ q.2 x) c := by
  rw [FH_val, applyLinH_val, Lcoord_apply]
  simp only [LcoordFun, Sum.elim_inr, zero_add]
  show GstB χ c (hN N, stencilVal r q x) = _
  unfold GstB
  have hu : uL (stencilVal r q x) 0 = metOf q.1.1 x := by
    funext c; simp [uL, stencilVal]
  have ha : aL (stencilVal r q x) 0 0 = connOfZ q.2 x := by
    funext μ k; simp [aL, stencilVal]
  rw [hu, ha]
  rfl

/-- **The stationary components of the joint residual are the explicit stationary row**, for `h`
and the sup norm of the connection below an `N`-independent radius. -/
theorem exists_FH_inl_val : ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (hNo : Odd N) (χ : ℝ) (r : ℕ)
    (q : XH N r × ZH N r), hN N < δ → ‖connOfZ q.2‖ < δ → ∀ (μ : Fin 4) (k : Fin 6) (x : Grid N),
      GridH.val (FH hNo χ r q (Sum.inl (μ, k))) x =
        statRowExplicit χ (fun y => eU (metOf q.1.1 y))
          (fun i y => PdLoc χ (metOf q.1.1 y) (velOfZ q.2 y) i) (connOfZ q.2) x μ k := by
  obtain ⟨δ, hδ, hrow⟩ := exists_statRowExplicit_eq_local
  refine ⟨δ, hδ, fun N _ hNo χ r q hh hA μ k x => ?_⟩
  rw [FH_val, val_dPart, hrow N χ _ _ _ hh hA x]
  show _ + GstA χ μ k (hN N, stencilVal r q x) = _
  unfold GstA
  have hu : ∀ ℓ, uL (stencilVal r q x) ℓ = metOf q.1.1 (x - offs ℓ) := by
    intro ℓ; funext c; simp [uL, stencilVal]
  have hv : vL (stencilVal r q x) = velOfZ q.2 x := by
    funext c; simp [vL, stencilVal]
  have ha : ∀ ℓ ν, aL (stencilVal r q x) ℓ ν = connOfZ q.2 (x - offs ℓ + offs ν) := by
    intro ℓ ν; funext μ' k'; simp [aL, stencilVal]
  have hloc : ∀ ℓ, loc offs (x - offs ℓ) (connOfZ q.2) = fun ν => connOfZ q.2 (x - offs ℓ + offs ν) := by
    intro ℓ; funext ν; rfl
  simp only [hu, hv, ha, hloc, offs_zero, sub_zero, add_zero, Pi.add_apply]
  rw [fLoc_eq_add _ _ (fun i => PdLoc χ (metOf q.1.1 x) (velOfZ q.2 x) i)]
  simp only [Pi.add_apply]
  ring

/-! ### The residual at flat data and its normal derivative -/

theorem metOf_zero {s : ℕ} : metOf (0 : MetH N s) = 0 := rfl

theorem connOfZ_zero {s : ℕ} : connOfZ (0 : J30 → GridH N s) = 0 := rfl

theorem velOfZ_zero {s : ℕ} : velOfZ (0 : J30 → GridH N s) = 0 := rfl

theorem iota_zero' : iota (0 : Fin 6 → ℝ) = 0 := by simp [iota]

theorem legLoc_zero_zero (χ : ℝ) (c : Fin 6) : legLoc χ 0 0 0 c = 0 := by
  simp [legLoc, frob, symMat, iota_zero', pairing_zero_right]

theorem fPh_const (χ : ℝ) (E : M4) (P : Fin 3 → Site N → M4) (x : Site N) :
    fPh χ (fun _ => E) P x = fLocP (fun i => P i x) := by
  rw [fPh_apply, fLoc_eq_add]
  have h0 : fLoc (fun i K L => pd i (fun _ : Site N => piArr χ E i K L) x)
      (fun j i K L => pd j (fun _ : Site N => sigmaArr χ E j i K L) x) 0 = 0 := by
    have hc : ∀ (i : Fin 3) (c : ℝ), pd i (fun _ : Site N => c) x = 0 := fun i c => by
      rw [pd_const]; rfl
    funext μ k
    cases μ using Fin.cases with
    | zero => simp [fLoc, hc, coord_eq_sum]
    | succ i => simp [fLoc, hc, coord_eq_sum]
  rw [h0, zero_add]

/-- **`F_h(0) = 0`** (for `h` below the radius of `exists_FH_inl_val`). -/
theorem exists_FH_zero : ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (hNo : Odd N) (χ : ℝ) (r : ℕ),
    hN N < δ → FH hNo χ r 0 = 0 := by
  obtain ⟨δ, hδ, hval⟩ := exists_FH_inl_val
  refine ⟨δ, hδ, fun N _ hNo χ r hh => ?_⟩
  funext m
  refine GridH.ext fun x => ?_
  rcases m with ⟨μ, k⟩ | c
  · rw [hval N hNo χ r 0 hh (by rw [Prod.snd_zero, connOfZ_zero, norm_zero]; exact hδ)]
    simp only [Prod.fst_zero, Prod.snd_zero, metOf_zero, velOfZ_zero, connOfZ_zero, Pi.zero_apply]
    have hP : (fun (i : Fin 3) (_ : Site N) => PdLoc χ 0 0 i) = 0 := by
      funext i y; exact PdLoc_zero_right χ 0 i
    rw [hP, statRowExplicit_zero_of_fPh_zero χ _ _ (by rw [eU_zero]; exact fPh_const_zero χ 1)]
    rfl
  · rw [FH_inr_val]
    simp only [Prod.fst_zero, Prod.snd_zero, metOf_zero, connOfZ_zero, Pi.zero_apply]
    exact legLoc_zero_zero χ c

/-- The connection of an unknown, as a continuous linear map. -/
def connOfZL (r : ℕ) : ZH N r →L[ℝ] Conn N :=
  LinearMap.toContinuousLinearMap
    { toFun := connOfZ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem connOfZL_apply (r : ℕ) (z : ZH N r) : connOfZL r z = connOfZ z := rfl

/-- The encoding of a connection-valued remainder into the stationary components. -/
def encA (r : ℕ) : Conn N →L[ℝ] ZH N r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A m => Sum.elim (fun mk : Fin 4 × Fin 6 => GridH.mk (fun x => A x mk.1 mk.2))
        (fun _ => 0) m
      map_add' := fun A B => by
        funext m; rcases m with ⟨μ, k⟩ | c
        · exact GridH.ext fun x => rfl
        · simp
      map_smul' := fun t A => by
        funext m; rcases m with ⟨μ, k⟩ | c
        · exact GridH.ext fun x => rfl
        · simp }

theorem encA_inl (r : ℕ) (A : Conn N) (μ : Fin 4) (k : Fin 6) (x : Grid N) :
    GridH.val (encA r A (Sum.inl (μ, k))) x = A x μ k := rfl

theorem encA_inr (r : ℕ) (A : Conn N) (c : Fin 6) : encA r A (Sum.inr c) = 0 := rfl

/-- **The normal derivative of the joint residual at flat data is the site-wise flat block.** -/
theorem exists_hasFDerivAt_FH_zero_right : ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (hNo : Odd N) (χ : ℝ)
    (r : ℕ), hN N < δ →
      HasFDerivAt (fun z : ZH N r => FH hNo χ r (0, z)) (applyLinH (r + 1) (MlocLin χ)) 0 := by
  obtain ⟨δ, hδ, hval⟩ := exists_FH_inl_val
  obtain ⟨ε₀, hε₀, κ, hκ, hlip⟩ := exists_Nh_lipschitz
  refine ⟨δ, hδ, fun N _ hNo χ r hh => ?_⟩
  set R : ZH N r → ZH N r := fun z => encA r (Nh χ (fun _ => 1) (connOfZ z))
  -- the remainder has zero derivative
  have hR : HasFDerivAt R (0 : ZH N r →L[ℝ] ZH N r) 0 := by
    have hs : HasFDerivAt (fun z : ZH N r => connOfZL r z) (connOfZL r) 0 :=
      (connOfZL r).hasFDerivAt
    refine QuadJet.hasFDerivAt_zero_of_sq_le (K := ‖encA (N := N) r‖ * (κ * (|χ| * 1 ^ 2) * hN N))
      hs (map_zero _) ?_
    have hc : ContinuousAt (fun z : ZH N r => hN N * ‖connOfZL r z‖) 0 :=
      continuousAt_const.mul (continuous_norm.comp (connOfZL r).continuous).continuousAt
    have h0 : (fun z : ZH N r => hN N * ‖connOfZL r z‖) 0 < ε₀ := by
      show hN N * ‖connOfZ (0 : ZH N r)‖ < ε₀
      rw [connOfZ_zero, norm_zero, mul_zero]; exact hε₀
    filter_upwards [hc.eventually (gt_mem_nhds h0)] with z hz
    have he : ∀ x : Site N, ‖(fun _ : Site N => (1 : M4)) x‖ ≤ 1 := fun x => by
      show ‖(1 : M4)‖ ≤ 1
      exact le_of_eq norm_one
    have hz' : hN N * ‖connOfZ z‖ ≤ ε₀ := hz.le
    have h1 := hlip N χ 1 ‖connOfZ z‖ (fun _ => 1) (norm_nonneg _) hz' he (connOfZ z) 0 le_rfl
      (by simp)
    rw [Nh_zero, sub_zero, sub_zero] at h1
    show ‖encA (N := N) r (Nh χ (fun _ => 1) (connOfZ z))‖ ≤ _
    calc ‖encA (N := N) r (Nh χ (fun _ => 1) (connOfZ z))‖
        ≤ ‖encA (N := N) r‖ * ‖Nh χ (fun _ => 1) (connOfZ z)‖ :=
          (encA (N := N) r).le_opNorm (Nh χ (fun _ => 1) (connOfZ z))
      _ ≤ ‖encA (N := N) r‖ * (κ * (|χ| * 1 ^ 2) * (hN N * ‖connOfZ z‖) * ‖connOfZ z‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖encA (N := N) r‖ * (κ * (|χ| * 1 ^ 2) * hN N) * ‖connOfZL r z‖ ^ 2 := by
          simp only [connOfZL_apply]; ring
  -- the residual is the flat block plus the remainder near `0`
  have hev : (fun z : ZH N r => FH hNo χ r (0, z)) =ᶠ[𝓝 0]
      fun z => applyLinH (r + 1) (MlocLin χ) z + R z := by
    have hc : ContinuousAt (fun z : ZH N r => ‖connOfZL r z‖) 0 :=
      (continuous_norm.comp (connOfZL r).continuous).continuousAt
    have h0 : (fun z : ZH N r => ‖connOfZL r z‖) 0 < δ := by
      show ‖connOfZ (0 : ZH N r)‖ < δ
      rw [connOfZ_zero, norm_zero]; exact hδ
    filter_upwards [hc.eventually (gt_mem_nhds h0)] with z hz
    funext m
    refine GridH.ext fun x => ?_
    rw [Pi.add_apply, GridH.val_add, Pi.add_apply, applyLinH_val, MlocLin_apply]
    rcases m with ⟨μ, k⟩ | c
    · rw [hval N hNo χ r (0, z) hh hz]
      simp only [Prod.fst_zero, metOf_zero, Pi.zero_apply, encA_inl, R]
      simp only [statRowExplicit, Pi.add_apply, fPh_const, cartanOp_apply, eU_zero]
      have e1 : aOf (fun n => GridH.val (z n) x) = connOfZ z x := rfl
      have e2 : vOf (fun n => GridH.val (z n) x) = velOfZ z x := rfl
      simp only [MlocFun, Sum.elim_inl, e1, e2, Pi.add_apply]
      ring
    · rw [FH_inr_val]
      have e1 : aOf (fun n => GridH.val (z n) x) = connOfZ z x := rfl
      simp only [R, encA_inr, Prod.fst_zero, metOf_zero, Pi.zero_apply, GridH.val_zero, add_zero,
        MlocFun, Sum.elim_inr, e1]
      rfl
  have hsum := ((applyLinH (N := N) (r + 1) (MlocLin χ)).hasFDerivAt (x := (0 : ZH N r))).add hR
  rw [add_zero] at hsum
  exact hsum.congr_of_eventuallyEq hev

/-! ### The uniform implicit function theorem for the joint solve -/

theorem Mloc_toLinearMap {χ : ℝ} (hχ : χ ≠ 0) : (Mloc hχ).toLinearMap = MlocLin χ := by
  ext w; rfl

/-- The site-wise flat block on the unknowns, as a continuous linear equivalence. -/
def TH {χ : ℝ} (hχ : χ ≠ 0) (r : ℕ) : ZH N r ≃L[ℝ] ZH N r := applyEquivH (r + 1) (Mloc hχ)

/-- The `N`-independent bound on the inverse flat block. -/
def aBlock {χ : ℝ} (hχ : χ ≠ 0) : ℝ := coefNorm (Mloc hχ).symm.toLinearMap + 1

theorem aBlock_pos {χ : ℝ} (hχ : χ ≠ 0) : 0 < aBlock hχ := by
  have := coefNorm_nonneg (Mloc hχ).symm.toLinearMap
  unfold aBlock; linarith

/-- **The hypotheses of the uniform implicit function theorem hold for the joint solve, with
constants independent of the cutoff.**  For `χ ≠ 0`, `r ≥ 2` and every `K` there are `M, ρ > 0`
and a spacing threshold `h₀ > 0` such that for every odd `N` with `h = 1/N < h₀`, the joint
residual `F_h` satisfies `UniformImplicit.Hyp F_h T K M a ρ` with `T` the site-wise flat block and
`a` the `N`-independent bound `aBlock` on its inverse. -/
theorem exists_uniform_solve {χ : ℝ} (hχ : χ ≠ 0) (r : ℕ) (hr : 2 ≤ r) (K : ℕ) :
    ∃ M ρ h₀ : ℝ, 0 < h₀ ∧ ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
      UniformImplicit.Hyp (FH hNo χ r) (TH (N := N) hχ r) K M (aBlock hχ) ρ := by
  obtain ⟨ρ, hρ, M, hM, h₁, hh₁, hbd⟩ := exists_derivBound_FH χ r hr (K + 2)
  obtain ⟨h₂, hh₂, hzero⟩ := exists_FH_zero
  obtain ⟨h₃, hh₃, hder⟩ := exists_hasFDerivAt_FH_zero_right
  refine ⟨M, ρ, min h₁ (min h₂ h₃), lt_min hh₁ (lt_min hh₂ hh₃), fun N _ hNo hh => ?_⟩
  have hh1 : hN N < h₁ := hh.trans_le (min_le_left _ _)
  have hh2 : hN N < h₂ := hh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hh3 : hN N < h₃ := hh.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hF := hbd N hNo hh1
  refine ⟨hρ, aBlock_pos hχ, ?_, hF, hzero N hNo χ r hh2, ?_⟩
  · refine (norm_applyEquivH_symm_le (N := N) (r := r + 1) (Mloc hχ)).trans ?_
    unfold aBlock; linarith
  · have hd : DifferentiableAt ℝ (FH hNo χ r) 0 :=
      (hF.contDiffAt isOpen_ball (mem_ball_self hρ)).differentiableAt (by simp)
    have hin : HasFDerivAt (fun z : ZH N r => ((0 : XH N r), z))
        (ContinuousLinearMap.inr ℝ (XH N r) (ZH N r)) 0 :=
      (hasFDerivAt_const (0 : XH N r) (0 : ZH N r)).prodMk (hasFDerivAt_id 0)
    have hc : HasFDerivAt (fun z : ZH N r => FH hNo χ r ((0 : XH N r), z))
        ((fderiv ℝ (FH hNo χ r) 0).comp (ContinuousLinearMap.inr ℝ (XH N r) (ZH N r))) 0 := by
      have hd' : HasFDerivAt (FH hNo χ r) (fderiv ℝ (FH hNo χ r) 0) (((0 : XH N r), (0 : ZH N r))) :=
        hd.hasFDerivAt
      exact hd'.comp (0 : ZH N r) hin
    have hu := hc.unique (hder N hNo χ r hh3)
    rw [hu]
    show applyLinH (r + 1) (MlocLin χ) = applyLinH (r + 1) (Mloc hχ).toLinearMap
    rw [Mloc_toLinearMap]

/-- The joint solution `z_h(X) = (A_h(X), V_h(X))` of the uniform solve. -/
def zSol (hNo : Odd N) (χ : ℝ) (r : ℕ) (M a ρ : ℝ) : XH N r → ZH N r :=
  UniformImplicit.imp (FH hNo χ r) M a ρ

end RenewalGeometry.ExactPhaseAction.InitialCalculus
