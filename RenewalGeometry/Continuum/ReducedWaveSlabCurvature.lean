/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveSlabLipschitz
import RenewalGeometry.Gravity.CoordinateCurvature

/-!
# `thm:hyperbolic`, curvature clause: `Riem(g_h)` is Cauchy in `L¹_tH^{s-3}`

(Einstein–Standard-Model action-closure manuscript, "Common-slab metric stability".)

* `GamF`, `RiemF` — the coordinate Christoffel symbols and Riemann tensor of a smooth metric
  field, through the library's coordinate formulas (`RenewalGeometry.christoffel`,
  `RenewalGeometry.riemann` of `Gravity/CoordinateCurvature.lean`):
  `Γ^c_{ij} = ½ g^{cn}(∂ᵢg_{nj} + ∂ⱼg_{ni} - ∂_n g_{ij})`,
  `R^a_{bcd} = ∂_cΓ^a_{db} - ∂_dΓ^a_{cb} + Γ^a_{ce}Γ^e_{db} - Γ^a_{de}Γ^e_{cb}`.
* `uhi_Gam` (the Christoffel symbols are `H^{s-2}`-Lipschitz), `pd_GamF` (the derivative of `Γ`),
  `ulo_dGam` (on the slab `∂_eΓ = ½(∂_e g^{-1})Y + ½ g^{-1}∂_eY`, `∂g^{-1} = -g^{-1}(∂g)g^{-1}`),
  **`ulo_Riem`** — the Riemann tensor is `ULo`: "the coordinate formula for curvature, linear in
  the second derivatives and quadratic in first derivatives", with `∂ₜ²g` from the reduced
  equation.
* **`riem_cauchy`** — `Riem(g_h)` is Cauchy in `L¹_tH^{s-3}` under the hypotheses of
  `thm:hyperbolic` (Cauchy initial data and sources).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveStab

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ]

/-- The Christoffel symbols `Γ^c_{ij}` of a metric field (coordinate formula). -/
def GamF (g : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (c i j : Fin 4) (x : X) : ℝ :=
  christoffel (fun a b => gi a b x) (fun i j k => pd (g (j, k)) i x) c i j

/-- The Riemann tensor `R^a_{bcd}` of a metric field (coordinate formula). -/
def RiemF (g : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (a b c d : Fin 4) (x : X) : ℝ :=
  riemann (fun c i j => GamF g gi c i j x) (fun e c i j => pd (GamF g gi c i j) e x) a b c d

/-- `Y_{nij} = ∂ᵢg_{nj} + ∂ⱼg_{ni} - ∂_n g_{ij}`. -/
def Yf (g : Idx → X → ℝ) (n i j : Fin 4) (x : X) : ℝ :=
  pd (g (n, j)) i x + pd (g (n, i)) j x - pd (g (i, j)) n x

theorem GamF_eq (g : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (c i j : Fin 4) :
    GamF g gi c i j = fun x => 1 / 2 * ∑ n, gi c n x * Yf g n i j x := rfl

theorem contDiff_Yf {g : Idx → X → ℝ} (sg : ∀ c, ContDiff ℝ ∞ (g c)) (n i j : Fin 4) :
    ContDiff ℝ ∞ (Yf g n i j) := by
  unfold Yf
  exact ((contDiff_pd_top (sg _) _).add (contDiff_pd_top (sg _) _)).sub (contDiff_pd_top (sg _) _)

theorem contDiff_GamF {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    (sg : ∀ c, ContDiff ℝ ∞ (g c)) (sgi : ∀ a b, ContDiff ℝ ∞ (gi a b)) (c i j : Fin 4) :
    ContDiff ℝ ∞ (GamF g gi c i j) := by
  rw [GamF_eq]
  exact contDiff_const.mul (ContDiff.sum fun n _ => (sgi c n).mul (contDiff_Yf sg n i j))

theorem isSPeriodic_GamF {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    (pg : ∀ c, IsSPeriodic (g c)) (pgi : ∀ a b, IsSPeriodic (gi a b)) (c i j : Fin 4) :
    IsSPeriodic (GamF g gi c i j) := fun k x => by
  rw [GamF_eq]
  simp only [Yf, fun a b => pgi a b k x, fun c μ => isSPeriodic_pd (pg c) μ k x]

/-- The derivative of the Christoffel symbols (at any point). -/
theorem pd_GamF {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    (sg : ∀ c, ContDiff ℝ ∞ (g c)) (sgi : ∀ a b, ContDiff ℝ ∞ (gi a b)) (c i j e : Fin 4)
    (x : X) :
    pd (GamF g gi c i j) e x = 1 / 2 * ∑ n, (pd (gi c n) e x * Yf g n i j x +
      gi c n x * (pd (pd (g (n, j)) i) e x + pd (pd (g (n, i)) j) e x -
        pd (pd (g (i, j)) n) e x)) := by
  have hY : ∀ n, HasDerivAt (fun s : ℝ => Yf g n i j (x + s • ev e))
      (pd (pd (g (n, j)) i) e x + pd (pd (g (n, i)) j) e x - pd (pd (g (i, j)) n) e x) 0 :=
    fun n => ((hasDerivAt_line_pd (contDiff_pd_top (sg _) _) x e).fun_add
      (hasDerivAt_line_pd (contDiff_pd_top (sg _) _) x e)).fun_sub
      (hasDerivAt_line_pd (contDiff_pd_top (sg _) _) x e)
  have hd : HasDerivAt (fun s : ℝ => GamF g gi c i j (x + s • ev e))
      (1 / 2 * ∑ n, (pd (gi c n) e x * Yf g n i j x +
        gi c n x * (pd (pd (g (n, j)) i) e x + pd (pd (g (n, i)) j) e x -
          pd (pd (g (i, j)) n) e x))) 0 := by
    have := (HasDerivAt.fun_sum (u := Finset.univ) fun n _ =>
      (hasDerivAt_line_pd (sgi c n) x e).fun_mul (hY n)).const_mul (1 / 2 : ℝ)
    simp only [zero_smul, add_zero] at this
    exact this
  exact (hasDerivAt_line_pd (contDiff_GamF sg sgi c i j) x e).unique hd

/-- The decomposed derivative of the Christoffel symbols (equal to `∂_eΓ` on the slab). -/
def dGamDec (m : MD) (e c i j : Fin 4) (x : X) : ℝ :=
  1 / 2 * ∑ n, ((-1) * (∑ a, ∑ b, m.2.1 c a x * pd (m.1 (a, b)) e x * m.2.1 b n x) *
      Yf m.1 n i j x +
    m.2.1 c n x * (pd (pd (m.1 (n, j)) i) e x + pd (pd (m.1 (n, i)) j) e x -
      pd (pd (m.1 (i, j)) n) e x))

namespace Ctx

variable {C : Ctx κ}

theorem uhi_Y (G : C.Good) (n i j : Fin 4) : C.UHi (fun m => Yf m.1 n i j) :=
  ((uhi_dg G (n, j) i).add (uhi_dg G (n, i) j)).sub (uhi_dg G (i, j) n)

/-- **The Christoffel symbols are `H^{s-2}`-Lipschitz.** -/
theorem uhi_Gam (G : C.Good) (c i j : Fin 4) : C.UHi (fun m => GamF m.1 m.2.1 c i j) :=
  (UHi.sum fun n => (uhi_gi G c n).mul G.hk (uhi_Y G n i j)).const_mul (1 / 2)

theorem ulo_dGamDec (G : C.Good) (e c i j : Fin 4) : C.ULo (fun m => dGamDec m e c i j) :=
  (ULo.sum fun n =>
    ((((UHi.sum fun a => UHi.sum fun b =>
      ((uhi_gi G c a).mul G.hk (uhi_dg G (a, b) e)).mul G.hk (uhi_gi G b n)).const_mul
        (-1)).mul G.hk (uhi_Y G n i j)).toLo).add
    (ULo.mul_hi G.hk (uhi_gi G c n) (((ulo_D2 G (n, j) e i).add (ulo_D2 G (n, i) e j)).sub
      (ulo_D2 G (i, j) e n)))).const_mul (1 / 2)

/-- **The derivatives of the Christoffel symbols are `ULo`.** -/
theorem ulo_dGam (G : C.Good) (e c i j : Fin 4) :
    C.ULo (fun m => pd (GamF m.1 m.2.1 c i j) e) := by
  refine (ulo_dGamDec G e c i j).congr
    (fun m hm => contDiff_pd_top (contDiff_GamF (MetricHyp.sg hm) (MetricHyp.sgi hm) c i j) e)
    (fun m hm => isSPeriodic_pd (isSPeriodic_GamF (MetricHyp.pg hm) (MetricHyp.pgi hm) c i j) e)
    (fun m hm x hx => ?_)
  rw [pd_GamF (MetricHyp.sg hm) (MetricHyp.sgi hm)]
  unfold dGamDec
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  have he : e ≠ 0 ∨ 0 < C.T := Or.inr G.hT
  rw [pd_inv_eq (G := fun a b => m.1 (a, b)) (fun a b => MetricHyp.sg hm (a, b))
    (MetricHyp.sgi hm) (MetricHyp.inv hm) e he hx c n]
  ring

/-- **The Riemann tensor is `ULo`.** -/
theorem ulo_Riem (G : C.Good) (a b c d : Fin 4) :
    C.ULo (fun m => RiemF m.1 m.2.1 a b c d) :=
  (((ulo_dGam G c a d b).sub (ulo_dGam G d a c b)).add
    ((UHi.sum fun e => (uhi_Gam G a c e).mul G.hk (uhi_Gam G e d b)).toLo)).sub
    ((UHi.sum fun e => (uhi_Gam G a d e).mul G.hk (uhi_Gam G e c b)).toLo)

end Ctx

theorem sqrt_add3_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c :=
  (sqrt_add_le' (add_nonneg ha hb) hc).trans (by linarith [sqrt_add_le' ha hb])

/-- **`thm:hyperbolic`, curvature clause (Cauchy form)**: under the hypotheses of
`thm:hyperbolic` (`Σ = 𝕋³`, `s ≥ 5`, common constants, initial data Cauchy in
`H^{s-1} × H^{s-2}`, sources Cauchy in `L¹_tH^{s-2}`), the Riemann tensors `Riem(g_h)` are Cauchy
in `L¹_tH^{s-3}`: `∫₀ᵀ ‖Riem(g_h) - Riem(g_j)‖_{H^{s-3}} dt → 0`. -/
theorem riem_cauchy {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ} {T a0 lam Λ K0 : ℝ}
    {s : ℕ} (hs : 5 ≤ s) (hT : 0 < T) (ha : 0 < a0) (hlam : 0 < lam)
    {g : ℕ → Idx → X → ℝ} {gi : ℕ → Fin 4 → Fin 4 → X → ℝ} {S : ℕ → Idx → X → ℝ}
    (hg : ∀ h, MetricHyp Np θ s T a0 lam Λ K0 (g h) (gi h) (S h))
    (hinit : Tendsto (fun p : ℕ × ℕ => ∑ c, (Q (s - 1) (fun x => g p.1 c x - g p.2 c x) 0 +
      Q (s - 2) (fun x => pd (g p.1 c) 0 x - pd (g p.2 c) 0 x) 0)) atTop (𝓝 0))
    (hsrc : Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T,
      Real.sqrt (∑ c, Q (s - 2) (fun x => S p.1 c x - S p.2 c x) t)) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T, Real.sqrt (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      Q (s - 3) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t)) atTop (𝓝 0) := by
  have hcau := common_slab_cauchy hs hT ha hlam hg hinit hsrc
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  have hk : 3 ≤ k := by omega
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 2 - 2 = k := by omega
  have e3 : k + 2 - 3 = k - 1 := by omega
  simp only [e1, e2, e3] at hinit hsrc hcau ⊢
  set C : Ctx κ := ⟨Np, θ, k, T, a0, lam, Λ, K0⟩
  have G : C.Good := ⟨hk, hT, ha, hlam, (hg 0).sθ, (hg 0).K0_nonneg hT.le⟩
  have hadm : ∀ h, C.Adm (g h, gi h, S h) := hg
  -- the uniform Lipschitz constants of the curvature components
  have hR : ∀ q : Fin 4 × Fin 4 × Fin 4 × Fin 4, ∃ L : ℝ, 0 ≤ L ∧ ∀ m m' : MD, C.Adm m →
      C.Adm m' → ∀ t ∈ Icc 0 T, Q (k - 1) (fun x => RiemF m.1 m.2.1 q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF m'.1 m'.2.1 q.1 q.2.1 q.2.2.1 q.2.2.2 x) t ≤ L * C.Dl m m' t := fun q => by
    obtain ⟨_, _, B, L, _, hL, h⟩ := Ctx.ulo_Riem G q.1 q.2.1 q.2.2.1 q.2.2.2
    exact ⟨L, hL, fun m m' hm hm' t ht => (h m m' hm hm' t ht).2⟩
  choose L hL hRL using hR
  set Lt := ∑ q, L q
  have hLt : 0 ≤ Lt := Finset.sum_nonneg fun q _ => hL q
  obtain ⟨BS, hBS⟩ := sources_bounded (k := k) (fun h => (hg h).sS) hsrc hT.le
  have hBS0 : 0 ≤ BS := (intervalIntegral.integral_nonneg hT.le fun t _ =>
    Real.sqrt_nonneg _).trans (hBS 0)
  set A := Real.sqrt (256 * Lt)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  -- continuity of the integrands
  have hcR : ∀ p : ℕ × ℕ, Continuous fun t => Real.sqrt (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      Q (k - 1) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t) := fun p => by
    refine (continuous_finsetSum _ fun q _ => continuous_Q _ ?_).sqrt
    have h1 := (Ctx.ulo_Riem G q.1 q.2.1 q.2.2.1 q.2.2.2).1 _ (hadm p.1)
    have h2 := (Ctx.ulo_Riem G q.1 q.2.1 q.2.2.1 q.2.2.2).1 _ (hadm p.2)
    exact h1.sub h2
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set η := δ / (4 * (A + 1) * (T + 2 * BS + 1))
  have hη : 0 < η := by positivity
  set ε2 := δ / (4 * (A + 1))
  have hε2 : 0 < ε2 := by positivity
  filter_upwards [hcau (η ^ 2) (by positivity),
    (Metric.tendsto_nhds.mp hsrc) ε2 hε2] with p hW hS
  have hS' : ∫ t in (0)..T, srcD k (S p.1) (S p.2) t < ε2 := by
    have := hS
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hI0 : 0 ≤ ∫ t in (0)..T, Real.sqrt (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      Q (k - 1) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t) :=
    intervalIntegral.integral_nonneg hT.le fun t _ => Real.sqrt_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hI0]
  -- the pointwise bound
  have hpt : ∀ t ∈ Icc 0 T, Real.sqrt (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      Q (k - 1) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t) ≤
      A * (η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) + srcD k (S p.1) (S p.2) t) := by
    intro t ht
    set m : MD := (g p.1, gi p.1, S p.1)
    set m' : MD := (g p.2, gi p.2, S p.2)
    have hD := Ctx.Dl_nonneg (C := C) m m' t
    have h1 : ∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
        Q (k - 1) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
          RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t ≤ 256 * Lt * C.Dl m m' t := by
      calc _ ≤ ∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4, Lt * C.Dl m m' t :=
            Finset.sum_le_sum fun q _ => (hRL q m m' (hadm _) (hadm _) t ht).trans
              (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := L) (fun q _ => hL q)
                (Finset.mem_univ q)) hD)
        _ = _ := by simp; ring
    have hW' : Wn k (g p.1) (g p.2) t ≤ η ^ 2 := by
      rw [Wn_eq (hg p.1).sg (hg p.2).sg]; exact hW t ht
    have hW0 := Wn_nonneg k (g p.1) (g p.2) t
    have hsW : Real.sqrt (Wn k (g p.1) (g p.2) t) ≤ η := by
      rw [show η = Real.sqrt (η ^ 2) from (Real.sqrt_sq hη.le).symm]
      exact Real.sqrt_le_sqrt hW'
    have hZ := Ctx.Zs_nonneg (C := C) m t
    have hZ' := Ctx.Zs_nonneg (C := C) m' t
    have hΔ : 0 ≤ ∑ c, Q k (fun x => S p.1 c x - S p.2 c x) t :=
      Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
    have h2 : Real.sqrt (C.Dl m m' t) ≤ η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) +
        srcD k (S p.1) (S p.2) t := by
      unfold Ctx.Dl
      refine (sqrt_add_le' (mul_nonneg hW0 (by linarith)) hΔ).trans ?_
      rw [Real.sqrt_mul hW0]
      have h3 : Real.sqrt (1 + C.Zs m t + C.Zs m' t) ≤ 1 + srcN k (S p.1) t + srcN k (S p.2) t := by
        refine (sqrt_add3_le zero_le_one hZ hZ').trans ?_
        rw [Real.sqrt_one]; rfl
      have := Real.sqrt_nonneg (1 + C.Zs m t + C.Zs m' t)
      have : 0 ≤ 1 + srcN k (S p.1) t + srcN k (S p.2) t := by
        unfold srcN; positivity
      have h4 : Real.sqrt (Wn k (g p.1) (g p.2) t) * Real.sqrt (1 + C.Zs m t + C.Zs m' t) ≤
          η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) :=
        mul_le_mul hsW h3 (Real.sqrt_nonneg _) hη.le
      unfold srcD
      linarith
    calc _ ≤ Real.sqrt (256 * Lt * C.Dl m m' t) := Real.sqrt_le_sqrt h1
      _ = A * Real.sqrt (C.Dl m m' t) := Real.sqrt_mul (by positivity) _
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hA
  have hc1 := continuous_srcN k (hg p.1).sS
  have hc2 := continuous_srcN k (hg p.2).sS
  have hc3 := continuous_srcD k (hg p.1).sS (hg p.2).sS
  have cR : Continuous fun t => A * (η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) +
      srcD k (S p.1) (S p.2) t) := by fun_prop
  have hint : (∫ t in (0)..T, Real.sqrt (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      Q (k - 1) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t)) ≤
      ∫ t in (0)..T, A * (η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) +
        srcD k (S p.1) (S p.2) t) :=
    intervalIntegral.integral_mono_on (μ := volume) hT.le ((hcR p).intervalIntegrable _ _)
      (cR.intervalIntegrable _ _) hpt
  have i1 : Continuous fun t => η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) := by fun_prop
  have i2 : Continuous fun t => 1 + srcN k (S p.1) t := by fun_prop
  have hval : ∫ t in (0)..T, A * (η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) +
      srcD k (S p.1) (S p.2) t) = A * (η * (T + ((∫ t in (0)..T, srcN k (S p.1) t) +
        ∫ t in (0)..T, srcN k (S p.2) t)) + ∫ t in (0)..T, srcD k (S p.1) (S p.2) t) := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add (f := fun t => η * (1 + srcN k (S p.1) t + srcN k (S p.2) t))
      (g := fun t => srcD k (S p.1) (S p.2) t) (i1.intervalIntegrable _ _)
      (hc3.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add (f := fun t => 1 + srcN k (S p.1) t)
      (g := fun t => srcN k (S p.2) t) (i2.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_add (f := fun _ => (1 : ℝ)) (g := fun t => srcN k (S p.1) t)
      (continuous_const.intervalIntegrable _ _) (hc1.intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    ring
  rw [hval] at hint
  have hb1 := hBS p.1
  have hb2 := hBS p.2
  have hT0 := hT.le
  have hkey : η * (T + ((∫ t in (0)..T, srcN k (S p.1) t) + ∫ t in (0)..T, srcN k (S p.2) t)) ≤
      η * (T + 2 * BS + 1) := mul_le_mul_of_nonneg_left (by linarith) hη.le
  have hηv : η * (T + 2 * BS + 1) = δ / (4 * (A + 1)) := by
    simp only [η]; field_simp
  have hfin : A * (δ / (4 * (A + 1)) + ε2) < δ := by
    simp only [ε2]
    have : A * (δ / (4 * (A + 1)) + δ / (4 * (A + 1))) = δ / 2 * (A / (A + 1)) := by
      field_simp; ring
    rw [this]
    have : A / (A + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  calc _ ≤ _ := hint
    _ ≤ A * (δ / (4 * (A + 1)) + ε2) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        linarith
    _ < δ := hfin

end ReducedWaveStab

end RenewalGeometry
