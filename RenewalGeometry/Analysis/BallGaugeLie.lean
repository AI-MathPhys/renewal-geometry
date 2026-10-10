/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallGaugeStructure
import RenewalGeometry.Continuum.UhlenbeckRadialGauge

/-!
# Gauge transforms of `𝔤`-valued `H^s(B)` connections are `𝔤`-valued
  (stage D1 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `matOfSmooth` — smooth matrix-valued functions as elements of `H^s(B, M_m(ℂ))`
  (`evM_matOfSmooth`, `derM_matOfSmooth`, `ext_evM`);
* `exp_embX_ofSmooth` — for smooth coordinates, the Banach-algebra exponential is the smooth
  function `x ↦ exp(Σ u_a(x) e_a)`;
* `ae_dexp_mem` — **`(∂_μ e^X) e^{-X}` is `𝔤`-valued a.e.** for every `𝔤`-valued
  `X ∈ H⁵(B)` (pointwise dexp formula for smooth `X`, density of smooth fields, closedness of `𝔤`);
* `ae_gaugeAct_mem` — the gauge action of `exp X` on a `𝔤`-valued connection is `𝔤`-valued a.e.,
  and `gaugeAct_eq_embX` — hence it is `embX` of its own coordinates.
-/

open MeasureTheory Set Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

section MatSmooth

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {s : ℕ} [hs : Fact (3 ≤ s)] {m : ℕ}

theorem contDiff_re_entry {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hF : ∀ i j, ContDiff ℝ ∞ (fun x => F x i j)) (i j : Fin m) :
    ContDiff ℝ ∞ (fun x => (F x i j).re) :=
  Complex.reCLM.contDiff.comp (hF i j)

theorem contDiff_im_entry {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hF : ∀ i j, ContDiff ℝ ∞ (fun x => F x i j)) (i j : Fin m) :
    ContDiff ℝ ∞ (fun x => (F x i j).im) :=
  Complex.imCLM.contDiff.comp (hF i j)

/-- A smooth matrix-valued function as an element of `H^s(B, M_m(ℂ))`. -/
def matOfSmooth (s : ℕ) [Fact (3 ≤ s)] (F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    (hF : ∀ i j, ContDiff ℝ ∞ (fun x => F x i j)) : MatSob c r s m :=
  Matrix.of fun i j => ⟨ofSmooth _ (contDiff_re_entry hF i j), ofSmooth _ (contDiff_im_entry hF i j)⟩

theorem evM_matOfSmooth {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hF : ∀ i j, ContDiff ℝ ∞ (fun x => F x i j)) :
    evM (matOfSmooth (c := c) (r := r) s F hF) =ᵐ[volume.restrict (euclBall c r)] F := by
  refine ae_matrix_of_entries fun i j => ?_
  filter_upwards [fn_ofSmooth (c := c) (r := r) (s := s) (contDiff_re_entry hF i j),
    fn_ofSmooth (c := c) (r := r) (s := s) (contDiff_im_entry hF i j)] with x e1 e2
  simp only [evM_apply, matOfSmooth, Matrix.of_apply, evC, e1, e2]
  exact Complex.re_add_im _

/-- Matrix fields are determined by their pointwise values. -/
theorem ext_evM {M N : MatSob c r s m}
    (h : evM M =ᵐ[volume.restrict (euclBall c r)] evM N) : M = N := by
  refine Matrix.ext fun i j => ext_evC ?_
  filter_upwards [h] with x hx
  exact congrFun (congrFun hx i) j

theorem pd_re_comp {f : (Fin 4 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (μ : Fin 4) :
    pd (fun x => (f x).re) μ = fun x => (pd f μ x).re := by
  funext x
  have h := (Complex.reCLM.hasFDerivAt (x := f x)).comp x
    ((hf.differentiable (by simp)) x).hasFDerivAt
  simp only [pd]
  rw [show (fun x => (f x).re) = Complex.reCLM ∘ f from rfl, h.fderiv]
  rfl

theorem pd_im_comp {f : (Fin 4 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (μ : Fin 4) :
    pd (fun x => (f x).im) μ = fun x => (pd f μ x).im := by
  funext x
  have h := (Complex.imCLM.hasFDerivAt (x := f x)).comp x
    ((hf.differentiable (by simp)) x).hasFDerivAt
  simp only [pd]
  rw [show (fun x => (f x).im) = Complex.imCLM ∘ f from rfl, h.fderiv]
  rfl

theorem contDiff_pdM_entry {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hF : ∀ i j, ContDiff ℝ ∞ (fun x => F x i j)) (μ : Fin 4) (i j : Fin m) :
    ContDiff ℝ ∞ (fun x => pdM F μ x i j) := by
  simp only [pdM, Matrix.of_apply]
  exact contDiff_pd (hF i j) μ

/-- The derivative of a smooth matrix field is the classical derivative. -/
theorem derM_matOfSmooth {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hF : ∀ i j, ContDiff ℝ ∞ (fun x => F x i j)) (μ : Fin 4) :
    derM μ (matOfSmooth (c := c) (r := r) (s + 1) F hF) =
      matOfSmooth s (pdM F μ) (contDiff_pdM_entry hF μ) := by
  refine Matrix.ext fun i j => ?_
  rw [derM_apply]
  simp only [matOfSmooth, Matrix.of_apply, derS_ofSmooth]
  ext
  · show ofSmooth _ _ = ofSmooth _ _
    congr 1
    rw [pd_re_comp (hF i j)]
    rfl
  · show ofSmooth _ _ = ofSmooth _ _
    congr 1
    rw [pd_im_comp (hF i j)]
    rfl

theorem rhoM_matOfSmooth {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hF : ∀ i j, ContDiff ℝ ∞ (fun x => F x i j)) :
    rhoM (matOfSmooth (c := c) (r := r) (s + 1) F hF) = matOfSmooth s F hF := by
  refine Matrix.ext fun i j => ?_
  rw [rhoM_apply]
  rfl

theorem evM_rhoM (M : MatSob c r (s + 1) m) : evM (rhoM M) = evM M := rfl

theorem evM_rhoML (M : MatSob c r (s + 1) m) : evM (rhoML M) = evM M := rfl

end MatSmooth

/-! ### The pointwise dexp formula and density -/

section Dexp

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m d : ℕ}

open UhlenbeckPregauge in
/-- The smooth `𝔤`-valued function with coordinates `u`. -/
def Umat (L : LieBasis m d) (u : Fin d → (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) :
    Matrix (Fin m) (Fin m) ℂ := ∑ a, ((u a x : ℝ) : ℂ) • L.e a

theorem Umat_mem (L : LieBasis m d) (u : Fin d → (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) :
    Umat L u x ∈ L.lieAlg := by
  have := L.sum_mem (fun a => u a x)
  simpa [Umat, Complex.coe_smul] using this

theorem contDiff_Umat_entry (L : LieBasis m d) {u : Fin d → (Fin 4 → ℝ) → ℝ}
    (hu : ∀ a, ContDiff ℝ ∞ (u a)) (i j : Fin m) : ContDiff ℝ ∞ (fun x => Umat L u x i j) := by
  simp only [Umat, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact ContDiff.sum fun a _ => (Complex.ofRealCLM.contDiff.comp (hu a)).mul contDiff_const

theorem contDiff_expUmat_entry (L : LieBasis m d) {u : Fin d → (Fin 4 → ℝ) → ℝ}
    (hu : ∀ a, ContDiff ℝ ∞ (u a)) (i j : Fin m) :
    ContDiff ℝ ∞ (fun x => exp (Umat L u x) i j) :=
  UhlenbeckPregauge.contDiff_entry_of_matrix (UhlenbeckPregauge.contDiff_exp_matrix.comp
    (UhlenbeckPregauge.contDiff_matrix_of_entries (contDiff_Umat_entry L hu))) i j

theorem embX_ofSmooth {s : ℕ} [Fact (3 ≤ s)] (L : LieBasis m d) {u : Fin d → (Fin 4 → ℝ) → ℝ}
    (hu : ∀ a, ContDiff ℝ ∞ (u a)) :
    embX L (fun a => ofSmooth (c := c) (r := r) (s := s) (u a) (hu a)) =
      matOfSmooth s (Umat L u) (contDiff_Umat_entry L hu) := by
  refine ext_evM ?_
  have h1 := evM_embX L (fun a => ofSmooth (c := c) (r := r) (s := s) (u a) (hu a))
  have h2 : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ a,
      fn (ofSmooth (c := c) (r := r) (s := s) (u a) (hu a)) x = u a x := by
    rw [ae_all_iff]; exact fun a => fn_ofSmooth (hu a)
  filter_upwards [h1, h2, evM_matOfSmooth (c := c) (r := r) (s := s) (contDiff_Umat_entry L hu)]
    with x e1 e2 e3
  rw [e1, e3]
  simp only [Umat, e2]

set_option backward.isDefEq.respectTransparency false in
theorem exp_embX_ofSmooth {s : ℕ} [Fact (3 ≤ s)] (L : LieBasis m d)
    {u : Fin d → (Fin 4 → ℝ) → ℝ} (hu : ∀ a, ContDiff ℝ ∞ (u a)) :
    exp (embX L (fun a => ofSmooth (c := c) (r := r) (s := s) (u a) (hu a))) =
      matOfSmooth s (fun x => exp (Umat L u x)) (contDiff_expUmat_entry L hu) := by
  refine ext_evM ?_
  rw [embX_ofSmooth L hu]
  filter_upwards [evM_exp (matOfSmooth (c := c) (r := r) s (Umat L u) (contDiff_Umat_entry L hu)),
    evM_matOfSmooth (c := c) (r := r) (s := s) (contDiff_Umat_entry L hu),
    evM_matOfSmooth (c := c) (r := r) (s := s) (contDiff_expUmat_entry L hu)] with x e1 e2 e3
  rw [e1, e2, e3]

theorem pdM_Umat (L : LieBasis m d) {u : Fin d → (Fin 4 → ℝ) → ℝ}
    (hu : ∀ a, ContDiff ℝ ∞ (u a)) (μ : Fin 4) (x : Fin 4 → ℝ) :
    pdM (Umat L u) μ x = Umat L (fun a => pd (u a) μ) x := by
  ext i j
  simp only [pdM, Matrix.of_apply, Umat, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [pd_sum_complex (F := fun a y => ((u a y : ℝ) : ℂ) * L.e a i j) (fun a _ =>
    ((Complex.ofRealCLM.contDiff.comp (hu a)).mul contDiff_const).differentiable (by simp) x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hm := pd_mul_complex (f := fun y => ((u a y : ℝ) : ℂ)) (g := fun _ => L.e a i j)
    (((Complex.ofRealCLM.contDiff.comp (hu a))).differentiable (by simp) x)
    (differentiableAt_const _) μ
  rw [hm, pd_const_complex, mul_zero, add_zero]
  congr 1
  have h := (Complex.ofRealCLM.hasFDerivAt (x := u a x)).comp x
    (((hu a).differentiable (by simp)) x).hasFDerivAt
  simp only [pd]
  rw [show (fun y => ((u a y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ u a from rfl, h.fderiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The chain rule for the matrix exponential of a smooth matrix function. -/
theorem pdM_exp_comp {U : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hU : ∀ i j, ContDiff ℝ ∞ (fun x => U x i j)) (μ : Fin 4) (x : Fin 4 → ℝ) :
    pdM (fun y => exp (U y)) μ x = fderiv ℝ exp (U x) (pdM U μ x) := by
  have hUd : ContDiff ℝ ∞ U := UhlenbeckPregauge.contDiff_matrix_of_entries hU
  have hU1 : DifferentiableAt ℝ U x := (hUd.differentiable (by simp)) x
  have he : DifferentiableAt ℝ exp (U x) :=
    (UhlenbeckPregauge.contDiff_exp_matrix.differentiable (by simp)) (U x)
  have hpdM : ∀ (F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ), DifferentiableAt ℝ F x →
      pdM F μ x = fderiv ℝ F x (Pi.single μ 1) := by
    intro F hF
    ext i j
    simp only [pdM, Matrix.of_apply, pd]
    have h := ((LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt
      (x := F x)).comp x hF.hasFDerivAt
    rw [show (fun y => F y i j) = (LinearMap.toContinuousLinearMap
      (Matrix.entryLinearMap ℝ ℂ i j)) ∘ F from rfl, h.fderiv]
    rfl
  rw [hpdM (fun y => exp (U y)) (he.comp x hU1), hpdM _ hU1]
  rw [show (fun y => exp (U y)) = exp ∘ U from rfl, fderiv_comp x he hU1]
  rfl

theorem evM_neg {s : ℕ} [Fact (3 ≤ s)] (M : MatSob c r s m) :
    evM (-M) =ᵐ[volume.restrict (euclBall c r)] fun x => -evM M x := by
  filter_upwards [evM_smul (-1 : ℝ) M] with x hx
  rw [show -M = (-1 : ℝ) • M by simp, hx]
  simp

theorem evM_embX_mem {s : ℕ} [Fact (3 ≤ s)] (L : LieBasis m d) (u : Fin d → SobAlg c r s) :
    ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (embX L u) x ∈ L.lieAlg := by
  filter_upwards [evM_embX L u] with x hx
  rw [hx]
  have := L.sum_mem (fun a => fn (u a) x)
  simpa [Complex.coe_smul] using this

set_option backward.isDefEq.respectTransparency false in
/-- **The pointwise dexp formula for smooth `𝔤`-valued fields.** -/
theorem ae_dexp_mem_smooth (L : LieBasis m d) {u : Fin d → (Fin 4 → ℝ) → ℝ}
    (hu : ∀ a, ContDiff ℝ ∞ (u a)) (μ : Fin 4) :
    ∀ᵐ x ∂(volume.restrict (euclBall c r)),
      evM (derM μ (exp (embX L (fun a => ofSmooth (c := c) (r := r) (s := 5) (u a) (hu a)))) *
        rhoML (exp (-embX L (fun a => ofSmooth (c := c) (r := r) (s := 5) (u a) (hu a))))) x ∈
          L.lieAlg := by
  set X := embX L (fun a => ofSmooth (c := c) (r := r) (s := 5) (u a) (hu a))
  have hX : exp X = matOfSmooth (4 + 1) (fun x => exp (Umat L u x)) (contDiff_expUmat_entry L hu) :=
    exp_embX_ofSmooth L hu
  have hD : derM μ (exp X) = matOfSmooth 4 (pdM (fun x => exp (Umat L u x)) μ)
      (contDiff_pdM_entry (contDiff_expUmat_entry L hu) μ) := by
    rw [hX, derM_matOfSmooth]
  have hXv : evM X =ᵐ[volume.restrict (euclBall c r)] Umat L u := by
    rw [show X = matOfSmooth 5 (Umat L u) (contDiff_Umat_entry L hu) from embX_ofSmooth L hu]
    exact evM_matOfSmooth (contDiff_Umat_entry L hu)
  filter_upwards [evM_mul (derM μ (exp X)) (rhoML (exp (-X))),
    evM_matOfSmooth (c := c) (r := r) (s := 4)
      (contDiff_pdM_entry (contDiff_expUmat_entry L hu) μ),
    evM_exp (-X), evM_neg X, hXv] with x e1 e2 e3 e4 e5
  rw [e1, hD, e2, evM_rhoML, e3, e4, e5, pdM_exp_comp (contDiff_Umat_entry L hu),
    pdM_Umat L hu]
  exact L.fderiv_exp_mul_mem (Umat_mem L u x) (Umat_mem L _ x)

set_option backward.isDefEq.respectTransparency false in
theorem continuous_dexpMap (L : LieBasis m d) (μ : Fin 4) :
    Continuous fun ξ : Fin d → SobAlg c r 5 =>
      derM (s := 4) μ (exp (embX L ξ)) * rhoML (exp (-embX L ξ)) := by
  have hE := (embXL (c := c) (r := r) (s := 5) (m := m) L).continuous
  have hexp : Continuous (exp : MatSob c r 5 m → MatSob c r 5 m) :=
    (contDiff_exp_matSob (c := c) (r := r) (s := 5) (m := m)).continuous
  exact ((derM (c := c) (r := r) (s := 4) (m := m) μ).continuous.comp (hexp.comp hE)).mul
    ((rhoML (c := c) (r := r) (s := 4) (m := m)).continuous.comp (hexp.comp hE.neg))

set_option backward.isDefEq.respectTransparency false in
/-- **`(∂_μ e^X) e^{-X}` is `𝔤`-valued a.e. for every `𝔤`-valued `X ∈ H⁵(B)`.** -/
theorem ae_dexp_mem (L : LieBasis m d) (ξ : Fin d → SobAlg c r 5) (μ : Fin 4) :
    ∀ᵐ x ∂(volume.restrict (euclBall c r)),
      evM (derM μ (exp (embX L ξ)) * rhoML (exp (-embX L ξ))) x ∈ L.lieAlg := by
  choose φ hφ hlim using fun a => exists_tendsto_ofSmooth (ξ a)
  set ξs : ℕ → Fin d → SobAlg c r 5 := fun n a => ofSmooth (φ a n) (hφ a n)
  have hξs : Tendsto ξs atTop (𝓝 ξ) := tendsto_pi_nhds.mpr fun a => hlim a
  have hΓ := ((continuous_dexpMap (m := m) L μ).tendsto ξ).comp hξs
  obtain ⟨ns, -, hae⟩ := exists_subseq_tendsto_evM hΓ
  have hmem : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ n,
      evM (derM μ (exp (embX L (ξs n))) * rhoML (exp (-embX L (ξs n)))) x ∈ L.lieAlg := by
    rw [ae_all_iff]
    intro n
    exact ae_dexp_mem_smooth (c := c) (r := r) L (u := fun a => φ a n) (fun a => hφ a n) μ
  filter_upwards [hae, hmem] with x hx1 hx2
  exact L.closed_lieAlg.mem_of_tendsto hx1 (Eventually.of_forall fun k => hx2 (ns k))

set_option backward.isDefEq.respectTransparency false in
/-- **The gauge action preserves `𝔤`-valued connections** (pointwise a.e.). -/
theorem ae_gaugeAct_mem (L : LieBasis m d) (t : Fin 4 → Fin d → SobAlg c r 4)
    (ξ : Fin d → SobAlg c r 5) (μ : Fin 4) :
    ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (gaugeAct L t ξ μ) x ∈ L.lieAlg := by
  filter_upwards [evM_sub (rhoML (exp (embX L ξ)) * embX L (t μ) * rhoML (exp (-embX L ξ)))
      (derM μ (exp (embX L ξ)) * rhoML (exp (-embX L ξ))),
    evM_mul (rhoML (exp (embX L ξ)) * embX L (t μ)) (rhoML (exp (-embX L ξ))),
    evM_mul (rhoML (exp (embX L ξ))) (embX L (t μ)),
    evM_exp (embX L ξ), evM_exp (-embX L ξ), evM_neg (embX L ξ),
    evM_embX_mem L ξ, evM_embX_mem L (t μ), ae_dexp_mem L ξ μ] with x e1 e2 e3 e4 e5 e6 h1 h2 h3
  rw [gaugeAct, e1, e2, e3, evM_rhoML, evM_rhoML, e4, e5, e6]
  exact Submodule.sub_mem _ (L.exp_conj_mem h1 h2) h3

/-- A `𝔤`-valued matrix field is `embX` of its coordinates. -/
theorem embX_coordL_of_ae_mem {s : ℕ} [Fact (3 ≤ s)] (L : LieBasis m d) {M : MatSob c r s m}
    (hM : ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM M x ∈ L.lieAlg) :
    embX L (coordL L M) = M := by
  refine ext_evM ?_
  have h1 := evM_embX L (coordL L M)
  have h2 : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ a,
      fn (coordL L M a) x = L.κ (evM M x) a := by
    rw [ae_all_iff]; exact fun a => fn_coordL L M a
  filter_upwards [h1, h2, hM] with x e1 e2 e3
  rw [e1]
  simp only [e2]
  have := L.sum_κ_of_mem e3
  simpa [Complex.coe_smul] using this

end Dexp

end RenewalGeometry.BallAnalysis.BallAlg
