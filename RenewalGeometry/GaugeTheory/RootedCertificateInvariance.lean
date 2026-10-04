/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.MatrixDetExp
import RenewalGeometry.GaugeTheory.RootedWilsonSeedExact

/-!
# A conjugation-invariant logarithm chart and gauge invariance of the rooted certificate
  (`prop:rooted-gauge-certificate`, Einstein–SM action closure)

* `exists_conj_invariant_chart`: for complex `n × n` matrices there is a radius `r > 0` such that
  `exp` is injective on the operator-norm ball `opBall r = {‖Y‖ < r}`; this ball is invariant
  under unitary conjugation (`opBall_conj`), so it is a *conjugation-invariant logarithm chart*.
* `chartLog r = (exp|_{opBall r})⁻¹` (`Function.invFunOn`), with `chartLog (e^Y) = Y` on the
  chart (`chartLog_exp`).
* `chartLog_conj` (**log equivariance**): `Log(U P U⁻¹) = U Log(P) U⁻¹` for unitary `U` and `P`
  in the image of the chart; hence `‖Log(U P U⁻¹)‖ = ‖Log P‖` (`norm_chartLog_conj`).
* `rootedSeed_gauge`, `plaquetteLog_gauge`: on any oriented graph with unitary links and any
  rooted family of walks, the rooted seed `B_e = h⁻¹ Log W_e` and the plaquette logarithms
  `h⁻² Log P` are mapped by a site gauge to `Ad(g_o) B_e` and `Ad(g_v) (h⁻² Log P)`; admissibility
  is gauge invariant and all their norms are unchanged.  Consequently the rooted certificate
  `‖B^𝔗‖_{4,h} + ‖𝔽_h‖_{2,h}` (`eq:rooted-Wilson-certificate`; `rootedCertificate`) is invariant
  under arbitrary finite site gauges (`rootedCertificate_gauge`).
-/

namespace RenewalGeometry.RootedCertificate

open Matrix RootedWilson

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

section Chart

open scoped Matrix.Norms.L2Operator

/-- The operator-norm ball `{‖Y‖ < r}` of complex matrices. -/
def opBall (r : ℝ) : Set (Matrix n n ℂ) := {Y | ‖Y‖ < r}

theorem entry_le_opNorm (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  have h := A.l2_opNorm_mulVec (EuclideanSpace.single j 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le
    ((EuclideanSpace.equiv n ℂ).symm (A.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  refine le_trans (le_of_eq ?_) this
  congr 1
  simp

/-- The ball is invariant under unitary conjugation. -/
theorem opBall_conj (r : ℝ) (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (Y : Matrix n n ℂ)
    (hY : Y ∈ opBall r) : U * Y * star U ∈ opBall r := by
  change ‖U * Y * star U‖ < r
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU), CStarRing.norm_mem_unitary_mul _ hU]
  exact hY

/-- **A conjugation-invariant injectivity chart of the matrix exponential.** -/
theorem exists_conj_invariant_chart :
    ∃ r : ℝ, 0 < r ∧ Set.InjOn NormedSpace.exp (opBall (n := n) r) := by
  obtain ⟨r, hr, hinj⟩ := MatrixDetExp.exists_injOn_exp_entry_ball (𝕂 := ℂ) (n := n)
  exact ⟨r, hr, hinj.mono fun Y hY i j => (entry_le_opNorm Y i j).trans_lt hY⟩

/-- The chart logarithm `Log = (exp|_{opBall r})⁻¹`. -/
def chartLog (r : ℝ) : Matrix n n ℂ → Matrix n n ℂ :=
  Function.invFunOn NormedSpace.exp (opBall r)

theorem chartLog_exp {r : ℝ} (hinj : Set.InjOn NormedSpace.exp (opBall (n := n) r))
    {Y : Matrix n n ℂ} (hY : Y ∈ opBall r) : chartLog r (NormedSpace.exp Y) = Y :=
  hinj.leftInvOn_invFunOn hY

theorem exp_unitary_conj (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (Y : Matrix n n ℂ) :
    NormedSpace.exp (U * Y * star U) = U * NormedSpace.exp Y * star U := by
  have h1 := (mem_unitaryGroup_iff.1 hU)
  have h2 := (mem_unitaryGroup_iff'.1 hU)
  let u : (Matrix n n ℂ)ˣ := ⟨U, star U, h1, h2⟩
  have := Matrix.exp_units_conj u Y
  exact this

/-- **Log equivariance on the conjugation-invariant chart**: `Log(U P U⁻¹) = U Log(P) U⁻¹`. -/
theorem chartLog_conj {r : ℝ} (hinj : Set.InjOn NormedSpace.exp (opBall (n := n) r))
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) {P : Matrix n n ℂ}
    (hP : ∃ Y ∈ opBall r, NormedSpace.exp Y = P) :
    chartLog r (U * P * star U) = U * chartLog r P * star U := by
  obtain ⟨Y, hY, rfl⟩ := hP
  rw [← exp_unitary_conj U hU, chartLog_exp hinj (opBall_conj r U hU Y hY), chartLog_exp hinj hY]

theorem admissible_conj {r : ℝ} (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ)
    {P : Matrix n n ℂ} (hP : ∃ Y ∈ opBall r, NormedSpace.exp Y = P) :
    ∃ Y ∈ opBall r, NormedSpace.exp Y = U * P * star U := by
  obtain ⟨Y, hY, rfl⟩ := hP
  exact ⟨U * Y * star U, opBall_conj r U hU Y hY, exp_unitary_conj U hU Y⟩

theorem norm_unitary_conj (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ‖U * A * star U‖ = ‖A‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU), CStarRing.norm_mem_unitary_mul _ hU]

theorem norm_chartLog_conj {r : ℝ} (hinj : Set.InjOn NormedSpace.exp (opBall (n := n) r))
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) {P : Matrix n n ℂ}
    (hP : ∃ Y ∈ opBall r, NormedSpace.exp Y = P) (c : ℂ) :
    ‖c • chartLog r (U * P * star U)‖ = ‖c • chartLog r P‖ := by
  rw [chartLog_conj hinj U hU hP, show c • (U * chartLog r P * star U) =
    U * (c • chartLog r P) * star U by rw [Matrix.mul_smul, Matrix.smul_mul],
    norm_unitary_conj U hU]

end Chart

/-! ### Gauge invariance of the rooted certificate -/

section Certificate

open scoped Matrix.Norms.L2Operator

variable {V E : Type*} {src tgt : E → V} {o : V}

theorem coe_gauge (g : V → unitaryGroup n ℂ) (U : E → unitaryGroup n ℂ) (e : E) :
    ((gaugeLinks src tgt g U e : unitaryGroup n ℂ) : Matrix n n ℂ) =
      (g (tgt e) : Matrix n n ℂ) * U e * star (g (src e) : Matrix n n ℂ) := by
  simp [gaugeLinks_apply]

/-- The rooted word transforms by unitary conjugation at the root, as matrices. -/
theorem rootedWord_coe_gauge (w : ∀ v, LatticeWalk src tgt v o) (g : V → unitaryGroup n ℂ)
    (U : E → unitaryGroup n ℂ) (e : E) :
    ((rootedWord w (gaugeLinks src tgt g U) e : unitaryGroup n ℂ) : Matrix n n ℂ) =
      (g o : Matrix n n ℂ) * ((rootedWord w U e : unitaryGroup n ℂ) : Matrix n n ℂ) * star (g o : Matrix n n ℂ) := by
  rw [rootedWord_gaugeLinks]
  simp

/-- **Rooted seed under a site gauge** (`eq:rooted-Wilson-seed`): admissibility is gauge
invariant, `B(g·U) = Ad(g_o) B(U)`, and `‖B_e(g·U)‖ = ‖B_e(U)‖`. -/
theorem rootedSeed_gauge {r : ℝ} (hinj : Set.InjOn NormedSpace.exp (opBall (n := n) r)) (h : ℝ)
    (w : ∀ v, LatticeWalk src tgt v o) (g : V → unitaryGroup n ℂ) (U : E → unitaryGroup n ℂ)
    (e : E) (hadm : ∃ Y ∈ opBall r, NormedSpace.exp Y = ((rootedWord w U e : unitaryGroup n ℂ) : Matrix n n ℂ)) :
    (∃ Y ∈ opBall r, NormedSpace.exp Y =
      ((rootedWord w (gaugeLinks src tgt g U) e : unitaryGroup n ℂ) : Matrix n n ℂ)) ∧
    (h : ℂ)⁻¹ • chartLog r ((rootedWord w (gaugeLinks src tgt g U) e : unitaryGroup n ℂ) : Matrix n n ℂ) =
      (g o : Matrix n n ℂ) * ((h : ℂ)⁻¹ • chartLog r ((rootedWord w U e : unitaryGroup n ℂ) : Matrix n n ℂ)) *
        star (g o : Matrix n n ℂ) ∧
    ‖(h : ℂ)⁻¹ • chartLog r ((rootedWord w (gaugeLinks src tgt g U) e : unitaryGroup n ℂ) : Matrix n n ℂ)‖ =
      ‖(h : ℂ)⁻¹ • chartLog r ((rootedWord w U e : unitaryGroup n ℂ) : Matrix n n ℂ)‖ := by
  rw [rootedWord_coe_gauge]
  have hg := (g o).2
  refine ⟨admissible_conj _ hg hadm, ?_, norm_chartLog_conj hinj _ hg hadm _⟩
  rw [chartLog_conj hinj _ hg hadm, Matrix.mul_smul, Matrix.smul_mul]

/-- **Plaquette logarithms under a site gauge**: the holonomy of a closed walk at `v` is
conjugated by `g_v`, so the curvature `h⁻² Log P` is mapped to `Ad(g_v)(h⁻² Log P)`; admissibility
and norms are unchanged. -/
theorem plaquetteLog_gauge {r : ℝ} (hinj : Set.InjOn NormedSpace.exp (opBall (n := n) r))
    (h : ℝ) {v : V} (p : LatticeWalk src tgt v v) (g : V → unitaryGroup n ℂ)
    (U : E → unitaryGroup n ℂ)
    (hadm : ∃ Y ∈ opBall r, NormedSpace.exp Y = ((p.holonomy U : unitaryGroup n ℂ) : Matrix n n ℂ)) :
    (∃ Y ∈ opBall r, NormedSpace.exp Y = ((p.holonomy (gaugeLinks src tgt g U) : unitaryGroup n ℂ) : Matrix n n ℂ)) ∧
    ‖((h : ℂ) ^ 2)⁻¹ • chartLog r ((p.holonomy (gaugeLinks src tgt g U) : unitaryGroup n ℂ) : Matrix n n ℂ)‖ =
      ‖((h : ℂ) ^ 2)⁻¹ • chartLog r ((p.holonomy U : unitaryGroup n ℂ) : Matrix n n ℂ)‖ := by
  have hc : ((p.holonomy (gaugeLinks src tgt g U) : unitaryGroup n ℂ) : Matrix n n ℂ) =
      (g v : Matrix n n ℂ) * ((p.holonomy U : unitaryGroup n ℂ) : Matrix n n ℂ) * star (g v : Matrix n n ℂ) := by
    rw [p.holonomy_gaugeLinks_closed]; simp
  rw [hc]
  exact ⟨admissible_conj _ (g v).2 hadm, norm_chartLog_conj hinj _ (g v).2 hadm _⟩

/-- The rooted certificate `‖B^𝔗‖_{4,h} + ‖𝔽_h‖_{2,h}` (`eq:rooted-Wilson-certificate`) on a
finite graph of dimension `d` (cell mass `h^d`), with plaquettes given as closed walks `pl f`
based at `base f`. -/
def rootedCertificate [Fintype E] {Fc : Type*} [Fintype Fc] (r h : ℝ) (d : ℕ)
    (w : ∀ v, LatticeWalk src tgt v o) (base : Fc → V) (pl : ∀ f, LatticeWalk src tgt (base f) (base f))
    (U : E → unitaryGroup n ℂ) : ℝ :=
  (h ^ d * ∑ e, ‖(h : ℂ)⁻¹ • chartLog r ((rootedWord w U e : unitaryGroup n ℂ) : Matrix n n ℂ)‖ ^ 4) ^ ((1 : ℝ) / 4) +
    Real.sqrt (h ^ d * ∑ f, ‖((h : ℂ) ^ 2)⁻¹ • chartLog r (((pl f).holonomy U : unitaryGroup n ℂ) : Matrix n n ℂ)‖ ^ 2)

/-- **`prop:rooted-gauge-certificate`, certificate invariance**: on its admissible chart the
rooted certificate is invariant under arbitrary finite site gauges (and admissibility is
preserved). -/
theorem rootedCertificate_gauge [Fintype E] {Fc : Type*} [Fintype Fc] {r : ℝ}
    (hinj : Set.InjOn NormedSpace.exp (opBall (n := n) r)) (h : ℝ) (d : ℕ)
    (w : ∀ v, LatticeWalk src tgt v o) (base : Fc → V)
    (pl : ∀ f, LatticeWalk src tgt (base f) (base f)) (g : V → unitaryGroup n ℂ)
    (U : E → unitaryGroup n ℂ)
    (hW : ∀ e, ∃ Y ∈ opBall r, NormedSpace.exp Y = ((rootedWord w U e : unitaryGroup n ℂ) : Matrix n n ℂ))
    (hP : ∀ f, ∃ Y ∈ opBall r, NormedSpace.exp Y = (((pl f).holonomy U : unitaryGroup n ℂ) : Matrix n n ℂ)) :
    rootedCertificate r h d w base pl (gaugeLinks src tgt g U) =
      rootedCertificate r h d w base pl U := by
  unfold rootedCertificate
  have h1 : ∑ e, ‖(h : ℂ)⁻¹ • chartLog r
        ((rootedWord w (gaugeLinks src tgt g U) e : unitaryGroup n ℂ) : Matrix n n ℂ)‖ ^ 4 =
      ∑ e, ‖(h : ℂ)⁻¹ • chartLog r ((rootedWord w U e : unitaryGroup n ℂ) : Matrix n n ℂ)‖ ^ 4 :=
    Finset.sum_congr rfl fun e _ => by rw [(rootedSeed_gauge hinj h w g U e (hW e)).2.2]
  have h2 : ∑ f, ‖((h : ℂ) ^ 2)⁻¹ • chartLog r
        (((pl f).holonomy (gaugeLinks src tgt g U) : unitaryGroup n ℂ) : Matrix n n ℂ)‖ ^ 2 =
      ∑ f, ‖((h : ℂ) ^ 2)⁻¹ • chartLog r
        (((pl f).holonomy U : unitaryGroup n ℂ) : Matrix n n ℂ)‖ ^ 2 :=
    Finset.sum_congr rfl fun f _ => by rw [(plaquetteLog_gauge hinj h (pl f) g U (hP f)).2]
  rw [h1, h2]

end Certificate

end

end RenewalGeometry.RootedCertificate
