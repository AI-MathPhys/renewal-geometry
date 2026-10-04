/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.FiniteCoulombNormalization
import RenewalGeometry.GaugeTheory.RootedWilsonSeedExact

/-!
# The rooted same-record certificate puts the original links in exact Coulomb gauge
  (Coulomb clause of `prop:rooted-gauge-certificate`, Einstein–SM action closure)

Lattice graph: sites `x : (ℤ/n)^ι`, links `(x, μ)` transporting from `x + e_μ` to `x`
(`latSrc`, `latTgt`), so that the site gauge acts as `U_μ(x) ↦ g_x U_μ(x) g_{x+μ}⁻¹`
(`RootedWilson.gaugeLinks`).  Links take values in the unitary group of a finite-dimensional
C*-algebra `𝔸` with an invariant metric `toE` (as in `FiniteCoulomb`).  For a rooted family of
walks `w` (the tree paths of a rooted spanning tree), the rooted words
`W_μ(x) = C_x U_μ(x) C_{x+μ}⁻¹` define the seed `B^𝔗 = h⁻¹ Log W` (`treeSeed`,
`eq:rooted-Wilson-seed`), and the certificate is `‖B^𝔗‖_{4,h} + ‖𝔽_h(U)‖_{2,h}` with the literal
plaquette curvature `𝔽_h(U) = h⁻² Log(U_μ(x) U_ν(x+μ) U_μ(x+ν)⁻¹ U_ν(x)⁻¹)` of the original links
(`litCurvL2`, `eq:rooted-Wilson-certificate`).

* `curvL2_treeSeed`: on the admissible chart, the curvature packet of the tree representative
  equals the literal curvature packet of the original links (plaquette endpoint cancellation and
  conjugation equivariance of the logarithm).
* **`rooted_coulomb_normalization`**: there are `ε_c, C_c` (independent of `n`, `h` at fixed side)
  such that whenever the certificate is `≤ ε_c`, the exact tree gauge `C` followed by the gauge `q`
  of `thm:finite-Coulomb-normalization` — the single site gauge `g_x = q_x C_x` — puts the
  original links in exact small discrete Coulomb gauge: the logarithmic coordinates
  `A_μ(x) = h⁻¹ Log((g·U)_μ(x))` satisfy `δ_h A = 0`,
  `‖A‖_{1,h} + ‖A‖_{4,h} ≤ C_c(‖B^𝔗‖_{2,h} + ‖𝔽_h(U)‖_{2,h} + ‖B^𝔗‖²_{4,h})` and
  `‖A‖_{4,h} ≤ ε_*`.
-/

open NormedSpace Finset Set

namespace RenewalGeometry.RootedCoulomb

open SeriesLogChart GridSobolev CoulombApriori CurvatureSplit FiniteCoulomb RootedWilson
  CoulombHomotopy

noncomputable section

variable {𝔸 : Type*} [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ E]
variable (toE : 𝔸 ≃L[ℝ] E)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {n : ℕ} [NeZero n]

/-- The source `x + e_μ` of the lattice link `(x, μ)`. -/
def latSrc (e : (ι → ZMod n) × ι) : ι → ZMod n := e.1 + gridStep e.2

/-- The target `x` of the lattice link `(x, μ)`. -/
def latTgt (e : (ι → ZMod n) × ι) : ι → ZMod n := e.1

omit [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] in
theorem coe_inv_unitary (u : unitary 𝔸) : ((u⁻¹ : unitary 𝔸) : 𝔸) = star (u : 𝔸) := rfl

/-- The tree seed `B^𝔗_μ(x) = h⁻¹ Log W^𝔗_μ(x)` (`eq:rooted-Wilson-seed`). -/
def treeSeed (h : ℝ) {o : ι → ZMod n} (w : ∀ v, LatticeWalk (latSrc (ι := ι) (n := n)) latTgt v o)
    (U : (ι → ZMod n) × ι → unitary 𝔸) : ι → (ι → ZMod n) → 𝔸 :=
  fun μ x => h⁻¹ • logChart ((rootedWord w U (x, μ) : unitary 𝔸) : 𝔸)

/-- The literal plaquette `U_μ(x) U_ν(x+μ) U_μ(x+ν)⁻¹ U_ν(x)⁻¹` of unitary links. -/
def litPlaq (U : (ι → ZMod n) × ι → unitary 𝔸) (μ ν : ι) (x : ι → ZMod n) : 𝔸 :=
  (U (x, μ) : 𝔸) * (U (x + gridStep μ, ν) : 𝔸) * star (U (x + gridStep ν, μ) : 𝔸) *
    star (U (x, ν) : 𝔸)

/-- The literal plaquette curvature `𝔽_h(U)_{μν}(x) = h⁻² Log(plaquette)`. -/
def litCurv (h : ℝ) (U : (ι → ZMod n) × ι → unitary 𝔸) (μ ν : ι) (x : ι → ZMod n) : 𝔸 :=
  (h ^ 2)⁻¹ • logChart (litPlaq U μ ν x)

/-- `‖𝔽_h(U)‖_{2,h} = (Σ_{μ<ν} ‖toE 𝔽_h(U)_{μν}‖²_{2,h})^{1/2}`. -/
def litCurvL2 (h : ℝ) (U : (ι → ZMod n) × ι → unitary 𝔸) : ℝ :=
  √(∑ p ∈ pairs ι, gridL2Norm h (fun x => toE (litCurv h U p.1 p.2 x)) ^ 2)

theorem exp_treeSeed {h : ℝ} (hh : h ≠ 0) {o : ι → ZMod n}
    (w : ∀ v, LatticeWalk (latSrc (ι := ι) (n := n)) latTgt v o) (U : (ι → ZMod n) × ι → unitary 𝔸)
    (hadm : ∀ μ x, ‖((rootedWord w U (x, μ) : unitary 𝔸) : 𝔸) - 1‖ ≤ 1 / 64) (μ : ι)
    (x : ι → ZMod n) :
    exp (h • treeSeed h w U μ x) = ((rootedWord w U (x, μ) : unitary 𝔸) : 𝔸) := by
  simp only [treeSeed, smul_smul, mul_inv_cancel₀ hh, one_smul]
  exact exp_logChart ((hadm μ x).trans_lt (by norm_num))

theorem treeSeed_skew {h : ℝ} {o : ι → ZMod n}
    (w : ∀ v, LatticeWalk (latSrc (ι := ι) (n := n)) latTgt v o) (U : (ι → ZMod n) × ι → unitary 𝔸)
    (hadm : ∀ μ x, ‖((rootedWord w U (x, μ) : unitary 𝔸) : 𝔸) - 1‖ ≤ 1 / 64) (μ : ι)
    (x : ι → ZMod n) : star (treeSeed h w U μ x) = -treeSeed h w U μ x := by
  have hW := (rootedWord w U (x, μ)).2
  have hL : ‖logChart ((rootedWord w U (x, μ) : unitary 𝔸) : 𝔸)‖ ≤ 1 / 32 :=
    (norm_logChart_le ((hadm μ x).trans (by norm_num))).trans (by linarith [hadm μ x])
  have := logChart_skew' hW ((hadm μ x).trans_lt (by norm_num)) hL
  simp only [treeSeed, star_smul, star_trivial, this, smul_neg]

/-- **The curvature of the tree representative is the literal curvature, conjugated at the base
point**: `F_h(B^𝔗)_{μν}(x) = C_x 𝔽_h(U)_{μν}(x) C_x^*`. -/
theorem curvature_treeSeed {h : ℝ} (hh : h ≠ 0) {o : ι → ZMod n}
    (w : ∀ v, LatticeWalk (latSrc (ι := ι) (n := n)) latTgt v o) (U : (ι → ZMod n) × ι → unitary 𝔸)
    (hadm : ∀ μ x, ‖((rootedWord w U (x, μ) : unitary 𝔸) : 𝔸) - 1‖ ≤ 1 / 64)
    (hplaq : ∀ μ ν x, ‖litPlaq U μ ν x - 1‖ < 1) (μ ν : ι) (x : ι → ZMod n) :
    curvature h (treeSeed h w U) μ ν x =
      ((rootedPath w U x : unitary 𝔸) : 𝔸) * litCurv h U μ ν x *
        star ((rootedPath w U x : unitary 𝔸) : 𝔸) := by
  set C : (ι → ZMod n) → unitary 𝔸 := rootedPath w U
  have hW : ∀ μ y, ((rootedWord w U (y, μ) : unitary 𝔸) : 𝔸) =
      (C y : 𝔸) * (U (y, μ) : 𝔸) * star (C (y + gridStep μ) : 𝔸) := by
    intro μ y
    rfl
  have e1 : ∀ μ y, exp (h • treeSeed h w U μ y) =
      (C y : 𝔸) * (U (y, μ) : 𝔸) * star (C (y + gridStep μ) : 𝔸) := fun μ y => by
    rw [exp_treeSeed hh w U hadm, hW]
  have e2 : ∀ μ y, exp (-(h • treeSeed h w U μ y)) =
      (C (y + gridStep μ) : 𝔸) * star (U (y, μ) : 𝔸) * star (C y : 𝔸) := by
    intro μ y
    set Q := (C (y + gridStep μ) : 𝔸) * star (U (y, μ) : 𝔸) * star (C y : 𝔸)
    have hP : exp (h • treeSeed h w U μ y) * Q = 1 := by
      rw [e1]
      simp only [Q, mul_assoc]
      rw [star_mul_cancel_left' (C _).2, ← mul_assoc (U (y, μ) : 𝔸),
        Unitary.mul_star_self_of_mem (U (y, μ)).2, one_mul, Unitary.mul_star_self_of_mem (C y).2]
    calc exp (-(h • treeSeed h w U μ y))
        = exp (-(h • treeSeed h w U μ y)) * (exp (h • treeSeed h w U μ y) * Q) := by
          rw [hP, mul_one]
      _ = Q := by rw [← mul_assoc, MatrixExpDerivative.exp_neg_mul_exp, one_mul]
  have hplaq' : plaquette h (treeSeed h w U) μ ν x =
      (C x : 𝔸) * litPlaq U μ ν x * star (C x : 𝔸) := by
    simp only [plaquette, litPlaq]
    rw [e1, e1, e2, e2, add_right_comm x (gridStep ν) (gridStep μ)]
    simp only [mul_assoc]
    rw [star_mul_cancel_left' (C _).2, star_mul_cancel_left' (C _).2,
      star_mul_cancel_left' (C _).2]
  have hM' : ‖((unitUnit (C x).2 : 𝔸ˣ) : 𝔸) * (litPlaq U μ ν x - 1) *
      ↑(unitUnit (C x).2)⁻¹‖ < 1 := by
    change ‖(C x : 𝔸) * (litPlaq U μ ν x - 1) * star (C x : 𝔸)‖ < 1
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (C x).2),
      CStarRing.norm_mem_unitary_mul _ (C x).2]
    exact hplaq μ ν x
  have hlog := logChart_conj (unitUnit (C x).2) (hplaq μ ν x) hM'
  change logChart ((C x : 𝔸) * litPlaq U μ ν x * star (C x : 𝔸)) =
    (C x : 𝔸) * logChart (litPlaq U μ ν x) * star (C x : 𝔸) at hlog
  rw [curvature, hplaq', hlog, litCurv, mul_smul_comm, smul_mul_assoc]

/-- On the admissible chart, `‖𝔽_h(B^𝔗)‖_{2,h} = ‖𝔽_h(U)‖_{2,h}` (invariant metric). -/
theorem curvL2_treeSeed (hM1 : ∀ V ∈ unitary 𝔸, ∀ X, ‖toE (V * X * star V)‖ = ‖toE X‖)
    {h : ℝ} (hh : h ≠ 0) {o : ι → ZMod n}
    (w : ∀ v, LatticeWalk (latSrc (ι := ι) (n := n)) latTgt v o) (U : (ι → ZMod n) × ι → unitary 𝔸)
    (hadm : ∀ μ x, ‖((rootedWord w U (x, μ) : unitary 𝔸) : 𝔸) - 1‖ ≤ 1 / 64)
    (hplaq : ∀ μ ν x, ‖litPlaq U μ ν x - 1‖ < 1) :
    curvL2 h (toE : 𝔸 →L[ℝ] E) (treeSeed h w U) = litCurvL2 toE h U := by
  unfold curvL2 packetL2 litCurvL2
  congr 1
  refine sum_congr rfl fun p _ => ?_
  congr 1
  simp only [gridL2Norm, periodicHodgeNormSq]
  congr 2
  refine sum_congr rfl fun x _ => ?_
  rw [curvature_treeSeed hh w U hadm hplaq]
  change ‖toE (((rootedPath w U x : unitary 𝔸) : 𝔸) * _ *
    star ((rootedPath w U x : unitary 𝔸) : 𝔸))‖ ^ 2 = _
  rw [hM1 _ (rootedPath w U x).2]

/-- **Coulomb clause of `prop:rooted-gauge-certificate`.**  There are `ε_c, C_c > 0`
(independent of `n` and `h` at fixed side `L`, given `ε_* > 0`) such that whenever the rooted
seed is admissible and the certificate `‖B^𝔗‖_{4,h} + ‖𝔽_h(U)‖_{2,h} ≤ ε_c`, a single site gauge
`g` (the exact tree gauge followed by the Coulomb normalization) puts the original links in exact
small discrete Coulomb gauge, with the estimates of `thm:finite-Coulomb-normalization`. -/
theorem rooted_coulomb_normalization (hι : Fintype.card ι = 4)
    (hM1 : ∀ V ∈ unitary 𝔸, ∀ X, ‖toE (V * X * star V)‖ = ‖toE X‖)
    (hM2 : ∀ a : 𝔸, star a = -a → ∀ u, inner ℝ (toE a) (toE (a * u - u * a)) = 0)
    {L : ℝ} (hL : 0 < L) {εstar : ℝ} (hεstar : 0 < εstar) :
    ∃ εc Cc : ℝ, 0 < εc ∧ 0 < Cc ∧ ∀ (m : ℕ) [NeZero m] (h : ℝ), 0 < h → (m : ℝ) * h = L →
      ∀ (o : ι → ZMod m) (w : ∀ v, LatticeWalk (latSrc (ι := ι) (n := m)) latTgt v o)
        (U : (ι → ZMod m) × ι → unitary 𝔸),
      (∀ μ x, ‖((rootedWord w U (x, μ) : unitary 𝔸) : 𝔸) - 1‖ ≤ 1 / 64) →
      (∀ μ ν x, ‖litPlaq U μ ν x - 1‖ < 1) →
      oneL4 h (toE : 𝔸 →L[ℝ] E) (treeSeed h w U) + litCurvL2 toE h U ≤ εc →
      ∃ g : (ι → ZMod m) → unitary 𝔸,
        let A : ι → (ι → ZMod m) → 𝔸 := fun μ x =>
          h⁻¹ • logChart ((gaugeLinks latSrc latTgt g U (x, μ) : unitary 𝔸) : 𝔸)
        (∀ μ x, star (A μ x) = -A μ x) ∧
        periodicHodgeCodiff h gridStep (bar (toE : 𝔸 →L[ℝ] E) A) = 0 ∧
        oneH1 h (toE : 𝔸 →L[ℝ] E) A + oneL4 h (toE : 𝔸 →L[ℝ] E) A ≤
          Cc * (oneL2 h (toE : 𝔸 →L[ℝ] E) (treeSeed h w U) + litCurvL2 toE h U +
            oneL4 h (toE : 𝔸 →L[ℝ] E) (treeSeed h w U) ^ 2) ∧
        oneL4 h (toE : 𝔸 →L[ℝ] E) A ≤ εstar := by
  obtain ⟨εc, Cc, hεc, hCc, H⟩ := finite_coulomb_normalization toE hι hM1 hM2 hL hεstar
  refine ⟨εc, Cc, hεc, hCc, fun m _ h hh hmh o w U hadm hplaq hcert => ?_⟩
  have hcurv := curvL2_treeSeed toE hM1 hh.ne' w U hadm hplaq
  rw [← hcurv] at hcert ⊢
  obtain ⟨q, hq, -, hskew, hcod, hest, hsmall, -⟩ :=
    H m h hh hmh (treeSeed h w U) (treeSeed_skew w U hadm) hcert
  set C := rootedPath w U
  refine ⟨fun x => ⟨q x, hq x⟩ * C x, ?_⟩
  have hA : ∀ μ x, h⁻¹ • logChart ((gaugeLinks latSrc latTgt
      (fun x => (⟨q x, hq x⟩ : unitary 𝔸) * C x) U (x, μ) : unitary 𝔸) : 𝔸) =
      linkA h (treeSeed h w U) 1 q μ x := by
    intro μ x
    simp only [linkA, linkP, one_smul]
    congr 2
    rw [exp_treeSeed hh.ne' w U hadm]
    simp only [gaugeLinks_apply, latTgt, latSrc, Submonoid.coe_mul, coe_inv_unitary, star_mul,
      rootedWord, rootedPath, mul_assoc]
    rfl
  simp only [hA]
  exact ⟨hskew, hcod, hest, hsmall⟩

end

end RenewalGeometry.RootedCoulomb
