/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib

/-!
# Electrical routing on a finite hierarchy block

This file proves `thm:hierarchy-electrical-router` in three layers.

* `electricalRouter_rightInverse_on_laplacianRange` proves directly from the
  Penrose range identity that `U B^T L^dagger` is an exact linear right
  inverse on the centered Laplacian range.
* `electricalRouter_congestion_bound` combines the normalized Rayleigh gap,
  finite Cauchy--Schwarz, the hierarchy mass-profile norm comparison, and the
  `sqrt 2` incidence-column bound.
* `k4_normalized_fiedler_floor` expands the six weighted edges of `K_4` and
  proves the lower bound `4 u_- / mu(Q)^(2/3)` on the centered space.

The last theorem also isolates a normalized low-energy Fiedler vector as an
explicit certificate that a proposed positive floor fails.
-/

open Matrix

namespace NCG
namespace HierarchyElectricalRouter

/-! ## Finite norms and mass-profile comparison -/

/-- Euclidean norm written as the square root of the finite sum of squares. -/
noncomputable def finiteL2Norm {a : Type*} [Fintype a]
    (x : a -> Real) : Real :=
  Real.sqrt (Finset.univ.sum fun i => x i ^ 2)

/-- Child-constant centered demand space. -/
def IsCentered {v : Type*} [Fintype v] (g : v -> Real) : Prop :=
  Finset.univ.sum g = 0

/-- The hierarchy demand norm `max_i |g_i| / mu_i^(2/3)`.  The positive
profile `scale` is the vector of child two-thirds mass powers. -/
noncomputable def hierarchyDemandNorm {v : Type*} [Fintype v] [Nonempty v]
    (scale g : v -> Real) : Real :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |g i| / scale i

/-- Weighted edge congestion `max_e |j_e| / u_e`. -/
noncomputable def hierarchyCongestionNorm {e : Type*} [Fintype e] [Nonempty e]
    (capacity current : e -> Real) : Real :=
  Finset.univ.sup' Finset.univ_nonempty fun i =>
    |current i| / capacity i

theorem hierarchyDemandNorm_nonneg {v : Type*} [Fintype v] [Nonempty v]
    (scale g : v -> Real) (hscale : forall i, 0 < scale i) :
    0 <= hierarchyDemandNorm scale g := by
  classical
  let i : v := Classical.choice inferInstance
  have hcoordinate : 0 <= |g i| / scale i :=
    div_nonneg (abs_nonneg _) (hscale i).le
  exact hcoordinate.trans
    (Finset.le_sup' (s := Finset.univ) (f := fun k => |g k| / scale k)
      (Finset.mem_univ i))

/-- Every demand coordinate is controlled by the hierarchy maximum norm. -/
theorem abs_coordinate_le_scale_mul_demandNorm
    {v : Type*} [Fintype v] [Nonempty v]
    (scale g : v -> Real) (hscale : forall i, 0 < scale i) (i : v) :
    |g i| <= scale i * hierarchyDemandNorm scale g := by
  classical
  have hmax : |g i| / scale i <= hierarchyDemandNorm scale g :=
    Finset.le_sup' (s := Finset.univ) (f := fun k => |g k| / scale k)
      (Finset.mem_univ i)
  calc
    |g i| = scale i * (|g i| / scale i) := by
      field_simp [(hscale i).ne']
    _ <= scale i * hierarchyDemandNorm scale g :=
      mul_le_mul_of_nonneg_left hmax (hscale i).le

/-- The mass-profile inequality
`sum mu_i^(4/3) <= mu(Q)^(4/3)` converts the hierarchy maximum norm to
the Euclidean norm used by the spectral estimate. -/
theorem finiteL2Norm_le_parentScale_mul_demandNorm
    {v : Type*} [Fintype v] [Nonempty v]
    (scale g : v -> Real) (parentScale : Real)
    (hscale : forall i, 0 < scale i) (hparent : 0 <= parentScale)
    (hprofile : Finset.univ.sum (fun i => scale i ^ 2) <= parentScale ^ 2) :
    finiteL2Norm g <= parentScale * hierarchyDemandNorm scale g := by
  classical
  let demand := hierarchyDemandNorm scale g
  have hdemand : 0 <= demand := hierarchyDemandNorm_nonneg scale g hscale
  have hcoordinate (i : v) : |g i| <= scale i * demand :=
    abs_coordinate_le_scale_mul_demandNorm scale g hscale i
  have hsquare (i : v) : g i ^ 2 <= (scale i * demand) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (hscale i).le hdemand)).2
      (hcoordinate i)
  rw [finiteL2Norm, Real.sqrt_le_iff]
  constructor
  · exact mul_nonneg hparent hdemand
  · calc
      Finset.univ.sum (fun i => g i ^ 2)
          <= Finset.univ.sum (fun i => (scale i * demand) ^ 2) :=
        Finset.sum_le_sum fun i _ => hsquare i
      _ = demand ^ 2 * Finset.univ.sum (fun i => scale i ^ 2) := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
        congr 1
        funext i
        ring
      _ <= demand ^ 2 * parentScale ^ 2 :=
        mul_le_mul_of_nonneg_left hprofile (sq_nonneg demand)
      _ = (parentScale * demand) ^ 2 := by ring

/-- Finite real Cauchy--Schwarz in the exact norm used below. -/
theorem abs_dotProduct_le_finiteL2Norm_mul_finiteL2Norm
    {a : Type*} [Fintype a] (x y : a -> Real) :
    |x ⬝ᵥ y| <= finiteL2Norm x * finiteL2Norm y := by
  have hupper := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset a) x y
  have hlower := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset a) (fun i => -x i) y
  have hupper' : x ⬝ᵥ y <= finiteL2Norm x * finiteL2Norm y := by
    simpa [dotProduct, finiteL2Norm] using hupper
  have hlower' : -(x ⬝ᵥ y) <= finiteL2Norm x * finiteL2Norm y := by
    simpa [dotProduct, finiteL2Norm] using hlower
  rw [abs_le]
  exact ⟨by linarith, hupper'⟩

/-! ## Moore--Penrose electrical router -/

/-- Weighted graph Laplacian `L = B U B^T`. -/
def electricalLaplacian {v e : Type*} [Fintype e] [DecidableEq e]
    (B : Matrix v e Real) (capacity : e -> Real) : Matrix v v Real :=
  B * Matrix.diagonal capacity * Bᵀ

/-- Electrical router `R_el = U B^T L^dagger`. -/
def electricalRouter {v e : Type*} [Fintype v] [Fintype e] [DecidableEq e]
    (B : Matrix v e Real) (capacity : e -> Real)
    (laplacianPseudoinverse : Matrix v v Real) : Matrix e v Real :=
  Matrix.diagonal capacity * Bᵀ * laplacianPseudoinverse

/-- The displayed electrical router is an exact right inverse on the range of
the Laplacian.  For a connected incidence matrix this is precisely the
centered demand space. -/
theorem electricalRouter_rightInverse_on_laplacianRange
    {v e : Type*} [Fintype v] [Fintype e] [DecidableEq e]
    (B : Matrix v e Real) (capacity : e -> Real)
    (G : Matrix v v Real)
    (hPenrose : electricalLaplacian B capacity * G *
        electricalLaplacian B capacity = electricalLaplacian B capacity)
    (g : v -> Real) (hRange : exists y,
      g = (electricalLaplacian B capacity).mulVec y) :
    B.mulVec ((electricalRouter B capacity G).mulVec g) = g := by
  obtain ⟨y, rfl⟩ := hRange
  calc
    B.mulVec ((electricalRouter B capacity G).mulVec
        ((electricalLaplacian B capacity).mulVec y))
        = (B * electricalRouter B capacity G *
            electricalLaplacian B capacity).mulVec y := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (electricalLaplacian B capacity * G *
          electricalLaplacian B capacity).mulVec y := by
          congr 2
          simp [electricalRouter, electricalLaplacian, Matrix.mul_assoc]
    _ = (electricalLaplacian B capacity).mulVec y := by rw [hPenrose]

/-- Matrix multiplication makes the electrical router a real-linear map. -/
def electricalRouterLinearMap {v e : Type*} [Fintype v] [Fintype e]
    [DecidableEq e]
    (B : Matrix v e Real) (capacity : e -> Real)
    (G : Matrix v v Real) :
    LinearMap (RingHom.id Real) (v -> Real) (e -> Real) :=
  (electricalRouter B capacity G).mulVecLin

/-- A normalized spectral gap is a Rayleigh lower bound on centered vectors.
`parentScale` is `mu(Q)^(2/3)`, so `lambda` is the second eigenvalue of
`parentScale^(-1) L`. -/
def HasNormalizedCenteredGap {v : Type*} [Fintype v]
    (L : Matrix v v Real) (parentScale lambda : Real) : Prop :=
  forall x, IsCentered x ->
    parentScale * lambda * finiteL2Norm x ^ 2 <= x ⬝ᵥ L.mulVec x

/-- The Rayleigh gap gives the spectral inverse estimate for the
pseudoinverse potential. -/
theorem pseudoinversePotential_bound
    {v : Type*} [Fintype v] [Nonempty v]
    (L G : Matrix v v Real) (scale : v -> Real)
    (parentScale lambda : Real)
    (hparent : 0 < parentScale) (hlambda : 0 < lambda)
    (hscale : forall i, 0 < scale i)
    (hprofile : Finset.univ.sum (fun i => scale i ^ 2) <= parentScale ^ 2)
    (hgap : HasNormalizedCenteredGap L parentScale lambda)
    (hGcentered : forall g, IsCentered g -> IsCentered (G.mulVec g))
    (hRight : forall g, IsCentered g -> L.mulVec (G.mulVec g) = g)
    (g : v -> Real) (hg : IsCentered g) :
    finiteL2Norm (G.mulVec g) <= hierarchyDemandNorm scale g / lambda := by
  let p := G.mulVec g
  let pNorm := finiteL2Norm p
  let gNorm := finiteL2Norm g
  let demand := hierarchyDemandNorm scale g
  have hp_nonneg : 0 <= pNorm := Real.sqrt_nonneg _
  have hdemand : 0 <= demand := hierarchyDemandNorm_nonneg scale g hscale
  have hgNorm : gNorm <= parentScale * demand :=
    finiteL2Norm_le_parentScale_mul_demandNorm scale g parentScale
      hscale hparent.le hprofile
  have hright : L.mulVec p = g := hRight g hg
  have hrayleigh : parentScale * lambda * pNorm ^ 2 <= p ⬝ᵥ g := by
    simpa [p, pNorm, hright] using hgap p (hGcentered g hg)
  have hcauchy : |p ⬝ᵥ g| <= pNorm * gNorm := by
    simpa [pNorm, gNorm] using
      abs_dotProduct_le_finiteL2Norm_mul_finiteL2Norm p g
  have hchain : parentScale * lambda * pNorm ^ 2 <=
      pNorm * (parentScale * demand) := by
    calc
      parentScale * lambda * pNorm ^ 2 <= p ⬝ᵥ g := hrayleigh
      _ <= |p ⬝ᵥ g| := le_abs_self _
      _ <= pNorm * gNorm := hcauchy
      _ <= pNorm * (parentScale * demand) :=
        mul_le_mul_of_nonneg_left hgNorm hp_nonneg
  change pNorm <= demand / lambda
  by_cases hpzero : pNorm = 0
  · rw [hpzero]
    exact div_nonneg hdemand hlambda.le
  · have hp_pos : 0 < pNorm := lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hfactor : 0 < parentScale * pNorm := mul_pos hparent hp_pos
    have hcancel : lambda * pNorm <= demand := by
      nlinarith [hchain]
    exact (le_div_iff₀ hlambda).2 (by simpa [mul_comm] using hcancel)

/-- Incidence columns of an ordinary oriented graph have Euclidean norm
`sqrt 2`; the weak inequality form also covers missing or shorted edges. -/
def HasIncidenceColumnBound {v e : Type*} [Fintype v]
    (B : Matrix v e Real) : Prop :=
  forall edge, finiteL2Norm (fun vertex => B vertex edge) <= Real.sqrt 2

/-- Pointwise edge estimate for the electrical current. -/
theorem electricalRouter_component_bound
    {v e : Type*} [Fintype v] [Fintype e] [DecidableEq e] [Nonempty v]
    (B : Matrix v e Real) (capacity : e -> Real) (G : Matrix v v Real)
    (scale : v -> Real) (lambda : Real)
    (hcapacity : forall edge, 0 < capacity edge)
    (hcolumns : HasIncidenceColumnBound B)
    (hpotential : forall g, IsCentered g ->
      finiteL2Norm (G.mulVec g) <= hierarchyDemandNorm scale g / lambda)
    (_hlambda : 0 < lambda) (g : v -> Real) (hg : IsCentered g)
    (edge : e) :
    |(electricalRouter B capacity G).mulVec g edge| / capacity edge <=
      Real.sqrt 2 / lambda * hierarchyDemandNorm scale g := by
  let p := G.mulVec g
  have hcurrentValue :
      (electricalRouter B capacity G).mulVec g edge =
        capacity edge * (Bᵀ.mulVec p) edge := by
    change ((Matrix.diagonal capacity * Bᵀ * G).mulVec g) edge =
      capacity edge * (Bᵀ.mulVec (G.mulVec g)) edge
    rw [show Matrix.diagonal capacity * Bᵀ * G =
        Matrix.diagonal capacity * (Bᵀ * G) by
      simp only [Matrix.mul_assoc]]
    calc
      ((Matrix.diagonal capacity * (Bᵀ * G)).mulVec g) edge =
          (Matrix.diagonal capacity).mulVec ((Bᵀ * G).mulVec g) edge := by
        rw [Matrix.mulVec_mulVec]
      _ = capacity edge * ((Bᵀ * G).mulVec g) edge := by
        rw [Matrix.mulVec_diagonal]
      _ = capacity edge * (Bᵀ.mulVec (G.mulVec g)) edge := by
        rw [Matrix.mulVec_mulVec]
  have hcurrent :
      (electricalRouter B capacity G).mulVec g edge / capacity edge =
        (fun vertex => B vertex edge) ⬝ᵥ p := by
    rw [hcurrentValue]
    field_simp [(hcapacity edge).ne']
    simp [Matrix.mulVec, dotProduct]
  have hcauchy := abs_dotProduct_le_finiteL2Norm_mul_finiteL2Norm
    (fun vertex => B vertex edge) p
  have hsqrt : 0 <= Real.sqrt 2 := Real.sqrt_nonneg _
  have hpnonneg : 0 <= finiteL2Norm p := Real.sqrt_nonneg _
  have hpbound := hpotential g hg
  have habs : |(electricalRouter B capacity G).mulVec g edge| /
      capacity edge =
      |(electricalRouter B capacity G).mulVec g edge / capacity edge| := by
    rw [abs_div, abs_of_pos (hcapacity edge)]
  rw [habs, hcurrent]
  calc
    |(fun vertex => B vertex edge) ⬝ᵥ p|
        <= finiteL2Norm (fun vertex => B vertex edge) * finiteL2Norm p :=
      hcauchy
    _ <= Real.sqrt 2 * finiteL2Norm p :=
      mul_le_mul_of_nonneg_right (hcolumns edge) hpnonneg
    _ <= Real.sqrt 2 * (hierarchyDemandNorm scale g / lambda) :=
      mul_le_mul_of_nonneg_left hpbound hsqrt
    _ = Real.sqrt 2 / lambda * hierarchyDemandNorm scale g := by ring

/-- The electrical router has congestion at most `sqrt 2 / lambda` in the
hierarchy demand norm.  This is the displayed bound on `C_Q^lin`, witnessed
by one explicit linear right inverse. -/
theorem electricalRouter_congestion_bound
    {v e : Type*} [Fintype v] [Fintype e]
    [DecidableEq e] [Nonempty v] [Nonempty e]
    (B : Matrix v e Real) (capacity : e -> Real) (G : Matrix v v Real)
    (scale : v -> Real) (lambda : Real)
    (hcapacity : forall edge, 0 < capacity edge)
    (hcolumns : HasIncidenceColumnBound B)
    (hpotential : forall g, IsCentered g ->
      finiteL2Norm (G.mulVec g) <= hierarchyDemandNorm scale g / lambda)
    (hlambda : 0 < lambda) (g : v -> Real) (hg : IsCentered g) :
    hierarchyCongestionNorm capacity
        ((electricalRouter B capacity G).mulVec g) <=
      Real.sqrt 2 / lambda * hierarchyDemandNorm scale g := by
  unfold hierarchyCongestionNorm
  apply Finset.sup'_le
  intro edge hedge
  exact electricalRouter_component_bound B capacity G scale lambda
    hcapacity hcolumns hpotential hlambda g hg edge

/-! ## The weighted `K_4` Fiedler floor -/

/-- The six-capacity Laplacian of the complete graph on four vertices. -/
def k4WeightedLaplacian
    (u01 u02 u03 u12 u13 u23 : Real) : Matrix (Fin 4) (Fin 4) Real :=
  !![u01 + u02 + u03, -u01, -u02, -u03;
     -u01, u01 + u12 + u13, -u12, -u13;
     -u02, -u12, u02 + u12 + u23, -u23;
     -u03, -u13, -u23, u03 + u13 + u23]

/-- Quadratic form of the weighted `K_4` Laplacian. -/
theorem k4WeightedLaplacian_energy
    (u01 u02 u03 u12 u13 u23 : Real) (x : Fin 4 -> Real) :
    x ⬝ᵥ (k4WeightedLaplacian u01 u02 u03 u12 u13 u23).mulVec x =
      u01 * (x 0 - x 1) ^ 2 + u02 * (x 0 - x 2) ^ 2 +
      u03 * (x 0 - x 3) ^ 2 + u12 * (x 1 - x 2) ^ 2 +
      u13 * (x 1 - x 3) ^ 2 + u23 * (x 2 - x 3) ^ 2 := by
  simp [k4WeightedLaplacian, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- If all six capacities are at least `uMin`, the weighted `K_4` Laplacian
has centered Rayleigh floor `4 uMin`. -/
theorem k4_fiedler_floor
    (uMin u01 u02 u03 u12 u13 u23 : Real)
    (hu01 : uMin <= u01) (hu02 : uMin <= u02)
    (hu03 : uMin <= u03) (hu12 : uMin <= u12)
    (hu13 : uMin <= u13) (hu23 : uMin <= u23)
    (x : Fin 4 -> Real) (hcenter : x 0 + x 1 + x 2 + x 3 = 0) :
    4 * uMin * Finset.univ.sum (fun i => x i ^ 2) <=
      x ⬝ᵥ (k4WeightedLaplacian u01 u02 u03 u12 u13 u23).mulVec x := by
  have h01 := mul_le_mul_of_nonneg_right hu01 (sq_nonneg (x 0 - x 1))
  have h02 := mul_le_mul_of_nonneg_right hu02 (sq_nonneg (x 0 - x 2))
  have h03 := mul_le_mul_of_nonneg_right hu03 (sq_nonneg (x 0 - x 3))
  have h12 := mul_le_mul_of_nonneg_right hu12 (sq_nonneg (x 1 - x 2))
  have h13 := mul_le_mul_of_nonneg_right hu13 (sq_nonneg (x 1 - x 3))
  have h23 := mul_le_mul_of_nonneg_right hu23 (sq_nonneg (x 2 - x 3))
  have hpair :
      (x 0 - x 1) ^ 2 + (x 0 - x 2) ^ 2 + (x 0 - x 3) ^ 2 +
        (x 1 - x 2) ^ 2 + (x 1 - x 3) ^ 2 + (x 2 - x 3) ^ 2 =
      4 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) := by
    have hsquare : (x 0 + x 1 + x 2 + x 3) ^ 2 = 0 := by rw [hcenter]; norm_num
    nlinarith
  rw [k4WeightedLaplacian_energy]
  simp only [Fin.sum_univ_four]
  calc
    4 * uMin * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2)
        = uMin * ((x 0 - x 1) ^ 2 + (x 0 - x 2) ^ 2 +
          (x 0 - x 3) ^ 2 + (x 1 - x 2) ^ 2 +
          (x 1 - x 3) ^ 2 + (x 2 - x 3) ^ 2) := by rw [hpair]; ring
    _ <= u01 * (x 0 - x 1) ^ 2 + u02 * (x 0 - x 2) ^ 2 +
        u03 * (x 0 - x 3) ^ 2 + u12 * (x 1 - x 2) ^ 2 +
        u13 * (x 1 - x 3) ^ 2 + u23 * (x 2 - x 3) ^ 2 := by linarith

/-- After division by the parent two-thirds mass scale, the `K_4` Fiedler
floor is `4 uMin / parentScale`. -/
theorem k4_normalized_fiedler_floor
    (parentScale uMin u01 u02 u03 u12 u13 u23 : Real)
    (hparent : 0 < parentScale)
    (hu01 : uMin <= u01) (hu02 : uMin <= u02)
    (hu03 : uMin <= u03) (hu12 : uMin <= u12)
    (hu13 : uMin <= u13) (hu23 : uMin <= u23)
    (x : Fin 4 -> Real) (hcenter : x 0 + x 1 + x 2 + x 3 = 0) :
    (4 * uMin / parentScale) * Finset.univ.sum (fun i => x i ^ 2) <=
      x ⬝ᵥ ((parentScale⁻¹) •
        k4WeightedLaplacian u01 u02 u03 u12 u13 u23).mulVec x := by
  have hfloor := k4_fiedler_floor uMin u01 u02 u03 u12 u13 u23
    hu01 hu02 hu03 hu12 hu13 hu23 x hcenter
  have hscaled := mul_le_mul_of_nonneg_left hfloor (inv_nonneg.mpr hparent.le)
  calc
    (4 * uMin / parentScale) * Finset.univ.sum (fun i => x i ^ 2)
        = parentScale⁻¹ *
          (4 * uMin * Finset.univ.sum (fun i => x i ^ 2)) := by
            rw [div_eq_inv_mul]
            ring
    _ <= parentScale⁻¹ *
        (x ⬝ᵥ (k4WeightedLaplacian u01 u02 u03 u12 u13 u23).mulVec x) :=
      hscaled
    _ = x ⬝ᵥ ((parentScale⁻¹) •
        k4WeightedLaplacian u01 u02 u03 u12 u13 u23).mulVec x := by
      simp [Matrix.smul_mulVec, dotProduct, Finset.mul_sum]
      ring

/-- Equal child mass `m` gives the manuscript's exact denominator
`(4m)^(2/3)`. -/
theorem equalMass_k4_normalized_fiedler_floor
    (m uMin u01 u02 u03 u12 u13 u23 : Real) (hm : 0 < m)
    (hu01 : uMin <= u01) (hu02 : uMin <= u02)
    (hu03 : uMin <= u03) (hu12 : uMin <= u12)
    (hu13 : uMin <= u13) (hu23 : uMin <= u23)
    (x : Fin 4 -> Real) (hcenter : x 0 + x 1 + x 2 + x 3 = 0) :
    (4 * uMin / ((4 * m) ^ (2 / 3 : Real))) *
        Finset.univ.sum (fun i => x i ^ 2) <=
      x ⬝ᵥ ((((4 * m) ^ (2 / 3 : Real))⁻¹) •
        k4WeightedLaplacian u01 u02 u03 u12 u13 u23).mulVec x := by
  apply k4_normalized_fiedler_floor
  · exact Real.rpow_pos_of_pos (by positivity) _
  · exact hu01
  · exact hu02
  · exact hu03
  · exact hu12
  · exact hu13
  · exact hu23
  · exact hcenter

/-- The assumption `uMin >= c0 m^(2/3)` gives a mass-independent positive
lower bound for the normalized `K_4` Fiedler coefficient. -/
theorem equalMass_capacityScaling_uniform_fiedlerCoefficient
    (m c0 uMin : Real) (hm : 0 < m)
    (hcapacityScaling : c0 * m ^ (2 / 3 : Real) <= uMin) :
    4 * c0 / (4 : Real) ^ (2 / 3 : Real) <=
      4 * uMin / (4 * m) ^ (2 / 3 : Real) := by
  have hmPow : 0 < m ^ (2 / 3 : Real) := Real.rpow_pos_of_pos hm _
  have h4Pow : 0 < (4 : Real) ^ (2 / 3 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.mul_rpow (by norm_num) hm.le]
  apply (div_le_div_iff₀ h4Pow (mul_pos h4Pow hmPow)).2
  nlinarith

/-- Consequently the reciprocal electrical-router coefficient is uniformly
bounded by a constant depending only on `c0`, not on the child mass. -/
theorem equalMass_capacityScaling_uniform_routerCoefficient
    (m c0 uMin : Real) (hm : 0 < m) (hc0 : 0 < c0)
    (hcapacityScaling : c0 * m ^ (2 / 3 : Real) <= uMin) :
    Real.sqrt 2 / (4 * uMin / (4 * m) ^ (2 / 3 : Real)) <=
      Real.sqrt 2 / (4 * c0 / (4 : Real) ^ (2 / 3 : Real)) := by
  have hfloor := equalMass_capacityScaling_uniform_fiedlerCoefficient
    m c0 uMin hm hcapacityScaling
  have hmPow : 0 < m ^ (2 / 3 : Real) := Real.rpow_pos_of_pos hm _
  have h4Pow : 0 < (4 : Real) ^ (2 / 3 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have huMin : 0 < uMin := lt_of_lt_of_le (mul_pos hc0 hmPow) hcapacityScaling
  have hactual : 0 < 4 * uMin / (4 * m) ^ (2 / 3 : Real) := by positivity
  have huniform : 0 < 4 * c0 / (4 : Real) ^ (2 / 3 : Real) := by positivity
  apply (div_le_div_iff₀ hactual huniform).2
  exact mul_le_mul_of_nonneg_left hfloor (Real.sqrt_nonneg _)

/-- A normalized centered vector whose energy lies below a proposed positive
floor is the explicit Fiedler obstruction to that floor. -/
theorem normalizedFiedlerVector_obstructs_gap
    {v : Type*} [Fintype v] (L : Matrix v v Real) (lambda : Real)
    (x : v -> Real) (hcenter : IsCentered x)
    (hnormalized : Finset.univ.sum (fun i => x i ^ 2) = 1)
    (hcollapse : x ⬝ᵥ L.mulVec x < lambda) :
    Not (forall y, IsCentered y ->
      lambda * Finset.univ.sum (fun i => y i ^ 2) <= y ⬝ᵥ L.mulVec y) := by
  intro hgap
  have hx := hgap x hcenter
  rw [hnormalized, mul_one] at hx
  exact (not_lt_of_ge hx) hcollapse

end HierarchyElectricalRouter
end NCG
