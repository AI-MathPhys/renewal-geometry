/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The second and contracted Bianchi identities on the metric 3-jet
  (infrastructure for `lem:supp-open-subsidiary`, `eq:supp-open-exact-subsidiary`;
  emergent-spacetime manuscript)

Everything is exact finite index algebra at a point, over an arbitrary finite index type `n`.
A metric 3-jet `J : Jet3 n` consists of matrices `g`, `G` (`g G = 1`), `dg a = ∂_a g`,
`ddg a b = ∂_a∂_b g`, `dddg a b c = ∂_a∂_b∂_c g`, symmetric in the matrix indices and in the
derivative indices (`Jet3.Valid`).  We use the matrix-valued connection formalism:

* `low a` — the lowered Christoffel matrix `(low a)_{ks} = Γ_{k,as}
  = ½(∂_a g_{ks} + ∂_s g_{ka} - ∂_k g_{as})`; `dlow`, `ddlow` its formal first and second
  derivatives (linear in `ddg`, `dddg`);
* `chr a = G * low a`, so `(chr a)_{ls} = Γ^l_{as}`; `dchr b a = ∂_b Γ_a`, `ddchr c b a = ∂_c∂_b Γ_a`
  are the product-rule jets (with `∂ G = -G (∂g) G`);
* `riem a b = ∂_a Γ_b - ∂_b Γ_a + Γ_a Γ_b - Γ_b Γ_a`, so `(riem a b)_{ls} = R^l_{s a b}`;
  `driem c a b = ∂_c R_{ab}` and `nablaRiem c a b = ∇_c R^·_{· a b}`;
* `ric s b = R^l_{s l b}`, `scal = G^{sb} R_{sb}`, `nablaRic`, `ein = Ric - ½ g R`, `nablaEin`.

Main results:

* `bianchi_two` — the **second Bianchi identity** `∇_c R_{ab} + ∇_a R_{bc} + ∇_b R_{ca} = 0` for
  the torsion-free connection jet (gauge part by `noncomm_ring`, torsion part by `Γ` symmetric);
* `metric_mul_riem_antisymm`, `metric_mul_nablaRiem_antisymm` — `g R_{ab}` and `g ∇_c R_{ab}` are
  antisymmetric matrices (pair antisymmetry of the Levi-Civita curvature and of its covariant
  derivative);
* `contracted_bianchi_ricci` — `2 ∇^l R_{lb} = ∂_b R`;
* `contracted_bianchi` — **`∇^μ G_{μν} = 0`** (`divEin = 0`) for every valid metric 3-jet.
-/

open Finset Matrix
open scoped BigOperators

namespace RenewalGeometry.ContractedBianchiJet

noncomputable section

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A metric 3-jet at a point: the metric `g`, its inverse `G`, and the matrices of first,
second and third partial derivatives of `g`. -/
structure Jet3 (n : Type*) where
  g : Matrix n n ℝ
  G : Matrix n n ℝ
  dg : n → Matrix n n ℝ
  ddg : n → n → Matrix n n ℝ
  dddg : n → n → n → Matrix n n ℝ

/-- Validity of a metric 3-jet: `g G = 1`, all matrices symmetric, derivative indices
commuting. -/
structure Jet3.Valid (J : Jet3 n) : Prop where
  gG : J.g * J.G = 1
  g_symm : J.gᵀ = J.g
  G_symm : J.Gᵀ = J.G
  dg_symm : ∀ a, (J.dg a)ᵀ = J.dg a
  ddg_symm : ∀ a b, (J.ddg a b)ᵀ = J.ddg a b
  ddg_comm : ∀ a b, J.ddg a b = J.ddg b a
  dddg_symm : ∀ a b c, (J.dddg a b c)ᵀ = J.dddg a b c
  dddg_comm1 : ∀ a b c, J.dddg a b c = J.dddg b a c
  dddg_comm2 : ∀ a b c, J.dddg a b c = J.dddg a c b

namespace Jet3

variable (J : Jet3 n)

theorem Valid.Gg {J : Jet3 n} (hv : J.Valid) : J.G * J.g = 1 :=
  mul_eq_one_comm.mp hv.gG

theorem Valid.dg_apply {J : Jet3 n} (hv : J.Valid) (a k s : n) : J.dg a k s = J.dg a s k := by
  conv_rhs => rw [← hv.dg_symm a]
  rfl

theorem Valid.ddg_apply {J : Jet3 n} (hv : J.Valid) (a b k s : n) :
    J.ddg a b k s = J.ddg a b s k := by
  conv_rhs => rw [← hv.ddg_symm a b]
  rfl

theorem Valid.dddg_apply {J : Jet3 n} (hv : J.Valid) (a b c k s : n) :
    J.dddg a b c k s = J.dddg a b c s k := by
  conv_rhs => rw [← hv.dddg_symm a b c]
  rfl

/-! ### Lowered Christoffel matrices and their jets -/

/-- `(low a)_{ks} = Γ_{k,as} = ½(∂_a g_{ks} + ∂_s g_{ka} - ∂_k g_{as})`. -/
def low (a : n) : Matrix n n ℝ :=
  Matrix.of fun k s => (1 / 2 : ℝ) * (J.dg a k s + J.dg s k a - J.dg k a s)

/-- `∂_b` of `low a`. -/
def dlow (b a : n) : Matrix n n ℝ :=
  Matrix.of fun k s => (1 / 2 : ℝ) * (J.ddg b a k s + J.ddg b s k a - J.ddg b k a s)

/-- `∂_c∂_b` of `low a`. -/
def ddlow (c b a : n) : Matrix n n ℝ :=
  Matrix.of fun k s => (1 / 2 : ℝ) * (J.dddg c b a k s + J.dddg c b s k a - J.dddg c b k a s)

theorem low_add_transpose {J : Jet3 n} (hv : J.Valid) (a : n) : J.low a + (J.low a)ᵀ = J.dg a := by
  ext k s
  simp only [low, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [hv.dg_apply s k a, hv.dg_apply k a s, hv.dg_apply a s k]
  ring

theorem dlow_add_transpose {J : Jet3 n} (hv : J.Valid) (b a : n) :
    J.dlow b a + (J.dlow b a)ᵀ = J.ddg b a := by
  ext k s
  simp only [dlow, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [hv.ddg_apply b s k a, hv.ddg_apply b k a s, hv.ddg_apply b a s k]
  ring

theorem ddlow_add_transpose {J : Jet3 n} (hv : J.Valid) (c b a : n) :
    J.ddlow c b a + (J.ddlow c b a)ᵀ = J.dddg c b a := by
  ext k s
  simp only [ddlow, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [hv.dddg_apply c b s k a, hv.dddg_apply c b k a s, hv.dddg_apply c b a s k]
  ring

theorem low_apply_comm {J : Jet3 n} (hv : J.Valid) (a k s : n) : J.low a k s = J.low s k a := by
  simp only [low, Matrix.of_apply]
  rw [hv.dg_apply k a s]
  ring

theorem ddlow_swap {J : Jet3 n} (hv : J.Valid) (c b a : n) : J.ddlow c b a = J.ddlow b c a := by
  ext k s
  simp only [ddlow, Matrix.of_apply]
  simp only [hv.dddg_comm1 c b]

/-! ### Christoffel matrices and their jets -/

/-- `(chr a)_{ls} = Γ^l_{as}`. -/
def chr (a : n) : Matrix n n ℝ := J.G * J.low a

/-- `∂_a G = -G (∂_a g) G`. -/
def dG (a : n) : Matrix n n ℝ := -(J.G * J.dg a * J.G)

/-- `∂_b Γ_a = G (∂_b low_a - ∂_b g Γ_a)`. -/
def dchr (b a : n) : Matrix n n ℝ := J.G * (J.dlow b a - J.dg b * J.chr a)

/-- `∂_c∂_b Γ_a`. -/
def ddchr (c b a : n) : Matrix n n ℝ :=
  J.G * (J.ddlow c b a - J.ddg c b * J.chr a - J.dg c * J.dchr b a - J.dg b * J.dchr c a)

theorem chr_apply_comm {J : Jet3 n} (hv : J.Valid) (a l s : n) : J.chr a l s = J.chr s l a := by
  simp only [chr, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [low_apply_comm hv a k s]

theorem ddchr_swap {J : Jet3 n} (hv : J.Valid) (c b a : n) : J.ddchr c b a = J.ddchr b c a := by
  unfold ddchr
  rw [ddlow_swap hv c b a, hv.ddg_comm c b]
  noncomm_ring

theorem metric_mul_chr {J : Jet3 n} (hv : J.Valid) (a : n) : J.g * J.chr a = J.low a := by
  rw [chr, ← Matrix.mul_assoc, hv.gG, Matrix.one_mul]

theorem metric_mul_dchr {J : Jet3 n} (hv : J.Valid) (b a : n) :
    J.g * J.dchr b a = J.dlow b a - J.dg b * J.chr a := by
  rw [dchr, ← Matrix.mul_assoc, hv.gG, Matrix.one_mul]

theorem metric_mul_ddchr {J : Jet3 n} (hv : J.Valid) (c b a : n) :
    J.g * J.ddchr c b a =
      J.ddlow c b a - J.ddg c b * J.chr a - J.dg c * J.dchr b a - J.dg b * J.dchr c a := by
  rw [ddchr, ← Matrix.mul_assoc, hv.gG, Matrix.one_mul]

/-! ### Riemann matrices -/

/-- `(riem a b)_{ls} = R^l_{s a b}`. -/
def riem (a b : n) : Matrix n n ℝ :=
  J.dchr a b - J.dchr b a + J.chr a * J.chr b - J.chr b * J.chr a

/-- `∂_c R_{ab}` (product rule). -/
def driem (c a b : n) : Matrix n n ℝ :=
  J.ddchr c a b - J.ddchr c b a + J.dchr c a * J.chr b + J.chr a * J.dchr c b
    - J.dchr c b * J.chr a - J.chr b * J.dchr c a

/-- The gauge-covariant derivative `∂_c R_{ab} + [Γ_c, R_{ab}]` (endomorphism indices only). -/
def gaugeDRiem (c a b : n) : Matrix n n ℝ :=
  J.driem c a b + J.chr c * J.riem a b - J.riem a b * J.chr c

/-- The full covariant derivative `∇_c R^l_{s a b}` as a matrix in `(l, s)`. -/
def nablaRiem (c a b : n) : Matrix n n ℝ :=
  J.gaugeDRiem c a b - ∑ l, J.chr c l a • J.riem l b - ∑ l, J.chr c l b • J.riem a l

theorem riem_antisymm (a b : n) : J.riem a b = -J.riem b a := by
  unfold riem; noncomm_ring

theorem gaugeDRiem_antisymm (c a b : n) : J.gaugeDRiem c a b = -J.gaugeDRiem c b a := by
  unfold gaugeDRiem driem riem; noncomm_ring

theorem nablaRiem_antisymm (c a b : n) : J.nablaRiem c a b = -J.nablaRiem c b a := by
  unfold nablaRiem
  rw [J.gaugeDRiem_antisymm c a b]
  have h1 : ∑ l, J.chr c l b • J.riem a l = -∑ l, J.chr c l b • J.riem l a := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [J.riem_antisymm a l, smul_neg]
  have h2 : ∑ l, J.chr c l a • J.riem b l = -∑ l, J.chr c l a • J.riem l b := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [J.riem_antisymm b l, smul_neg]
  rw [h1, h2]
  abel

/-- Gauge part of the second Bianchi identity (Jacobi identity plus symmetry of `∂∂Γ`). -/
theorem gauge_bianchi {J : Jet3 n} (hv : J.Valid) (c a b : n) :
    J.gaugeDRiem c a b + J.gaugeDRiem a b c + J.gaugeDRiem b c a = 0 := by
  unfold gaugeDRiem driem riem
  rw [ddchr_swap hv a c b, ddchr_swap hv b a c, ddchr_swap hv c b a]
  noncomm_ring

/-- **The second Bianchi identity** for the Levi-Civita connection jet:
`∇_c R^l_{s a b} + ∇_a R^l_{s b c} + ∇_b R^l_{s c a} = 0`. -/
theorem bianchi_two {J : Jet3 n} (hv : J.Valid) (c a b : n) :
    J.nablaRiem c a b + J.nablaRiem a b c + J.nablaRiem b c a = 0 := by
  have hg := gauge_bianchi hv c a b
  unfold nablaRiem
  have ht : (∑ l, J.chr c l a • J.riem l b + ∑ l, J.chr c l b • J.riem a l) +
      (∑ l, J.chr a l b • J.riem l c + ∑ l, J.chr a l c • J.riem b l) +
      (∑ l, J.chr b l c • J.riem l a + ∑ l, J.chr b l a • J.riem c l) = 0 := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [J.riem_antisymm a l, J.riem_antisymm b l, J.riem_antisymm c l,
      chr_apply_comm hv a l c, chr_apply_comm hv b l a, chr_apply_comm hv c l b]
    simp only [smul_neg]
    abel
  calc _ = (J.gaugeDRiem c a b + J.gaugeDRiem a b c + J.gaugeDRiem b c a) -
      ((∑ l, J.chr c l a • J.riem l b + ∑ l, J.chr c l b • J.riem a l) +
      (∑ l, J.chr a l b • J.riem l c + ∑ l, J.chr a l c • J.riem b l) +
      (∑ l, J.chr b l c • J.riem l a + ∑ l, J.chr b l a • J.riem c l)) := by abel
    _ = 0 := by rw [hg, ht, sub_zero]


/-! ### Pair antisymmetry of the Levi-Civita curvature and of its covariant derivative -/

/-- `g R_{ab} = ∂_a low_b - ∂_b low_a - low_aᵀ Γ_b + low_bᵀ Γ_a`. -/
def lowRiem (a b : n) : Matrix n n ℝ :=
  J.dlow a b - J.dlow b a - (J.low a)ᵀ * J.chr b + (J.low b)ᵀ * J.chr a

/-- The formal derivative `∂_c (g R_{ab})` of `lowRiem`. -/
def dlowRiem (c a b : n) : Matrix n n ℝ :=
  J.ddlow c a b - J.ddlow c b a - (J.dlow c a)ᵀ * J.chr b - (J.low a)ᵀ * J.dchr c b
    + (J.dlow c b)ᵀ * J.chr a + (J.low b)ᵀ * J.dchr c a

theorem metric_mul_riem {J : Jet3 n} (hv : J.Valid) (a b : n) : J.g * J.riem a b = J.lowRiem a b := by
  calc J.g * J.riem a b = J.g * J.dchr a b - J.g * J.dchr b a + (J.g * J.chr a) * J.chr b
        - (J.g * J.chr b) * J.chr a := by unfold riem; noncomm_ring
    _ = _ := by
        rw [metric_mul_dchr hv, metric_mul_dchr hv, metric_mul_chr hv, metric_mul_chr hv,
          ← low_add_transpose hv a, ← low_add_transpose hv b]
        unfold lowRiem
        noncomm_ring

theorem metric_mul_driem {J : Jet3 n} (hv : J.Valid) (c a b : n) :
    J.g * J.driem c a b = J.dlowRiem c a b - J.dg c * J.riem a b := by
  have e1 : J.g * J.driem c a b = J.g * J.ddchr c a b - J.g * J.ddchr c b a
      + (J.g * J.dchr c a) * J.chr b + (J.g * J.chr a) * J.dchr c b
      - (J.g * J.dchr c b) * J.chr a - (J.g * J.chr b) * J.dchr c a := by
    unfold driem; noncomm_ring
  rw [e1, metric_mul_ddchr hv, metric_mul_ddchr hv, metric_mul_dchr hv, metric_mul_dchr hv,
    metric_mul_chr hv, metric_mul_chr hv]
  have hca := dlow_add_transpose hv c a
  have hcb := dlow_add_transpose hv c b
  rw [← hca, ← hcb, ← low_add_transpose hv a, ← low_add_transpose hv b]
  unfold dlowRiem riem
  noncomm_ring

theorem chr_transpose {J : Jet3 n} (hv : J.Valid) (a : n) : (J.chr a)ᵀ = (J.low a)ᵀ * J.G := by
  rw [chr, Matrix.transpose_mul, hv.G_symm]

/-- **Pair antisymmetry**: `g R_{ab}` is an antisymmetric matrix (`R_{ks ab} = -R_{sk ab}`). -/
theorem lowRiem_antisymm {J : Jet3 n} (hv : J.Valid) (a b : n) :
    (J.lowRiem a b)ᵀ = -J.lowRiem a b := by
  have hab : (J.dlow a b)ᵀ = J.ddg a b - J.dlow a b := by
    rw [← dlow_add_transpose hv a b]; abel
  have hba : (J.dlow b a)ᵀ = J.ddg a b - J.dlow b a := by
    rw [hv.ddg_comm a b, ← dlow_add_transpose hv b a]; abel
  unfold lowRiem
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose, chr_transpose hv, hab, hba]
  unfold chr
  noncomm_ring

theorem metric_mul_riem_antisymm {J : Jet3 n} (hv : J.Valid) (a b : n) :
    (J.g * J.riem a b)ᵀ = -(J.g * J.riem a b) := by
  rw [metric_mul_riem hv, lowRiem_antisymm hv]

theorem dlowRiem_antisymm {J : Jet3 n} (hv : J.Valid) (c a b : n) :
    (J.dlowRiem c a b)ᵀ = -J.dlowRiem c a b := by
  have h1 : (J.ddlow c b a)ᵀ = J.dddg c a b - J.ddlow c b a := by
    rw [hv.dddg_comm2 c a b, ← ddlow_add_transpose hv c b a]; abel
  have h2 : (J.ddlow c a b)ᵀ = J.dddg c a b - J.ddlow c a b := by
    rw [← ddlow_add_transpose hv c a b]; abel
  have hdg : (J.dg c)ᵀ = J.dg c := hv.dg_symm c
  unfold dlowRiem dchr
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose, chr_transpose hv, h1, h2, hdg, hv.G_symm]
  unfold chr
  noncomm_ring

/-- If `g N` is antisymmetric then `N G = -(G Nᵀ)`. -/
theorem mul_G_of_antisymm {J : Jet3 n} (hv : J.Valid) (N : Matrix n n ℝ)
    (hN : (J.g * N)ᵀ = -(J.g * N)) : N * J.G = -(J.G * Nᵀ) := by
  have hN' : N = J.G * (J.g * N) := by rw [← Matrix.mul_assoc, hv.Gg, Matrix.one_mul]
  have : Nᵀ = -((J.g * N) * J.G) := by
    conv_lhs => rw [hN']
    rw [Matrix.transpose_mul, hN, hv.G_symm, Matrix.neg_mul]
  rw [this]
  conv_lhs => rw [hN']
  noncomm_ring

/-- **Pair antisymmetry of `∇R`**: `g ∇_c R_{ab}` is antisymmetric. -/
theorem metric_mul_nablaRiem_antisymm {J : Jet3 n} (hv : J.Valid) (c a b : n) :
    (J.g * J.nablaRiem c a b)ᵀ = -(J.g * J.nablaRiem c a b) := by
  have hR : J.riem a b = J.G * J.lowRiem a b := by
    rw [← metric_mul_riem hv, ← Matrix.mul_assoc, hv.Gg, Matrix.one_mul]
  have hgauge : J.g * J.gaugeDRiem c a b =
      J.dlowRiem c a b - (J.low c)ᵀ * J.G * J.lowRiem a b - J.lowRiem a b * J.G * J.low c := by
    have e : J.g * J.gaugeDRiem c a b = J.g * J.driem c a b + (J.g * J.chr c) * J.riem a b
        - (J.g * J.riem a b) * J.chr c := by unfold gaugeDRiem; noncomm_ring
    rw [e, metric_mul_driem hv, metric_mul_chr hv, metric_mul_riem hv, ← low_add_transpose hv c,
      hR, chr]
    noncomm_ring
  have hga : (J.g * J.gaugeDRiem c a b)ᵀ = -(J.g * J.gaugeDRiem c a b) := by
    rw [hgauge]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, dlowRiem_antisymm hv, lowRiem_antisymm hv, hv.G_symm]
    noncomm_ring
  have hsum : ∀ (w : n → ℝ) (P : n → Matrix n n ℝ), (∀ l, (J.g * P l)ᵀ = -(J.g * P l)) →
      (J.g * ∑ l, w l • P l)ᵀ = -(J.g * ∑ l, w l • P l) := by
    intro w P hP
    rw [Matrix.mul_sum, Matrix.transpose_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_smul, Matrix.transpose_smul, hP l, smul_neg]
  have h1 := hsum (fun l => J.chr c l a) (fun l => J.riem l b)
    (fun l => metric_mul_riem_antisymm hv l b)
  have h2 := hsum (fun l => J.chr c l b) (fun l => J.riem a l)
    (fun l => metric_mul_riem_antisymm hv a l)
  unfold nablaRiem
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.transpose_sub, Matrix.transpose_sub, hga, h1, h2]
  abel


/-! ### Ricci tensor, scalar curvature, Einstein tensor and their covariant derivatives -/

/-- The Ricci matrix `Ric_{sb} = R^l_{s l b}`. -/
def ricM : Matrix n n ℝ := Matrix.of fun s b => ∑ l, J.riem l b l s

/-- Its formal derivative `∂_c Ric_{sb}`. -/
def dricM (c : n) : Matrix n n ℝ := Matrix.of fun s b => ∑ l, J.driem c l b l s

/-- `∇_c Ric_{sb} = ∂_c Ric_{sb} - Γ^l_{cs} Ric_{lb} - Γ^l_{cb} Ric_{sl}`. -/
def nablaRicM (c : n) : Matrix n n ℝ := J.dricM c - (J.chr c)ᵀ * J.ricM - J.ricM * J.chr c

/-- Scalar curvature `R = G^{sb} Ric_{sb}`. -/
def scal : ℝ := Matrix.trace (J.G * J.ricMᵀ)

/-- Its formal derivative `∂_c R`. -/
def dscal (c : n) : ℝ := Matrix.trace (J.dG c * J.ricMᵀ) + Matrix.trace (J.G * (J.dricM c)ᵀ)

/-- `∇^l Ric_{lb} = G^{lk} ∇_l Ric_{kb}`. -/
def divRic (b : n) : ℝ := ∑ l, ∑ k, J.G l k * J.nablaRicM l k b

/-- The Einstein matrix `G_{sb} = Ric_{sb} - ½ g_{sb} R`. -/
def einM : Matrix n n ℝ := J.ricM - ((1 / 2 : ℝ) * J.scal) • J.g

/-- Its formal derivative `∂_c G_{sb}`. -/
def deinM (c : n) : Matrix n n ℝ :=
  J.dricM c - ((1 / 2 : ℝ) * J.dscal c) • J.g - ((1 / 2 : ℝ) * J.scal) • J.dg c

/-- `∇_c G_{sb}`. -/
def nablaEinM (c : n) : Matrix n n ℝ := J.deinM c - (J.chr c)ᵀ * J.einM - J.einM * J.chr c

/-- The divergence `∇^μ G_{μν} = G^{lk} ∇_l G_{kν}`. -/
def divEin (b : n) : ℝ := ∑ l, ∑ k, J.G l k * J.nablaEinM l k b

/-- Contraction commutes with covariant differentiation:
`Σ_l (∇_c R)^l_{s l b} = ∇_c Ric_{sb}`. -/
theorem sum_nablaRiem_contract (c s b : n) :
    ∑ l, J.nablaRiem c l b l s = J.nablaRicM c s b := by
  simp only [nablaRiem, gaugeDRiem, nablaRicM, dricM, ricM, Matrix.sub_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply,
    Matrix.of_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have e1 : ∑ l, ∑ k, J.chr c l k * J.riem l b k s = ∑ l, ∑ k, J.chr c k l * J.riem k b l s :=
    Finset.sum_comm
  have e2 : ∑ l, ∑ k, J.riem l b l k * J.chr c k s = ∑ k, J.chr c k s * ∑ l, J.riem l b l k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have e3 : ∑ l, ∑ k, J.chr c k b * J.riem l k l s = ∑ k, ∑ l, J.chr c k b * J.riem l k l s :=
    Finset.sum_comm
  have e4 : ∀ k, ∑ l, J.chr c k b * J.riem l k l s = J.chr c k b * ∑ l, J.riem l k l s :=
    fun k => (Finset.mul_sum _ _ _).symm
  rw [e1, e2, e3]
  simp only [e4]
  ring_nf
  congr 1
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- **Once-contracted second Bianchi identity**:
`Σ_l ∇_l R^l_{s a b} - ∇_a Ric_{sb} + ∇_b Ric_{sa} = 0`. -/
theorem bianchi_once_contracted {J : Jet3 n} (hv : J.Valid) (a b s : n) :
    ∑ l, J.nablaRiem l a b l s - J.nablaRicM a s b + J.nablaRicM b s a = 0 := by
  have h : ∀ l, J.nablaRiem l a b l s + J.nablaRiem a b l l s + J.nablaRiem b l a l s = 0 := by
    intro l
    have := congrFun (congrFun (bianchi_two hv l a b) l) s
    simpa only [Matrix.add_apply, Matrix.zero_apply] using this
  have h2 : ∑ l, J.nablaRiem a b l l s = -J.nablaRicM a s b := by
    rw [← J.sum_nablaRiem_contract a s b, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [J.nablaRiem_antisymm a b l, Matrix.neg_apply]
  have h3 : ∑ l, J.nablaRiem b l a l s = J.nablaRicM b s a := J.sum_nablaRiem_contract b s a
  have hsum : ∑ l, (J.nablaRiem l a b l s + J.nablaRiem a b l l s + J.nablaRiem b l a l s) = 0 :=
    Finset.sum_eq_zero fun l _ => h l
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h2, h3] at hsum
  linarith

/-- `∂ G = -(Γ G) - (Γ G)ᵀ`. -/
theorem dG_eq {J : Jet3 n} (hv : J.Valid) (c : n) :
    J.dG c = -(J.chr c * J.G) - (J.chr c * J.G)ᵀ := by
  rw [dG, Matrix.transpose_mul, chr_transpose hv, ← low_add_transpose hv c, chr, hv.G_symm]
  noncomm_ring

theorem sum_sum_mul_eq_trace (A B : Matrix n n ℝ) :
    ∑ s, ∑ a, A s a * B s a = Matrix.trace (A * Bᵀ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]

/-- Contracting `∇_b Ric` with `G` gives `∂_b R`. -/
theorem trace_nablaRic {J : Jet3 n} (hv : J.Valid) (b : n) :
    ∑ s, ∑ a, J.G s a * J.nablaRicM b s a = J.dscal b := by
  rw [sum_sum_mul_eq_trace, dscal, dG_eq hv, nablaRicM]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, hv.G_symm,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.neg_mul, Matrix.trace_sub, Matrix.trace_neg]
  have t1 : Matrix.trace (J.chr b * J.G * J.ricMᵀ) = Matrix.trace (J.G * (J.ricMᵀ * J.chr b)) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have t2 : Matrix.trace (J.G * (J.chr b)ᵀ * J.ricMᵀ) =
      Matrix.trace (J.G * ((J.chr b)ᵀ * J.ricMᵀ)) := by rw [Matrix.mul_assoc]
  rw [t1, t2]
  ring

/-- Contraction of `∇_l R^l_{s a b}` against `G^{sa}` gives `-∇^l Ric_{lb}`. -/
theorem trace_sum_nablaRiem {J : Jet3 n} (hv : J.Valid) (b : n) :
    ∑ s, ∑ a, J.G s a * ∑ l, J.nablaRiem l a b l s = -J.divRic b := by
  have key : ∀ l a, ∑ s, J.nablaRiem l a b l s * J.G s a =
      -∑ k, J.G l k * J.nablaRiem l a b a k := by
    intro l a
    have := congrFun (congrFun (mul_G_of_antisymm hv (J.nablaRiem l a b)
      (metric_mul_nablaRiem_antisymm hv l a b)) l) a
    simpa only [Matrix.mul_apply, Matrix.neg_apply, Matrix.transpose_apply] using this
  calc ∑ s, ∑ a, J.G s a * ∑ l, J.nablaRiem l a b l s
      = ∑ s, ∑ a, ∑ l, J.G s a * J.nablaRiem l a b l s := by simp only [Finset.mul_sum]
    _ = ∑ a, ∑ s, ∑ l, J.G s a * J.nablaRiem l a b l s := Finset.sum_comm
    _ = ∑ a, ∑ l, ∑ s, J.G s a * J.nablaRiem l a b l s :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ s, J.G s a * J.nablaRiem l a b l s := Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ s, J.nablaRiem l a b l s * J.G s a :=
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun s _ => mul_comm _ _
    _ = ∑ l, ∑ a, -∑ k, J.G l k * J.nablaRiem l a b a k := by simp only [key]
    _ = -∑ l, ∑ k, J.G l k * ∑ a, J.nablaRiem l a b a k := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_neg_distrib, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ = -J.divRic b := by
        simp only [sum_nablaRiem_contract, divRic]

/-- **The contracted Bianchi identity for the Ricci tensor**: `2 ∇^l Ric_{lb} = ∂_b R`. -/
theorem contracted_bianchi_ricci {J : Jet3 n} (hv : J.Valid) (b : n) :
    2 * J.divRic b = J.dscal b := by
  have h : ∀ s a, J.G s a * (∑ l, J.nablaRiem l a b l s - J.nablaRicM a s b +
      J.nablaRicM b s a) = 0 := fun s a => by rw [bianchi_once_contracted hv a b s, mul_zero]
  have hsum : ∑ s, ∑ a, J.G s a * (∑ l, J.nablaRiem l a b l s - J.nablaRicM a s b +
      J.nablaRicM b s a) = 0 := Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun a _ => h s a
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [trace_sum_nablaRiem hv, trace_nablaRic hv] at hsum
  have h2 : ∑ s, ∑ a, J.G s a * J.nablaRicM a s b = J.divRic b := by
    unfold divRic
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
    have : J.G s a = J.G a s := by
      conv_lhs => rw [← hv.G_symm]
      rfl
    rw [this]
  rw [h2] at hsum
  linarith

/-- Metric compatibility at jet level: `∂_c g - Γ_cᵀ g - g Γ_c = 0`. -/
theorem metric_compat {J : Jet3 n} (hv : J.Valid) (c : n) :
    J.dg c - (J.chr c)ᵀ * J.g - J.g * J.chr c = 0 := by
  rw [metric_mul_chr hv, chr_transpose hv, Matrix.mul_assoc, hv.Gg, Matrix.mul_one,
    ← low_add_transpose hv c]
  abel

theorem nablaEinM_eq {J : Jet3 n} (hv : J.Valid) (c : n) :
    J.nablaEinM c = J.nablaRicM c - ((1 / 2 : ℝ) * J.dscal c) • J.g := by
  have h := metric_compat hv c
  have : J.dg c = (J.chr c)ᵀ * J.g + J.g * J.chr c := by
    rw [← sub_eq_zero, ← h]; abel
  unfold nablaEinM deinM einM nablaRicM
  rw [this]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add]
  abel

/-- **The contracted Bianchi identity** `∇^μ G_{μν} = 0` for every valid metric 3-jet. -/
theorem contracted_bianchi {J : Jet3 n} (hv : J.Valid) (b : n) : J.divEin b = 0 := by
  have hG : ∀ l, ∑ k, J.G l k * J.g k b = if l = b then 1 else 0 := by
    intro l
    have := congrFun (congrFun hv.Gg l) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  unfold divEin
  simp only [nablaEinM_eq hv, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib]
  have e : ∑ l, ∑ k, J.G l k * ((1 / 2 : ℝ) * J.dscal l * J.g k b) = (1 / 2 : ℝ) * J.dscal b := by
    have : ∀ l, ∑ k, J.G l k * ((1 / 2 : ℝ) * J.dscal l * J.g k b) =
        (1 / 2 : ℝ) * J.dscal l * (if l = b then 1 else 0) := by
      intro l
      rw [← hG l, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [e]
  have := contracted_bianchi_ricci hv b
  unfold divRic at this
  linarith

end Jet3

end

end RenewalGeometry.ContractedBianchiJet
