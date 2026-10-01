/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ContractedBianchiJet

/-!
# The forced harmonic subsidiary identity on the metric 3-jet
  (`eq:supp-open-exact-subsidiary`, `eq:supp-open-reduced-residual`; emergent-spacetime
  manuscript, `lem:supp-open-subsidiary`)

Exact jet algebra over an arbitrary finite index type, on top of
`Gravity/ContractedBianchiJet.lean`.  For a valid metric 3-jet `J` and an arbitrary covector
2-jet `(c, dc, ddc)` (`dc a b = ∂_a c_b`, `ddc e a b = ∂_e∂_a c_b`, symmetric in `e a`):

* `Nc` — `∇_a c_b`; `NNc e` — `∇_e∇_a c_b` (matrix in `(a, b)`);
* `ricci_identity` — the **Ricci identity** `∇_e∇_a c_b - ∇_a∇_e c_b = -R^l_{b e a} c_l`;
* `hM` — the harmonic-defect tensor `𝓗_{ab}(g, c) = ∇_{(a}c_{b)} - ½ g_{ab} ∇^d c_d`
  (`eq:supp-open-reduced-residual`), `dhM` its formal derivative, `divH` its divergence;
* `divH_eq` — `∇^a 𝓗_{ab} = ½ □c_b + ½ Ric^l{}_b c_l` with `□c_b = G^{ea}∇_e∇_a c_b`;
* `forced_subsidiary` — **`eq:supp-open-exact-subsidiary`**: for the reduced residual
  `r = G(g) - 𝓗(g, c)`, `□c_b + Ric^l{}_b c_l = -2 ∇^a r_{ab}` (by the contracted Bianchi
  identity `contracted_bianchi`).
* `gaugeCov`, `dgaugeCov`, `ddgaugeCov` — the lower-index gauge covector
  `c_b(g) = g_{bμ} g^{αβ} Γ^μ_{αβ} = G^{kl} Γ_{b,kl}` of the metric and its formal jets;
  `ddgaugeCov_swap` — its second jet is symmetric, so the identities above apply to it.
-/

open Finset Matrix
open scoped BigOperators

namespace RenewalGeometry.ContractedBianchiJet

noncomputable section

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Jet3

variable (J : Jet3 n)

/-- The Christoffel-transported covector `(∑_l Γ^l_{ab} c_l)` as a matrix in `(a, b)`. -/
def chrC (c : n → ℝ) : Matrix n n ℝ := Matrix.of fun a b => ∑ l, J.chr a l b * c l

/-- `∇_a c_b = ∂_a c_b - Γ^l_{ab} c_l`. -/
def nc (c : n → ℝ) (dc : Matrix n n ℝ) : Matrix n n ℝ := dc - J.chrC c

/-- `∂_e ∇_a c_b`. -/
def dnc (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ) (e : n) : Matrix n n ℝ :=
  ddc e - Matrix.of fun a b => ∑ l, (J.dchr e a l b * c l + J.chr a l b * dc e l)

/-- `∇_e ∇_a c_b` as a matrix in `(a, b)`. -/
def nnc (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ) (e : n) : Matrix n n ℝ :=
  J.dnc c dc ddc e - (J.chr e)ᵀ * J.nc c dc - J.nc c dc * J.chr e

theorem nnc_apply (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ) (e a b : n) :
    J.nnc c dc ddc e a b = ddc e a b - ∑ l, J.dchr e a l b * c l - ∑ l, J.chr a l b * dc e l
      - ∑ l, J.chr e l a * dc l b + ∑ l, ∑ m, J.chr e l a * (J.chr l m b * c m)
      - ∑ l, J.chr e l b * dc a l + ∑ l, ∑ m, J.chr e l b * (J.chr a m l * c m) := by
  simp only [nnc, dnc, nc, chrC, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.transpose_apply, Finset.sum_add_distrib, mul_sub,
    Finset.mul_sum, sub_mul, Finset.sum_mul]
  have h1 : ∑ x, ∑ i, J.chr a i x * c i * J.chr e x b = ∑ l, ∑ m, J.chr e l b * (J.chr a m l * c m) :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ x, dc a x * J.chr e x b = ∑ l, J.chr e l b * dc a l :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [h1, h2]
  ring

/-- **The Ricci identity** for a covector 2-jet (`∂∂c` symmetric):
`∇_e∇_a c_b - ∇_a∇_e c_b = -Σ_l R^l_{b e a} c_l`. -/
theorem ricci_identity {J : Jet3 n} (hv : J.Valid) (c : n → ℝ) (dc : Matrix n n ℝ)
    (ddc : n → Matrix n n ℝ) (hddc : ∀ e a, ddc e a = ddc a e) (e a b : n) :
    J.nnc c dc ddc e a b - J.nnc c dc ddc a e b = -∑ l, J.riem e a l b * c l := by
  rw [J.nnc_apply, J.nnc_apply, hddc e a]
  have s1 : ∑ l, J.chr a l e * dc l b = ∑ l, J.chr e l a * dc l b :=
    Finset.sum_congr rfl fun l _ => by rw [chr_apply_comm hv a l e]
  have s2 : ∑ l, ∑ m, J.chr a l e * (J.chr l m b * c m) =
      ∑ l, ∑ m, J.chr e l a * (J.chr l m b * c m) :=
    Finset.sum_congr rfl fun l _ => by rw [chr_apply_comm hv a l e]
  rw [s1, s2]
  have r : ∑ l, J.riem e a l b * c l = ∑ l, J.dchr e a l b * c l - ∑ l, J.dchr a e l b * c l
      + ∑ l, ∑ m, J.chr e l m * J.chr a m b * c l - ∑ l, ∑ m, J.chr a l m * J.chr e m b * c l := by
    simp only [riem, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, sub_mul, add_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul]
  have t1 : ∑ l, ∑ m, J.chr e l b * (J.chr a m l * c m) = ∑ l, ∑ m, J.chr a l m * J.chr e m b * c l := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring
  have t2 : ∑ l, ∑ m, J.chr a l b * (J.chr e m l * c m) = ∑ l, ∑ m, J.chr e l m * J.chr a m b * c l := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring
  rw [r, t1, t2]
  ring

/-! ### The harmonic-defect tensor and its divergence -/

/-- `∇^d c_d = G^{kl} ∇_k c_l`. -/
def trN (c : n → ℝ) (dc : Matrix n n ℝ) : ℝ := Matrix.trace (J.G * (J.nc c dc)ᵀ)

/-- Formal derivative `∂_e (G^{kl} ∇_k c_l)`. -/
def dtrN (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ) (e : n) : ℝ :=
  Matrix.trace (J.dG e * (J.nc c dc)ᵀ) + Matrix.trace (J.G * (J.dnc c dc ddc e)ᵀ)

/-- **The harmonic-defect tensor** `𝓗_{ab} = ∇_{(a}c_{b)} - ½ g_{ab} ∇^d c_d`
(`eq:supp-open-reduced-residual`). -/
def hM (c : n → ℝ) (dc : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (J.nc c dc + (J.nc c dc)ᵀ) - ((1 / 2 : ℝ) * J.trN c dc) • J.g

/-- Its formal derivative `∂_e 𝓗_{ab}`. -/
def dhM (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ) (e : n) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (J.dnc c dc ddc e + (J.dnc c dc ddc e)ᵀ) - ((1 / 2 : ℝ) * J.trN c dc) • J.dg e
    - ((1 / 2 : ℝ) * J.dtrN c dc ddc e) • J.g

/-- `∇_e 𝓗_{ab}`. -/
def nablaH (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ) (e : n) : Matrix n n ℝ :=
  J.dhM c dc ddc e - (J.chr e)ᵀ * J.hM c dc - J.hM c dc * J.chr e

/-- `∇^a 𝓗_{ab} = G^{ea} ∇_e 𝓗_{ab}`. -/
def divH (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ) (b : n) : ℝ :=
  ∑ e, ∑ a, J.G e a * J.nablaH c dc ddc e a b

/-- The wave operator `□c_b = G^{ea} ∇_e∇_a c_b`. -/
def boxC (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ) (b : n) : ℝ :=
  ∑ e, ∑ a, J.G e a * J.nnc c dc ddc e a b

/-- The Ricci action `Ric^l{}_b c_l = G^{lk} Ric_{kb} c_l`. -/
def ricC (c : n → ℝ) (b : n) : ℝ := ∑ l, (∑ k, J.G l k * J.ricM k b) * c l

/-- The metric trace of a covariant derivative is the derivative of the trace (`∇G = 0`). -/
theorem trace_covDeriv {J : Jet3 n} (hv : J.Valid) (X dX : Matrix n n ℝ) (e : n) :
    ∑ s, ∑ a, J.G s a * (dX - (J.chr e)ᵀ * X - X * J.chr e) s a =
      Matrix.trace (J.dG e * Xᵀ) + Matrix.trace (J.G * dXᵀ) := by
  rw [sum_sum_mul_eq_trace, dG_eq hv]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, hv.G_symm,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.neg_mul, Matrix.trace_sub, Matrix.trace_neg]
  have t1 : Matrix.trace (J.chr e * J.G * Xᵀ) = Matrix.trace (J.G * (Xᵀ * J.chr e)) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have t2 : Matrix.trace (J.G * (J.chr e)ᵀ * Xᵀ) =
      Matrix.trace (J.G * ((J.chr e)ᵀ * Xᵀ)) := by rw [Matrix.mul_assoc]
  rw [t1, t2]
  ring

theorem dtrN_eq {J : Jet3 n} (hv : J.Valid) (c : n → ℝ) (dc : Matrix n n ℝ)
    (ddc : n → Matrix n n ℝ) (e : n) :
    J.dtrN c dc ddc e = ∑ s, ∑ a, J.G s a * J.nnc c dc ddc e s a := by
  rw [dtrN, nnc, trace_covDeriv hv]

theorem nablaH_eq {J : Jet3 n} (hv : J.Valid) (c : n → ℝ) (dc : Matrix n n ℝ)
    (ddc : n → Matrix n n ℝ) (e : n) :
    J.nablaH c dc ddc e = (1 / 2 : ℝ) • (J.nnc c dc ddc e + (J.nnc c dc ddc e)ᵀ)
      - ((1 / 2 : ℝ) * J.dtrN c dc ddc e) • J.g := by
  have h := metric_compat hv e
  have hdg : J.dg e = (J.chr e)ᵀ * J.g + J.g * J.chr e := by
    rw [← sub_eq_zero, ← h]; abel
  unfold nablaH dhM hM nnc
  rw [hdg]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_add, smul_sub]
  abel

/-- `∇^a 𝓗_{ab} = ½ □c_b + ½ Ric^l{}_b c_l` for every covector 2-jet with symmetric second jet. -/
theorem divH_eq {J : Jet3 n} (hv : J.Valid) (c : n → ℝ) (dc : Matrix n n ℝ)
    (ddc : n → Matrix n n ℝ) (hddc : ∀ e a, ddc e a = ddc a e) (b : n) :
    J.divH c dc ddc b = (1 / 2 : ℝ) * J.boxC c dc ddc b + (1 / 2 : ℝ) * J.ricC c b := by
  have hG : ∀ e, ∑ a, J.G e a * J.g a b = if e = b then 1 else 0 := by
    intro e
    have := congrFun (congrFun hv.Gg e) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hGs : ∀ e a, J.G e a = J.G a e := fun e a => by
    conv_lhs => rw [← hv.G_symm]
    rfl
  -- the three pieces
  have p1 : ∑ e, ∑ a, J.G e a * J.nnc c dc ddc e b a -
      ∑ e, ∑ a, J.G e a * J.nnc c dc ddc b e a = J.ricC c b := by
    rw [← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    simp only [ricci_identity hv c dc ddc hddc]
    -- `Σ_{e,a} G_{ea} R^l_{b e a}`-contraction via pair antisymmetry
    have key : ∀ e l, ∑ a, J.riem e b l a * J.G a e = -∑ k, J.G l k * J.riem e b e k := by
      intro e l
      have := congrFun (congrFun (mul_G_of_antisymm hv (J.riem e b)
        (metric_mul_riem_antisymm hv e b)) l) e
      simpa only [Matrix.mul_apply, Matrix.neg_apply, Matrix.transpose_apply] using this
    calc ∑ e, ∑ a, J.G e a * -∑ l, J.riem e b l a * c l
        = -∑ e, ∑ a, ∑ l, J.G e a * (J.riem e b l a * c l) := by
          simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
      _ = -∑ e, ∑ l, ∑ a, J.G e a * (J.riem e b l a * c l) := by
          congr 1
          exact Finset.sum_congr rfl fun e _ => Finset.sum_comm
      _ = -∑ l, ∑ e, ∑ a, J.G e a * (J.riem e b l a * c l) := by
          congr 1
          exact Finset.sum_comm
      _ = -∑ l, (∑ e, ∑ a, J.riem e b l a * J.G a e) * c l := by
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [Finset.sum_mul]
          refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
          rw [hGs e a]; ring
      _ = J.ricC c b := by
          simp only [key, Finset.sum_neg_distrib, neg_mul, neg_neg, ricC, ricM, Matrix.of_apply]
          refine Finset.sum_congr rfl fun l _ => ?_
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
  have p2 : ∑ e, ∑ a, J.G e a * J.nnc c dc ddc b e a = J.dtrN c dc ddc b := (dtrN_eq hv _ _ _ _).symm
  have p3 : ∑ e, ∑ a, J.G e a * (((1 / 2 : ℝ) * J.dtrN c dc ddc e) * J.g a b) =
      (1 / 2 : ℝ) * J.dtrN c dc ddc b := by
    have : ∀ e, ∑ a, J.G e a * (((1 / 2 : ℝ) * J.dtrN c dc ddc e) * J.g a b) =
        (1 / 2 : ℝ) * J.dtrN c dc ddc e * (if e = b then 1 else 0) := by
      intro e
      rw [← hG e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold divH boxC
  simp only [nablaH_eq hv, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  rw [p3]
  have e1 : ∑ e, ∑ a, J.G e a * ((1 / 2 : ℝ) * J.nnc c dc ddc e a b) =
      (1 / 2 : ℝ) * ∑ e, ∑ a, J.G e a * J.nnc c dc ddc e a b := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  have e2 : ∑ e, ∑ a, J.G e a * ((1 / 2 : ℝ) * J.nnc c dc ddc e b a) =
      (1 / 2 : ℝ) * ∑ e, ∑ a, J.G e a * J.nnc c dc ddc e b a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  rw [e1, e2]
  linarith

/-! ### The forced subsidiary equation -/

/-- The reduced residual `r = G(g) - 𝓗(g, c)` (`eq:supp-open-reduced-residual`). -/
def resM (c : n → ℝ) (dc : Matrix n n ℝ) : Matrix n n ℝ := J.einM - J.hM c dc

/-- Its formal derivative. -/
def dresM (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ) (e : n) : Matrix n n ℝ :=
  J.deinM e - J.dhM c dc ddc e

/-- `∇^a r_{ab}`. -/
def divRes (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ) (b : n) : ℝ :=
  ∑ e, ∑ a, J.G e a *
    (J.dresM c dc ddc e - (J.chr e)ᵀ * J.resM c dc - J.resM c dc * J.chr e) a b

theorem divRes_eq (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ) (b : n) :
    J.divRes c dc ddc b = J.divEin b - J.divH c dc ddc b := by
  unfold divRes divEin divH nablaEinM nablaH resM dresM
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp only [Matrix.sub_apply, Matrix.mul_sub, Matrix.sub_mul]
  ring

/-- **The forced harmonic subsidiary equation** `eq:supp-open-exact-subsidiary`: for every valid
metric 3-jet and every covector 2-jet with symmetric second jet, the reduced residual
`r = G(g) - 𝓗(g, c)` satisfies `□c_b + Ric^l{}_b c_l = -2 ∇^a r_{ab}`. -/
theorem forced_subsidiary {J : Jet3 n} (hv : J.Valid) (c : n → ℝ) (dc : Matrix n n ℝ)
    (ddc : n → Matrix n n ℝ) (hddc : ∀ e a, ddc e a = ddc a e) (b : n) :
    J.boxC c dc ddc b + J.ricC c b = -2 * J.divRes c dc ddc b := by
  rw [divRes_eq, contracted_bianchi hv, divH_eq hv c dc ddc hddc]
  ring

end Jet3

end

end RenewalGeometry.ContractedBianchiJet
