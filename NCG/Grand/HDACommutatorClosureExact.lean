/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.FiniteHDA

/-!
# Finite HDA: the algebraic bracket identifications

Algebra layer for `thm:finite-HDA`, addressing the fidelity-audit gap ("the
identification of reduced commutators with the three HDA right-hand sides"):

* `hh_oriented_reduction`: the `[H,H]` commutator reduces to a sum over the
  **oriented** edge set with the antisymmetrized coefficient
  `N_x M_y − M_x N_y` — combining the proved smearing/locality engine with the
  orientation bookkeeping;
* `edge_coefficient_gradient`: the oriented coefficient is the manuscript's
  gradient form `N_x ∇_e M − M_x ∇_e N`;
* `hh_bracket`: **the `HH` identity** — with (H3) identifying each oriented
  edge current `−i[n_x,n_y]` with the declared tangential copy, the reduced
  commutator is `D_h` of the discrete field carried by the oriented edge
  coefficients `G^{-1}(N ∂M − M ∂N)`;
* `dd_bracket_of_scalar_commutant`: **the `DD` identity** — the closure
  defect `Z(v,w) = −i[D_v,D_w] − D_{[v,w]}` commutes with every retained
  lapse by the operator Jacobi identity, the `DH` relation, and
  `[ℓ_v,ℓ_w] = ℓ_{[v,w]}`; under the scalar-commutant branch (H6) it is
  scalar, and canonical centering makes it traceless, hence zero;
* `feshbach_cross_vanishes`: on the reducing source carrier (H4), every
  Schur–Feshbach cross term `PAQBP − PBQAP` vanishes.
-/

open Matrix Finset

namespace NCG
namespace HDAClosure

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The smeared normal generator `H_h[N] = Σ_x N_x n_{x,h}`. -/
def smear (nloc : ι → Matrix (Fin d) (Fin d) ℂ) (N : ι → ℂ) :
    Matrix (Fin d) (Fin d) ℂ := ∑ x, N x • nloc x

/-- The local edge commutator `c_{xy} = [n_x, n_y]`. -/
def edgeComm (nloc : ι → Matrix (Fin d) (Fin d) ℂ) (p : ι × ι) :
    Matrix (Fin d) (Fin d) ℂ := nloc p.1 * nloc p.2 - nloc p.2 * nloc p.1

omit [DecidableEq ι] in
/-- **Oriented reduction of the `HH` commutator**: over an oriented one-link
edge set the commutator carries the antisymmetrized coefficient
`N_x M_y − M_x N_y`. -/
theorem hh_oriented_reduction (nloc : ι → Matrix (Fin d) (Fin d) ℂ)
    (N M : ι → ℂ) (E : Finset (ι × ι))
    (horient : ∀ p ∈ E, (p.2, p.1) ∉ E)
    (hloc : ∀ x y : ι, (x, y) ∉ E → (y, x) ∉ E →
      nloc x * nloc y = nloc y * nloc x) :
    smear nloc N * smear nloc M - smear nloc M * smear nloc N
      = ∑ p ∈ E, (N p.1 * M p.2 - M p.1 * N p.2) • edgeComm nloc p := by
  classical
  have hdisj : Disjoint E (E.image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro p hp hps
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp hps
    have hq' : q = (p.2, p.1) := by
      rw [← hqe]
      simp
    rw [hq'] at hq
    exact horient p hp hq
  have hloc' : ∀ x y : ι, (x, y) ∉ E ∪ E.image Prod.swap →
      nloc x * nloc y = nloc y * nloc x := by
    intro x y hxy
    rw [Finset.mem_union, not_or] at hxy
    obtain ⟨h1, h2⟩ := hxy
    refine hloc x y h1 fun hyx => h2 ?_
    exact Finset.mem_image.mpr ⟨(y, x), hyx, rfl⟩
  have hred := finite_hda_locality nloc N M (E ∪ E.image Prod.swap) hloc'
  have hexp := finite_hda_smearing nloc N M
  unfold smear
  rw [hexp, hred, Finset.sum_union hdisj]
  have himg : ∑ p ∈ E.image Prod.swap, (N p.1 * M p.2) •
      (nloc p.1 * nloc p.2 - nloc p.2 * nloc p.1)
      = ∑ p ∈ E, (-(M p.1 * N p.2)) • edgeComm nloc p := by
    rw [Finset.sum_image (fun p _ q _ h => Prod.swap_injective h)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Prod.fst_swap, Prod.snd_swap, edgeComm]
    rw [show nloc p.2 * nloc p.1 - nloc p.1 * nloc p.2
        = -(nloc p.1 * nloc p.2 - nloc p.2 * nloc p.1) from (neg_sub _ _).symm]
    rw [smul_neg, ← neg_smul, mul_comm (N p.2) (M p.1)]
  rw [himg, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [edgeComm]
  rw [← add_smul, ← sub_eq_add_neg]

omit [Fintype ι] [DecidableEq ι] in
/-- The oriented coefficient is the manuscript's gradient form
`N_x ∇_e M − M_x ∇_e N`. -/
theorem edge_coefficient_gradient (N M : ι → ℂ) (p : ι × ι) :
    N p.1 * M p.2 - M p.1 * N p.2
      = N p.1 * (M p.2 - M p.1) - M p.1 * (N p.2 - N p.1) := by
  ring

/-- **The `HH` bracket**: with (H3) identifying each oriented edge current
`−i[n_x, n_y]` with the declared tangential copy, the reduced commutator is
`D_h` of the discrete field carried by the oriented edge coefficients. -/
theorem hh_bracket (nloc : ι → Matrix (Fin d) (Fin d) ℂ)
    (N M : ι → ℂ) (E : Finset (ι × ι))
    (D : ((ι × ι) → ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (horient : ∀ p ∈ E, (p.2, p.1) ∉ E)
    (hloc : ∀ x y : ι, (x, y) ∉ E → (y, x) ∉ E →
      nloc x * nloc y = nloc y * nloc x)
    (hedge : ∀ p ∈ E, (-Complex.I) • edgeComm nloc p = D (Pi.single p 1)) :
    (-Complex.I) • (smear nloc N * smear nloc M - smear nloc M * smear nloc N)
      = D (∑ p ∈ E, (N p.1 * M p.2 - M p.1 * N p.2) • Pi.single p 1) := by
  rw [hh_oriented_reduction nloc N M E horient hloc, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [map_smul, ← hedge p hp, smul_comm]

/-- **The `DD` bracket from the scalar-commutant branch (H6)**: the closure
defect `Z(v,w) = −i[D_v,D_w] − D_{[v,w]}` commutes with every retained lapse
(operator Jacobi identity, the `DH` relation, and `[ℓ_v,ℓ_w] = ℓ_{[v,w]}`);
if the normal-history commutant is scalar and `D` is canonically centered,
the defect vanishes: `−i[D_v, D_w] = D_{[v,w]}`. -/
theorem dd_bracket_of_scalar_commutant {V L : Type*}
    (Dop : V → Matrix (Fin d) (Fin d) ℂ)
    (H : L → Matrix (Fin d) (Fin d) ℂ)
    (bracket : V → V → V) (ell : V → L → L)
    (v w : V)
    (hDH : ∀ (u : V) (N : L),
      (-Complex.I) • (Dop u * H N - H N * Dop u) = H (ell u N))
    (hell : ∀ N : L, H (ell v (ell w N)) - H (ell w (ell v N))
      = H (ell (bracket v w) N))
    (hscalar : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      (∀ N : L, X * H N = H N * X) → ∃ c : ℂ, X = c • 1)
    (hcenter : ∀ u : V, Matrix.trace (Dop u) = 0)
    (hd : 0 < d) :
    (-Complex.I) • (Dop v * Dop w - Dop w * Dop v) = Dop (bracket v w) := by
  have unsmul : ∀ {X Y : Matrix (Fin d) (Fin d) ℂ},
      (-Complex.I) • X = Y → X = Complex.I • Y := by
    intro X Y h
    have h2 := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => Complex.I • M) h
    simpa [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul] using h2
  set Z : Matrix (Fin d) (Fin d) ℂ :=
    (-Complex.I) • (Dop v * Dop w - Dop w * Dop v) - Dop (bracket v w)
    with hZdef
  have hZcomm : ∀ N : L, Z * H N = H N * Z := by
    intro N
    have hv := unsmul (hDH v N)
    have hw := unsmul (hDH w N)
    have hvw := unsmul (hDH v (ell w N))
    have hwv := unsmul (hDH w (ell v N))
    have hbr := unsmul (hDH (bracket v w) N)
    have jac : (Dop v * Dop w - Dop w * Dop v) * H N
        - H N * (Dop v * Dop w - Dop w * Dop v)
        = Dop v * (Dop w * H N - H N * Dop w)
          - (Dop w * H N - H N * Dop w) * Dop v
          - (Dop w * (Dop v * H N - H N * Dop v)
            - (Dop v * H N - H N * Dop v) * Dop w) := by
      noncomm_ring
    have t1 : Dop v * (Complex.I • H (ell w N))
        - (Complex.I • H (ell w N)) * Dop v
        = Complex.I • (Complex.I • H (ell v (ell w N))) := by
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, hvw]
    have t2 : Dop w * (Complex.I • H (ell v N))
        - (Complex.I • H (ell v N)) * Dop w
        = Complex.I • (Complex.I • H (ell w (ell v N))) := by
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, hwv]
    have hC : (Dop v * Dop w - Dop w * Dop v) * H N
        - H N * (Dop v * Dop w - Dop w * Dop v)
        = - H (ell (bracket v w) N) := by
      rw [jac, hw, hv, t1, t2, smul_smul, smul_smul, Complex.I_mul_I, ← hell N]
      module
    have expand : Z * H N - H N * Z
        = (-Complex.I) • ((Dop v * Dop w - Dop w * Dop v) * H N
            - H N * (Dop v * Dop w - Dop w * Dop v))
          - (Dop (bracket v w) * H N - H N * Dop (bracket v w)) := by
      rw [hZdef]
      simp only [Matrix.sub_mul, Matrix.mul_sub, smul_mul_assoc, mul_smul_comm,
        smul_sub]
      abel
    have hZN : Z * H N - H N * Z = 0 := by
      rw [expand, hC, hbr, smul_neg]
      module
    exact sub_eq_zero.mp hZN
  obtain ⟨c, hc⟩ := hscalar Z hZcomm
  have htr : Matrix.trace Z = 0 := by
    rw [hZdef, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_sub,
      Matrix.trace_mul_comm (Dop v) (Dop w), sub_self, smul_zero,
      hcenter (bracket v w), sub_zero]
  have hcz : c = 0 := by
    have h1 : Matrix.trace ((c • 1 : Matrix (Fin d) (Fin d) ℂ)) = 0 :=
      hc ▸ htr
    rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at h1
    have hdc : ((Fintype.card (Fin d) : ℂ)) ≠ 0 := by
      rw [Fintype.card_fin]
      exact_mod_cast hd.ne'
    exact (mul_eq_zero.mp h1).resolve_right hdc
  have hZ0 : Z = 0 := by rw [hc, hcz, zero_smul]
  exact sub_eq_zero.mp (hZdef.symm.trans hZ0)

/-- **The reducing-carrier Feshbach cancellation (H4)**: if the source
projection reduces both generator families (`QAP = QBP = 0`), every
Schur–Feshbach cross term `PAQBP − PBQAP` vanishes. -/
theorem feshbach_cross_vanishes (P Q A B : Matrix (Fin d) (Fin d) ℂ)
    (hQA : Q * A * P = 0) (hQB : Q * B * P = 0) :
    P * A * Q * B * P - P * B * Q * A * P = 0 := by
  have h1 : P * A * Q * B * P = 0 := by
    calc P * A * Q * B * P = P * (A * (Q * B * P)) := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQB, Matrix.mul_zero, Matrix.mul_zero]
  have h2 : P * B * Q * A * P = 0 := by
    calc P * B * Q * A * P = P * (B * (Q * A * P)) := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQA, Matrix.mul_zero, Matrix.mul_zero]
  rw [h1, h2, sub_zero]

end HDAClosure
end NCG
