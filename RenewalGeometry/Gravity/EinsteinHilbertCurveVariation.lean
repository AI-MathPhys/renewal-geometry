/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.EinsteinHilbertJetVariation
import RenewalGeometry.Gravity.ActualJetCurveCalculus
import RenewalGeometry.Analysis.SobolevOpenSet

/-!
# The Einstein–Hilbert variation along curves of metric jets and the Palatini flux of a field

Infrastructure for `thm:native-closure` (Einstein–Standard-Model action-closure manuscript,
bridge step P3), continuing `Gravity/EinsteinHilbertJetVariation.lean`.

* Generic curve calculus (any finite index type): along differentiable curves of jets, the
  Christoffel symbols, the inverse-metric jet, the Christoffel jet, the Ricci jet and the metric
  trace have the product-rule derivatives used to define `chrVar`, `dginvVar`, `dchrVar`,
  `ricciVarJ` (`hasDerivAt_chr'`, `hasDerivAt_dginv'`, `hasDerivAt_dchr'`, `hasDerivAt_ricciJ'`,
  `hasDerivAt_trG'`).
* `hasDerivAt_volM_curve` — Jacobi: along a curve of nondegenerate symmetric metrics with
  `det g < 0`, `d√(-det g) = ½ √(-det g) g^{μν}k_{μν}`.
* **`hasDerivAt_volScal_curve`** — along a curve of metric 2-jets `(g(t), ∂g(t), ∂∂g(t))` with
  derivative `(k, dk, ddk)` at `t = 0`,
  `d/dt[√(-det g) R] = -√(-det g) G^{μν}k_{μν} + √(-det g)(∂_λV^λ + Γ^a_{aλ}V^λ)`
  (`EHJetVariation.eh_jet_variation`).
* **`sum_pd_flux_eq`** — for smooth metric and variation fields on `ℝ⁴`, the jet expression
  `√(-det g)(∂_λV^λ + Γ^a_{aλ}V^λ)` is the actual divergence `Σ_λ ∂_λ W^λ` of the Palatini flux
  field `W^λ = √(-det g) V^λ(g⁻¹, δΓ)` (`palatiniFlux`).
-/

namespace RenewalGeometry

namespace EHFieldVariation

open Finset HarmonicDefect EHJetVariation ActualJetSystem
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Generic curve calculus of the metric jets -/

section Curves

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem hasDerivAt_chr' {gi : ℝ → n → n → ℝ} {dg : ℝ → n → n → n → ℝ} {t : ℝ}
    {gi' : n → n → ℝ} {dg' : n → n → n → ℝ}
    (hgi : ∀ a b, HasDerivAt (fun s => gi s a b) (gi' a b) t)
    (hdg : ∀ α a b, HasDerivAt (fun s => dg s α a b) (dg' α a b) t) (l μ ν : n) :
    HasDerivAt (fun s => chr (gi s) (dg s) l μ ν)
      (chr gi' (dg t) l μ ν + chr (gi t) dg' l μ ν) t := by
  unfold chr
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun σ _ =>
    (hgi l σ).fun_mul (((hdg μ σ ν).fun_add (hdg ν σ μ)).fun_sub (hdg σ μ ν))
  refine (h.const_mul (1 / 2 : ℝ)).congr_deriv ?_
  rw [← mul_add, ← Finset.sum_add_distrib]

theorem hasDerivAt_dginv' {gi : ℝ → n → n → ℝ} {dg : ℝ → n → n → n → ℝ} {t : ℝ}
    {gi' : n → n → ℝ} {dg' : n → n → n → ℝ}
    (hgi : ∀ a b, HasDerivAt (fun s => gi s a b) (gi' a b) t)
    (hdg : ∀ α a b, HasDerivAt (fun s => dg s α a b) (dg' α a b) t) (α l σ : n) :
    HasDerivAt (fun s => dginv (gi s) (dg s) α l σ)
      (-∑ a, ∑ b, (gi' l a * dg t α a b * gi t b σ + gi t l a * dg' α a b * gi t b σ +
        gi t l a * dg t α a b * gi' b σ)) t := by
  unfold dginv
  refine HasDerivAt.fun_neg ?_
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
  exact (((hgi l a).fun_mul (hdg α a b)).fun_mul (hgi b σ)).congr_deriv (by ring)

theorem hasDerivAt_dchr' {gi : ℝ → n → n → ℝ} {dg : ℝ → n → n → n → ℝ}
    {ddg : ℝ → n → n → n → n → ℝ} {t : ℝ}
    {gi' : n → n → ℝ} {dg' : n → n → n → ℝ} {ddg' : n → n → n → n → ℝ}
    (hgi : ∀ a b, HasDerivAt (fun s => gi s a b) (gi' a b) t)
    (hdg : ∀ α a b, HasDerivAt (fun s => dg s α a b) (dg' α a b) t)
    (hddg : ∀ β α a b, HasDerivAt (fun s => ddg s β α a b) (ddg' β α a b) t) (α l μ ν : n) :
    HasDerivAt (fun s => dchr (gi s) (dg s) (ddg s) α l μ ν)
      ((1 / 2) * ∑ σ, (-∑ a, ∑ b, (gi' l a * dg t α a b * gi t b σ +
          gi t l a * dg' α a b * gi t b σ + gi t l a * dg t α a b * gi' b σ)) *
          (dg t μ σ ν + dg t ν σ μ - dg t σ μ ν) +
        (1 / 2) * ∑ σ, dginv (gi t) (dg t) α l σ * (dg' μ σ ν + dg' ν σ μ - dg' σ μ ν) +
        (1 / 2) * ∑ σ, gi' l σ * (ddg t α μ σ ν + ddg t α ν σ μ - ddg t α σ μ ν) +
        (1 / 2) * ∑ σ, gi t l σ * (ddg' α μ σ ν + ddg' α ν σ μ - ddg' α σ μ ν)) t := by
  unfold dchr dchr1 dchr2
  have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun σ _ =>
    (hasDerivAt_dginv' hgi hdg α l σ).fun_mul
      (((hdg μ σ ν).fun_add (hdg ν σ μ)).fun_sub (hdg σ μ ν))
  have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun σ _ =>
    (hgi l σ).fun_mul (((hddg α μ σ ν).fun_add (hddg α ν σ μ)).fun_sub (hddg α σ μ ν))
  refine ((h1.const_mul (1 / 2 : ℝ)).fun_add (h2.const_mul (1 / 2 : ℝ))).congr_deriv ?_
  simp only [Finset.sum_add_distrib, mul_add]
  ring

theorem hasDerivAt_ricciJ' {Γ : ℝ → n → n → n → ℝ} {D : ℝ → n → n → n → n → ℝ} {t : ℝ}
    {Γ' : n → n → n → ℝ} {D' : n → n → n → n → ℝ}
    (hΓ : ∀ l a b, HasDerivAt (fun s => Γ s l a b) (Γ' l a b) t)
    (hD : ∀ α l a b, HasDerivAt (fun s => D s α l a b) (D' α l a b) t) (μ ν : n) :
    HasDerivAt (fun s => ricciJ (Γ s) (D s) μ ν) (ricciVarJ (Γ t) Γ' D' μ ν) t := by
  unfold ricciJ ricciVarJ
  have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun α _ => hD α α μ ν
  have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun α _ => hD ν α μ α
  have h3 := HasDerivAt.fun_sum (u := Finset.univ) fun α _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun l _ => (hΓ α α l).fun_mul (hΓ l μ ν)
  have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun α _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun l _ => (hΓ α ν l).fun_mul (hΓ l μ α)
  refine (((h1.fun_sub h2).fun_add h3).fun_sub h4).congr_deriv ?_
  simp only [Finset.sum_add_distrib]

theorem hasDerivAt_trG' {gi : ℝ → n → n → ℝ} {X : ℝ → n → n → ℝ} {t : ℝ}
    {gi' X' : n → n → ℝ} (hgi : ∀ a b, HasDerivAt (fun s => gi s a b) (gi' a b) t)
    (hX : ∀ a b, HasDerivAt (fun s => X s a b) (X' a b) t) :
    HasDerivAt (fun s => trG (gi s) (X s)) (trG gi' (X t) + trG (gi t) X') t := by
  unfold trG
  refine (HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun ν _ =>
    (hgi μ ν).fun_mul (hX μ ν)).congr_deriv ?_
  simp only [← Finset.sum_add_distrib]

theorem hasDerivAt_ginvVar' {gi k : ℝ → n → n → ℝ} {t : ℝ} {gi' k' : n → n → ℝ}
    (hgi : ∀ a b, HasDerivAt (fun s => gi s a b) (gi' a b) t)
    (hk : ∀ a b, HasDerivAt (fun s => k s a b) (k' a b) t) (a b : n) :
    HasDerivAt (fun s => ginvVar (gi s) (k s) a b)
      (-∑ c, ∑ d, (gi' a c * k t c d * gi t d b + gi t a c * k' c d * gi t d b +
        gi t a c * k t c d * gi' d b)) t := by
  unfold ginvVar
  refine HasDerivAt.fun_neg ?_
  refine HasDerivAt.fun_sum fun c _ => HasDerivAt.fun_sum fun d _ => ?_
  exact (((hgi a c).fun_mul (hk c d)).fun_mul (hgi d b)).congr_deriv (by ring)

end Curves

/-! ### Jacobi's formula and the volume factor along curves -/

section Volume

theorem ginvOf_symm' {g : Fin 4 → Fin 4 → ℝ} (hg : ∀ μ ν, g μ ν = g ν μ) (l σ : Fin 4) :
    ginvOf g l σ = ginvOf g σ l := by
  have hT : (Matrix.of g).transpose = Matrix.of g := by
    ext a b; simp [hg b a]
  unfold ginvOf
  have := congrFun (congrFun (Matrix.transpose_nonsing_inv (Matrix.of g)) σ) l
  rw [hT] at this
  simpa using this

/-- The volume factor `√(-det g)` of a Lorentzian metric. -/
def volM (g : Fin 4 → Fin 4 → ℝ) : ℝ := Real.sqrt (-(Matrix.of g).det)

theorem hasDerivAt_det_line' (A B : Matrix (Fin 4) (Fin 4) ℝ) (hA : IsUnit A.det) :
    HasDerivAt (fun s : ℝ => (A + s • B).det) (A.det * (A⁻¹ * B).trace) 0 := by
  set M := A⁻¹ * B
  set p := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C)).divX.divX
  have hfac : ∀ s : ℝ, (A + s • B).det = A.det * (1 + M.trace * s + p.eval s * s ^ 2) := by
    intro s
    have : A + s • B = A * (1 + s • M) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv A hA, Matrix.one_mul]
    rw [this, Matrix.det_mul, Matrix.det_one_add_smul]
  have hp : HasDerivAt (fun s : ℝ => p.eval s * s ^ 2) 0 0 := by
    have h1 := (Polynomial.hasDerivAt p 0).mul (hasDerivAt_pow 2 (0 : ℝ))
    have h2 : HasDerivAt (fun s : ℝ => p.eval s * s ^ 2) (Polynomial.eval 0
        (Polynomial.derivative p) * 0 ^ 2 + Polynomial.eval 0 p * (((2 : ℕ) : ℝ) * 0 ^ (2 - 1))) 0 :=
      h1
    exact h2.congr_deriv (by simp)
  have h := ((((hasDerivAt_id (0 : ℝ)).const_mul M.trace).const_add 1).add hp).const_mul A.det
  simp only [funext hfac]
  refine h.congr_deriv ?_
  simp

theorem differentiable_det : Differentiable ℝ (fun A : Fin 4 → Fin 4 → ℝ => (Matrix.of A).det) := by
  have : (fun A : Fin 4 → Fin 4 → ℝ => (Matrix.of A).det) =
      fun A => ∑ σ : Equiv.Perm (Fin 4), (Equiv.Perm.sign σ : ℝ) * ∏ i, A (σ i) i := by
    funext A; rw [Matrix.det_apply']; rfl
  rw [this]
  fun_prop

/-- The derivative of the determinant along a curve of matrices (Jacobi's formula). -/
theorem hasDerivAt_det_curve {G : ℝ → Fin 4 → Fin 4 → ℝ} {k : Fin 4 → Fin 4 → ℝ} {t : ℝ}
    (hG : ∀ μ ν, HasDerivAt (fun s => G s μ ν) (k μ ν) t) (hdet : (Matrix.of (G t)).det ≠ 0) :
    HasDerivAt (fun s => (Matrix.of (G s)).det)
      ((Matrix.of (G t)).det * ∑ a, ∑ b, ginvOf (G t) a b * k b a) t := by
  have hGc : HasDerivAt G k t := hasDerivAt_pi.2 fun μ => hasDerivAt_pi.2 fun ν => hG μ ν
  have hd := (differentiable_det (G t)).hasFDerivAt
  have hc := hd.comp_hasDerivAt t hGc
  refine hc.congr_deriv ?_
  -- identify `D det(G)[k]` through the line `G + s k`
  have hline : HasDerivAt (fun s : ℝ => (Matrix.of (G t) + s • Matrix.of k).det)
      ((Matrix.of (G t)).det * ((Matrix.of (G t))⁻¹ * Matrix.of k).trace) 0 :=
    hasDerivAt_det_line' _ _ (isUnit_iff_ne_zero.mpr hdet)
  have hline2 : HasDerivAt (fun s : ℝ => (Matrix.of (G t) + s • Matrix.of k).det)
      (fderiv ℝ (fun A : Fin 4 → Fin 4 → ℝ => (Matrix.of A).det) (G t) k) 0 := by
    have hl : HasDerivAt (fun s : ℝ => G t + s • k) k 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add (G t)
    have := (differentiable_det (G t + (0 : ℝ) • k)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    simp only [zero_smul, add_zero] at this
    exact this
  rw [hline2.unique hline]
  congr 1

/-- **Jacobi's formula for the volume factor**: along a curve of symmetric metrics with
`det g < 0`, `d√(-det g) = ½√(-det g) g^{μν} k_{μν}`. -/
theorem hasDerivAt_volM_curve {G : ℝ → Fin 4 → Fin 4 → ℝ} {k : Fin 4 → Fin 4 → ℝ} {t : ℝ}
    (hG : ∀ μ ν, HasDerivAt (fun s => G s μ ν) (k μ ν) t) (hdet : (Matrix.of (G t)).det < 0)
    (hsym : ∀ μ ν, G t μ ν = G t ν μ) :
    HasDerivAt (fun s => volM (G s)) ((1 / 2) * volM (G t) * trG (ginvOf (G t)) k) t := by
  have hD := hasDerivAt_det_curve hG hdet.ne
  have hpos : 0 < -(Matrix.of (G t)).det := by linarith
  have hs := (Real.hasDerivAt_sqrt hpos.ne').comp t hD.neg
  unfold volM
  refine hs.congr_deriv ?_
  have htr : ∑ a, ∑ b, ginvOf (G t) a b * k b a = trG (ginvOf (G t)) k := by
    unfold trG
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [ginvOf_symm' hsym]
  rw [htr]
  have hsq := Real.sq_sqrt hpos.le
  have hne : Real.sqrt (-(Matrix.of (G t)).det) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  field_simp
  rw [hsq]
  ring

end Volume

/-! ### The Einstein–Hilbert density along a curve of metric jets -/

section VolScal

/-- **The Einstein–Hilbert density along a curve of metric 2-jets.**  If the metric, its first and
second jets move along differentiable curves with derivatives `(k, dk, ddk)` at `t = 0`, the
metric being symmetric with `det g < 0` at `t = 0`, then `√(-det g) R` has derivative
`(½√(-det g) g^{μν}k_{μν}) R + √(-det g) δR`. -/
theorem hasDerivAt_volScal_curve {G : ℝ → Fin 4 → Fin 4 → ℝ} {dG : ℝ → Fin 4 → Fin 4 → Fin 4 → ℝ}
    {ddG : ℝ → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ} {k : Fin 4 → Fin 4 → ℝ}
    {dk : Fin 4 → Fin 4 → Fin 4 → ℝ} {ddk : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hG : ∀ μ ν, HasDerivAt (fun s => G s μ ν) (k μ ν) 0)
    (hdG : ∀ α μ ν, HasDerivAt (fun s => dG s α μ ν) (dk α μ ν) 0)
    (hddG : ∀ β α μ ν, HasDerivAt (fun s => ddG s β α μ ν) (ddk β α μ ν) 0)
    (hdet : (Matrix.of (G 0)).det < 0) (hsym : ∀ μ ν, G 0 μ ν = G 0 ν μ) :
    HasDerivAt (fun s => volM (G s) * scal (ginvOf (G s)) (dG s) (ddG s))
      (((1 / 2) * volM (G 0) * trG (ginvOf (G 0)) k) * scal (ginvOf (G 0)) (dG 0) (ddG 0) +
        volM (G 0) * scalVar (ginvOf (G 0)) (dG 0) (ddG 0) k dk ddk) 0 := by
  set gi0 := ginvOf (G 0)
  have hgi : ∀ a b, HasDerivAt (fun s => ginvOf (G s) a b) (ginvVar gi0 k a b) 0 := by
    intro a b
    have h := JetCurve.hasDerivAt_ginvOf (g := G) (t := 0) (dg := fun _ => k) 0
      (fun μ ν => hG μ ν) hdet.ne a b
    refine h.congr_deriv ?_
    unfold dginv ginvVar
    rfl
  have hΓ : ∀ l a b, HasDerivAt (fun s => chr (ginvOf (G s)) (dG s) l a b)
      (chrVar gi0 (dG 0) k dk l a b) 0 := fun l a b =>
    (hasDerivAt_chr' hgi hdG l a b).congr_deriv rfl
  have hD : ∀ α l a b, HasDerivAt (fun s => dchr (ginvOf (G s)) (dG s) (ddG s) α l a b)
      (dchrVar gi0 (dG 0) (ddG 0) k dk ddk α l a b) 0 := by
    intro α l a b
    refine (hasDerivAt_dchr' hgi hdG hddG α l a b).congr_deriv ?_
    unfold dchrVar dginvVar
    rfl
  have hRic : ∀ μ ν, HasDerivAt (fun s => ricci (ginvOf (G s)) (dG s) (ddG s) μ ν)
      (ricciVar gi0 (dG 0) (ddG 0) k dk ddk μ ν) 0 := fun μ ν =>
    hasDerivAt_ricciJ' hΓ hD μ ν
  have hscal : HasDerivAt (fun s => scal (ginvOf (G s)) (dG s) (ddG s))
      (scalVar gi0 (dG 0) (ddG 0) k dk ddk) 0 :=
    hasDerivAt_trG' hgi hRic
  have hvol := hasDerivAt_volM_curve hG hdet hsym
  exact (hvol.mul hscal).congr_deriv rfl

end VolScal


/-! ### The Palatini flux of smooth fields -/

section Flux

open SobolevOpen (pd)

/-- The first jet field `dF F z α μ ν = ∂_α F_{μν}(z)`. -/
def dF (F : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (z : Fin 4 → ℝ) (α μ ν : Fin 4) : ℝ :=
  pd F α z μ ν

/-- The second jet field `ddF F z β α μ ν = ∂_β∂_α F_{μν}(z)`. -/
def ddF (F : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (z : Fin 4 → ℝ) (β α μ ν : Fin 4) : ℝ :=
  pd (pd F α) β z μ ν

/-- **The Palatini flux** `W^λ = √(-det g) (g^{μν}δΓ^λ_{μν} - g^{λμ}δΓ^ν_{μν})` of a metric field
`g` along a variation field `k`. -/
def palatiniFlux (g k : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (lam : Fin 4) (z : Fin 4 → ℝ) : ℝ :=
  volM (g z) * fluxV (ginvOf (g z)) (chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z)) lam

/-- The derivative of `δg⁻¹ = -g⁻¹ k g⁻¹` along a coordinate direction is `δ(∂g⁻¹)`. -/
theorem ginvVar_deriv_eq (gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (k : Fin 4 → Fin 4 → ℝ) (dk : Fin 4 → Fin 4 → Fin 4 → ℝ) (lam a b : Fin 4) :
    -∑ c, ∑ d, (dginv gi dg lam a c * k c d * gi d b + gi a c * dk lam c d * gi d b +
        gi a c * k c d * dginv gi dg lam d b) = dginvVar gi dg k dk lam a b := by
  unfold dginvVar
  congr 1
  simp only [Finset.sum_add_distrib]
  have e1 : ∑ c, ∑ d, dginv gi dg lam a c * k c d * gi d b =
      ∑ x, ∑ y, gi a x * dg lam x y * ginvVar gi k y b := by
    unfold dginv ginvVar
    simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, Finset.sum_neg_distrib]
    congr 1
    refine EHJetVariation.sum4_reindex _ _
      { toFun := fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)
        invFun := fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)
        left_inv := fun x => rfl
        right_inv := fun x => rfl } fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  have e3 : ∑ c, ∑ d, gi a c * k c d * dginv gi dg lam d b =
      ∑ x, ∑ y, ginvVar gi k a x * dg lam x y * gi y b := by
    unfold dginv ginvVar
    simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, Finset.sum_neg_distrib]
    congr 1
    refine EHJetVariation.sum4_reindex _ _
      { toFun := fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)
        invFun := fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)
        left_inv := fun x => rfl
        right_inv := fun x => rfl } fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  linarith [e1, e3]

theorem hasDerivAt_line' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin 4 → ℝ) → E} {z : Fin 4 → ℝ} (lam : Fin 4) (hf : DifferentiableAt ℝ f z) :
    HasDerivAt (fun s : ℝ => f (z + s • Pi.single lam 1)) (pd f lam z) 0 := by
  have hl : HasDerivAt (fun s : ℝ => z + s • (Pi.single lam 1 : Fin 4 → ℝ)) (Pi.single lam 1) 0 :=
    by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single lam 1 : Fin 4 → ℝ)).const_add z
  have := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact this

theorem hasDerivAt_line_apply {F : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ} {z : Fin 4 → ℝ} (lam : Fin 4)
    (hF : DifferentiableAt ℝ F z) (μ ν : Fin 4) :
    HasDerivAt (fun s : ℝ => F (z + s • Pi.single lam 1) μ ν) (pd F lam z μ ν) 0 :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_line' lam hF) μ) ν

theorem pd_eq_of_line' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin 4 → ℝ) → E} {z : Fin 4 → ℝ} {lam : Fin 4} {D : E} (hf : DifferentiableAt ℝ f z)
    (h : HasDerivAt (fun s : ℝ => f (z + s • Pi.single lam 1)) D 0) : pd f lam z = D :=
  (hasDerivAt_line' lam hf).unique h

theorem contDiff_pd' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin 4 → ℝ) → E} (hF : ContDiff ℝ ∞ F) (α : Fin 4) : ContDiff ℝ ∞ (pd F α) := by
  unfold SobolevOpen.pd
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem pd_apply₂ {F : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ} {z : Fin 4 → ℝ}
    (hF : DifferentiableAt ℝ F z) (lam μ ν : Fin 4) :
    pd (fun y => F y μ ν) lam z = pd F lam z μ ν := by
  refine pd_eq_of_line' ?_ (hasDerivAt_line_apply lam hF μ ν)
  exact differentiableAt_pi.1 (differentiableAt_pi.1 hF μ) ν

theorem dF_symm {g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ} (hg : ∀ y, DifferentiableAt ℝ g y)
    (hgs : ∀ z μ ν, g z μ ν = g z ν μ) (z : Fin 4 → ℝ) (α μ ν : Fin 4) :
    dF g z α μ ν = dF g z α ν μ := by
  unfold dF
  rw [← pd_apply₂ (hg z), ← pd_apply₂ (hg z)]
  exact congrArg (fun F => pd F α z) (funext fun y => hgs y μ ν)

/-- **The divergence of the Palatini flux** of smooth fields: for a smooth symmetric metric field
with `det g < 0` and a smooth variation field `k`,
`Σ_λ ∂_λW^λ = √(-det g)(∂_λV^λ + Γ^a_{aλ}V^λ)` with the jet expressions of
`EHJetVariation.eh_jet_variation` (`V = fluxV g⁻¹ δΓ`, `∂V = fluxDivJ`, `∂δΓ = dchrVar`). -/
theorem sum_pd_flux_eq {g k : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ} (hg : ContDiff ℝ ∞ g)
    (hk : ContDiff ℝ ∞ k) (hgs : ∀ z μ ν, g z μ ν = g z ν μ)
    (hdet : ∀ z, (Matrix.of (g z)).det < 0) (z : Fin 4 → ℝ) :
    ∑ lam, pd (palatiniFlux g k lam) lam z =
      volM (g z) * (fluxDivJ (ginvOf (g z)) (dginv (ginvOf (g z)) (dF g z))
          (chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z))
          (dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z)) +
        ∑ lam, (∑ a, chr (ginvOf (g z)) (dF g z) a a lam) *
          fluxV (ginvOf (g z)) (chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z)) lam) := by
  -- smoothness of the jet fields
  have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => hg.differentiable (by simp) y
  have hkd : ∀ y, DifferentiableAt ℝ k y := fun y => hk.differentiable (by simp) y
  have hpg : ∀ α, ContDiff ℝ ∞ (pd g α) := fun α => contDiff_pd' hg α
  have hpk : ∀ α, ContDiff ℝ ∞ (pd k α) := fun α => contDiff_pd' hk α
  have hpgd : ∀ α y, DifferentiableAt ℝ (pd g α) y := fun α y =>
    (hpg α).differentiable (by simp) y
  have hpkd : ∀ α y, DifferentiableAt ℝ (pd k α) y := fun α y =>
    (hpk α).differentiable (by simp) y
  have hgic : ∀ a b, DifferentiableAt ℝ (fun y => ginvOf (g y) a b) z := fun a b =>
    ((ActualJetSmooth.ContDiffAt.ginvOf hg.contDiffAt (hdet z).ne a b).differentiableAt
      (by simp))
  have hdgc : ∀ α a b, DifferentiableAt ℝ (fun y => dF g y α a b) z := fun α a b =>
    differentiableAt_pi.1 (differentiableAt_pi.1 (hpgd α z) a) b
  have hdkc : ∀ α a b, DifferentiableAt ℝ (fun y => dF k y α a b) z := fun α a b =>
    differentiableAt_pi.1 (differentiableAt_pi.1 (hpkd α z) a) b
  have hkc : ∀ a b, DifferentiableAt ℝ (fun y => k y a b) z := fun a b =>
    differentiableAt_pi.1 (differentiableAt_pi.1 (hkd z) a) b
  have hdetd : DifferentiableAt ℝ (fun y => (Matrix.of (g y)).det) z :=
    (differentiable_det (g z)).comp z (hgd z)
  have hvold : DifferentiableAt ℝ (fun y => volM (g y)) z := by
    unfold volM
    exact hdetd.neg.sqrt (by have := hdet z; intro h; simp only [Pi.neg_apply] at h; linarith)
  have hWd : ∀ lam, DifferentiableAt ℝ (palatiniFlux g k lam) z := by
    intro lam
    unfold palatiniFlux fluxV chrVar chr ginvVar
    fun_prop (disch := assumption)
  -- the line derivative of each flux component
  have hline : ∀ lam, HasDerivAt (fun s : ℝ => palatiniFlux g k lam (z + s • Pi.single lam 1))
      ((1 / 2) * volM (g z) * trG (ginvOf (g z)) (dF g z lam) *
          fluxV (ginvOf (g z)) (chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z)) lam +
        volM (g z) * ((∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam μ ν *
            chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z) lam μ ν +
          ginvOf (g z) μ ν * dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z)
            lam lam μ ν)) -
          ∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam lam μ *
            chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z) ν μ ν +
          ginvOf (g z) lam μ * dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z)
            lam ν μ ν))) 0 := by
    intro lam
    set ℓ : ℝ → Fin 4 → ℝ := fun s => z + s • Pi.single lam 1 with hℓ
    have hℓ0 : ℓ 0 = z := by simp [hℓ]
    -- curves of the jets
    have hG : ∀ μ ν, HasDerivAt (fun s => g (ℓ s) μ ν) (dF g z lam μ ν) 0 := fun μ ν =>
      hasDerivAt_line_apply lam (hgd z) μ ν
    have hK : ∀ μ ν, HasDerivAt (fun s => k (ℓ s) μ ν) (dF k z lam μ ν) 0 := fun μ ν =>
      hasDerivAt_line_apply lam (hkd z) μ ν
    have hdG : ∀ α μ ν, HasDerivAt (fun s => dF g (ℓ s) α μ ν) (ddF g z lam α μ ν) 0 :=
      fun α μ ν => hasDerivAt_line_apply lam (hpgd α z) μ ν
    have hdK : ∀ α μ ν, HasDerivAt (fun s => dF k (ℓ s) α μ ν) (ddF k z lam α μ ν) 0 :=
      fun α μ ν => hasDerivAt_line_apply lam (hpkd α z) μ ν
    have hgi : ∀ a b, HasDerivAt (fun s => ginvOf (g (ℓ s)) a b)
        (dginv (ginvOf (g z)) (dF g z) lam a b) 0 := by
      intro a b
      have h := JetCurve.hasDerivAt_ginvOf (g := fun s => g (ℓ s)) (t := 0) (dg := dF g z) lam
        (fun μ ν => hG μ ν) (by rw [hℓ0]; exact (hdet z).ne) a b
      simpa [hℓ0] using h
    have hvol : HasDerivAt (fun s => volM (g (ℓ s)))
        ((1 / 2) * volM (g z) * trG (ginvOf (g z)) (dF g z lam)) 0 := by
      have h := hasDerivAt_volM_curve (G := fun s => g (ℓ s)) (k := dF g z lam) (t := 0)
        (fun μ ν => hG μ ν) (by rw [hℓ0]; exact hdet z) (by rw [hℓ0]; exact hgs z)
      simpa [hℓ0] using h
    have hgV : ∀ a b, HasDerivAt (fun s => ginvVar (ginvOf (g (ℓ s))) (k (ℓ s)) a b)
        (dginvVar (ginvOf (g z)) (dF g z) (k z) (dF k z) lam a b) 0 := by
      intro a b
      have h := hasDerivAt_ginvVar' hgi hK a b
      rw [hℓ0] at h
      exact h.congr_deriv (ginvVar_deriv_eq _ _ _ _ lam a b)
    have hX : ∀ l μ ν, HasDerivAt
        (fun s => chrVar (ginvOf (g (ℓ s))) (dF g (ℓ s)) (k (ℓ s)) (dF k (ℓ s)) l μ ν)
        (dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z) lam l μ ν) 0 := by
      intro l μ ν
      have h1 := hasDerivAt_chr' hgV hdG l μ ν
      have h2 := hasDerivAt_chr' hgi hdK l μ ν
      rw [hℓ0] at h1 h2
      refine (h1.fun_add h2).congr_deriv ?_
      unfold dchrVar chr
      ring
    have hV : HasDerivAt (fun s => fluxV (ginvOf (g (ℓ s)))
        (chrVar (ginvOf (g (ℓ s))) (dF g (ℓ s)) (k (ℓ s)) (dF k (ℓ s))) lam)
        ((∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam μ ν *
            chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z) lam μ ν +
          ginvOf (g z) μ ν * dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z)
            lam lam μ ν)) -
          ∑ μ, ∑ ν, (dginv (ginvOf (g z)) (dF g z) lam lam μ *
            chrVar (ginvOf (g z)) (dF g z) (k z) (dF k z) ν μ ν +
          ginvOf (g z) lam μ * dchrVar (ginvOf (g z)) (dF g z) (ddF g z) (k z) (dF k z) (ddF k z)
            lam ν μ ν)) 0 := by
      unfold fluxV
      have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
        HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => (hgi μ ν).fun_mul (hX lam μ ν)
      have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
        HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => (hgi lam μ).fun_mul (hX ν μ ν)
      simp only [hℓ0] at h1 h2
      exact h1.fun_sub h2
    have h := hvol.fun_mul hV
    simp only [hℓ0] at h
    exact h
  -- assemble
  have hpd : ∀ lam, pd (palatiniFlux g k lam) lam z = _ := fun lam =>
    pd_eq_of_line' (hWd lam) (hline lam)
  simp only [hpd]
  have htr : ∀ lam, trG (ginvOf (g z)) (dF g z lam) =
      2 * ∑ a, chr (ginvOf (g z)) (dF g z) a a lam := by
    intro lam
    rw [EHJetVariation.trace_chr _ _ (ginvOf_symm' (hgs z)) (dF_symm hgd hgs z)]
    unfold trG
    ring
  simp only [htr]
  unfold fluxDivJ
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun lam _ => ?_
  ring

end Flux


/-! ### Smoothness of the jet expressions along smooth jet fields -/

section FieldSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem contDiff_chr_field {gi : E → n → n → ℝ} {dg : E → n → n → n → ℝ}
    (hgi : ∀ a b, ContDiff ℝ ∞ fun z => gi z a b) (hdg : ∀ α a b, ContDiff ℝ ∞ fun z => dg z α a b)
    (l μ ν : n) : ContDiff ℝ ∞ fun z => chr (gi z) (dg z) l μ ν := by
  unfold chr; fun_prop

theorem contDiff_dginv_field {gi : E → n → n → ℝ} {dg : E → n → n → n → ℝ}
    (hgi : ∀ a b, ContDiff ℝ ∞ fun z => gi z a b) (hdg : ∀ α a b, ContDiff ℝ ∞ fun z => dg z α a b)
    (α l σ : n) : ContDiff ℝ ∞ fun z => dginv (gi z) (dg z) α l σ := by
  unfold dginv; fun_prop

theorem contDiff_dchr_field {gi : E → n → n → ℝ} {dg : E → n → n → n → ℝ}
    {ddg : E → n → n → n → n → ℝ}
    (hgi : ∀ a b, ContDiff ℝ ∞ fun z => gi z a b) (hdg : ∀ α a b, ContDiff ℝ ∞ fun z => dg z α a b)
    (hddg : ∀ β α a b, ContDiff ℝ ∞ fun z => ddg z β α a b) (α l μ ν : n) :
    ContDiff ℝ ∞ fun z => dchr (gi z) (dg z) (ddg z) α l μ ν := by
  have h1 := contDiff_dginv_field hgi hdg
  unfold dchr dchr1 dchr2; fun_prop

theorem contDiff_ricciJ_field {Γ : E → n → n → n → ℝ} {D : E → n → n → n → n → ℝ}
    (hΓ : ∀ l a b, ContDiff ℝ ∞ fun z => Γ z l a b) (hD : ∀ α l a b, ContDiff ℝ ∞ fun z => D z α l a b)
    (μ ν : n) : ContDiff ℝ ∞ fun z => ricciJ (Γ z) (D z) μ ν := by
  unfold ricciJ; fun_prop

theorem contDiff_trG_field {gi X : E → n → n → ℝ} (hgi : ∀ a b, ContDiff ℝ ∞ fun z => gi z a b)
    (hX : ∀ a b, ContDiff ℝ ∞ fun z => X z a b) : ContDiff ℝ ∞ fun z => trG (gi z) (X z) := by
  unfold trG; fun_prop

theorem contDiff_einsteinUp_field {g gi : E → n → n → ℝ} {dg : E → n → n → n → ℝ}
    {ddg : E → n → n → n → n → ℝ} (hg : ∀ a b, ContDiff ℝ ∞ fun z => g z a b)
    (hgi : ∀ a b, ContDiff ℝ ∞ fun z => gi z a b) (hdg : ∀ α a b, ContDiff ℝ ∞ fun z => dg z α a b)
    (hddg : ∀ β α a b, ContDiff ℝ ∞ fun z => ddg z β α a b) (μ ν : n) :
    ContDiff ℝ ∞ fun z => einsteinUp (g z) (gi z) (dg z) (ddg z) μ ν := by
  have hR : ∀ a b, ContDiff ℝ ∞ fun z => ricci (gi z) (dg z) (ddg z) a b := fun a b =>
    contDiff_ricciJ_field (contDiff_chr_field hgi hdg) (contDiff_dchr_field hgi hdg hddg) a b
  have hS : ContDiff ℝ ∞ fun z => trG (gi z) (ricci (gi z) (dg z) (ddg z)) :=
    contDiff_trG_field hgi hR
  have hE : ∀ a b, ContDiff ℝ ∞ fun z => einstein (g z) (gi z) (dg z) (ddg z) a b := by
    intro a b
    unfold einstein
    exact (hR a b).sub ((contDiff_const.mul (hg a b)).mul hS)
  unfold einsteinUp; fun_prop

theorem contDiff_ginvVar_field {gi k : E → n → n → ℝ} (hgi : ∀ a b, ContDiff ℝ ∞ fun z => gi z a b)
    (hk : ∀ a b, ContDiff ℝ ∞ fun z => k z a b) (a b : n) :
    ContDiff ℝ ∞ fun z => ginvVar (gi z) (k z) a b := by
  unfold ginvVar; fun_prop

theorem contDiff_chrVar_field {gi k : E → n → n → ℝ} {dg dk : E → n → n → n → ℝ}
    (hgi : ∀ a b, ContDiff ℝ ∞ fun z => gi z a b) (hdg : ∀ α a b, ContDiff ℝ ∞ fun z => dg z α a b)
    (hk : ∀ a b, ContDiff ℝ ∞ fun z => k z a b) (hdk : ∀ α a b, ContDiff ℝ ∞ fun z => dk z α a b)
    (l μ ν : n) : ContDiff ℝ ∞ fun z => chrVar (gi z) (dg z) (k z) (dk z) l μ ν := by
  unfold chrVar
  exact (contDiff_chr_field (contDiff_ginvVar_field hgi hk) hdg l μ ν).add
    (contDiff_chr_field hgi hdk l μ ν)

theorem contDiff_fluxV_field {gi : E → n → n → ℝ} {X : E → n → n → n → ℝ}
    (hgi : ∀ a b, ContDiff ℝ ∞ fun z => gi z a b) (hX : ∀ l a b, ContDiff ℝ ∞ fun z => X z l a b)
    (lam : n) : ContDiff ℝ ∞ fun z => fluxV (gi z) (X z) lam := by
  unfold fluxV; fun_prop

end FieldSmooth

end

end EHFieldVariation

end RenewalGeometry
