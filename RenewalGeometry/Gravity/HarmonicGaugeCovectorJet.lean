/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.HarmonicSubsidiaryJet
import RenewalGeometry.Gravity.HarmonicDefectForcingExact

/-!
# The harmonic gauge covector of a metric 3-jet and the bridge to `HarmonicDefect`
  (`eq:supp-open-reduced-residual`, `eq:supp-open-exact-subsidiary`; emergent-spacetime
  manuscript)

For a metric 3-jet `J` (`Gravity/ContractedBianchiJet.lean`):

* `gcUp k = G^{ab} Γ^k_{ab}` (the harmonic defect `C^k`), `dgcUp`, `ddgcUp` its product-rule jets
  (with `ddG`, the second jet of the inverse metric);
* `gc b = g_{bk} C^k` (the lower-index gauge covector `c_b(g) = g_{bμ}g^{αβ}Γ^μ_{αβ}` of
  `eq:supp-open-reduced-residual`), `dgc`, `ddgc` its first and second jets, with `ddgc_swap`
  (symmetry of the second jet);
* `metric_forced_subsidiary` — **`eq:supp-open-exact-subsidiary` for the metric's own gauge
  covector**: `□c_b + Ric^l{}_b c_l = -2∇^a r_{ab}`, `r = G(g) - 𝓗(g, c(g))`.

Bridge to `Gravity/HarmonicDefectForcingExact.lean` (array conventions, `ofArrays`):
`chr_ofArrays`, `dchr_ofArrays`, `ricM_ofArrays` (`= HarmonicDefect.ricci`), `einM_ofArrays`
(`= HarmonicDefect.einstein`), `gc_ofArrays` (`= HarmonicDefect.cDown`), `nc_ofArrays`
(`∇_a c_b = HarmonicDefect.nablaDefect`), `hM_ofArrays` (`𝓗 = HarmonicDefect.defectTensor`) and
`resM_ofArrays` (`r = HarmonicDefect.reducedEinstein`).
-/

open Finset Matrix
open scoped BigOperators

namespace RenewalGeometry.ContractedBianchiJet

noncomputable section

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Jet3

variable (J : Jet3 n)

/-- Second jet of the inverse metric, `∂_e∂_f G = -(∂_e G ∂_f g G + G ∂_e∂_f g G + G ∂_f g ∂_e G)`. -/
def ddG (e f : n) : Matrix n n ℝ := -(J.dG e * J.dg f * J.G + J.G * J.ddg e f * J.G + J.G * J.dg f * J.dG e)

/-- The harmonic defect `C^k = G^{ab} Γ^k_{ab}`. -/
def gcUp (k : n) : ℝ := ∑ a, ∑ b, J.G a b * J.chr a k b

/-- `∂_e C^k`. -/
def dgcUp (e k : n) : ℝ := ∑ a, ∑ b, (J.dG e a b * J.chr a k b + J.G a b * J.dchr e a k b)

/-- `∂_e∂_f C^k`. -/
def ddgcUp (e f k : n) : ℝ :=
  ∑ a, ∑ b, (J.ddG e f a b * J.chr a k b + J.dG f a b * J.dchr e a k b +
    J.dG e a b * J.dchr f a k b + J.G a b * J.ddchr e f a k b)

/-- The lower-index gauge covector `c_b = g_{bk} C^k`. -/
def gc (b : n) : ℝ := ∑ k, J.g b k * J.gcUp k

/-- Its jet `∂_e c_b` as a matrix in `(e, b)`. -/
def dgc : Matrix n n ℝ := Matrix.of fun e b => ∑ k, (J.dg e b k * J.gcUp k + J.g b k * J.dgcUp e k)

/-- Its second jet `∂_e∂_f c_b` (matrix in `(f, b)` for each `e`). -/
def ddgc (e : n) : Matrix n n ℝ := Matrix.of fun f b =>
  ∑ k, (J.ddg e f b k * J.gcUp k + J.dg f b k * J.dgcUp e k + J.dg e b k * J.dgcUp f k +
    J.g b k * J.ddgcUp e f k)

theorem ddG_swap {J : Jet3 n} (hv : J.Valid) (e f : n) : J.ddG e f = J.ddG f e := by
  unfold ddG dG
  rw [hv.ddg_comm e f]
  noncomm_ring

theorem ddgcUp_swap {J : Jet3 n} (hv : J.Valid) (e f k : n) : J.ddgcUp e f k = J.ddgcUp f e k := by
  unfold ddgcUp
  rw [ddG_swap hv e f]
  simp only [ddchr_swap hv e f]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem ddgc_swap {J : Jet3 n} (hv : J.Valid) (e f : n) : J.ddgc e f = J.ddgc f e := by
  ext b
  simp only [ddgc, Matrix.of_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hv.ddg_comm e f, ddgcUp_swap hv e f]
  ring

/-- **`eq:supp-open-exact-subsidiary` for the gauge covector of the metric**: for every valid
metric 3-jet, the gauge covector `c = c(g)` and the reduced residual `r = G(g) - 𝓗(g, c(g))`
satisfy `□c_b + Ric^l{}_b c_l = -2 ∇^a r_{ab}`. -/
theorem metric_forced_subsidiary {J : Jet3 n} (hv : J.Valid) (b : n) :
    J.boxC J.gc J.dgc J.ddgc b + J.ricC J.gc b = -2 * J.divRes J.gc J.dgc J.ddgc b :=
  forced_subsidiary hv _ _ _ (fun e a => ddgc_swap hv e a) b

end Jet3

/-! ### Bridge to the array conventions of `HarmonicDefect` -/

/-- The metric 2-jet in the array conventions of `HarmonicDefect` (with zero third jet). -/
def ofArrays (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) : Jet3 n :=
  ⟨Matrix.of g, Matrix.of gi, fun a => Matrix.of (dg a), fun a b => Matrix.of (ddg a b),
    fun _ _ _ => 0⟩

section Bridge

variable (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ)

theorem chr_ofArrays (a l s : n) :
    (ofArrays g gi dg ddg).chr a l s = HarmonicDefect.chr gi dg l a s := by
  simp only [Jet3.chr, Jet3.low, ofArrays, Matrix.mul_apply, Matrix.of_apply, HarmonicDefect.chr,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dG_ofArrays (e a b : n) :
    (ofArrays g gi dg ddg).dG e a b = HarmonicDefect.dginv gi dg e a b := by
  simp only [Jet3.dG, ofArrays, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply,
    HarmonicDefect.dginv, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem dchr_ofArrays (b a l s : n) :
    (ofArrays g gi dg ddg).dchr b a l s = HarmonicDefect.dchr gi dg ddg b l a s := by
  have h1 : (ofArrays g gi dg ddg).dchr b a l s =
      ∑ k, gi l k * (ofArrays g gi dg ddg).dlow b a k s -
        ∑ k, ∑ m, gi l k * dg b k m * (ofArrays g gi dg ddg).chr a m s := by
    simp only [Jet3.dchr, Matrix.mul_apply, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum]
    simp only [ofArrays, Matrix.of_apply, mul_assoc]
  rw [h1]
  simp only [HarmonicDefect.dchr, HarmonicDefect.dchr1, HarmonicDefect.dchr2,
    HarmonicDefect.dginv, Jet3.dlow, Jet3.chr, Jet3.low, ofArrays, Matrix.of_apply,
    Matrix.mul_apply]
  have e2 : ∑ k, gi l k * ((1 / 2 : ℝ) * (ddg b a k s + ddg b s k a - ddg b k a s)) =
      (1 / 2) * ∑ σ, gi l σ * (ddg b a σ s + ddg b s σ a - ddg b σ a s) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have e1 : ∑ k, ∑ m, gi l k * dg b k m *
      ∑ j, gi m j * ((1 / 2 : ℝ) * (dg a j s + dg s j a - dg j a s)) =
      -((1 / 2) * ∑ σ, -(∑ x, ∑ y, gi l x * dg b x y * gi y σ) * (dg a σ s + dg s σ a - dg σ a s)) := by
    calc ∑ k, ∑ m, gi l k * dg b k m *
          ∑ j, gi m j * ((1 / 2 : ℝ) * (dg a j s + dg s j a - dg j a s))
        = ∑ x, ∑ y, ∑ σ, (1 / 2 : ℝ) * (gi l x * dg b x y * gi y σ) *
            (dg a σ s + dg s σ a - dg σ a s) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
            Finset.sum_congr rfl fun σ _ => by ring
      _ = ∑ x, ∑ σ, ∑ y, (1 / 2 : ℝ) * (gi l x * dg b x y * gi y σ) *
            (dg a σ s + dg s σ a - dg σ a s) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ σ, ∑ x, ∑ y, (1 / 2 : ℝ) * (gi l x * dg b x y * gi y σ) *
            (dg a σ s + dg s σ a - dg σ a s) := Finset.sum_comm
      _ = _ := by
          simp only [neg_mul, Finset.sum_neg_distrib, mul_neg, neg_neg, Finset.mul_sum,
            Finset.sum_mul]
          exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun x _ =>
            Finset.sum_congr rfl fun y _ => by ring
  rw [e2, e1]
  ring

end Bridge


/-- Validity of a metric 2-jet in array form (the hypotheses of `HarmonicDefect`). -/
structure ArraysValid (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) :
    Prop where
  hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0
  hg : ∀ a b, g a b = g b a
  hgi : ∀ a b, gi a b = gi b a
  hdg : ∀ α a b, dg α a b = dg α b a
  hs1 : ∀ α β μ ν, ddg α β μ ν = ddg β α μ ν
  hs2 : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ

theorem ArraysValid.valid {g gi : n → n → ℝ} {dg : n → n → n → ℝ} {ddg : n → n → n → n → ℝ}
    (h : ArraysValid g gi dg ddg) : (ofArrays g gi dg ddg).Valid where
  gG := by
    ext a c
    simpa [ofArrays, Matrix.mul_apply, Matrix.one_apply] using h.hinv a c
  g_symm := by ext a b; simp [ofArrays, h.hg a b]
  G_symm := by ext a b; simp [ofArrays, h.hgi a b]
  dg_symm := fun α => by ext a b; simp [ofArrays, h.hdg α a b]
  ddg_symm := fun α β => by ext a b; simp [ofArrays, h.hs2 α β a b]
  ddg_comm := fun α β => by ext a b; simp [ofArrays, h.hs1 α β a b]
  dddg_symm := fun _ _ _ => by simp [ofArrays]
  dddg_comm1 := fun _ _ _ => rfl
  dddg_comm2 := fun _ _ _ => rfl

namespace Jet3

theorem dchr_apply_comm {J : Jet3 n} (hv : J.Valid) (b a l s : n) :
    J.dchr b a l s = J.dchr b s l a := by
  simp only [dchr, Matrix.mul_apply, Matrix.sub_apply, dlow, Matrix.of_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [hv.ddg_apply b k a s, hv.ddg_apply b s k a]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun m _ => by rw [chr_apply_comm hv a m s]

end Jet3

section Bridge2

variable {g gi : n → n → ℝ} {dg : n → n → n → ℝ} {ddg : n → n → n → n → ℝ}

theorem ricM_ofArrays (h : ArraysValid g gi dg ddg) (s b : n) :
    (ofArrays g gi dg ddg).ricM s b = HarmonicDefect.ricci gi dg ddg s b := by
  have hv := h.valid
  set J := ofArrays g gi dg ddg
  have hchr : ∀ a l s, HarmonicDefect.chr gi dg l a s = J.chr a l s :=
    fun a l s => (chr_ofArrays g gi dg ddg a l s).symm
  have hdchr : ∀ b a l s, HarmonicDefect.dchr gi dg ddg b l a s = J.dchr b a l s :=
    fun b a l s => (dchr_ofArrays g gi dg ddg b a l s).symm
  simp only [HarmonicDefect.ricci, HarmonicDefect.ricciJ, hchr, hdchr, Jet3.ricM, Jet3.riem,
    Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have t1 : ∑ x, J.dchr x b x s = ∑ α, J.dchr α s α b :=
    Finset.sum_congr rfl fun x _ => Jet3.dchr_apply_comm hv x b x s
  have t2 : ∑ x, J.dchr b x x s = ∑ α, J.dchr b s α α :=
    Finset.sum_congr rfl fun x _ => Jet3.dchr_apply_comm hv b x x s
  have t3 : ∑ x, ∑ m, J.chr x x m * J.chr b m s = ∑ α, ∑ l, J.chr α α l * J.chr s l b :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun m _ => by
      rw [Jet3.chr_apply_comm hv b m s]
  have t4 : ∑ x, ∑ m, J.chr b x m * J.chr x m s = ∑ α, ∑ l, J.chr b α l * J.chr s l α :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun m _ => by
      rw [Jet3.chr_apply_comm hv x m s]
  rw [t1, t2, t3, t4]

theorem einM_ofArrays (h : ArraysValid g gi dg ddg) (s b : n) :
    (ofArrays g gi dg ddg).einM s b = HarmonicDefect.einstein g gi dg ddg s b := by
  have hr : ∀ s b, (ofArrays g gi dg ddg).ricM s b = HarmonicDefect.ricci gi dg ddg s b :=
    ricM_ofArrays h
  simp only [Jet3.einM, Jet3.scal, ← Jet3.sum_sum_mul_eq_trace, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, hr, HarmonicDefect.einstein, HarmonicDefect.trG]
  simp only [ofArrays, Matrix.of_apply]
  ring

theorem gcUp_ofArrays (k : n) :
    (ofArrays g gi dg ddg).gcUp k = HarmonicDefect.cUp gi (HarmonicDefect.chr gi dg) k := by
  simp only [Jet3.gcUp, HarmonicDefect.cUp, chr_ofArrays]
  rfl

theorem gc_ofArrays (b : n) :
    (ofArrays g gi dg ddg).gc b = HarmonicDefect.cDown g gi (HarmonicDefect.chr gi dg) b := by
  simp only [Jet3.gc, HarmonicDefect.cDown, gcUp_ofArrays]
  rfl

theorem dgcUp_ofArrays (e k : n) :
    (ofArrays g gi dg ddg).dgcUp e k = HarmonicDefect.dcUp gi (HarmonicDefect.dginv gi dg)
      (HarmonicDefect.chr gi dg) (HarmonicDefect.dchr gi dg ddg) e k := by
  simp only [Jet3.dgcUp, HarmonicDefect.dcUp, chr_ofArrays, dchr_ofArrays, dG_ofArrays]
  rfl

theorem nc_ofArrays (a b : n) :
    (ofArrays g gi dg ddg).nc (ofArrays g gi dg ddg).gc (ofArrays g gi dg ddg).dgc a b =
      HarmonicDefect.nablaDefect g gi dg ddg a b := by
  simp only [Jet3.nc, Jet3.dgc, Jet3.chrC, Matrix.sub_apply, Matrix.of_apply, gc_ofArrays,
    gcUp_ofArrays, dgcUp_ofArrays, chr_ofArrays, HarmonicDefect.nablaDefect, HarmonicDefect.nablaC]
  simp only [ofArrays, Matrix.of_apply]

theorem trN_ofArrays :
    (ofArrays g gi dg ddg).trN (ofArrays g gi dg ddg).gc (ofArrays g gi dg ddg).dgc =
      HarmonicDefect.divDefect g gi dg ddg := by
  rw [Jet3.trN, ← Jet3.sum_sum_mul_eq_trace]
  simp only [nc_ofArrays, HarmonicDefect.divDefect, HarmonicDefect.trG]
  simp only [ofArrays, Matrix.of_apply]

theorem hM_ofArrays (a b : n) :
    (ofArrays g gi dg ddg).hM (ofArrays g gi dg ddg).gc (ofArrays g gi dg ddg).dgc a b =
      HarmonicDefect.defectTensor g gi dg ddg a b := by
  simp only [Jet3.hM, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul, nc_ofArrays, trN_ofArrays, HarmonicDefect.defectTensor,
    HarmonicDefect.symDefect]
  simp only [ofArrays, Matrix.of_apply]
  ring

/-- The reduced residual of the jet is `HarmonicDefect.reducedEinstein`
(`r = G - 𝓗 = Ĝ`, `eq:supp-open-reduced-residual`). -/
theorem resM_ofArrays (h : ArraysValid g gi dg ddg) (a b : n) :
    (ofArrays g gi dg ddg).resM (ofArrays g gi dg ddg).gc (ofArrays g gi dg ddg).dgc a b =
      HarmonicDefect.reducedEinstein g gi dg ddg a b := by
  rw [HarmonicDefect.reducedEinstein_eq, Jet3.resM, Matrix.sub_apply, einM_ofArrays h,
    hM_ofArrays]

end Bridge2

end

end RenewalGeometry.ContractedBianchiJet
