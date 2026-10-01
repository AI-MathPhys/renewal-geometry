/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.HarmonicGaugeCovectorJet

/-!
# Chain rule for the formal metric jets
  (infrastructure for `lem:supp-open-subsidiary` and the vacuum clause of
  `thm:supp-open-einstein`; emergent-spacetime manuscript)

The formal derivatives of `Gravity/ContractedBianchiJet.lean`, `HarmonicSubsidiaryJet.lean` and
`HarmonicGaugeCovectorJet.lean` (`dlow`, `dchr`, `driem`, `dricM`, `dscal`, `deinM`, `dgcUp`,
`ddgcUp`, `dgc`, `ddgc`, `dnc`, `dtrN`, `dhM`, `dresM`) are the actual derivatives along every
differentiable path of jets whose own derivatives are the next jets.

`MHasDeriv A A' s` is entrywise differentiability of a matrix-valued function.  A path of metric
jets `J : ℝ → Jet3 n` is **consistent in direction `e` at `s`** (`Jet3.PathDeriv`) if
`∂ₛg = dg e`, `∂ₛG = dG e = -G (dg e) G`, `∂ₛ(dg a) = ddg e a`, `∂ₛ(ddg a b) = dddg e a b` at `s`.
For such paths:

* `PathDeriv.chr`, `.dchr`, `.riem`, `.ricM`, `.scal`, `.einM` — Christoffel symbols, their first
  jets, Riemann, Ricci, scalar curvature and Einstein tensor differentiate to the formal jets;
* `PathDeriv.gcUp`, `.dgcUp`, `.gc`, `.dgc` — the gauge covector and its first jet differentiate to
  `dgc`, `ddgc`;
* `PathDeriv.hM`, `.resM` — the harmonic-defect tensor `𝓗(g, c(g))` and the reduced residual
  `r = G - 𝓗` differentiate to `dhM`, `dresM` (with `c = gc`, `∂c = dgc`, `∂∂c = ddgc`);
  `PathDeriv.dresM_eq_zero` — a residual vanishing near `s` has vanishing formal derivative;
* `subsidiary_of_residual_zero` — where `r` and its formal derivatives vanish, the gauge
  covector obeys the homogeneous subsidiary equation `□c + Ric·c = 0`.
-/

open Finset Matrix
open scoped BigOperators

namespace RenewalGeometry.ContractedBianchiJet

noncomputable section

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise derivative of a matrix-valued function. -/
def MHasDeriv (A : ℝ → Matrix n n ℝ) (A' : Matrix n n ℝ) (s : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) s

namespace MHasDeriv

variable {A B : ℝ → Matrix n n ℝ} {A' B' : Matrix n n ℝ} {s : ℝ}

theorem add (hA : MHasDeriv A A' s) (hB : MHasDeriv B B' s) :
    MHasDeriv (fun s => A s + B s) (A' + B') s := fun i j => (hA i j).add (hB i j)

theorem sub (hA : MHasDeriv A A' s) (hB : MHasDeriv B B' s) :
    MHasDeriv (fun s => A s - B s) (A' - B') s := fun i j => (hA i j).sub (hB i j)

theorem neg (hA : MHasDeriv A A' s) : MHasDeriv (fun s => -A s) (-A') s :=
  fun i j => (hA i j).neg

theorem mul (hA : MHasDeriv A A' s) (hB : MHasDeriv B B' s) :
    MHasDeriv (fun s => A s * B s) (A' * B s + A s * B') s := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => ((hA i k).fun_mul (hB k j)).congr_deriv (by ring)

theorem transpose (hA : MHasDeriv A A' s) : MHasDeriv (fun s => (A s)ᵀ) A'ᵀ s :=
  fun i j => hA j i

theorem smul {c : ℝ → ℝ} {c' : ℝ} (hc : HasDerivAt c c' s) (hA : MHasDeriv A A' s) :
    MHasDeriv (fun s => c s • A s) (c' • A s + c s • A') s := by
  intro i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  exact (hc.fun_mul (hA i j))

theorem congr {A'' : Matrix n n ℝ} (hA : MHasDeriv A A' s) (h : A' = A'') : MHasDeriv A A'' s :=
  h ▸ hA

theorem trace (hA : MHasDeriv A A' s) : HasDerivAt (fun s => Matrix.trace (A s)) (Matrix.trace A') s := by
  simp only [Matrix.trace, Matrix.diag]
  exact HasDerivAt.fun_sum fun i _ => hA i i

end MHasDeriv

namespace Jet3

/-- A path of metric 3-jets is consistent in direction `e` at `s`: the derivatives of
`g, G, ∂g, ∂²g` are `∂_e g`, `∂_e G = -G ∂_e g G`, `∂_e ∂g`, `∂_e ∂²g` of the jet at `s`. -/
structure PathDeriv (J : ℝ → Jet3 n) (e : n) (s : ℝ) : Prop where
  g : MHasDeriv (fun s => (J s).g) ((J s).dg e) s
  G : MHasDeriv (fun s => (J s).G) ((J s).dG e) s
  dg : ∀ a, MHasDeriv (fun s => (J s).dg a) ((J s).ddg e a) s
  ddg : ∀ a b, MHasDeriv (fun s => (J s).ddg a b) ((J s).dddg e a b) s

variable {J : ℝ → Jet3 n} {e : n} {s : ℝ}

namespace PathDeriv

theorem low (h : PathDeriv J e s) (a : n) :
    MHasDeriv (fun s => (J s).low a) ((J s).dlow e a) s := by
  intro k l
  simp only [Jet3.low, Jet3.dlow, Matrix.of_apply]
  exact (((h.dg a k l).add (h.dg l k a)).sub (h.dg k a l)).const_mul _

theorem dlow (h : PathDeriv J e s) (b a : n) :
    MHasDeriv (fun s => (J s).dlow b a) ((J s).ddlow e b a) s := by
  intro k l
  simp only [Jet3.dlow, Jet3.ddlow, Matrix.of_apply]
  exact (((h.ddg b a k l).add (h.ddg b l k a)).sub (h.ddg b k a l)).const_mul _

theorem chr (h : PathDeriv J e s) (a : n) :
    MHasDeriv (fun s => (J s).chr a) ((J s).dchr e a) s := by
  refine (h.G.mul (h.low a)).congr ?_
  simp only [Jet3.dchr, Jet3.dG, Jet3.chr]
  noncomm_ring

theorem dG (h : PathDeriv J e s) (f : n) :
    MHasDeriv (fun s => (J s).dG f) ((J s).ddG e f) s := by
  refine ((h.G.mul (h.dg f)).mul h.G).neg.congr ?_
  simp only [Jet3.ddG]
  noncomm_ring

theorem dchr (h : PathDeriv J e s) (b a : n) :
    MHasDeriv (fun s => (J s).dchr b a) ((J s).ddchr e b a) s := by
  refine (h.G.mul ((h.dlow b a).sub ((h.dg b).mul (h.chr a)))).congr ?_
  simp only [Jet3.ddchr, Jet3.dchr, Jet3.dG, Jet3.chr]
  noncomm_ring

theorem riem (h : PathDeriv J e s) (a b : n) :
    MHasDeriv (fun s => (J s).riem a b) ((J s).driem e a b) s := by
  refine ((((h.dchr a b).sub (h.dchr b a)).add ((h.chr a).mul (h.chr b))).sub
    ((h.chr b).mul (h.chr a))).congr ?_
  simp only [Jet3.driem]
  noncomm_ring

theorem ricM (h : PathDeriv J e s) : MHasDeriv (fun s => (J s).ricM) ((J s).dricM e) s := by
  intro k l
  simp only [Jet3.ricM, Jet3.dricM, Matrix.of_apply]
  exact HasDerivAt.fun_sum fun m _ => h.riem m l m k

theorem scal (h : PathDeriv J e s) : HasDerivAt (fun s => (J s).scal) ((J s).dscal e) s := by
  have := ((h.G.mul h.ricM.transpose)).trace
  simp only [Matrix.trace_add] at this
  exact this

theorem einM (h : PathDeriv J e s) : MHasDeriv (fun s => (J s).einM) ((J s).deinM e) s := by
  refine (h.ricM.sub (MHasDeriv.smul (h.scal.const_mul (1 / 2 : ℝ)) h.g)).congr ?_
  simp only [Jet3.deinM]
  abel

theorem gcUp (h : PathDeriv J e s) (k : n) :
    HasDerivAt (fun s => (J s).gcUp k) ((J s).dgcUp e k) s := by
  simp only [Jet3.gcUp, Jet3.dgcUp]
  exact HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ =>
    (h.G a b).fun_mul (h.chr a k b)

theorem dgcUp (h : PathDeriv J e s) (f k : n) :
    HasDerivAt (fun s => (J s).dgcUp f k) ((J s).ddgcUp e f k) s := by
  simp only [Jet3.dgcUp, Jet3.ddgcUp]
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
  refine (((h.dG f a b).fun_mul (h.chr a k b)).add ((h.G a b).fun_mul (h.dchr f a k b))).congr_deriv ?_
  ring

theorem gc (h : PathDeriv J e s) (b : n) :
    HasDerivAt (fun s => (J s).gc b) ((J s).dgc e b) s := by
  simp only [Jet3.gc, Jet3.dgc, Matrix.of_apply]
  exact HasDerivAt.fun_sum fun k _ => (h.g b k).fun_mul (h.gcUp k)

theorem dgc (h : PathDeriv J e s) : MHasDeriv (fun s => (J s).dgc) ((J s).ddgc e) s := by
  intro f b
  simp only [Jet3.dgc, Jet3.ddgc, Matrix.of_apply]
  refine HasDerivAt.fun_sum fun k _ => ?_
  refine (((h.dg f b k).fun_mul (h.gcUp k)).add ((h.g b k).fun_mul (h.dgcUp f k))).congr_deriv ?_
  ring

theorem nc (h : PathDeriv J e s) :
    MHasDeriv (fun s => (J s).nc (J s).gc (J s).dgc)
      ((J s).dnc (J s).gc (J s).dgc (J s).ddgc e) s := by
  intro a b
  simp only [Jet3.nc, Jet3.dnc, Jet3.chrC, Matrix.sub_apply, Matrix.of_apply]
  exact (h.dgc a b).sub (HasDerivAt.fun_sum fun l _ => (h.chr a l b).fun_mul (h.gc l))

theorem trN (h : PathDeriv J e s) :
    HasDerivAt (fun s => (J s).trN (J s).gc (J s).dgc)
      ((J s).dtrN (J s).gc (J s).dgc (J s).ddgc e) s := by
  have := (h.G.mul h.nc.transpose).trace
  simp only [Matrix.trace_add] at this
  exact this

theorem hM (h : PathDeriv J e s) :
    MHasDeriv (fun s => (J s).hM (J s).gc (J s).dgc)
      ((J s).dhM (J s).gc (J s).dgc (J s).ddgc e) s := by
  have h1 : MHasDeriv (fun s => (1 / 2 : ℝ) • ((J s).nc (J s).gc (J s).dgc +
      ((J s).nc (J s).gc (J s).dgc)ᵀ))
      ((0 : ℝ) • ((J s).nc (J s).gc (J s).dgc + ((J s).nc (J s).gc (J s).dgc)ᵀ) +
        (1 / 2 : ℝ) • ((J s).dnc (J s).gc (J s).dgc (J s).ddgc e +
          ((J s).dnc (J s).gc (J s).dgc (J s).ddgc e)ᵀ)) s :=
    MHasDeriv.smul (hasDerivAt_const _ _) (h.nc.add h.nc.transpose)
  refine (h1.sub (MHasDeriv.smul (h.trN.const_mul (1 / 2 : ℝ)) h.g)).congr ?_
  simp only [Jet3.dhM, zero_smul, zero_add]
  abel

theorem resM (h : PathDeriv J e s) :
    MHasDeriv (fun s => (J s).resM (J s).gc (J s).dgc)
      ((J s).dresM (J s).gc (J s).dgc (J s).ddgc e) s :=
  h.einM.sub h.hM

/-- If the reduced residual vanishes along the path near `s`, its formal derivative vanishes. -/
theorem dresM_eq_zero (h : PathDeriv J e s)
    (hz : ∀ᶠ s' in nhds s, (J s').resM (J s').gc (J s').dgc = 0) :
    (J s).dresM (J s).gc (J s).dgc (J s).ddgc e = 0 := by
  ext a b
  have h1 := h.resM a b
  have h2 : HasDerivAt (fun s' => (J s').resM (J s').gc (J s').dgc a b) 0 s :=
    (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq
      (hz.mono fun s' hs' => by simp only [hs', Matrix.zero_apply])
  exact h1.unique h2

end PathDeriv

/-- **Homogeneous subsidiary equation**: at a jet where the reduced residual and its formal
derivatives vanish (e.g. at every point of an exact solution of the reduced equation, by
`PathDeriv.dresM_eq_zero`), the gauge covector `c = c(g)` satisfies `□c_b + Ric^l{}_b c_l = 0`. -/
theorem subsidiary_of_residual_zero {J : Jet3 n} (hv : J.Valid)
    (hr : J.resM J.gc J.dgc = 0) (hdr : ∀ e, J.dresM J.gc J.dgc J.ddgc e = 0) (b : n) :
    J.boxC J.gc J.dgc J.ddgc b + J.ricC J.gc b = 0 := by
  rw [metric_forced_subsidiary hv b]
  have : J.divRes J.gc J.dgc J.ddgc b = 0 := by
    unfold divRes
    simp [hr, hdr]
  rw [this, mul_zero]

end Jet3

/-- Non-vacuity: the constant path at the flat jet is consistent in every direction. -/
example (e : n) (s : ℝ) :
    Jet3.PathDeriv (fun _ => (⟨1, 1, fun _ => 0, fun _ _ => 0, fun _ _ _ => 0⟩ : Jet3 n)) e s where
  g := fun i j => by simpa using hasDerivAt_const s ((1 : Matrix n n ℝ) i j)
  G := fun i j => by simpa [Jet3.dG] using hasDerivAt_const s ((1 : Matrix n n ℝ) i j)
  dg := fun _ i j => by simpa using hasDerivAt_const s (0 : ℝ)
  ddg := fun _ _ i j => by simpa using hasDerivAt_const s (0 : ℝ)

end

end RenewalGeometry.ContractedBianchiJet
