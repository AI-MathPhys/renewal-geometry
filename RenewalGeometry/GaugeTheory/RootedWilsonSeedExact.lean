/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.LatticeHolonomyGaugeCovariance
import RenewalGeometry.GaugeTheory.DeterminantSemisimpleSplitExact

/-!
# Rooted Wilson words: endpoint cancellation and central lift changes
  (`prop:rooted-gauge-certificate`, `prop:native-determinant-split`, Einstein–SM action closure)

On an oriented graph `(V, E, src, tgt)` with links `U : E → G` (`U_e` transports the fibre at
`src e` to the fibre at `tgt e`; gauge action `U_e ↦ g_{tgt e} U_e g_{src e}⁻¹`, as in
`LatticeHolonomyGaugeCovariance.lean`), fix walks `w v` from every vertex `v` to a root `o`
(the tree paths of a rooted spanning tree; any family of walks works).  Then:

* `rootedPath w U v = hol_{w v}(U)` is `C_v(U)`, and `C_v(g·U) = g_o C_v(U) g_v⁻¹`
  (`rootedPath_gaugeLinks`, endpoint cancellation along the tree);
* `rootedWord w U e = C_{tgt e} U_e C_{src e}⁻¹` is the root-based closed word
  `W^𝔗_μ(x)` of `eq:rooted-Wilson-seed`; it transforms by the constant conjugation
  `W(g·U) = g_o W(U) g_o⁻¹` (`rootedWord_gaugeLinks`), so every class function of it is gauge
  invariant (`classFunction_rootedWord_gaugeLinks`);
* `rootedWord_eq_gaugeLinks`: the tree representative is an exact gauge transform of the
  original links (gauge `C`); `rootedWord_eq_one_of_tree_edge`: it is trivial on tree edges;
* `rootedWord_central_gauge`: a gauge whose root value is central leaves every rooted word
  unchanged.

Applied to `prop:native-determinant-split`: changing the site lifts `t ↦ t + 2πk` changes
`V` by the central `G_ss` site gauge `z₆^k`, which leaves every rooted word of `V`
(`splitLinks_rootedWord_lift_change`) and every plaquette of `V`
(`splitLinks_plaq_lift_change`) unchanged — so the rooted certificate
`‖h⁻¹ Log W‖₄ + ‖𝔽_h‖₂` of `eq:rooted-Wilson-certificate`, and any function of the rooted
words and plaquettes, is unchanged, with no use of the logarithm chart.
-/

namespace RenewalGeometry

namespace RootedWilson

universe u v

section Graph

variable {V : Type u} {E : Type v} {src tgt : E → V} {G : Type*} [Group G]

/-- `C_v(U)`: the holonomy along the fixed walk from `v` to the root. -/
def rootedPath {o : V} (w : ∀ v, LatticeWalk src tgt v o) (U : E → G) (v : V) : G :=
  (w v).holonomy U

/-- The root-based closed word `W_e = C_{tgt e} U_e C_{src e}⁻¹` (`eq:rooted-Wilson-seed`). -/
def rootedWord {o : V} (w : ∀ v, LatticeWalk src tgt v o) (U : E → G) (e : E) : G :=
  rootedPath w U (tgt e) * U e * (rootedPath w U (src e))⁻¹

/-- **Endpoint cancellation along the tree**: `C_v(g·U) = g_o C_v(U) g_v⁻¹`. -/
theorem rootedPath_gaugeLinks {o : V} (w : ∀ v, LatticeWalk src tgt v o) (g : V → G)
    (U : E → G) (v : V) :
    rootedPath w (gaugeLinks src tgt g U) v = g o * rootedPath w U v * (g v)⁻¹ :=
  (w v).holonomy_gaugeLinks g U

/-- **Gauge covariance of the rooted word**: `W(g·U) = g_o W(U) g_o⁻¹`. -/
theorem rootedWord_gaugeLinks {o : V} (w : ∀ v, LatticeWalk src tgt v o) (g : V → G)
    (U : E → G) (e : E) :
    rootedWord w (gaugeLinks src tgt g U) e = g o * rootedWord w U e * (g o)⁻¹ := by
  simp only [rootedWord, rootedPath_gaugeLinks, gaugeLinks_apply]
  group

/-- Every class function of a rooted word is site-gauge invariant. -/
theorem classFunction_rootedWord_gaugeLinks {o : V} {X : Type*} (f : G → X)
    (hf : ∀ g P, f (g * P * g⁻¹) = f P) (w : ∀ v, LatticeWalk src tgt v o) (g : V → G)
    (U : E → G) (e : E) : f (rootedWord w (gaugeLinks src tgt g U) e) = f (rootedWord w U e) := by
  rw [rootedWord_gaugeLinks, hf]

/-- A gauge whose root value is central leaves every rooted word unchanged. -/
theorem rootedWord_central_gauge {o : V} (w : ∀ v, LatticeWalk src tgt v o) (g : V → G)
    (hg : ∀ y : G, g o * y = y * g o) (U : E → G) (e : E) :
    rootedWord w (gaugeLinks src tgt g U) e = rootedWord w U e := by
  rw [rootedWord_gaugeLinks, hg, mul_assoc, mul_inv_cancel, mul_one]

/-- **The tree representative is an exact gauge transform**: `W = C · U`. -/
theorem rootedWord_eq_gaugeLinks {o : V} (w : ∀ v, LatticeWalk src tgt v o) (U : E → G) :
    rootedWord w U = gaugeLinks src tgt (rootedPath w U) U := by
  funext e
  rfl

/-- On a tree edge (`C_{src e} = C_{tgt e} U_e`) the rooted word is trivial. -/
theorem rootedWord_eq_one_of_tree_edge {o : V} (w : ∀ v, LatticeWalk src tgt v o)
    (U : E → G) (e : E) (htree : rootedPath w U (src e) = rootedPath w U (tgt e) * U e) :
    rootedWord w U e = 1 := by
  rw [rootedWord, htree, mul_inv_cancel]

end Graph

/-! ### The central lift change of `prop:native-determinant-split` -/

section Split

open DeterminantSplit SMDescentYukawa

variable {X D : Type*} (shift : X → D → X)

/-- The oriented lattice graph: the link `U_μ(x)` transports from `x + e_μ` to `x`. -/
def latticeSrc (e : X × D) : X := shift e.1 e.2

/-- The target of the link `(x, μ)` is `x`. -/
def latticeTgt (e : X × D) : X := e.1

theorem gaugeTr_eq_gaugeLinks (g : X → SMGaugeGroup) (U : X → D → SMGaugeGroup) (x : X)
    (μ : D) :
    gaugeTr shift g U x μ =
      gaugeLinks (latticeSrc shift) latticeTgt g (fun e => U e.1 e.2) (x, μ) := rfl

theorem zSix_zpow_comm (k : ℤ) (y : SMGaugeGroup) : zSix ^ k * y = y * zSix ^ k := by
  rw [zSix, ← centralElem_zsmul, centralElem_comm]

/-- **Lift change and rooted words**: replacing the lifts `t` by `t + 2πk` leaves every rooted
word of `V = e^{-haZ_c} U^{e^{tZ_c}}` unchanged. -/
theorem splitLinks_rootedWord_lift_change (h : ℝ) (t : X → ℝ) (k : X → ℤ) (a : X → D → ℝ)
    (U : X → D → SMGaugeGroup) {o : X}
    (w : ∀ v, LatticeWalk (latticeSrc shift) latticeTgt v o) (e : X × D) :
    rootedWord w (fun e => splitLinks shift h (fun x => t x + 2 * Real.pi * k x) a U e.1 e.2) e =
      rootedWord w (fun e => splitLinks shift h t a U e.1 e.2) e := by
  have hV : (fun e : X × D => splitLinks shift h (fun x => t x + 2 * Real.pi * k x) a U e.1 e.2) =
      gaugeLinks (latticeSrc shift) latticeTgt (fun x => zSix ^ k x)
        (fun e => splitLinks shift h t a U e.1 e.2) := by
    funext e
    rw [splitLinks_lift_change]
    rfl
  rw [hV]
  exact rootedWord_central_gauge (G := SMGaugeGroup) w (fun x => zSix ^ k x)
    (fun y => zSix_zpow_comm (k o) y) (fun e => splitLinks shift h t a U e.1 e.2) e

/-- **Lift change and plaquettes**: on a lattice with commuting shifts, the plaquettes of `V`
are unchanged by the lift change `t ↦ t + 2πk`. -/
theorem splitLinks_plaq_lift_change (hcomm : ∀ x μ ν, shift (shift x μ) ν = shift (shift x ν) μ)
    (h : ℝ) (t : X → ℝ) (k : X → ℤ) (a : X → D → ℝ) (U : X → D → SMGaugeGroup) (x : X)
    (μ ν : D) :
    plaq shift (splitLinks shift h (fun x => t x + 2 * Real.pi * k x) a U) x μ ν =
      plaq shift (splitLinks shift h t a U) x μ ν := by
  have hV : splitLinks shift h (fun x => t x + 2 * Real.pi * k x) a U =
      gaugeTr shift (fun x => zSix ^ k x) (splitLinks shift h t a U) := by
    funext x μ
    exact splitLinks_lift_change shift h t k a U x μ
  rw [hV]
  have hz : ∀ x, zSix ^ k x = centralElem ((k x : ℝ) * (2 * Real.pi)) := by
    intro x; rw [zSix, centralElem_zsmul]
  simp only [plaq, gaugeTr, hz, central_conj]
  rw [plaq_central, hcomm x μ ν]
  have h0 : (k x : ℝ) * (2 * Real.pi) - (k (shift x μ) : ℝ) * (2 * Real.pi) +
      ((k (shift x μ) : ℝ) * (2 * Real.pi) - (k (shift (shift x ν) μ) : ℝ) * (2 * Real.pi)) -
      ((k (shift x ν) : ℝ) * (2 * Real.pi) - (k (shift (shift x ν) μ) : ℝ) * (2 * Real.pi)) -
      ((k x : ℝ) * (2 * Real.pi) - (k (shift x ν) : ℝ) * (2 * Real.pi)) = 0 := by ring
  rw [h0, centralElem_zero, one_mul]

end Split

end RootedWilson

end RenewalGeometry
