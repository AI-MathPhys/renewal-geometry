/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.RegulatedStandardModelAction

/-!
# Exact colour-vacuum restriction of the active Standard-Model action

Exact formalization for `thm:SMYM-colour-restriction` (CY.1–CY.2).

A concrete finite field record (`SMField`: colour links, weak links, Higgs, fermion
packet) carries the four local densities of the regulated Standard-Model action of
`thm:SM-active-SM-II`.  The colour-vacuum embedding `ι₃` (CY.1) sets the weak links
to `I₂`, the Higgs to the frozen vacuum `v_H·h₀`, and the fermions to zero.  Then:

* `edge_embed`, `site_embed`, `fermion_embed`: the covariant Higgs difference, the
  radial potential at its vacuum, and the fermion bilinear vanish **exactly**;
* `face_embed`: the weak plaquette curvature of identity links vanishes, so the
  invariant gauge metric leaves exactly the `𝔰𝔲(3)` plaquette term;
* `colour_restriction` (CY.2): `𝒮_SM ∘ ι₃ = ½⟨F³, ⋆₂F³⟩_{g₃}` — the restricted
  action is the local `SU(3)` lattice action on the same regulator;
* `colourAction_gaugeInvariant`: the colour Ward identity is inherited — the
  restricted action is invariant under vertex-local unitary colour gauge maps
  (Hilbert–Schmidt norm invariance of the conjugated curvature, proved via trace
  cyclicity).
-/

open Matrix

namespace NCG
namespace ColourRestriction

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

/-- The finite active Standard-Model field record: colour links, weak links, Higgs
doublet, fermion packet. -/
structure SMField (V E : Type*) where
  linkC : E → Matrix (Fin 3) (Fin 3) ℂ
  linkW : E → Matrix (Fin 2) (Fin 2) ℂ
  higgs : V → Fin 2 → ℂ
  psi : V → Fin 4 → ℂ

/-- Squared Hilbert–Schmidt norm as the real part of `tr(AᴴA)`. -/
noncomputable def hsNormSq {m : Type*} [Fintype m] (A : Matrix m m ℂ) : ℝ :=
  (Matrix.trace (Aᴴ * A)).re

theorem hsNormSq_zero {m : Type*} [Fintype m] : hsNormSq (0 : Matrix m m ℂ) = 0 := by
  rw [hsNormSq, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]

/-- Two-sided unitary invariance of the Hilbert–Schmidt norm. -/
theorem hsNormSq_unitary_conj {m : Type*} [Fintype m] [DecidableEq m]
    {g h : Matrix m m ℂ} (hg : g ∈ Matrix.unitaryGroup m ℂ)
    (hh : h ∈ Matrix.unitaryGroup m ℂ) (A : Matrix m m ℂ) :
    hsNormSq (g * A * hᴴ) = hsNormSq A := by
  rw [hsNormSq, hsNormSq]
  congr 1
  have hgU : gᴴ * g = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hg
  have hhU : hᴴ * h = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hh
  have hexp : (g * A * hᴴ)ᴴ * (g * A * hᴴ) = h * (Aᴴ * (A * hᴴ)) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc gᴴ g, hgU, Matrix.one_mul]
  rw [hexp, Matrix.trace_mul_comm, Matrix.mul_assoc Aᴴ (A * hᴴ) h,
    Matrix.mul_assoc A hᴴ h, hhU, Matrix.mul_one]

/-- Plaquette data: the four boundary edges and the two boundary corners. -/
structure Plaquette (V E : Type*) where
  e₁ : E
  e₂ : E
  e₃ : E
  e₄ : E
  src : V
  tgt : V

variable (s t : E → V)

/-- Endpoint compatibility of a plaquette with the edge incidence maps: the two
paths `e₁·e₂` and `e₄·e₃` both run from `src` to `tgt`. -/
def Compatible (P : Plaquette V E) : Prop :=
  s P.e₁ = P.src ∧ s P.e₄ = P.src ∧ t P.e₂ = P.tgt ∧ t P.e₃ = P.tgt
    ∧ t P.e₁ = s P.e₂ ∧ t P.e₄ = s P.e₃

/-- The colour plaquette curvature `F³(p) = U₁U₂ - U₄U₃` (difference of the two
path-ordered transports). -/
def curvC (P : Plaquette V E) (Φ : SMField V E) : Matrix (Fin 3) (Fin 3) ℂ :=
  Φ.linkC P.e₁ * Φ.linkC P.e₂ - Φ.linkC P.e₄ * Φ.linkC P.e₃

/-- The weak plaquette curvature `F²(p)`. -/
def curvW (P : Plaquette V E) (Φ : SMField V E) : Matrix (Fin 2) (Fin 2) ℂ :=
  Φ.linkW P.e₁ * Φ.linkW P.e₂ - Φ.linkW P.e₄ * Φ.linkW P.e₃

/-- The gauge-coupling face density: `g₃‖F³‖² + g₂‖F²‖²`. -/
noncomputable def faceDensity (g₃ g₂ : ℝ) (plaq : F → Plaquette V E)
    (p : F) (Φ : SMField V E) : ℝ :=
  g₃ * hsNormSq (curvC (plaq p) Φ) + g₂ * hsNormSq (curvW (plaq p) Φ)

/-- The covariant-Higgs edge density `‖U⁽²⁾_e H_{s e} - H_{t e}‖²`. -/
noncomputable def edgeDensity (e : E) (Φ : SMField V E) : ℝ :=
  ∑ i, Complex.normSq ((Φ.linkW e *ᵥ Φ.higgs (s e)) i - Φ.higgs (t e) i)

/-- The radial Higgs site density `λ(‖H_v‖² - v_H²)²`. -/
noncomputable def siteDensity (lam vH : ℝ) (v : V) (Φ : SMField V E) : ℝ :=
  lam * ((∑ i, Complex.normSq (Φ.higgs v i)) - vH ^ 2) ^ 2

/-- The fermion bilinear site density (any finite real Dirac/Yukawa pairing). -/
noncomputable def fermionDensity (Y : Matrix (Fin 4) (Fin 4) ℂ) (v : V)
    (Φ : SMField V E) : ℝ :=
  (∑ a, ∑ b, starRingEnd ℂ (Φ.psi v a) * Y a b * Φ.psi v b).re

/-- **CY.1, the colour-vacuum embedding**: colour links kept, weak links `I₂`, the
Higgs frozen at `v_H·h₀`, fermions zero. -/
def embed (vH : ℝ) (h₀ : Fin 2 → ℂ) (U : E → Matrix (Fin 3) (Fin 3) ℂ) :
    SMField V E where
  linkC := U
  linkW := fun _ => 1
  higgs := fun _ => fun i => (vH : ℂ) * h₀ i
  psi := fun _ => 0

omit [Fintype V] [Fintype E] in
theorem edge_embed (vH : ℝ) (h₀ : Fin 2 → ℂ) (U : E → Matrix (Fin 3) (Fin 3) ℂ)
    (e : E) : edgeDensity s t e (embed vH h₀ U) = 0 := by
  rw [edgeDensity]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [embed]
  simp [Matrix.one_mulVec]

omit [Fintype V] [Fintype E] in
theorem site_embed (lam vH : ℝ) (h₀ : Fin 2 → ℂ)
    (hnorm : ∑ i, Complex.normSq (h₀ i) = 1)
    (U : E → Matrix (Fin 3) (Fin 3) ℂ) (v : V) :
    siteDensity lam vH v (embed vH h₀ U) = 0 := by
  rw [siteDensity, embed]
  have h1 : (∑ i, Complex.normSq ((vH : ℂ) * h₀ i)) = vH ^ 2 := by
    calc ∑ i, Complex.normSq ((vH : ℂ) * h₀ i)
        = ∑ i, vH ^ 2 * Complex.normSq (h₀ i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.normSq_mul, Complex.normSq_ofReal]
          ring
      _ = vH ^ 2 := by rw [← Finset.mul_sum, hnorm, mul_one]
  rw [h1]
  ring

omit [Fintype V] [Fintype E] in
theorem fermion_embed (Y : Matrix (Fin 4) (Fin 4) ℂ) (vH : ℝ) (h₀ : Fin 2 → ℂ)
    (U : E → Matrix (Fin 3) (Fin 3) ℂ) (v : V) :
    fermionDensity Y v (embed vH h₀ U) = 0 := by
  rw [fermionDensity, embed]
  simp

omit [Fintype V] [Fintype E] [Fintype F] in
theorem face_embed (g₃ g₂ : ℝ) (plaq : F → Plaquette V E) (vH : ℝ) (h₀ : Fin 2 → ℂ)
    (U : E → Matrix (Fin 3) (Fin 3) ℂ) (p : F) :
    faceDensity g₃ g₂ plaq p (embed vH h₀ U)
      = g₃ * hsNormSq (curvC (plaq p) (embed vH h₀ U)) := by
  rw [faceDensity]
  have hW : curvW (plaq p) (embed (E := E) (V := V) vH h₀ U) = 0 := by
    rw [curvW, embed]
    simp
  rw [hW, hsNormSq_zero, mul_zero, add_zero]

/-- **CY.2, the exact colour-vacuum restriction**: the active Standard-Model action
composed with the colour-vacuum embedding is exactly the local `SU(3)` lattice
action `½⟨F³, ⋆₂F³⟩_{g₃}` on the same regulator. -/
theorem colour_restriction (g₃ g₂ lam vH : ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (plaq : F → Plaquette V E) (h₀ : Fin 2 → ℂ)
    (hnorm : ∑ i, Complex.normSq (h₀ i) = 1)
    (U : E → Matrix (Fin 3) (Fin 3) ℂ) :
    regulatedStandardModelAction (faceDensity g₃ g₂ plaq) (edgeDensity s t)
      (siteDensity lam vH) (fermionDensity Y) (embed vH h₀ U)
      = (2 : ℝ)⁻¹ * ∑ p, g₃ * hsNormSq (curvC (plaq p) (embed vH h₀ U)) := by
  rw [regulatedStandardModelAction]
  rw [Finset.sum_congr rfl fun p _ => face_embed g₃ g₂ plaq vH h₀ U p,
    Finset.sum_congr rfl fun e _ => edge_embed s t vH h₀ U e,
    Finset.sum_congr rfl fun v _ => site_embed lam vH h₀ hnorm U v,
    Finset.sum_congr rfl fun v _ => fermion_embed Y vH h₀ U v]
  simp

/-- Vertex-local colour gauge action on the colour links. -/
def gaugeActC (g : V → Matrix (Fin 3) (Fin 3) ℂ)
    (U : E → Matrix (Fin 3) (Fin 3) ℂ) : E → Matrix (Fin 3) (Fin 3) ℂ :=
  fun e => g (s e) * U e * (g (t e))ᴴ

omit [Fintype V] [Fintype E] in
/-- The colour curvature transforms by two-sided conjugation on a compatible
plaquette. -/
theorem curvC_gauge (P : Plaquette V E) (hP : Compatible s t P)
    (g : V → Matrix (Fin 3) (Fin 3) ℂ)
    (hg : ∀ v, g v ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (vH : ℝ) (h₀ : Fin 2 → ℂ) (U : E → Matrix (Fin 3) (Fin 3) ℂ) :
    curvC P (embed vH h₀ (gaugeActC s t g U))
      = g P.src * curvC P (embed vH h₀ U) * (g P.tgt)ᴴ := by
  obtain ⟨h1, h4, h2, h3, h12, h43⟩ := hP
  simp only [curvC, embed, gaugeActC]
  rw [h1, h4, h2, h3, h12, h43]
  have hcancel : ∀ v : V, (g v)ᴴ * g v = 1 := by
    intro v
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp (hg v)
  rw [Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((g (s P.e₂))ᴴ) (g (s P.e₂)), hcancel, Matrix.one_mul]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((g (s P.e₃))ᴴ) (g (s P.e₃)), hcancel, Matrix.one_mul]

omit [Fintype V] [Fintype E] in
/-- **The inherited colour Ward identity**: the restricted `SU(3)` action is exactly
invariant under vertex-local unitary colour gauge maps. -/
theorem colourAction_gaugeInvariant (g₃ : ℝ) (plaq : F → Plaquette V E)
    (hcomp : ∀ p, Compatible s t (plaq p))
    (g : V → Matrix (Fin 3) (Fin 3) ℂ)
    (hg : ∀ v, g v ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (vH : ℝ) (h₀ : Fin 2 → ℂ) (U : E → Matrix (Fin 3) (Fin 3) ℂ) :
    (2 : ℝ)⁻¹ * ∑ p, g₃ * hsNormSq (curvC (plaq p) (embed vH h₀ (gaugeActC s t g U)))
      = (2 : ℝ)⁻¹ * ∑ p, g₃ * hsNormSq (curvC (plaq p) (embed vH h₀ U)) := by
  refine congrArg (fun x => (2 : ℝ)⁻¹ * x) (Finset.sum_congr rfl fun p _ => ?_)
  rw [curvC_gauge s t (plaq p) (hcomp p) g hg vH h₀ U,
    hsNormSq_unitary_conj (hg (plaq p).src) (hg (plaq p).tgt)]

/-- **Bundle for `thm:SMYM-colour-restriction`**: CY.1 embedding, the exact CY.2
restriction identity, and the inherited colour Ward identity. -/
theorem smym_colour_restriction (g₃ g₂ lam vH : ℝ) (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (plaq : F → Plaquette V E) (hcomp : ∀ p, Compatible s t (plaq p))
    (h₀ : Fin 2 → ℂ) (hnorm : ∑ i, Complex.normSq (h₀ i) = 1) :
    (∀ U : E → Matrix (Fin 3) (Fin 3) ℂ,
      regulatedStandardModelAction (faceDensity g₃ g₂ plaq) (edgeDensity s t)
        (siteDensity lam vH) (fermionDensity Y) (embed vH h₀ U)
        = (2 : ℝ)⁻¹ * ∑ p, g₃ * hsNormSq (curvC (plaq p) (embed vH h₀ U))) ∧
    (∀ (g : V → Matrix (Fin 3) (Fin 3) ℂ),
      (∀ v, g v ∈ Matrix.unitaryGroup (Fin 3) ℂ) →
      ∀ U : E → Matrix (Fin 3) (Fin 3) ℂ,
      (2 : ℝ)⁻¹ * ∑ p, g₃ * hsNormSq (curvC (plaq p) (embed vH h₀ (gaugeActC s t g U)))
        = (2 : ℝ)⁻¹ * ∑ p, g₃ * hsNormSq (curvC (plaq p) (embed vH h₀ U))) :=
  ⟨fun U => colour_restriction s t g₃ g₂ lam vH Y plaq h₀ hnorm U,
   fun g hg U => colourAction_gaugeInvariant s t g₃ plaq hcomp g hg vH h₀ U⟩

end ColourRestriction
end NCG
