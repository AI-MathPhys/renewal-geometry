/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.FiniteGraphSpectralUniversalityFibreExact

/-!
# Finite spectral universality

Paper `predictive_spectral_geometry`, label `thm:supp-spectral-universality`
(with the dimension clause of `cor:supp-fibre-dimension`).

For a real oriented incidence matrix `B` of a connected graph with positive
conductances `c`, the same-spectralization fibre
`GraphSpectralFibre (complexify B) c` of stationary currents is

* the intersection of the real cycle space `ker B` with the open conductance
  box `{ j | ∀ e, |j e| < c e }` (`graphSpectralFibre_eq_inter`);
* a star-shaped neighbourhood of `0` inside the cycle space, whose real
  dimension is the first Betti number `|E| - |V| + 1`
  (`finrank_realCycleSpace`);
* injectively parametrizing the directed flux data `c ± j`, hence the renewal
  generators, while every member has the same symmetrized flux `c`
  (`forwardFlux_injective`, `symmetricFlux_eq_conductance`).

When `b₁ > 0` the fibre contains a nonzero current `j`, and the entropy
production separates the corresponding stationary dynamics from the reversible
member `j = 0` while both have the same spectral image
(`finite_spectral_universality`).

The paper's "dynamically inequivalent" is formalised as: distinct directed
flux (hence generator) data with identical symmetric conductances, together
with the entropy-production witness against the reversible member.  Pairwise
non-isomorphism of two *arbitrary* nonzero currents up to vertex relabelling
is not what the paper's proof establishes and is not claimed here.
-/

open Matrix Finset

namespace RenewalGeometry
namespace FiniteSpectralUniversality

open FiniteGraphSpectralUniversalityFibre

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The complexification of a real incidence matrix. -/
def complexify (B : Matrix V E ℝ) : Matrix V E ℂ := B.map Complex.ofRealHom

/-- The real cycle space `ker B`. -/
def realCycleSpace (B : Matrix V E ℝ) : Submodule ℝ (E → ℝ) :=
  LinearMap.ker B.mulVecLin

/-- The open conductance box `{ j | ∀ e, |j e| < c e }`. -/
def conductanceBox (c : E → ℝ) : Set (E → ℝ) := {j | ∀ e, |j e| < c e}

omit [Fintype V] in
theorem complexify_mulVec_re (B : Matrix V E ℝ) (z : E → ℂ) (v : V) :
    ((complexify B *ᵥ z) v).re = (B *ᵥ fun e => (z e).re) v := by
  simp [complexify, Matrix.mulVec, dotProduct, Complex.re_sum]

omit [Fintype V] in
theorem complexify_mulVec_im (B : Matrix V E ℝ) (z : E → ℂ) (v : V) :
    ((complexify B *ᵥ z) v).im = (B *ᵥ fun e => (z e).im) v := by
  simp [complexify, Matrix.mulVec, dotProduct, Complex.im_sum]

omit [Fintype V] in
/-- The complex kernel condition is the pair of real kernel conditions on real
and imaginary parts. -/
theorem complexify_mulVec_eq_zero_iff (B : Matrix V E ℝ) (z : E → ℂ) :
    complexify B *ᵥ z = 0 ↔
      (B *ᵥ fun e => (z e).re) = 0 ∧ (B *ᵥ fun e => (z e).im) = 0 := by
  constructor
  · intro h
    constructor
    · funext v
      have := congrArg Complex.re (congrFun h v)
      rw [complexify_mulVec_re] at this
      simpa using this
    · funext v
      have := congrArg Complex.im (congrFun h v)
      rw [complexify_mulVec_im] at this
      simpa using this
  · rintro ⟨hre, him⟩
    funext v
    apply Complex.ext
    · rw [complexify_mulVec_re, hre]; simp
    · rw [complexify_mulVec_im, him]; simp

omit [Fintype V] in
/-- A real current is stationary for the complexified incidence exactly when it
lies in the real cycle space. -/
theorem isStationaryCurrent_complexify_iff (B : Matrix V E ℝ) (j : E → ℝ) :
    IsStationaryCurrent (complexify B) j ↔ j ∈ realCycleSpace B := by
  unfold IsStationaryCurrent realCycleSpace
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, complexify_mulVec_eq_zero_iff]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rw [show (fun _ : E => (0 : ℝ)) = 0 from rfl, Matrix.mulVec_zero]

/-- `eq:supp-realization-fibre` in real form: the fibre is the cycle space cut
by the open conductance box. -/
theorem graphSpectralFibre_eq_inter (B : Matrix V E ℝ) (c : E → ℝ) :
    GraphSpectralFibre (complexify B) c =
      (realCycleSpace B : Set (E → ℝ)) ∩ conductanceBox c := by
  ext j
  simp only [GraphSpectralFibre, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe,
    conductanceBox, isStationaryCurrent_complexify_iff]

/-- The conductance box is open. -/
theorem isOpen_conductanceBox (c : E → ℝ) : IsOpen (conductanceBox c) := by
  have hset : conductanceBox c = ⋂ e, {j : E → ℝ | |j e| < c e} := by
    ext j
    simp [conductanceBox]
  rw [hset]
  exact isOpen_iInter_of_finite fun e =>
    isOpen_lt ((continuous_apply e).abs) continuous_const

/-- The fibre is star-shaped around the reversible member: every cycle-space
direction stays inside the fibre for all sufficiently small amplitudes. -/
theorem exists_smul_mem_fibre (B : Matrix V E ℝ) (c : E → ℝ) (hc : ∀ e, 0 < c e)
    {j : E → ℝ} (hj : j ∈ realCycleSpace B) :
    ∃ t : ℝ, 0 < t ∧ ∀ s : ℝ, |s| ≤ t → s • j ∈ GraphSpectralFibre (complexify B) c := by
  set M : ℝ := ∑ e, |j e| / c e with hM
  have hMnonneg : 0 ≤ M := Finset.sum_nonneg fun e _ => div_nonneg (abs_nonneg _) (hc e).le
  refine ⟨1 / (1 + M), by positivity, fun s hs => ?_⟩
  rw [graphSpectralFibre_eq_inter]
  refine ⟨Submodule.smul_mem _ s hj, fun e => ?_⟩
  have hle : |j e| / c e ≤ M := by
    rw [hM]
    exact Finset.single_le_sum (fun e _ => div_nonneg (abs_nonneg _) (hc e).le)
      (Finset.mem_univ e)
  have hlt : |j e| < (1 + M) * c e := by
    have := (div_le_iff₀ (hc e)).mp hle
    linarith [hc e]
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  calc |s| * |j e| ≤ (1 / (1 + M)) * |j e| :=
        mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    _ < (1 / (1 + M)) * ((1 + M) * c e) :=
        mul_lt_mul_of_pos_left hlt (by positivity)
    _ = c e := by field_simp

omit [Fintype E] in
/-- Distinct currents give distinct forward flux data, hence distinct
stationary renewal generators `k = (c + j)/m`. -/
theorem forwardFlux_injective (c : E → ℝ) :
    Function.Injective (forwardFlux c) := by
  intro j₁ j₂ h
  funext e
  have := congrFun h e
  simp only [forwardFlux] at this
  linarith

omit [Fintype V] in
/-- A nonzero complex kernel vector has a nonzero real or imaginary part in the
real cycle space. -/
theorem exists_ne_zero_mem_realCycleSpace_of_complex (B : Matrix V E ℝ)
    {z : E → ℂ} (hz : complexify B *ᵥ z = 0) (hne : z ≠ 0) :
    ∃ j : E → ℝ, j ∈ realCycleSpace B ∧ j ≠ 0 := by
  obtain ⟨hre, him⟩ := (complexify_mulVec_eq_zero_iff B z).mp hz
  by_cases hr : (fun e => (z e).re) = 0
  · refine ⟨fun e => (z e).im, ?_, ?_⟩
    · exact LinearMap.mem_ker.mpr (by rw [Matrix.mulVecLin_apply]; exact him)
    · intro hi
      apply hne
      funext e
      apply Complex.ext
      · simpa using congrFun hr e
      · simpa using congrFun hi e
  · exact ⟨fun e => (z e).re,
      LinearMap.mem_ker.mpr (by rw [Matrix.mulVecLin_apply]; exact hre), hr⟩

/-- A positive complex cycle-space dimension yields a nonzero real cycle. -/
theorem exists_ne_zero_mem_realCycleSpace (B : Matrix V E ℝ)
    (hpos : 0 < Module.finrank ℂ (LinearMap.ker (complexify B).mulVecLin)) :
    ∃ j : E → ℝ, j ∈ realCycleSpace B ∧ j ≠ 0 := by
  obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hzker : complexify B *ᵥ (z : E → ℂ) = 0 := by
    have := z.2
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
  have hzne : (z : E → ℂ) ≠ 0 := fun h => hz (Subtype.ext h)
  exact exists_ne_zero_mem_realCycleSpace_of_complex B hzker hzne

section Dimension

omit [Fintype V] in
/-- Real and imaginary parts of a complex cycle are real cycles. -/
theorem re_mem_realCycleSpace (B : Matrix V E ℝ) (z : LinearMap.ker (complexify B).mulVecLin) :
    (fun e => ((z : E → ℂ) e).re) ∈ realCycleSpace B := by
  have hz : complexify B *ᵥ (z : E → ℂ) = 0 := by
    have := z.2
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
  exact LinearMap.mem_ker.mpr
    (by rw [Matrix.mulVecLin_apply]; exact ((complexify_mulVec_eq_zero_iff B _).mp hz).1)

omit [Fintype V] in
theorem im_mem_realCycleSpace (B : Matrix V E ℝ) (z : LinearMap.ker (complexify B).mulVecLin) :
    (fun e => ((z : E → ℂ) e).im) ∈ realCycleSpace B := by
  have hz : complexify B *ᵥ (z : E → ℂ) = 0 := by
    have := z.2
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
  exact LinearMap.mem_ker.mpr
    (by rw [Matrix.mulVecLin_apply]; exact ((complexify_mulVec_eq_zero_iff B _).mp hz).2)

omit [Fintype V] in
theorem combine_mem_complexKernel (B : Matrix V E ℝ) (u v : realCycleSpace B) :
    (fun e => ((u : E → ℝ) e : ℂ) + ((v : E → ℝ) e : ℂ) * Complex.I) ∈
      LinearMap.ker (complexify B).mulVecLin := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, complexify_mulVec_eq_zero_iff]
  have hu : B *ᵥ (u : E → ℝ) = 0 := by
    have := LinearMap.mem_ker.mp (show (u : E → ℝ) ∈ LinearMap.ker B.mulVecLin from u.2)
    rwa [Matrix.mulVecLin_apply] at this
  have hv : B *ᵥ (v : E → ℝ) = 0 := by
    have := LinearMap.mem_ker.mp (show (v : E → ℝ) ∈ LinearMap.ker B.mulVecLin from v.2)
    rwa [Matrix.mulVecLin_apply] at this
  constructor
  · simpa using hu
  · simpa using hv

/-- **`cor:supp-fibre-dimension` (real form).**  The real cycle space of a
connected incidence matrix has dimension `|E| - |V| + 1 = b₁`. -/
theorem finrank_realCycleSpace (B : Matrix V E ℝ) [Nonempty V]
    (hconnected : IsConnectedIncidence (complexify B)) :
    Module.finrank ℝ (realCycleSpace B) = Fintype.card E + 1 - Fintype.card V := by
  classical
  set kerC := LinearMap.ker (complexify B).mulVecLin with hkerC
  let _ : Module ℝ kerC := Module.complexToReal kerC
  let toC : realCycleSpace B × realCycleSpace B →ₗ[ℝ] kerC :=
    { toFun := fun p => ⟨fun e => ((p.1 : E → ℝ) e : ℂ) + ((p.2 : E → ℝ) e : ℂ) * Complex.I,
        combine_mem_complexKernel B p.1 p.2⟩
      map_add' := by
        intro p q
        apply Subtype.ext
        funext e
        simp only [Submodule.coe_add, Pi.add_apply, Prod.fst_add, Prod.snd_add]
        push_cast
        ring
      map_smul' := by
        intro r p
        apply Subtype.ext
        funext e
        change ((r • (p.1 : E → ℝ)) e : ℂ) + ((r • (p.2 : E → ℝ)) e : ℂ) * Complex.I =
          ((r : ℂ) • (fun e => ((p.1 : E → ℝ) e : ℂ) + ((p.2 : E → ℝ) e : ℂ) * Complex.I)) e
        simp only [Pi.smul_apply, smul_eq_mul]
        push_cast
        ring }
  let toR : kerC →ₗ[ℝ] realCycleSpace B × realCycleSpace B :=
    { toFun := fun z => (⟨fun e => ((z : E → ℂ) e).re, re_mem_realCycleSpace B z⟩,
        ⟨fun e => ((z : E → ℂ) e).im, im_mem_realCycleSpace B z⟩)
      map_add' := by
        intro z w
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> funext e <;> simp
      map_smul' := by
        intro r z
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> funext e
        · change ((((r : ℂ) • (z : E → ℂ)) e).re) = r * ((z : E → ℂ) e).re
          simp
        · change ((((r : ℂ) • (z : E → ℂ)) e).im) = r * ((z : E → ℂ) e).im
          simp }
  let equiv : (realCycleSpace B × realCycleSpace B) ≃ₗ[ℝ] kerC :=
    { toC with
      invFun := toR
      left_inv := by
        intro p
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> funext e <;> simp [toC, toR]
      right_inv := by
        intro z
        apply Subtype.ext
        funext e
        simp [toC, toR] }
  have h1 : Module.finrank ℝ (realCycleSpace B × realCycleSpace B) = Module.finrank ℝ kerC :=
    LinearEquiv.finrank_eq equiv
  rw [Module.finrank_prod, finrank_real_of_complex kerC, hkerC,
    cycleKernel_finrank hconnected] at h1
  omega

end Dimension

/-- **Theorem `thm:supp-spectral-universality`.**  Let `B` be the real
oriented incidence matrix of a connected graph with `b₁ = |E| - |V| + 1 > 0`
and let `c > 0` be conductances.  Then:

1. there is a nonzero stationary current `j` in the same-spectralization
   fibre, whose directed flux data (hence renewal generator) and whose entropy
   production differ from those of the reversible member `0`, although both
   members have the same symmetrized flux `c`, i.e. the same metric spectral
   triple;
2. the fibre is the open box `{|j| < c}` inside the real cycle space, a
   star-shaped neighbourhood of `0` whose dimension is `b₁`, and its members
   have pairwise distinct generators. -/
theorem finite_spectral_universality (B : Matrix V E ℝ) [Nonempty V]
    (hconnected : IsConnectedIncidence (complexify B)) (c : E → ℝ) (hc : ∀ e, 0 < c e)
    (hb₁ : Fintype.card V < Fintype.card E + 1) :
    (∃ j ∈ GraphSpectralFibre (complexify B) c, j ≠ 0 ∧
        forwardFlux c j ≠ forwardFlux c 0 ∧
        entropyProduction c j ≠ entropyProduction c 0 ∧
        ∀ e, (forwardFlux c j e + reverseFlux c j e) / 2 = c e) ∧
      GraphSpectralFibre (complexify B) c =
        (realCycleSpace B : Set (E → ℝ)) ∩ conductanceBox c ∧
      IsOpen (conductanceBox c) ∧
      (0 : E → ℝ) ∈ GraphSpectralFibre (complexify B) c ∧
      (∀ j ∈ realCycleSpace B, ∃ t : ℝ, 0 < t ∧
        ∀ s : ℝ, |s| ≤ t → s • j ∈ GraphSpectralFibre (complexify B) c) ∧
      Module.finrank ℝ (realCycleSpace B) = Fintype.card E + 1 - Fintype.card V ∧
      Function.Injective (forwardFlux c) := by
  refine ⟨?_, graphSpectralFibre_eq_inter B c, isOpen_conductanceBox c,
    zero_mem_fibre _ c hc, fun j hj => exists_smul_mem_fibre B c hc hj,
    finrank_realCycleSpace B hconnected, forwardFlux_injective c⟩
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker (complexify B).mulVecLin) := by
    rw [cycleKernel_finrank hconnected]
    omega
  obtain ⟨j₀, hj₀, hne₀⟩ := exists_ne_zero_mem_realCycleSpace B hpos
  obtain ⟨t, ht, hmem⟩ := exists_smul_mem_fibre B c hc hj₀
  refine ⟨t • j₀, hmem t (by rw [abs_of_pos ht]), ?_, ?_, ?_, fun e => symmetricFlux_eq_conductance c _ e⟩
  · exact smul_ne_zero ht.ne' hne₀
  · intro h
    exact smul_ne_zero ht.ne' hne₀ (forwardFlux_injective c h)
  · exact entropyProduction_ne_equilibrium c _ hc (hmem t (by rw [abs_of_pos ht])).2
      (smul_ne_zero ht.ne' hne₀)

end FiniteSpectralUniversality
end RenewalGeometry
