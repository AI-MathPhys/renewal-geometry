/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HankelFeedbackOperatorExact

/-!
# The exhaustive finite-resolution profile of a loaded memory

Machinery for `cor:finite-resolution-memory`.  For a Hodge-dominated loaded transient packet with
spectral splitting `1 = P_R + Q_R` (`HankelFeedback.Splitting`), the loaded memory
`ℌ = ℌ_{≤R} + ℌ_{>R}` splits into the finite-rank low-mode part and a high-energy tail of norm
`≤ b c/(2R)`.  Relative to a declared carrier `D` (the already-declared connection and matter
fields) the finite low-mode range `L = ran ℌ_{≤R}` decomposes orthogonally as

`L = (L ⊓ D) ⊕ (innovations)`, `innovations = (L ⊓ D)ᗮ ⊓ L`,

so every memory output is **declared low modes ⊕ canonical finite field innovations ⊕ a vanishing
high-energy tail** (`memory_profile`).  A low mode belongs to the declared carrier exactly when
its residual against `D` vanishes (`low_mode_declared_iff`), and the counting law bounds the
number of innovations by the rank envelope (`finrank_innovations_le`).  Under the counting law,
the transient floor, the coupling bounds and cutoff compactness, no fixed-resolution growing-rank
or noncompact-memory obstruction can persist (`no_amorphous_branch`).
-/

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace NCG
namespace HankelFeedback

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [MeasurableSpace H₀] [BorelSpace H₀] [SecondCountableTopology H₀]

variable (W : Splitting H₀)

/-- The low-mode range `L = ran ℌ_{≤R}`. -/
noncomputable def lowRange : Submodule ℝ (Lp H₀ 2 halfLine) :=
  LinearMap.range (hankel W.lowScreen).toLinearMap

/-- The low-mode range is finite-dimensional when the carrier is. -/
theorem finiteDimensional_lowRange [FiniteDimensional ℝ H₀] :
    FiniteDimensional ℝ (lowRange W) := by
  have hsub : lowRange W ≤
      LinearMap.range ((obsL W.lowScreen).toLinearMap.comp
        (LinearMap.range W.P.toLinearMap).subtype) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨⟨ctrl W.lowScreen f, ctrl_mem_range W.lowScreen W.commP W.Pidem f⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hsub

/-- The declared part of the low-mode range relative to a declared carrier `D`. -/
noncomputable def declaredPart (D : Submodule ℝ (Lp H₀ 2 halfLine)) :
    Submodule ℝ (Lp H₀ 2 halfLine) :=
  lowRange W ⊓ D

/-- The canonical finite field innovations: the orthogonal complement of the declared part inside
the low-mode range. -/
noncomputable def innovations (D : Submodule ℝ (Lp H₀ 2 halfLine)) :
    Submodule ℝ (Lp H₀ 2 halfLine) :=
  (declaredPart W D)ᗮ ⊓ lowRange W

theorem declaredPart_le (D : Submodule ℝ (Lp H₀ 2 halfLine)) : declaredPart W D ≤ lowRange W :=
  inf_le_left

theorem innovations_le (D : Submodule ℝ (Lp H₀ 2 halfLine)) : innovations W D ≤ lowRange W :=
  inf_le_right

/-- The declared part and the innovations are orthogonal (trivial intersection). -/
theorem declaredPart_inf_innovations (D : Submodule ℝ (Lp H₀ 2 halfLine)) :
    declaredPart W D ⊓ innovations W D = ⊥ := by
  refine le_antisymm ?_ bot_le
  calc declaredPart W D ⊓ innovations W D ≤ declaredPart W D ⊓ (declaredPart W D)ᗮ :=
        inf_le_inf_left _ inf_le_left
    _ = ⊥ := Submodule.inf_orthogonal_eq_bot _

/-- **Three-way profile of a low mode**: `v = d + i` with `d` declared and `i` an innovation. -/
theorem lowMode_decomp [FiniteDimensional ℝ H₀] (D : Submodule ℝ (Lp H₀ 2 halfLine))
    {v : Lp H₀ 2 halfLine} (hv : v ∈ lowRange W) :
    ∃ d ∈ declaredPart W D, ∃ i ∈ innovations W D, v = d + i := by
  haveI : FiniteDimensional ℝ (lowRange W) := finiteDimensional_lowRange W
  haveI : FiniteDimensional ℝ (declaredPart W D) :=
    Submodule.finiteDimensional_of_le (declaredPart_le W D)
  set K := declaredPart W D with hK
  refine ⟨K.starProjection v, K.starProjection_apply_mem v, v - K.starProjection v,
    ⟨K.sub_starProjection_mem_orthogonal v, ?_⟩, by abel⟩
  exact (lowRange W).sub_mem hv (declaredPart_le W D (K.starProjection_apply_mem v))

/-- A low mode is already part of the declared carrier exactly when its residual against the
carrier vanishes. -/
theorem low_mode_declared_iff (D : Submodule ℝ (Lp H₀ 2 halfLine)) [D.HasOrthogonalProjection]
    {v : Lp H₀ 2 halfLine} (hv : v ∈ lowRange W) :
    v - D.starProjection v = 0 ↔ v ∈ declaredPart W D := by
  rw [sub_eq_zero, eq_comm, D.starProjection_eq_self_iff]
  exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩

/-- The number of innovations is bounded by the rank of the low-mode range, hence by the rank of
the spectral screen `P_R`. -/
theorem finrank_innovations_le [FiniteDimensional ℝ H₀] (D : Submodule ℝ (Lp H₀ 2 halfLine)) :
    Module.finrank ℝ (innovations W D)
      ≤ Module.finrank ℝ (LinearMap.range W.P.toLinearMap) := by
  haveI : FiniteDimensional ℝ (lowRange W) := finiteDimensional_lowRange W
  exact (Submodule.finrank_mono (innovations_le W D)).trans
    (finrank_range_hankel_le W.lowScreen W.commP W.Pidem)

/-- **The exhaustive finite-resolution profile** (`cor:finite-resolution-memory`): every memory
output `ℌ f` is a declared low mode plus a canonical finite innovation plus a high-energy tail of
norm at most `b c/(2R) ‖f‖`. -/
theorem memory_profile [FiniteDimensional ℝ H₀] (D : Submodule ℝ (Lp H₀ 2 halfLine))
    (f : Lp H₀ 2 halfLine) :
    ∃ d ∈ declaredPart W D, ∃ i ∈ innovations W D,
      hankel W.fullScreen f = d + i + hankel W.highScreen f ∧
        ‖hankel W.highScreen f‖ ≤ W.b * W.c / (2 * W.R) * ‖f‖ := by
  obtain ⟨d, hd, i, hi, hdi⟩ := lowMode_decomp W D (v := hankel W.lowScreen f) ⟨f, rfl⟩
  refine ⟨d, hd, i, hi, ?_, ?_⟩
  · rw [hankel_full_eq, add_apply, ← hdi]
  · exact (hankel W.highScreen).le_of_opNorm_le (norm_hankel_le W.highScreen) f

/-- **No amorphous loaded-memory branch**: under the counting law (rank envelope), the transient
floor, the coupling bounds and cutoff compactness (all packaged in the splitting), the
fixed-resolution rank is bounded by `C_W R^{3/2}`, the tail vanishes at rate `b c/(2R)`, and the
memory is compact. -/
theorem no_amorphous_branch [FiniteDimensional ℝ H₀] {CW : ℝ}
    (hrank : (Module.finrank ℝ (LinearMap.range W.P.toLinearMap) : ℝ) ≤ CW * W.R ^ ((3 : ℝ) / 2))
    (D : Submodule ℝ (Lp H₀ 2 halfLine)) :
    (Module.finrank ℝ (lowRange W) : ℝ) ≤ CW * W.R ^ ((3 : ℝ) / 2) ∧
      (Module.finrank ℝ (innovations W D) : ℝ) ≤ CW * W.R ^ ((3 : ℝ) / 2) ∧
      ‖hankel W.fullScreen - hankel W.lowScreen‖ ≤ W.b * W.c / (2 * W.R) ∧
      IsCompactOperator (hankel W.fullScreen) := by
  obtain ⟨htail, hlow, hcpt⟩ := hankel_truncation W
  refine ⟨?_, ?_, htail, hcpt⟩
  · exact (Nat.cast_le.mpr hlow).trans hrank
  · exact (Nat.cast_le.mpr (finrank_innovations_le W D)).trans hrank

end HankelFeedback
end NCG
