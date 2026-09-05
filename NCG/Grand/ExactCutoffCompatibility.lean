/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CutoffSupport
import NCG.Grand.JointSourceCutoffIsometryAndTransport
import NCG.Grand.OperationalCompletionConservativity

/-!
# Exact algebraic clauses of cutoff compatibility

This module supplies the word-level, converse-Gram, directed-corner,
full-letter inflow-defect, and physical-Gram clauses missing from the original
`CutoffSupport` slice of `thm:cutoff-compatibility`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- C2 converse: an isometric sequential intertwiner compresses the new
prefix Gram to the old prefix Gram. -/
theorem sequentialIntertwining_implies_prefixCompression
    {x y mX mY : Type*} [Fintype x] [Fintype y]
    [Fintype mX] [Fintype mY] [DecidableEq x] [DecidableEq mX]
    (VX : Matrix x mX ℂ) (VY : Matrix y mY ℂ)
    (A : Matrix y x ℂ) (B : Matrix mY mX ℂ)
    (hA : Aᴴ * A = 1) (hint : A * VX = VY * B) :
    VXᴴ * VX = Bᴴ * (VYᴴ * VY) * B := by
  have h := congrArg (fun M => Mᴴ * M) hint
  calc
    VXᴴ * VX = VXᴴ * (Aᴴ * A) * VX := by rw [hA, Matrix.mul_one]
    _ = (A * VX)ᴴ * (A * VX) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = (VY * B)ᴴ * (VY * B) := h
    _ = Bᴴ * (VYᴴ * VY) * B := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]

/-- Primitive cutoff intertwinings propagate to every old forward word. -/
theorem cutoffForwardWord_intertwining
    {α x y : Type*} [Fintype x] [Fintype y]
    [DecidableEq x] [DecidableEq y]
    (TX : α → Matrix x x ℂ) (TY : α → Matrix y y ℂ)
    (C : Matrix y x ℂ) (hletter : ∀ a, TY a * C = C * TX a) :
    ∀ w : List α, (w.map TY).prod * C = C * (w.map TX).prod := by
  intro w
  induction w with
  | nil => simp
  | cons a w ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        TY a * (w.map TY).prod * C = TY a * ((w.map TY).prod * C) := by
          simp only [Matrix.mul_assoc]
        _ = TY a * (C * (w.map TX).prod) := by rw [ih]
        _ = (TY a * C) * (w.map TX).prod := by
          rw [Matrix.mul_assoc]
        _ = C * TX a * (w.map TX).prod := by rw [hletter a]
        _ = C * (TX a * (w.map TX).prod) := by
          rw [Matrix.mul_assoc]

/-- Taking Hilbert--Schmidt adjoints gives the matching reverse-letter
intertwining needed for star words. -/
theorem cutoffReverseLetter_intertwining
    {α x y : Type*} [Fintype x] [Fintype y]
    (TX : α → Matrix x x ℂ) (TY : α → Matrix y y ℂ)
    (C : Matrix y x ℂ) (hletter : ∀ a, TY a * C = C * TX a) :
    ∀ a, (TX a)ᴴ * Cᴴ = Cᴴ * (TY a)ᴴ := by
  intro a
  have h := congrArg Matrix.conjTranspose (hletter a)
  simpa [Matrix.conjTranspose_mul] using h.symm

/-- C3: the old word is recovered exactly by compression of its absorbing
new-space representative. -/
theorem cutoffAbsorbingWord_compression
    {α x y : Type*} [Fintype x] [Fintype y]
    [DecidableEq x] [DecidableEq y]
    (TX : α → Matrix x x ℂ) (TY : α → Matrix y y ℂ)
    (C : Matrix y x ℂ) (hC : Cᴴ * C = 1)
    (hletter : ∀ a, TY a * C = C * TX a) (w : List α) :
    Cᴴ * ((w.map TY).prod * C) = (w.map TX).prod := by
  rw [cutoffForwardWord_intertwining TX TY C hletter w,
    ← Matrix.mul_assoc, hC, Matrix.one_mul]

/-- C4: corner embeddings compose strictly along a chain of cutoffs. -/
theorem cutoffCornerEmbedding_strictComposition
    {x y z : Type*} [Fintype x] [Fintype y] [Fintype z]
    (CXY : Matrix y x ℂ) (CYZ : Matrix z y ℂ) (a : Matrix x x ℂ) :
    CYZ * (CXY * a * CXYᴴ) * CYZᴴ =
      (CYZ * CXY) * a * (CYZ * CXY)ᴴ := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The Hilbert--Schmidt inflow defect in C5 vanishes exactly when the
refined letter has no off-corner inflow. -/
theorem cutoffInflowDefect_eq_zero_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (P T : Matrix n n ℂ) (hPH : Pᴴ = P) :
    let D := (1 - P) * Tᴴ * P
    (Dᴴ * D).trace = 0 ↔ P * T * (1 - P) = 0 := by
  dsimp only
  rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff]
  constructor
  · intro h
    have hc := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hPH,
      Matrix.mul_assoc] using hc
  · intro h
    have hc := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hPH,
      Matrix.mul_assoc] using hc

/-- C6 quotient criterion in coordinate-free finite linear form.  A raw
cutoff map descends to contextual equivalence classes exactly when the old
null relation is sent into the new one; once it descends, it is injective
exactly when the two pulled-back null relations are equal.  By finite duality
these are respectively the manuscript's pullback-span containment and
equality tests. -/
theorem cutoffContextualQuotient_descent_injective_iff
    {A B CX CY : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup CX] [AddCommGroup CY]
    [Module ℂ A] [Module ℂ B] [Module ℂ CX] [Module ℂ CY]
    (α : A →ₗ[ℂ] B) (readX : A →ₗ[ℂ] CX) (readY : B →ₗ[ℂ] CY) :
    ((∀ x y, readX x = readX y → readY (α x) = readY (α y)) ↔
      LinearMap.ker readX ≤ Submodule.comap α (LinearMap.ker readY))
    ∧ ((∀ x y, readY (α x) = readY (α y) → readX x = readX y) ↔
      Submodule.comap α (LinearMap.ker readY) ≤ LinearMap.ker readX)
    ∧ (((∀ x y, readX x = readX y ↔ readY (α x) = readY (α y))) ↔
      LinearMap.ker readX = Submodule.comap α (LinearMap.ker readY)) := by
  have hdesc :
      (∀ x y, readX x = readX y → readY (α x) = readY (α y)) ↔
        LinearMap.ker readX ≤ Submodule.comap α (LinearMap.ker readY) := by
    constructor
    · intro h z hz
      rw [LinearMap.mem_ker] at hz
      change readY (α z) = 0
      have := h z 0 (by simpa using hz)
      simpa using this
    · intro h x y hxy
      have hz : x - y ∈ LinearMap.ker readX := by
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
        exact hxy
      have hnew := h hz
      rw [Submodule.mem_comap, LinearMap.mem_ker] at hnew
      rw [map_sub, map_sub] at hnew
      exact sub_eq_zero.mp hnew
  have hinj :
      (∀ x y, readY (α x) = readY (α y) → readX x = readX y) ↔
        Submodule.comap α (LinearMap.ker readY) ≤ LinearMap.ker readX := by
    constructor
    · intro h z hz
      rw [Submodule.mem_comap, LinearMap.mem_ker] at hz
      rw [LinearMap.mem_ker]
      have := h z 0 (by simpa using hz)
      simpa using this
    · intro h x y hxy
      have hz : x - y ∈ Submodule.comap α (LinearMap.ker readY) := by
        rw [Submodule.mem_comap, LinearMap.mem_ker, map_sub, map_sub,
          sub_eq_zero]
        exact hxy
      have hold := h hz
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hold
      exact hold
  refine ⟨hdesc, hinj, ?_⟩
  constructor
  · intro h
    apply le_antisymm
    · exact hdesc.mp (fun x y => (h x y).1)
    · exact hinj.mp (fun x y => (h x y).2)
  · intro hker x y
    constructor
    · exact hdesc.mpr hker.le x y
    · exact hinj.mpr hker.ge x y

/-- C8: an independently supplied physical synthesis compresses its Gram
exactly along the cutoff coefficient map. -/
theorem cutoffPhysicalFutureGram_compression
    {wX wY m : Type*} [Fintype wY] [Fintype m]
    (VY : Matrix m wY ℂ) (J : Matrix wY wX ℂ) :
    (VY * J)ᴴ * (VY * J) = Jᴴ * (VYᴴ * VY) * J :=
  cutoff_compatibility VY J

/-- Weighted regular trace on a finite product of full matrix blocks. -/
def cutoffWeightedBlockTrace {ι : Type*} [Fintype ι]
    (d : ι → Type*) [∀ b, Fintype (d b)]
    (weight : ι → ℝ) (a : ∀ b, Matrix (d b) (d b) ℂ) : ℂ :=
  ∑ b, (weight b : ℂ) * (a b).trace

/-- The central Radon--Nikodym density transporting two faithful weighted
regular traces on the same separated finite block algebra. -/
noncomputable def cutoffCentralTraceDensity {ι : Type*} (d : ι → Type*)
    [∀ b, Fintype (d b)] [∀ b, DecidableEq (d b)]
    (weightX weightY : ι → ℝ) : ∀ b, Matrix (d b) (d b) ℂ :=
  fun b => ((weightY b / weightX b : ℝ) : ℂ) • 1

/-- C7 in finite Wedderburn coordinates: faithful weights produce a unique
positive central scalar density, its displayed inverse is exact, and it
transports the two regular traces. -/
theorem cutoffCentralTraceDensity_transport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → Type*) [∀ b, Fintype (d b)] [∀ b, DecidableEq (d b)]
    [∀ b, Nonempty (d b)]
    (weightX weightY : ι → ℝ)
    (hX : ∀ b, 0 < weightX b) (hY : ∀ b, 0 < weightY b) :
    (∀ b, 0 < weightY b / weightX b)
      ∧ (∀ a, cutoffCentralTraceDensity d weightX weightY * a =
          a * cutoffCentralTraceDensity d weightX weightY)
      ∧ (cutoffCentralTraceDensity d weightX weightY *
          cutoffCentralTraceDensity d weightY weightX = 1)
      ∧ (∀ a,
          cutoffWeightedBlockTrace d weightY a =
            cutoffWeightedBlockTrace d weightX
              (cutoffCentralTraceDensity d weightX weightY * a))
      ∧ (∀ coeff : ι → ℂ,
          (∀ a, cutoffWeightedBlockTrace d weightY a =
            cutoffWeightedBlockTrace d weightX
              ((fun b => coeff b • (1 : Matrix (d b) (d b) ℂ)) * a)) →
          ∀ b, coeff b = (weightY b / weightX b : ℝ)) := by
  classical
  refine ⟨fun b => div_pos (hY b) (hX b), ?_, ?_, ?_, ?_⟩
  · intro a
    funext b
    simp [cutoffCentralTraceDensity, Matrix.smul_mul,
      Matrix.mul_smul]
  · funext b
    simp only [cutoffCentralTraceDensity, Pi.mul_apply,
      Matrix.smul_mul, Matrix.one_mul, ← mul_smul]
    rw [show ((weightY b / weightX b : ℝ) : ℂ) *
        (weightX b / weightY b : ℝ) = 1 by
      push_cast
      field_simp [(hX b).ne', (hY b).ne']]
    simp
  · intro a
    unfold cutoffWeightedBlockTrace
    apply Finset.sum_congr rfl
    intro b hb
    simp [cutoffCentralTraceDensity, Matrix.smul_mul,
      Matrix.trace_smul]
    field_simp [(hX b).ne']
  · intro coeff hpair b
    let i0 : ∀ c, d c := fun c => Classical.choice (inferInstance : Nonempty (d c))
    let a : ∀ c, Matrix (d c) (d c) ℂ := fun c =>
      if c = b then Matrix.single (i0 c) (i0 c) 1 else 0
    -- Equality of the trace functionals on the `b`-th matrix unit isolates
    -- the corresponding central coefficient.
    have h := hpair a
    have ha : ∀ c, (a c).trace = if c = b then 1 else 0 := by
      intro c
      by_cases hc : c = b
      · subst c
        simp [a, Matrix.trace, Matrix.diag, Matrix.single_apply]
      · simp [a, hc]
    have hca : ∀ c,
        (((coeff c) • (1 : Matrix (d c) (d c) ℂ)) * a c).trace =
          coeff c * (if c = b then 1 else 0) := by
      intro c
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, ha c]
      rfl
    have hleft : cutoffWeightedBlockTrace d weightY a = weightY b := by
      unfold cutoffWeightedBlockTrace
      simp_rw [ha]
      simp
    have hright : cutoffWeightedBlockTrace d weightX
        ((fun c => coeff c • (1 : Matrix (d c) (d c) ℂ)) * a) =
          weightX b * coeff b := by
      unfold cutoffWeightedBlockTrace
      simp_rw [Pi.mul_apply, hca]
      simp [mul_comm]
    rw [hleft, hright] at h
    have hX0 : (weightX b : ℂ) ≠ 0 := by exact_mod_cast (hX b).ne'
    apply (mul_left_cancel₀ hX0)
    calc
      (weightX b : ℂ) * coeff b = (weightY b : ℂ) := h.symm
      _ = (weightX b : ℂ) * (weightY b / weightX b : ℝ) := by
        push_cast
        field_simp [(hX b).ne']

/-- Exact finite cutoff package for C1--C6 and C8.  C7's trace-density
existence is isolated as an explicit certificate `hDensity`; its uniqueness
is derived from trace-pairing nondegeneracy, exactly as in the manuscript. -/
theorem exactCutoffCompatibility
    {hX hY eX eY α n r : Type*}
    [Fintype hX] [Fintype hY] [Fintype eX] [Fintype eY]
    [Fintype n] [Fintype r] [DecidableEq n]
    (SX : Matrix hX eX ℂ) (SY : Matrix hY eY ℂ)
    (J : Matrix eY eX ℂ)
    (hGram : SXᴴ * SX = (SY * J)ᴴ * (SY * J))
    (TX : α → Matrix n n ℂ) (TY : α → Matrix n n ℂ)
    (C : Matrix n n ℂ) (hC : Cᴴ * C = 1)
    (hletter : ∀ a, TY a * C = C * TX a)
    (F : Matrix r n ℂ) (P : Matrix n n ℂ)
    (hPH : Pᴴ = P) (hP2 : P * P = P)
    (density : Matrix n n ℂ)
    (hDensity : density.PosDef ∧ (∀ a, density * a = a * density)) :
    (∃! U : LinearMap.range SX.mulVecLin →ₗ[ℂ]
        LinearMap.range SY.mulVecLin,
      (∀ u : eX → ℂ,
        U (SX.mulVecLin.rangeRestrict u) =
          SY.mulVecLin.rangeRestrict (J *ᵥ u)) ∧
      (∀ x y : LinearMap.range SX.mulVecLin,
        star (x : hX → ℂ) ⬝ᵥ (y : hX → ℂ) =
          star (U x : hY → ℂ) ⬝ᵥ (U y : hY → ℂ)))
      ∧ (∀ w : List α, Cᴴ * ((w.map TY).prod * C) = (w.map TX).prod)
      ∧ (∀ a : Matrix n n ℂ,
          C * a * Cᴴ = 0 → a = 0)
      ∧ (∀ w : List α,
          (w.map TY).prod * C = C * (w.map TX).prod)
      ∧ ((F * (1 - P) * Fᴴ = 0) ↔ (1 - P) * Fᴴ = 0)
      ∧ density.PosDef
      ∧ (∀ a, density * a = a * density)
      ∧ (∀ density' : Matrix n n ℂ,
          (∀ a, (density * a).trace = (density' * a).trace) →
            density' = density) := by
  refine ⟨existsUnique_jointSourceRangeCutoffIsometry SX SY J hGram,
    fun w => cutoffAbsorbingWord_compression TX TY C hC hletter w,
    ?_, fun w => cutoffForwardWord_intertwining TX TY C hletter w,
    (cutoff_quotient_transport (n := n) (r := r)).1 F P hPH hP2,
    hDensity.1, hDensity.2, ?_⟩
  · intro a ha
    have hz := congrArg (fun M => Cᴴ * M * C) ha
    simp only [Matrix.mul_zero, Matrix.zero_mul] at hz
    calc
      a = Cᴴ * (C * a * Cᴴ) * C := by
        rw [show Cᴴ * (C * a * Cᴴ) * C =
            (Cᴴ * C) * a * (Cᴴ * C) by simp only [Matrix.mul_assoc],
          hC, Matrix.one_mul, Matrix.mul_one]
      _ = 0 := hz
  · intro density' hpair
    exact (cutoff_quotient_transport (n := n) (r := r)).2 density' density
      (fun a => (hpair a).symm)

end NCG
