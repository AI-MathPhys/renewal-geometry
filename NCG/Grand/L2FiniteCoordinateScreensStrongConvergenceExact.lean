import NCG.Grand.L2BlockDiagonalCompactness
import NCG.Grand.SMSTPositiveScreenExact

/-!
# Strong convergence of finite coordinate screens on `ℓ²`

The canonical projections onto the first `n` coordinates converge strongly to
the identity.  Consequently the finite compressions of every bounded operator
converge strongly to that operator, and the multiplicativity defects of the
compressed operators vanish strongly.  When the fibre is finite-dimensional,
every member of the approximating family is compact.

These are the exact analytic screen facts used by the strong-cofinal part of
`thm:GT-NCG-essential-image-trichotomy`.
-/

noncomputable section

open Filter Topology
open scoped lp

namespace NCG

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The initial-segment coordinate projections on `ℓ²(ℕ,E)` converge strongly
to the identity. -/
theorem tendsto_l2FinsetScreen_range_apply (f : ℓ²(ℕ, E)) :
    Tendsto
      (fun n : ℕ ↦ l2FinsetScreen (E := E) (Finset.range n) f)
      atTop (𝓝 f) := by
  have hsum :=
    (lp.hasSum_single (E := fun _ : ℕ ↦ E)
      (p := (2 : ENNReal)) ENNReal.ofNat_ne_top f).tendsto_sum_nat
  have heq :
      (fun n : ℕ ↦ l2FinsetScreen (E := E) (Finset.range n) f) =
        fun n : ℕ ↦ ∑ i ∈ Finset.range n, lp.single 2 i (f i) := by
    funext n
    apply lp.ext
    funext i
    rw [l2FinsetScreen_apply]
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp_rw [lp.coeFn_single]
    by_cases hi : i < n <;> simp [hi, Pi.single_apply]
  rw [heq]
  exact hsum

/-- Every bounded operator is the strong limit of its canonical finite
coordinate compressions. -/
theorem tendsto_screenCompression_l2FinsetScreen_range_apply
    (T : ℓ²(ℕ, E) →L[ℂ] ℓ²(ℕ, E)) (f : ℓ²(ℕ, E)) :
    Tendsto
      (fun n : ℕ ↦
        screenCompression (l2FinsetScreen (E := E) (Finset.range n)) T f)
      atTop (𝓝 (T f)) := by
  let P : ℕ → ℓ²(ℕ, E) →L[ℂ] ℓ²(ℕ, E) :=
    fun n ↦ l2FinsetScreen (E := E) (Finset.range n)
  have hP : ∀ v : ℓ²(ℕ, E),
      Tendsto (fun n ↦ P n v) atTop (𝓝 v) :=
    fun v ↦ tendsto_l2FinsetScreen_range_apply v
  have hT : Tendsto (fun n ↦ T (P n f)) atTop (𝓝 (T f)) :=
    (T.continuous.tendsto f).comp (hP f)
  have htransfer := SMSTChannel.strong_convergence_transfer
    (Y := ℓ²(ℕ, E)) P (1 : ℓ²(ℕ, E) →L[ℂ] ℓ²(ℕ, E)) 1
    (fun n ↦ l2FinsetScreen_opNorm_le_one (E := E) (Finset.range n))
    (fun (v : ℓ²(ℕ, E)) ↦ by simpa using hP v)
    (fun n ↦ T (P n f)) (T f) hT
  simpa only [screenCompression, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply, P] using htransfer

/-- Each member of the canonical strong approximating family is compact when
the fibre is finite-dimensional. -/
theorem canonical_screenCompression_isCompactOperator
    [FiniteDimensional ℂ E]
    (n : ℕ) (T : ℓ²(ℕ, E) →L[ℂ] ℓ²(ℕ, E)) :
    IsCompactOperator
      ((screenCompression
        (l2FinsetScreen (E := E) (Finset.range n)) T :
          ℓ²(ℕ, E) →L[ℂ] ℓ²(ℕ, E)) : ℓ²(ℕ, E) → ℓ²(ℕ, E)) :=
  screenCompression_l2FinsetScreen_isCompactOperator
    (E := E) (Finset.range n) T

/-- Products of two canonical compressed operators converge strongly to the
product of the original operators. -/
theorem tendsto_product_screenCompressions_apply
    (A B : ℓ²(ℕ, E) →L[ℂ] ℓ²(ℕ, E)) (f : ℓ²(ℕ, E)) :
    Tendsto
      (fun n : ℕ ↦
        screenCompression (l2FinsetScreen (E := E) (Finset.range n)) A
          (screenCompression (l2FinsetScreen (E := E) (Finset.range n)) B f))
      atTop (𝓝 (A (B f))) := by
  let P : ℕ → ℓ²(ℕ, E) →L[ℂ] ℓ²(ℕ, E) :=
    fun n ↦ l2FinsetScreen (E := E) (Finset.range n)
  let Ac : ℕ → ℓ²(ℕ, E) →L[ℂ] ℓ²(ℕ, E) :=
    fun n ↦ screenCompression (P n) A
  have hAc : ∀ v : ℓ²(ℕ, E), Tendsto (fun n ↦ Ac n v) atTop (𝓝 (A v)) :=
    fun v ↦ tendsto_screenCompression_l2FinsetScreen_range_apply A v
  have hAcNorm : ∀ n, ‖Ac n‖ ≤ ‖A‖ := by
    intro n
    dsimp [Ac, P, screenCompression]
    have hPnorm :=
      l2FinsetScreen_opNorm_le_one (E := E) (Finset.range n)
    have hinner :
        ‖A.comp (l2FinsetScreen (E := E) (Finset.range n))‖ ≤ ‖A‖ * 1 :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hPnorm (norm_nonneg A))
    calc
      ‖(l2FinsetScreen (E := E) (Finset.range n)).comp
          (A.comp (l2FinsetScreen (E := E) (Finset.range n)))‖
          ≤ ‖l2FinsetScreen (E := E) (Finset.range n)‖ *
              ‖A.comp (l2FinsetScreen (E := E) (Finset.range n))‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (‖A‖ * 1) :=
            mul_le_mul hPnorm hinner (norm_nonneg _) zero_le_one
      _ = ‖A‖ := by ring
  have hB := tendsto_screenCompression_l2FinsetScreen_range_apply B f
  have htransfer := SMSTChannel.strong_convergence_transfer
    (Y := ℓ²(ℕ, E)) Ac A ‖A‖ hAcNorm hAc
    (fun n ↦ screenCompression (P n) B f) (B f) hB
  simpa only [Ac, P] using htransfer

/-- The multiplicativity defect of canonical finite compressions vanishes in
the strong operator topology. -/
theorem tendsto_screenCompression_multiplicativity_defect_apply
    (A B : ℓ²(ℕ, E) →L[ℂ] ℓ²(ℕ, E)) (f : ℓ²(ℕ, E)) :
    Tendsto
      (fun n : ℕ ↦
        screenCompression (l2FinsetScreen (E := E) (Finset.range n)) A
            (screenCompression (l2FinsetScreen (E := E) (Finset.range n)) B f) -
          screenCompression (l2FinsetScreen (E := E) (Finset.range n))
            (A.comp B) f)
      atTop (𝓝 0) := by
  have hprod := tendsto_product_screenCompressions_apply A B f
  have hcomp :=
    tendsto_screenCompression_l2FinsetScreen_range_apply (A.comp B) f
  simpa only [ContinuousLinearMap.comp_apply, sub_self] using hprod.sub hcomp

end NCG
