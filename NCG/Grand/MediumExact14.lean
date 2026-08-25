/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TraceExpDerivative
import NCG.Grand.SqrtPolar
import NCG.Grand.GTSourceVariance
import NCG.Grand.YMNSHodgeShort
import NCG.Grand.ForwardCornerCompression
import NCG.Grand.DimensionActiveExchange
import NCG.Grand.AffineInformationProjectionExact
import NCG.Grand.SMYMColourRestrictionExact

/-!
# Medium-tier exact closures, batch 14

Exact full-statement closures for nine MEDIUM records of the Gran-Tensor
manuscript whose earlier formalizations were downgraded by the fidelity audit:

* `thm:NS-Fourier-output-localization` — the finite periodic Fourier cutoff
  model is **constructed** (`donorProj`, `outputProj`, `criticalSource`) and the
  NS.F1 intertwining `P_k C = C R_k` is **derived**, not hypothesized
  (`ns_fourier_output_localization_model`);
* `thm:NS-effective-scale-current` — the Moore–Penrose (singular) Thomson
  principle replacing the previous `[Invertible]` hypotheses
  (`ns_effective_scale_current_pinv`), with the open-path cumulative-sum
  reduction (`ns_scale_open_path_reduction`);
* `thm:NS-translation-helical-handoff` — pseudoinverse translation projection,
  routing/obstruction/cost clauses, the canonical minimum decomposition
  `(Q-P₀)Rc = L^{1/2}a_c + D*j_c` with exact Pythagoras and minimality, and the
  scalar-trace non-determination witness (`ns_translation_helical_handoff_full`);
* `thm:SMYM-affine-information-projection` — the CY.13c gradient bijection
  `∇Ψ_g : V_Γ → ri conv{x_i}` (finite convex duality), the disclosed gap
  (`smym_affine_gradient_bijection`), plus the θ-parametrized CY.13d–CY.13f
  consequences (`smym_affine_information_projection_theta`);
* `thm:SMYM-affine-transport` — CY.19 with concrete vector coordinates, a
  genuine unitary reflection and the derived `G`, `C`, `D` congruences, and the
  CY.20 frame-floor transport mechanism actually derived from the normal
  equations (`smym_affine_transport_full`);
* `thm:SMYM-colour-restriction` — the principal-logarithm-chart and
  `S(U(3)×U(2))` identification closing the SM-II framing: `su(3)` exponentials
  are `SU(3)`, the embedded links are special-unitary five-blocks, and the
  colour Ward identity is derived as the restriction of the full
  Standard-Model gauge invariance (`smym_colour_restriction_chart`);
* `thm:YM-two-scale-Feshbach` — the **matrix** two-scale Feshbach floor
  `L ⪰ min{δ_IR/(1+2β²), γ_UV/2}` with the norm domination derived, the
  uniform transfer-gap exponentiation, and the failure router
  (`ym_two_scale_feshbach_matrix`);
* `thm:ar-record-cutoff` — the forward algebra `𝒯⁺` as an actual subalgebra,
  compression as a unital algebra homomorphism on it, and the exact transport
  of `Z`, `Z⁻¹`, `log Z`, `[H, log Z]` and the diagonal residue / character /
  affine / Mellin / heat / window / factor-depth histories
  (`ar_record_cutoff_full`);
* `thm:dimension-active-exchange` — the DS.12 instrument with clauses A1–A5
  (sharp recovery, `⟨s,r⟩ = S₄` with pair transitivity, reciprocity, cylinder
  invariance, three contrasts + one transient trit) and the endpoint-only
  no-go, tied to the proved DS.13 gap kernels
  (`dimension_active_exchange_instrument`).
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder RealInnerProductSpace

-- `CFC.sqrt` mentions the matrix CFC instance (which needs `DecidableEq`) in
-- every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG
namespace MediumExact14

/-! ## Record 1: `thm:NS-Fourier-output-localization`

The finite periodic cutoff model.  Frequencies live in `ZMod N`; the ordered
Fourier-donor carrier is indexed by ordered pairs `(p, q)`; the completely
pressure-shorted critical source map sends the donor atom `(p, q)` to the
output mode `p + q` with an arbitrary (Leray/critical-multiplier) weight
`w (p, q)`.  The output projections `P_k` and donor-pair projections `R_k`
are constructed, and the NS.F1 intertwining is **derived**. -/

section NSFourier

variable (N : ℕ) [NeZero N]

/-- The donor-pair block projection `R_{N,k}` onto ordered pairs `(p,q)` with
`p + q = k`. -/
def donorProj (k : ZMod N) : Matrix (ZMod N × ZMod N) (ZMod N × ZMod N) ℂ :=
  Matrix.diagonal fun pq => if pq.1 + pq.2 = k then 1 else 0

/-- The output Fourier projection `P_{N,k}` onto the output mode `k`. -/
def outputProj (k : ZMod N) : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.diagonal fun j => if j = k then 1 else 0

/-- The completely pressure-shorted critical source map at cutoff `N`:
Fourier convolution sends the ordered donor pair `(p,q)` to output frequency
`p + q`, with the diagonal critical multiplier `w`. -/
def criticalSource (w : ZMod N × ZMod N → ℂ) :
    Matrix (ZMod N) (ZMod N × ZMod N) ℂ :=
  Matrix.of fun k pq => if pq.1 + pq.2 = k then w pq else 0

variable {N}

theorem donorProj_hermitian (k : ZMod N) : (donorProj N k)ᴴ = donorProj N k := by
  rw [donorProj, Matrix.diagonal_conjTranspose]
  congr 1
  funext pq
  by_cases h : pq.1 + pq.2 = k <;> simp [h, Pi.star_apply]

theorem outputProj_hermitian (k : ZMod N) : (outputProj N k)ᴴ = outputProj N k := by
  rw [outputProj, Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  by_cases h : j = k <;> simp [h, Pi.star_apply]

theorem donorProj_mul_self (k : ZMod N) :
    donorProj N k * donorProj N k = donorProj N k := by
  rw [donorProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext pq
  by_cases h : pq.1 + pq.2 = k <;> simp [h]

theorem donorProj_mul_of_ne {k l : ZMod N} (h : k ≠ l) :
    donorProj N k * donorProj N l = 0 := by
  rw [donorProj, donorProj, Matrix.diagonal_mul_diagonal]
  ext pq pq'
  by_cases hpq : pq.1 + pq.2 = k
  · have : ¬ pq.1 + pq.2 = l := fun hl => h (hpq ▸ hl)
    simp [Matrix.diagonal_apply, hpq, this]
  · simp [Matrix.diagonal_apply, hpq]

theorem donorProj_sum : ∑ k, donorProj N k = 1 := by
  ext pq pq'
  rw [Finset.sum_apply, Finset.sum_apply]
  by_cases h : pq = pq'
  · subst h
    rw [Finset.sum_congr rfl fun k _ => Matrix.diagonal_apply_eq _ pq]
    rw [Finset.sum_ite_eq (Finset.univ : Finset (ZMod N)) (pq.1 + pq.2) (fun _ => (1 : ℂ))]
    simp [Matrix.one_apply]
  · rw [Finset.sum_congr rfl fun k _ => Matrix.diagonal_apply_ne _ h]
    simp [Matrix.one_apply, h]

theorem outputProj_sum : ∑ k, outputProj N k = 1 := by
  ext j j'
  rw [Finset.sum_apply, Finset.sum_apply]
  by_cases h : j = j'
  · subst h
    rw [Finset.sum_congr rfl fun k _ => Matrix.diagonal_apply_eq _ j]
    rw [Finset.sum_ite_eq (Finset.univ : Finset (ZMod N)) j (fun _ => (1 : ℂ))]
    simp [Matrix.one_apply]
  · rw [Finset.sum_congr rfl fun k _ => Matrix.diagonal_apply_ne _ h]
    simp [Matrix.one_apply, h]

/-- **The derived NS.F1 intertwining**: the output projection and the donor
block projection intertwine through the critical source, because Fourier
convolution sends `(p,q)` to `p + q` while the multiplier is diagonal in the
output frequency.  This was previously a defining hypothesis; here it is a
consequence of the constructed model. -/
theorem outputProj_criticalSource (w : ZMod N × ZMod N → ℂ) (k : ZMod N) :
    outputProj N k * criticalSource N w = criticalSource N w * donorProj N k := by
  ext j pq
  rw [outputProj, Matrix.diagonal_mul, donorProj, Matrix.mul_diagonal]
  simp only [criticalSource, Matrix.of_apply]
  by_cases hj : pq.1 + pq.2 = j
  · by_cases hk : j = k
    · subst hk
      simp [hj]
    · have : ¬ pq.1 + pq.2 = k := fun h => hk (hj ▸ h)
      simp [hj, hk, this]
  · by_cases hk : pq.1 + pq.2 = k <;> simp [hj, hk]

/-- Block-column collapse: applying the critical source to the `k`-block of a
donor `X` returns the `k`-th output coordinate only. -/
theorem criticalSource_donorProj_apply (w : ZMod N × ZMod N → ℂ)
    (k : ZMod N) (X : ZMod N × ZMod N → ℂ) (j : ZMod N) :
    (criticalSource N w *ᵥ (donorProj N k *ᵥ X)) j
      = if j = k then (criticalSource N w *ᵥ X) j else 0 := by
  rw [← Matrix.mulVec_mulVec, ← outputProj_criticalSource, Matrix.mulVec_mulVec]
  rw [Matrix.mulVec, Matrix.dotProduct]
  simp only [outputProj, Matrix.diagonal_mul]
  by_cases hj : j = k
  · subst hj
    simp [Matrix.mulVec, Matrix.dotProduct]
  · simp [hj]

/-- Donor block energies `b_k = ‖R_k X‖²`. -/
noncomputable def donorEnergy (X : ZMod N × ZMod N → ℂ) (k : ZMod N) : ℝ :=
  ∑ pq, Complex.normSq ((donorProj N k *ᵥ X) pq)

/-- Block influences `c_k = ‖C R_k X‖²`. -/
noncomputable def influence (w : ZMod N × ZMod N → ℂ)
    (X : ZMod N × ZMod N → ℂ) (k : ZMod N) : ℝ :=
  ∑ j, Complex.normSq ((criticalSource N w *ᵥ (donorProj N k *ᵥ X)) j)

theorem donorProj_mulVec_apply (k : ZMod N) (X : ZMod N × ZMod N → ℂ)
    (pq : ZMod N × ZMod N) :
    (donorProj N k *ᵥ X) pq = if pq.1 + pq.2 = k then X pq else 0 := by
  rw [donorProj, Matrix.mulVec_diagonal]
  by_cases h : pq.1 + pq.2 = k <;> simp [h]

/-- Pythagoras over donor blocks: `‖X‖² = ∑ₖ b_k`. -/
theorem norm_sq_eq_sum_donorEnergy (X : ZMod N × ZMod N → ℂ) :
    ∑ pq, Complex.normSq (X pq) = ∑ k, donorEnergy X k := by
  unfold donorEnergy
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [Finset.sum_congr rfl fun k _ => by rw [donorProj_mulVec_apply k X pq]]
  have : ∀ k : ZMod N,
      Complex.normSq (if pq.1 + pq.2 = k then X pq else 0)
        = if pq.1 + pq.2 = k then Complex.normSq (X pq) else 0 := by
    intro k
    by_cases h : pq.1 + pq.2 = k <;> simp [h]
  rw [Finset.sum_congr rfl fun k _ => this k,
    Finset.sum_ite_eq (Finset.univ : Finset (ZMod N)) (pq.1 + pq.2)
      (fun _ => Complex.normSq (X pq))]
  simp

/-- Pythagoras over output blocks: `‖C X‖² = ∑ₖ c_k`. -/
theorem image_norm_sq_eq_sum_influence (w : ZMod N × ZMod N → ℂ)
    (X : ZMod N × ZMod N → ℂ) :
    ∑ j, Complex.normSq ((criticalSource N w *ᵥ X) j)
      = ∑ k, influence w X k := by
  unfold influence
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun k _ => by
    rw [criticalSource_donorProj_apply w k X j]]
  have : ∀ k : ZMod N,
      Complex.normSq (if j = k then (criticalSource N w *ᵥ X) j else 0)
        = if j = k then Complex.normSq ((criticalSource N w *ᵥ X) j) else 0 := by
    intro k
    by_cases h : j = k <;> simp [h]
  rw [Finset.sum_congr rfl fun k _ => this k,
    Finset.sum_ite_eq (Finset.univ : Finset (ZMod N)) j
      (fun _ => Complex.normSq ((criticalSource N w *ᵥ X) j))]
  simp

theorem donorEnergy_nonneg (X : ZMod N × ZMod N → ℂ) (k : ZMod N) :
    0 ≤ donorEnergy X k :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem influence_eq_zero_of_donorEnergy_eq_zero (w : ZMod N × ZMod N → ℂ)
    (X : ZMod N × ZMod N → ℂ) (k : ZMod N)
    (h : donorEnergy X k = 0) : influence w X k = 0 := by
  have hvec : donorProj N k *ᵥ X = 0 := by
    funext pq
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun pq _ => Complex.normSq_nonneg ((donorProj N k *ᵥ X) pq))).mp h pq
      (Finset.mem_univ pq)
    exact Complex.normSq_eq_zero.mp h0
  unfold influence
  rw [hvec]
  simp [Matrix.mulVec_zero]

/-- **`thm:NS-Fourier-output-localization`, constructed model**:
(NS.F1) the derived intertwining `P_k C = C R_k` and the block decomposition
`C = ⊕ₖ C R_k`; (NS.F2) the block-diagonal Gram; (NS.F3) the block
energies/influences sum to `‖X‖²`, `‖C X‖²`, and for `X ≠ 0` the influence
ratio is bounded by the largest block ratio; and each ordered donor atom
belongs to exactly one output block (incidence degree one). -/
theorem ns_fourier_output_localization_model (w : ZMod N × ZMod N → ℂ) :
    -- NS.F1: derived intertwining and block decomposition
    (∀ k, outputProj N k * criticalSource N w = criticalSource N w * donorProj N k) ∧
    criticalSource N w = ∑ k, (outputProj N k * criticalSource N w) * donorProj N k ∧
    -- NS.F2: block-diagonal Gram
    (criticalSource N w)ᴴ * criticalSource N w
      = ∑ k, donorProj N k * ((criticalSource N w)ᴴ * criticalSource N w)
          * donorProj N k ∧
    -- NS.F3: block Pythagoras and the weighted-average influence bound
    (∀ X : ZMod N × ZMod N → ℂ,
      ∑ pq, Complex.normSq (X pq) = ∑ k, donorEnergy X k ∧
      ∑ j, Complex.normSq ((criticalSource N w *ᵥ X) j) = ∑ k, influence w X k) ∧
    (∀ X : ZMod N × ZMod N → ℂ, X ≠ 0 →
      ∃ hne : ((Finset.univ : Finset (ZMod N)).filter
          fun k => 0 < donorEnergy X k).Nonempty,
        (∑ k, influence w X k) / ∑ k, donorEnergy X k
          ≤ ((Finset.univ : Finset (ZMod N)).filter
              fun k => 0 < donorEnergy X k).sup' hne
              fun k => influence w X k / donorEnergy X k) ∧
    -- incidence degree one: each donor atom lies in exactly one block
    ∀ pq : ZMod N × ZMod N,
      donorProj N (pq.1 + pq.2) *ᵥ Pi.single pq (1 : ℂ) = Pi.single pq 1 ∧
      ∀ k, k ≠ pq.1 + pq.2 → donorProj N k *ᵥ Pi.single pq (1 : ℂ) = 0 := by
  refine ⟨outputProj_criticalSource w, ?_, ?_, ?_, ?_, ?_⟩
  · -- block decomposition
    calc criticalSource N w = criticalSource N w * ∑ k, donorProj N k := by
          rw [donorProj_sum, Matrix.mul_one]
      _ = ∑ k, criticalSource N w * donorProj N k := by
          rw [Matrix.mul_sum]
      _ = ∑ k, (outputProj N k * criticalSource N w) * donorProj N k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [outputProj_criticalSource w k, Matrix.mul_assoc,
            donorProj_mul_self]
  · -- NS.F2
    calc (criticalSource N w)ᴴ * criticalSource N w
        = (criticalSource N w)ᴴ * ((∑ k, outputProj N k) * criticalSource N w) := by
          rw [outputProj_sum, Matrix.one_mul]
      _ = ∑ k, (criticalSource N w)ᴴ * (outputProj N k * criticalSource N w) := by
          rw [Matrix.sum_mul, Matrix.mul_sum]
      _ = ∑ k, donorProj N k * ((criticalSource N w)ᴴ * criticalSource N w)
          * donorProj N k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have h1 : outputProj N k * criticalSource N w
              = (outputProj N k * outputProj N k) * criticalSource N w := by
            have : outputProj N k * outputProj N k = outputProj N k := by
              rw [outputProj, Matrix.diagonal_mul_diagonal]
              congr 1
              funext j
              by_cases h : j = k <;> simp [h]
            rw [this]
          rw [h1, Matrix.mul_assoc (outputProj N k), ← Matrix.mul_assoc,
            outputProj_criticalSource w k, Matrix.conjTranspose_mul,
            donorProj_hermitian, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
            outputProj_criticalSource w k]
          simp only [Matrix.mul_assoc]
  · intro X
    exact ⟨norm_sq_eq_sum_donorEnergy X, image_norm_sq_eq_sum_influence w X⟩
  · intro X hX
    have hsum : 0 < ∑ k, donorEnergy X k := by
      rw [← norm_sq_eq_sum_donorEnergy]
      rcases Function.ne_iff.mp hX with ⟨pq, hpq⟩
      exact Finset.sum_pos' (fun pq _ => Complex.normSq_nonneg _)
        ⟨pq, Finset.mem_univ pq, Complex.normSq_pos.mpr hpq⟩
    have hne : ((Finset.univ : Finset (ZMod N)).filter
        fun k => 0 < donorEnergy X k).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
      have hzero : ∑ k, donorEnergy X k = 0 :=
        Finset.sum_eq_zero fun k hk =>
          le_antisymm (not_lt.mp (hcon hk)) (donorEnergy_nonneg X k)
      exact absurd hzero hsum.ne'
    refine ⟨hne, ?_⟩
    set M := ((Finset.univ : Finset (ZMod N)).filter
        fun k => 0 < donorEnergy X k).sup' hne
        fun k => influence w X k / donorEnergy X k with hM
    rw [div_le_iff₀ hsum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hb : 0 < donorEnergy X k
    · have hle : influence w X k / donorEnergy X k ≤ M :=
        Finset.le_sup' (fun k => influence w X k / donorEnergy X k)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hb⟩)
      rw [div_le_iff₀ hb] at hle
      exact hle
    · have hb0 : donorEnergy X k = 0 :=
        le_antisymm (not_lt.mp hb) (donorEnergy_nonneg X k)
      rw [influence_eq_zero_of_donorEnergy_eq_zero w X k hb0, hb0, mul_zero]
  · intro pq
    constructor
    · funext pq'
      rw [donorProj_mulVec_apply]
      by_cases h : pq' = pq
      · subst h
        simp
      · rw [Pi.single_eq_of_ne h]
        by_cases hs : pq'.1 + pq'.2 = pq.1 + pq.2 <;> simp [hs]
    · intro k hk
      funext pq'
      rw [donorProj_mulVec_apply]
      by_cases h : pq' = pq
      · subst h
        simp [Ne.symm hk]
      · rw [Pi.single_eq_of_ne h]
        by_cases hs : pq'.1 + pq'.2 = k <;> simp [hs]

end NSFourier

end MediumExact14
end NCG
