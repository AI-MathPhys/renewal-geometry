/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianImplicitEulerFamily
import NCG.Grand.VaryingHilbertStrongBoundedness
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Positive-time equicontinuity of finite Hermitian Euler powers

For fixed Euler order, the scalar multiplier `(1 + t * nu / k)⁻ᵏ` is uniformly Lipschitz on
times bounded away from zero.  The bound is independent of `nu`, hence of both the cutoff
dimension and spectral radius.  Spectral transport and boundedness of strongly convergent
varying-space vectors then make the cutoff equicontinuity hypothesis in positive-time semigroup
compilers automatic.
-/

open Filter Set Topology Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.ImplicitEuler

/-- A reciprocal affine function with nonnegative slope is uniformly Lipschitz on a positive
half-line, with a constant independent of the slope. -/
theorem abs_inv_one_add_mul_sub_inv_one_add_mul_le
    {c a s t : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hs : a ≤ s) (ht : a ≤ t) :
    |(1 + t * c)⁻¹ - (1 + s * c)⁻¹| ≤ |t - s| / a := by
  have hs0 : 0 ≤ s := le_trans ha.le hs
  have ht0 : 0 ≤ t := le_trans ha.le ht
  have hS : 0 < 1 + s * c := by positivity
  have hT : 0 < 1 + t * c := by positivity
  have hid :
      (1 + t * c)⁻¹ - (1 + s * c)⁻¹ =
        ((s - t) * c) / ((1 + t * c) * (1 + s * c)) := by
    field_simp
    ring
  have hcoeff : c * a ≤ (1 + t * c) * (1 + s * c) := by
    have hca : c * a ≤ t * c := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_right ht hc
    have hfirst : c * a ≤ 1 + t * c := hca.trans (le_add_of_nonneg_left zero_le_one)
    have hsecond : 1 ≤ 1 + s * c :=
      le_add_of_nonneg_right (mul_nonneg hs0 hc)
    calc
      c * a ≤ 1 + t * c := hfirst
      _ = (1 + t * c) * 1 := by ring
      _ ≤ (1 + t * c) * (1 + s * c) :=
        mul_le_mul_of_nonneg_left hsecond hT.le
  rw [hid, abs_div, abs_mul, abs_of_nonneg hc, abs_mul,
    abs_of_pos hT, abs_of_pos hS, div_le_div_iff₀ (mul_pos hT hS) ha]
  simpa [abs_sub_comm, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hcoeff (abs_nonneg (t - s))

/-- Fixed-order implicit-Euler multipliers are uniformly Lipschitz on a positive half-line,
uniformly over the nonnegative spectral parameter. -/
theorem abs_multiplier_mul_sub_multiplier_mul_le
    {k : ℕ} (hk : 0 < k) {nu a s t : ℝ} (hnu : 0 ≤ nu)
    (ha : 0 < a) (hs : a ≤ s) (ht : a ≤ t) :
    |multiplier k (t * nu) - multiplier k (s * nu)| ≤ |t - s| / a := by
  let c : ℝ := nu / (k : ℝ)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : 0 ≤ c := div_nonneg hnu hkR.le
  have hderiv : ∀ u ∈ Ici a,
      HasDerivAt (fun y : ℝ => (1 + y * c)⁻¹ ^ k)
        (-((k : ℝ) * c) / (1 + u * c) ^ (k + 1)) u := by
    intro u hu
    have hu0 : 0 ≤ u := ha.le.trans hu
    have hden : 0 < 1 + u * c := by positivity
    have hg : HasDerivAt (fun y : ℝ => 1 + y * c) c u := by
      simpa using ((hasDerivAt_id u).mul_const c).const_add 1
    have hp := (hg.inv hden.ne').pow k
    have hp' : HasDerivAt (fun y : ℝ => (1 + y * c)⁻¹ ^ k)
        ((k : ℝ) * (1 + u * c)⁻¹ ^ (k - 1) * (-c / (1 + u * c) ^ 2)) u := by
      exact hp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)
    convert hp' using 1
    rw [show k + 1 = (k - 1) + 2 by omega, pow_add, pow_two, inv_pow]
    field_simp [hden.ne']
  have hbound : ∀ u ∈ Ici a,
      ‖deriv (fun y : ℝ => (1 + y * c)⁻¹ ^ k) u‖ ≤ 1 / a := by
    intro u hu
    have hu0 : 0 ≤ u := ha.le.trans hu
    have hden : 0 < 1 + u * c := by positivity
    have hdenOne : 1 ≤ 1 + u * c :=
      le_add_of_nonneg_right (mul_nonneg hu0 hc)
    have hbern : 1 + (k : ℝ) * (u * c) ≤ (1 + u * c) ^ k :=
      one_add_mul_le_pow (by nlinarith [mul_nonneg hu0 hc]) k
    have hkau : (k : ℝ) * c * a ≤ (k : ℝ) * c * u :=
      mul_le_mul_of_nonneg_left hu (mul_nonneg (Nat.cast_nonneg _) hc)
    have hkac : (k : ℝ) * c * a ≤ (1 + u * c) ^ (k + 1) := by
      calc
        (k : ℝ) * c * a ≤ (k : ℝ) * c * u := hkau
        _ = (k : ℝ) * (u * c) := by ring
        _ ≤ 1 + (k : ℝ) * (u * c) := le_add_of_nonneg_left zero_le_one
        _ ≤ (1 + u * c) ^ k := hbern
        _ = (1 + u * c) ^ k * 1 := by ring
        _ ≤ (1 + u * c) ^ k * (1 + u * c) :=
          mul_le_mul_of_nonneg_left hdenOne (pow_nonneg hden.le _)
        _ = (1 + u * c) ^ (k + 1) := by rw [pow_succ]
    rw [(hderiv u hu).deriv, Real.norm_eq_abs, abs_div, abs_neg, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hc,
      abs_pow, abs_of_pos hden]
    rw [div_le_div_iff₀ (pow_pos hden _) ha]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hkac
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Ici a) (x := s) (y := t)
    (fun u hu => (hderiv u hu).differentiableAt) hbound (convex_Ici a) hs ht
  change |((1 + (t * nu) / (k : ℝ))⁻¹) ^ k -
    ((1 + (s * nu) / (k : ℝ))⁻¹) ^ k| ≤ _
  have hf_t : (1 + t * c)⁻¹ ^ k =
      ((1 + (t * nu) / (k : ℝ))⁻¹) ^ k := by
    dsimp [c]
    congr 3
    ring
  have hf_s : (1 + s * c)⁻¹ ^ k =
      ((1 + (s * nu) / (k : ℝ))⁻¹) ^ k := by
    dsimp [c]
    congr 3
    ring
  rw [← hf_t, ← hf_s]
  simpa [Real.norm_eq_abs, abs_sub_comm, div_eq_mul_inv, mul_comm] using hmv
universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The diagonal finite Euler family inherits the scalar dimension-free Lipschitz estimate. -/
theorem norm_finiteSpectralEuler_sub_le
    (nu : ι → ℝ) (k : ℕ) (hk : 0 < k) (hnu : ∀ i, 0 ≤ nu i)
    {a s t : ℝ} (ha : 0 < a) (hs : a ≤ s) (ht : a ≤ t) :
    ‖finiteSpectralEuler nu t k - finiteSpectralEuler nu s k‖ ≤
      |t - s| / a := by
  have htarget : 0 ≤ |t - s| / a := by positivity
  have hdiag :
      finiteSpectralEuler nu t k - finiteSpectralEuler nu s k =
        Matrix.diagonal (fun i ↦
          ((multiplier k (t * nu i) - multiplier k (s * nu i) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [finiteSpectralEuler]
    · simp [finiteSpectralEuler, hij]
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg htarget).2
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_multiplier_mul_sub_multiplier_mul_le hk (hnu i) ha hs ht

/-- Unitary spectral transport preserves the fixed-order Lipschitz estimate. -/
theorem norm_finiteUnitarySpectralEuler_sub_le
    (U : Matrix.unitaryGroup ι ℂ) (nu : ι → ℝ) (k : ℕ) (hk : 0 < k)
    (hnu : ∀ i, 0 ≤ nu i) {a s t : ℝ} (ha : 0 < a) (hs : a ≤ s) (ht : a ≤ t) :
    ‖finiteUnitarySpectralEuler U nu t k - finiteUnitarySpectralEuler U nu s k‖ ≤
      |t - s| / a := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have hsub :
      finiteUnitarySpectralEuler U nu t k - finiteUnitarySpectralEuler U nu s k =
        e (finiteSpectralEuler nu t k - finiteSpectralEuler nu s k) := by
    change e (finiteSpectralEuler nu t k) - e (finiteSpectralEuler nu s k) =
      e (finiteSpectralEuler nu t k - finiteSpectralEuler nu s k)
    exact (map_sub e _ _).symm
  rw [hsub]
  change ‖(U : Matrix ι ι ℂ) *
      (finiteSpectralEuler nu t k - finiteSpectralEuler nu s k) *
      (star U : Matrix ι ι ℂ)‖ ≤ _
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul]
  exact norm_finiteSpectralEuler_sub_le nu k hk hnu ha hs ht

/-- Canonical finite Hermitian Euler multipliers satisfy a dimension- and spectrum-independent
positive-time Lipschitz bound. -/
theorem norm_finiteHermitianEuler_sub_le
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (k : ℕ) (hk : 0 < k)
    {a s t : ℝ} (ha : 0 < a) (hs : a ≤ s) (ht : a ≤ t) :
    ‖finiteHermitianEuler hA.1 t k - finiteHermitianEuler hA.1 s k‖ ≤
      |t - s| / a :=
  norm_finiteUnitarySpectralEuler_sub_le hA.1.eigenvectorUnitary hA.1.eigenvalues
    k hk hA.eigenvalues_nonneg ha hs ht

/-- Literal finite Hermitian resolvent powers satisfy the same positive-time operator-norm
Lipschitz bound. -/
theorem norm_finiteHermitianEulerResolventOperator_sub_le
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (k : ℕ) (hk : 0 < k)
    {a s t : ℝ} (ha : 0 < a) (hs : a ≤ s) (ht : a ≤ t) :
    ‖finiteHermitianEulerResolventOperator A t k -
        finiteHermitianEulerResolventOperator A s k‖ ≤
      |t - s| / a := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
      (((1 : Matrix ι ι ℂ) + (((t / (k : ℝ) : ℝ) : ℂ) • A))⁻¹ ^ k) -
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
      (((1 : Matrix ι ι ℂ) + (((s / (k : ℝ) : ℝ) : ℂ) • A))⁻¹ ^ k)‖ ≤ _
  rw [← map_sub]
  change ‖((1 : Matrix ι ι ℂ) + (((t / (k : ℝ) : ℝ) : ℂ) • A))⁻¹ ^ k -
      ((1 : Matrix ι ι ℂ) + (((s / (k : ℝ) : ℝ) : ℂ) • A))⁻¹ ^ k‖ ≤ _
  rw [← finiteHermitianEuler_eq_inv_one_add_smul_pow hA.1 t k
      (le_trans ha.le ht) hk hA.eigenvalues_nonneg,
    ← finiteHermitianEuler_eq_inv_one_add_smul_pow hA.1 s k
      (le_trans ha.le hs) hk hA.eigenvalues_nonneg]
  exact norm_finiteHermitianEuler_sub_le hA k hk ha hs ht

end NCG.ImplicitEuler

namespace NCG.VaryingHilbert.System

universe u v

variable {ι : ℕ → Type u}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- On a compact set of strictly positive times, fixed-order finite Hermitian Euler trajectories
of every strongly convergent varying-space vector family are automatically equicontinuous. -/
theorem equicontinuousOn_finiteHermitianEulerResolventOperator
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (k : ℕ) (hk : 0 < k) (s : Set ℝ) (hs : IsCompact s)
    (hsPos : ∀ t ∈ s, 0 < t)
    (x : ∀ n, EuclideanSpace ℂ (ι n)) (xlim : H)
    (hx : J.StronglyConverges x xlim) :
    EquicontinuousOn
      (fun n t ↦ J.embedding n
        (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator (A n) t k (x n))) s := by
  by_cases hsempty : s = ∅
  · subst s
    intro t ht
    exact ht.elim
  obtain ⟨a, haMem, haMin⟩ := hs.exists_isMinOn (Set.nonempty_iff_ne_empty.mpr hsempty)
    continuous_id.continuousOn
  have ha : 0 < a := hsPos a haMem
  obtain ⟨C, hC, hCbound⟩ := hx.exists_pos_uniform_norm_bound J
  let L : NNReal := ⟨C / a, by positivity⟩
  have hLip : ∀ n, LipschitzOnWith L
      (fun t ↦ J.embedding n
        (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator (A n) t k (x n))) s := by
    intro n
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro t ht s' hs'
    have hat : a ≤ t := haMin ht
    have has' : a ≤ s' := haMin hs'
    rw [← map_sub]
    change ‖J.embedding n
      ((NCG.ImplicitEuler.finiteHermitianEulerResolventOperator (A n) t k -
        NCG.ImplicitEuler.finiteHermitianEulerResolventOperator (A n) s' k) (x n))‖ ≤ _
    rw [(J.embedding n).norm_map]
    calc
      ‖(NCG.ImplicitEuler.finiteHermitianEulerResolventOperator (A n) t k -
          NCG.ImplicitEuler.finiteHermitianEulerResolventOperator (A n) s' k) (x n)‖
          ≤ ‖NCG.ImplicitEuler.finiteHermitianEulerResolventOperator (A n) t k -
              NCG.ImplicitEuler.finiteHermitianEulerResolventOperator (A n) s' k‖ *
              ‖x n‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (|t - s'| / a) * C :=
        mul_le_mul
          (NCG.ImplicitEuler.norm_finiteHermitianEulerResolventOperator_sub_le
            (hA n) k hk ha has' hat)
          (hCbound n) (norm_nonneg _) (by positivity)
      _ = (L : ℝ) * ‖t - s'‖ := by
        rw [Real.norm_eq_abs]
        change (|t - s'| / a) * C = (C / a) * |t - s'|
        ring
  exact (LipschitzOnWith.uniformEquicontinuousOn _ L hLip).equicontinuousOn

/-- Away from time zero, the whole two-index family of cutoff Euler powers is uniformly
equicontinuous simultaneously in the cutoff and in the Euler order.  The common modulus is the
key extra information supplied by the sharp scalar derivative estimate. -/
theorem uniformEquicontinuousOn_finiteHermitianEulerResolventOperator_allOrders
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t)
    (x : ∀ n, EuclideanSpace ℂ (ι n)) (xlim : H)
    (hx : J.StronglyConverges x xlim) :
    UniformEquicontinuousOn
      (fun p : ℕ × ℕ => fun t ↦ J.embedding p.2
        (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
          (A p.2) t (p.1 + 1) (x p.2))) s := by
  by_cases hsempty : s = ∅
  · simp [hsempty, uniformEquicontinuousOn_iff_uniformContinuousOn, UniformContinuousOn]
  obtain ⟨a, haMem, haMin⟩ := hs.exists_isMinOn (Set.nonempty_iff_ne_empty.mpr hsempty)
    continuous_id.continuousOn
  have ha : 0 < a := hsPos a haMem
  obtain ⟨C, hC, hCbound⟩ := hx.exists_pos_uniform_norm_bound J
  let L : NNReal := ⟨C / a, by positivity⟩
  have hLip : ∀ p : ℕ × ℕ, LipschitzOnWith L
      (fun t ↦ J.embedding p.2
        (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
          (A p.2) t (p.1 + 1) (x p.2))) s := by
    intro p
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro t ht s' hs'
    have hat : a ≤ t := haMin ht
    have has' : a ≤ s' := haMin hs'
    rw [← map_sub]
    change ‖J.embedding p.2
      ((NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
          (A p.2) t (p.1 + 1) -
        NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
          (A p.2) s' (p.1 + 1)) (x p.2))‖ ≤ _
    rw [(J.embedding p.2).norm_map]
    calc
      ‖(NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
          (A p.2) t (p.1 + 1) -
        NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
          (A p.2) s' (p.1 + 1)) (x p.2)‖
          ≤ ‖NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
                (A p.2) t (p.1 + 1) -
              NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
                (A p.2) s' (p.1 + 1)‖ * ‖x p.2‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ (|t - s'| / a) * C :=
        mul_le_mul
          (NCG.ImplicitEuler.norm_finiteHermitianEulerResolventOperator_sub_le
            (hA p.2) (p.1 + 1) (Nat.succ_pos p.1) ha has' hat)
          (hCbound p.2) (norm_nonneg _) (by positivity)
      _ = (L : ℝ) * ‖t - s'‖ := by
        rw [Real.norm_eq_abs]
        change (|t - s'| / a) * C = (C / a) * |t - s'|
        ring
  exact LipschitzOnWith.uniformEquicontinuousOn _ L hLip
end NCG.VaryingHilbert.System
