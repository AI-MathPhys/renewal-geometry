import NCG.Grand.GRHPetzEuler
import NCG.Upstream.ModularSpectral
import Mathlib.LinearAlgebra.Lagrange

open Matrix Module
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace FiniteModular

open NCG.Upstream

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The logarithmic spectral gap attached to a matrix block. -/
noncomputable def gap (r : ι → ℝ) (j k : ι) : ℂ :=
  (Real.log (r j) - Real.log (r k) : ℝ)

/-- The blockwise action of a scalar function of the modular gap. -/
noncomputable def gapAction (P : ι → Matrix n n ℂ)
    (c : ι → ι → ℂ) (a : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ j, ∑ k, c j k • (P j * a * P k)

lemma gapAction_one (P : ι → Matrix n n ℂ)
    (hP : IsSpectralResolution P) (a : Matrix n n ℂ) :
    gapAction P (fun _ _ => 1) a = a := by
  simp only [gapAction, one_smul]
  exact (block_decomposition hP a).symm

lemma gapAction_comp (P : ι → Matrix n n ℂ)
    (hP : IsSpectralResolution P) (c d : ι → ι → ℂ)
    (a : Matrix n n ℂ) :
    gapAction P c (gapAction P d a) =
      gapAction P (fun j k => c j k * d j k) a := by
  classical
  unfold gapAction
  rw [Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ =>
      block_extract hP d a j k]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_smul]

lemma hasDerivAt_specFlow (r : ι → ℝ)
    (P : ι → Matrix n n ℂ) (a : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => specFlow r P s a)
      (gapAction P (fun j k =>
        Complex.I * gap r j k *
          Complex.exp (Complex.I * t * gap r j k)) a) t := by
  classical
  unfold specFlow gapAction gap
  apply HasDerivAt.sum
  intro j _
  apply HasDerivAt.sum
  intro k _
  have he : HasDerivAt
      (fun s : ℝ => Complex.exp
        (Complex.I * s *
          ((Real.log (r j) - Real.log (r k) : ℝ) : ℂ)))
      (Complex.I *
        ((Real.log (r j) - Real.log (r k) : ℝ) : ℂ) *
        Complex.exp (Complex.I * t *
          ((Real.log (r j) - Real.log (r k) : ℝ) : ℂ))) t := by
    convert (Complex.hasDerivAt_exp _).comp_ofReal t
      (((hasDerivAt_id t).ofReal_const_mul Complex.I).mul_const
        ((Real.log (r j) - Real.log (r k) : ℝ) : ℂ)) using 1 <;> ring
  convert he.smul_const (P j * a * P k) using 1 <;> ring

lemma derivative_mem_of_mem (N : Subalgebra ℂ (Matrix n n ℂ))
    (f : ℝ → Matrix n n ℂ) (f' : Matrix n n ℂ)
    (hf : ∀ t, f t ∈ N) (hd : HasDerivAt f f' 0) : f' ∈ N := by
  have hclosed : IsClosed (N.toSubmodule : Set (Matrix n n ℂ)) :=
    N.toSubmodule.closed_of_finiteDimensional
  apply hclosed.mem_of_tendsto hd.tendsto_slope
  filter_upwards with t ht
  rw [slope]
  exact N.toSubmodule.smul_mem
    ((t - 0)⁻¹ : ℝ) (N.toSubmodule.sub_mem (hf t) (hf 0))

lemma gapAction_add (P : ι → Matrix n n ℂ)
    (c d : ι → ι → ℂ) (a : Matrix n n ℂ) :
    gapAction P (fun j k => c j k + d j k) a =
      gapAction P c a + gapAction P d a := by
  classical
  simp only [gapAction, add_smul, Finset.sum_add_distrib]

lemma gapAction_const_mul (P : ι → Matrix n n ℂ)
    (z : ℂ) (c : ι → ι → ℂ) (a : Matrix n n ℂ) :
    gapAction P (fun j k => z * c j k) a =
      z • gapAction P c a := by
  classical
  simp only [gapAction, mul_smul, Finset.smul_sum]

/-- Real-time invariance of a finite spectral modular flow forces
invariance under its logarithmic generator.  This is the finite-dimensional
closed-subspace step in Takesaki's criterion. -/
lemma gapAction_mem_of_flow_invariant
    (N : Subalgebra ℂ (Matrix n n ℂ))
    (r : ι → ℝ) (P : ι → Matrix n n ℂ)
    (a : Matrix n n ℂ) (ha : a ∈ N)
    (hflow : ∀ t : ℝ, specFlow r P t a ∈ N) :
    gapAction P (gap r) a ∈ N := by
  have hd := hasDerivAt_specFlow r P a 0
  have hm := derivative_mem_of_mem N
    (fun t => specFlow r P t a)
    (gapAction P (fun j k =>
      Complex.I * gap r j k *
        Complex.exp (Complex.I * 0 * gap r j k)) a)
    hflow hd
  have hs := N.toSubmodule.smul_mem (-Complex.I) hm
  convert hs using 1
  simp only [mul_zero, Complex.exp_zero, mul_one]
  rw [← gapAction_const_mul]
  apply congrArg (fun c => gapAction P c a)
  funext j k
  ring

lemma gapAction_pow_mem
    (N : Subalgebra ℂ (Matrix n n ℂ))
    (P : ι → Matrix n n ℂ) (hP : IsSpectralResolution P)
    (g : ι → ι → ℂ)
    (hgen : ∀ b ∈ N, gapAction P g b ∈ N) :
    ∀ m : ℕ, ∀ a ∈ N,
      gapAction P (fun j k => (g j k) ^ m) a ∈ N := by
  intro m
  induction m with
  | zero =>
      intro a ha
      simpa using ha
  | succ m ih =>
      intro a ha
      have hm := ih a ha
      have hnext := hgen (gapAction P (fun j k => (g j k) ^ m) a) hm
      rw [gapAction_comp P hP] at hnext
      convert hnext using 1
      apply congrArg (fun c => gapAction P c a)
      funext j k
      simp [pow_succ']

/-- Every polynomial in the finite modular generator preserves an invariant
subalgebra. -/
lemma polynomialGapAction_mem
    (N : Subalgebra ℂ (Matrix n n ℂ))
    (P : ι → Matrix n n ℂ) (hP : IsSpectralResolution P)
    (g : ι → ι → ℂ)
    (hgen : ∀ b ∈ N, gapAction P g b ∈ N)
    (q : ℂ[X]) (a : Matrix n n ℂ) (ha : a ∈ N) :
    gapAction P (fun j k => q.eval (g j k)) a ∈ N := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show (fun j k => (p + q).eval (g j k)) =
          fun j k => p.eval (g j k) + q.eval (g j k) by
        funext j k
        simp]
      rw [gapAction_add]
      exact N.toSubmodule.add_mem (hp a ha) (hq a ha)
  | monomial m z =>
      rw [show (fun j k => (Polynomial.monomial m z).eval (g j k)) =
          fun j k => z * (g j k) ^ m by
        funext j k
        simp [Polynomial.eval_monomial]]
      rw [gapAction_const_mul]
      exact N.toSubmodule.smul_mem z
        (gapAction_pow_mem N P hP g hgen m a ha)

/-- Real modular invariance automatically extends to the imaginary time
`-i`, expressed spectrally by the weight `exp (-gap)`.  Finiteness is used
only through polynomial interpolation on the finite family of gaps. -/
theorem imaginaryTime_mem_of_flow_invariant
    (N : Subalgebra ℂ (Matrix n n ℂ))
    (r : ι → ℝ) (P : ι → Matrix n n ℂ)
    (hP : IsSpectralResolution P)
    (hflow : ∀ (t : ℝ) (a : Matrix n n ℂ), a ∈ N →
      specFlow r P t a ∈ N)
    (a : Matrix n n ℂ) (ha : a ∈ N) :
    gapAction P (fun j k => Complex.exp (-gap r j k)) a ∈ N := by
  let x : ι × ι → ℂ := fun u => gap r u.1 u.2
  let y : ι × ι → ℂ := fun u => Complex.exp (-gap r u.1 u.2)
  have hcompat : ∀ u v, x u = x v → y u = y v := by
    intro u v huv
    simp only [x, y] at huv ⊢
    rw [huv]
  obtain ⟨q, hq⟩ :=
    (Polynomial.exists_eval_eq_iff x y).2 hcompat
  have hgen : ∀ b ∈ N, gapAction P (gap r) b ∈ N := by
    intro b hb
    exact gapAction_mem_of_flow_invariant N r P b hb
      (fun t => hflow t b hb)
  have hpoly := polynomialGapAction_mem N P hP (gap r) hgen q a ha
  convert hpoly using 1
  apply congrArg (fun c => gapAction P c a)
  funext j k
  exact (hq (j, k)).symm

/-- The spectral inverse of a faithful finite density. -/
noncomputable def specInv (r : ι → ℝ)
    (P : ι → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ j, (((r j)⁻¹ : ℝ) : ℂ) • P j

lemma specInv_mul_specState (r : ι → ℝ)
    (P : ι → Matrix n n ℂ) (hP : IsSpectralResolution P)
    (hr : ∀ j, 0 < r j) :
    specInv r P * specState r P = 1 := by
  classical
  unfold specInv specState
  rw [Finset.sum_mul]
  calc
    (∑ j, (((r j)⁻¹ : ℝ) : ℂ) • P j *
        ∑ k, ((r k : ℝ) : ℂ) • P k)
        = ∑ j, P j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          rw [Finset.sum_eq_single j]
          · rw [smul_mul, mul_smul_comm, hP.orth j j, if_pos rfl,
              smul_smul]
            convert one_smul ℂ (P j) using 1
            push_cast
            field_simp [(hr j).ne']
          · intro k _ hkj
            rw [smul_mul, mul_smul_comm, hP.orth j k,
              if_neg (Ne.symm hkj), smul_zero]
          · intro hj
            exact absurd (Finset.mem_univ j) hj
    _ = 1 := hP.total

lemma specInv_eq_inv (r : ι → ℝ)
    (P : ι → Matrix n n ℂ) (hP : IsSpectralResolution P)
    (hr : ∀ j, 0 < r j) :
    specInv r P = (specState r P)⁻¹ := by
  exact (Matrix.inv_eq_left_inv (specInv_mul_specState r P hP hr)).symm

lemma specInv_conjugate_eq_gapAction (r : ι → ℝ)
    (P : ι → Matrix n n ℂ) (hP : IsSpectralResolution P)
    (hr : ∀ j, 0 < r j) (a : Matrix n n ℂ) :
    (specState r P)⁻¹ * a * specState r P =
      gapAction P (fun j k => Complex.exp (-gap r j k)) a := by
  classical
  rw [← specInv_eq_inv r P hP hr]
  unfold specInv specState
  rw [spectral_mul hP]
  change gapAction P (fun j k => (((r j)⁻¹ : ℝ) : ℂ)) a *
      (∑ k, ((r k : ℝ) : ℂ) • P k) = _
  rw [mul_spectral hP]
  rw [gapAction_comp P hP]
  apply congrArg (fun c => gapAction P c a)
  funext j k
  change ((((r j)⁻¹ : ℝ) : ℂ) * ((r k : ℝ) : ℂ)) =
    Complex.exp (-((Real.log (r j) - Real.log (r k) : ℝ) : ℂ))
  rw [← Complex.ofReal_exp]
  push_cast
  rw [show -(Real.log (r j) - Real.log (r k)) =
      Real.log (r k) - Real.log (r j) by ring,
    Real.exp_sub, Real.exp_log (hr k), Real.exp_log (hr j)]
  field_simp [(hr j).ne']

/-- Exact finite Takesaki bridge: invariance under every real modular time
implies the inverse-conjugation condition used by the Petz expectation. -/
theorem inverse_conjugate_mem_of_flow_invariant
    (N : Subalgebra ℂ (Matrix n n ℂ))
    (r : ι → ℝ) (P : ι → Matrix n n ℂ)
    (hP : IsSpectralResolution P) (hr : ∀ j, 0 < r j)
    (hflow : ∀ (t : ℝ) (a : Matrix n n ℂ), a ∈ N →
      specFlow r P t a ∈ N) :
    ∀ a ∈ N,
      (specState r P)⁻¹ * a * specState r P ∈ N := by
  intro a ha
  rw [specInv_conjugate_eq_gapAction r P hP hr a]
  exact imaginaryTime_mem_of_flow_invariant N r P hP hflow a ha

/-- `thm:GRH-Petz-Euler`, with the manuscript's real modular-invariance
hypothesis.  The finite spectral presentation is lossless for a faithful
density; the theorem constructs the unique state-preserving conditional
expectation, both bimodule laws, and the complete Gram contraction. -/
theorem grhPetzEuler_of_modularInvariant
    (N : Subalgebra ℂ (Matrix n n ℂ))
    (hstar : ∀ a ∈ N, aᴴ ∈ N)
    (r : ι → ℝ) (Pspec : ι → Matrix n n ℂ)
    (hP : IsSpectralResolution Pspec) (hr : ∀ j, 0 < r j)
    (hρ : (specState r Pspec).PosDef)
    (hflow : ∀ (t : ℝ) (a : Matrix n n ℂ), a ∈ N →
      specFlow r Pspec t a ∈ N) :
    ∃ E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ,
      (∀ x, E x ∈ N)
      ∧ (∀ a ∈ N, E a = a)
      ∧ (∀ (x a : Matrix n n ℂ), a ∈ N →
          (specState r Pspec * aᴴ * (x - E x)).trace = 0)
      ∧ (∀ Q : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ,
          (∀ x, Q x ∈ N) →
          (∀ (x a : Matrix n n ℂ), a ∈ N →
            (specState r Pspec * aᴴ * (x - Q x)).trace = 0) → Q = E)
      ∧ (∀ x, (specState r Pspec * E x).trace =
          (specState r Pspec * x).trace)
      ∧ (∀ (x a : Matrix n n ℂ), a ∈ N → E (a * x) = a * E x)
      ∧ (∀ (x a : Matrix n n ℂ), a ∈ N → E (x * a) = E x * a)
      ∧ (∀ {κ : Type} [Fintype κ]
          (v : κ → Matrix n n ℂ) (c : κ → ℂ),
          (∑ i, ∑ j, star (c i) * c j *
            (specState r Pspec * (E (v i))ᴴ * (E (v j))).trace).re
          ≤ (∑ i, ∑ j, star (c i) * c j *
            (specState r Pspec * (v i)ᴴ * (v j)).trace).re) := by
  apply grh_petz_euler_expectation N hstar (specState r Pspec) hρ
  exact inverse_conjugate_mem_of_flow_invariant N r Pspec hP hr hflow

end FiniteModular
end NCG
