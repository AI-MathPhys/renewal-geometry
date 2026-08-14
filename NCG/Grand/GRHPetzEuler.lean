/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar
import NCG.Algebra.SchwarzMap

/-!
# Finite Petz–Euler sufficient certificate
  (`thm:GRH-Petz-Euler`, Gran-Tensor manuscript)

* `grh_petz_euler`:
  (1) the faithfulness engine: for a faithful state density
      `ρ ≻ 0`, `Tr(ρ·dᴴd) = 0` forces `d = 0`;
  (2) uniqueness of the `ω`-preserving conditional
      expectation: two maps into the Euler subalgebra with the
      same `ω`-adjointness relations against the subalgebra
      coincide (the Takesaki uniqueness clause);
  (3) the Kadison–Schwarz Gram order: a Schwarz map satisfies
      `(Py)ᴴ(Py) ⪯ P(yᴴy)`, which applied to the completed
      source words gives the boxed `Ê_X ⪯ M̂_X`.

Rendering disclosed: the existence half of Takesaki's
criterion (modular invariance `ρ^{it}Nρ^{-it} = N` constructs
the expectation) is the manuscript's finite modular-theory
step; the matrix-amplified ("complete") version of the Gram
order is clause (3) applied entrywise to every matrix of
source-word combinations; compatibility with the nuisance
short is the declared preservation hypothesis.
-/

open Matrix Module
open scoped ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:GRH-Petz-Euler`. -/
theorem grh_petz_euler {n : Type*} [Fintype n]
    [DecidableEq n] :
    -- (1) faithfulness of the physical state
    (∀ ρ d : Matrix n n ℂ, ρ.PosDef →
      (ρ * (dᴴ * d)).trace = 0 → d = 0)
    -- (2) uniqueness of the ω-preserving expectation
    ∧ (∀ ρ : Matrix n n ℂ, ρ.PosDef →
        ∀ (N : Subalgebra ℂ (Matrix n n ℂ))
          (P P' : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ),
        (∀ x, P x ∈ N) → (∀ x, P' x ∈ N) →
        (∀ (x m : Matrix n n ℂ), m ∈ N →
          (ρ * (mᴴ * P x)).trace = (ρ * (mᴴ * x)).trace) →
        (∀ (x m : Matrix n n ℂ), m ∈ N →
          (ρ * (mᴴ * P' x)).trace = (ρ * (mᴴ * x)).trace) →
        ∀ x, P x = P' x)
    -- (3) the Kadison–Schwarz Gram order
    ∧ (∀ P : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ,
        IsSchwarzMap P →
        ∀ y : Matrix n n ℂ, (P y)ᴴ * P y ≤ P (yᴴ * y)) := by
  have hfaithful : ∀ ρ d : Matrix n n ℂ, ρ.PosDef →
      (ρ * (dᴴ * d)).trace = 0 → d = 0 := by
    intro ρ d hρ h0
    haveI := (sqrt_isUnit hρ).invertible
    have hs2 : CFC.sqrt ρ * CFC.sqrt ρ = ρ :=
      sqrt_mul_self_eq ρ hρ.posSemidef
    have hkey : ((d * CFC.sqrt ρ)ᴴ
        * (d * CFC.sqrt ρ)).trace = 0 := by
      rw [Matrix.conjTranspose_mul, sqrt_isHermitian]
      calc (CFC.sqrt ρ * dᴴ * (d * CFC.sqrt ρ)).trace
          = ((CFC.sqrt ρ * (dᴴ * d)) * CFC.sqrt ρ).trace := by
            congr 1
            simp only [Matrix.mul_assoc]
        _ = (CFC.sqrt ρ * (CFC.sqrt ρ * (dᴴ * d))).trace :=
            Matrix.trace_mul_comm _ _
        _ = (ρ * (dᴴ * d)).trace := by
            rw [← Matrix.mul_assoc, hs2]
        _ = 0 := h0
    have hzero : d * CFC.sqrt ρ = 0 :=
      Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hkey
    have h := congrArg (fun M => M * (CFC.sqrt ρ)⁻¹) hzero
    simpa [Matrix.mul_assoc, Matrix.mul_inv_of_invertible]
      using h
  refine ⟨hfaithful, ?_, ?_⟩
  · intro ρ hρ N P P' hPN hP'N hPadj hP'adj x
    have hd : P x - P' x ∈ N := sub_mem (hPN x) (hP'N x)
    have h0 : (ρ * ((P x - P' x)ᴴ * (P x - P' x))).trace
        = 0 := by
      rw [show (P x - P' x)ᴴ * (P x - P' x)
          = (P x - P' x)ᴴ * P x - (P x - P' x)ᴴ * P' x from
        Matrix.mul_sub _ _ _,
        Matrix.mul_sub, Matrix.trace_sub,
        hPadj x _ hd, hP'adj x _ hd, sub_self]
    have := hfaithful ρ (P x - P' x) hρ h0
    exact sub_eq_zero.mp this
  · intro P hP y
    have h := hP y
    rwa [Matrix.star_eq_conjTranspose,
      Matrix.star_eq_conjTranspose] at h

/-- `thm:GRH-Petz-Euler` (existence half, now proved):
the `ω`-orthogonal conditional expectation onto the Euler
subalgebra — existence, uniqueness, state preservation,
the Takesaki bimodule property from finite modular
invariance, and the boxed complete Gram order at every
matrix amplification. -/
theorem grh_petz_euler_expectation {n : Type*}
    [Fintype n] [DecidableEq n]
    (N : Subalgebra ℂ (Matrix n n ℂ))
    (hstar : ∀ a ∈ N, aᴴ ∈ N)
    (ρ : Matrix n n ℂ) (hρ : ρ.PosDef)
    (hinv : ∀ a ∈ N, ρ⁻¹ * a * ρ ∈ N) :
    ∃ P : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ,
      (∀ x, P x ∈ N)
      ∧ (∀ a ∈ N, P a = a)
      ∧ (∀ (x a : Matrix n n ℂ), a ∈ N →
          (ρ * aᴴ * (x - P x)).trace = 0)
      ∧ (∀ Q : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ,
          (∀ x, Q x ∈ N) →
          (∀ (x a : Matrix n n ℂ), a ∈ N →
            (ρ * aᴴ * (x - Q x)).trace = 0) → Q = P)
      ∧ (∀ x, (ρ * P x).trace = (ρ * x).trace)
      ∧ (∀ (x a : Matrix n n ℂ), a ∈ N →
          P (a * x) = a * P x)
      ∧ (∀ (x a : Matrix n n ℂ), a ∈ N →
          P (x * a) = P x * a)
      ∧ (∀ {ι : Type} [Fintype ι]
          (v : ι → Matrix n n ℂ) (c : ι → ℂ),
          (∑ i, ∑ j, star (c i) * c j *
            (ρ * (P (v i))ᴴ * (P (v j))).trace).re
          ≤ (∑ i, ∑ j, star (c i) * c j *
            (ρ * (v i)ᴴ * (v j)).trace).re) := by
  classical
  have hρu : IsUnit ρ.det :=
    (Matrix.isUnit_iff_isUnit_det ρ).mp hρ.isUnit
  have hfaithful : ∀ d : Matrix n n ℂ,
      (ρ * (dᴴ * d)).trace = 0 → d = 0 := by
    intro d hd
    exact (grh_petz_euler (n := n)).1 ρ d hρ hd
  -- the second-slot GNS functionals
  set ℓ : Matrix n n ℂ → (Matrix n n ℂ →ₗ[ℂ] ℂ) :=
    fun a =>
    { toFun := fun y => (ρ * aᴴ * y).trace
      map_add' := fun y z => by
        rw [Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun c y => by
        rw [Matrix.mul_smul, Matrix.trace_smul]
        rfl } with hℓ
  have hℓapp : ∀ a y : Matrix n n ℂ,
      ℓ a y = (ρ * aᴴ * y).trace := fun a y => rfl
  -- hermitian symmetry of the form
  have hBsymm : ∀ x y : Matrix n n ℂ,
      ℓ y x = star (ℓ x y) := by
    intro x y
    rw [hℓapp, hℓapp, ← Matrix.trace_conjTranspose]
    rw [Matrix.conjTranspose_mul (ρ * xᴴ) y,
      Matrix.conjTranspose_mul ρ xᴴ,
      Matrix.conjTranspose_conjTranspose, hρ.1.eq]
    calc (ρ * yᴴ * x).trace
        = (x * (ρ * yᴴ)).trace :=
          Matrix.trace_mul_comm _ _
      _ = ((x * ρ) * yᴴ).trace := by
          rw [Matrix.mul_assoc]
      _ = (yᴴ * (x * ρ)).trace :=
          Matrix.trace_mul_comm _ _
  -- positivity of the diagonal form values
  have hSherm : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ :=
    sqrt_isHermitian ρ
  have hSS : CFC.sqrt ρ * CFC.sqrt ρ = ρ :=
    sqrt_mul_self_eq ρ hρ.posSemidef
  have hBform : ∀ x : Matrix n n ℂ, ℓ x x
      = ((x * CFC.sqrt ρ)ᴴ
          * (x * CFC.sqrt ρ)).trace := by
    intro x
    rw [hℓapp]
    rw [Matrix.conjTranspose_mul, hSherm]
    calc (ρ * xᴴ * x).trace
        = (CFC.sqrt ρ * CFC.sqrt ρ * xᴴ * x).trace := by
          rw [hSS]
      _ = (CFC.sqrt ρ * (CFC.sqrt ρ * xᴴ * x)).trace := by
          simp only [Matrix.mul_assoc]
      _ = ((CFC.sqrt ρ * xᴴ * x) * CFC.sqrt ρ).trace :=
          Matrix.trace_mul_comm _ _
      _ = (CFC.sqrt ρ * xᴴ * (x * CFC.sqrt ρ)).trace := by
          simp only [Matrix.mul_assoc]
  have hBdiag_nonneg : ∀ x : Matrix n n ℂ,
      (0 : ℂ) ≤ ℓ x x := by
    intro x
    rw [hBform]
    exact (Matrix.posSemidef_conjTranspose_mul_self
      _).trace_nonneg
  have hBzero : ∀ x : Matrix n n ℂ,
      ℓ x x = 0 → x = 0 := by
    intro x hx
    apply hfaithful x
    rw [hℓapp] at hx
    rw [← Matrix.mul_assoc]
    exact hx
  -- the orthogonal complement of the subalgebra
  set Perp : Submodule ℂ (Matrix n n ℂ) :=
    ⨅ a : N.toSubmodule,
      LinearMap.ker (ℓ (a : Matrix n n ℂ)) with hPerp
  have hPerpMem : ∀ x : Matrix n n ℂ,
      x ∈ Perp ↔ ∀ a ∈ N, ℓ a x = 0 := by
    intro x
    rw [hPerp, Submodule.mem_iInf]
    constructor
    · intro h a ha
      have := h ⟨a, ha⟩
      simpa [LinearMap.mem_ker] using this
    · intro h a
      simp only [LinearMap.mem_ker]
      exact h (a : Matrix n n ℂ) a.2
  -- disjointness by faithfulness
  have hdisj : N.toSubmodule ⊓ Perp = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    apply hBzero
    exact (hPerpMem x).mp (Submodule.mem_inf.mp hx).2
      x (Submodule.mem_inf.mp hx).1
  -- codisjointness by rank-nullity
  set k := finrank ℂ N.toSubmodule with hk
  set b := Module.finBasis ℂ N.toSubmodule with hb
  set Ψ : Matrix n n ℂ →ₗ[ℂ] (Fin k → ℂ) :=
    LinearMap.pi (fun i => ℓ ((b i : N.toSubmodule) :
      Matrix n n ℂ)) with hΨ
  have hkerΨ : LinearMap.ker Ψ = Perp := by
    ext x
    rw [LinearMap.mem_ker, hPerpMem]
    constructor
    · intro hx a ha
      have hrep : (a : Matrix n n ℂ)
          = ∑ i, b.repr ⟨a, ha⟩ i •
            ((b i : N.toSubmodule) : Matrix n n ℂ) := by
        have hsum := b.sum_repr ⟨a, ha⟩
        calc (a : Matrix n n ℂ)
            = ((⟨a, ha⟩ : N.toSubmodule) :
              Matrix n n ℂ) := rfl
          _ = ((∑ i, b.repr ⟨a, ha⟩ i • b i :
              N.toSubmodule) : Matrix n n ℂ) := by
              rw [hsum]
          _ = ∑ i, b.repr ⟨a, ha⟩ i •
              ((b i : N.toSubmodule) :
                Matrix n n ℂ) := by
              push_cast
              rfl
      rw [hBsymm, hrep]
      have hexp : ℓ x (∑ i, b.repr ⟨a, ha⟩ i •
          ((b i : N.toSubmodule) : Matrix n n ℂ))
          = ∑ i, b.repr ⟨a, ha⟩ i *
            ℓ x ((b i : N.toSubmodule) :
              Matrix n n ℂ) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        rfl
      rw [hexp, star_sum]
      apply Finset.sum_eq_zero
      intro i _
      have hxi : ℓ ((b i : N.toSubmodule) :
          Matrix n n ℂ) x = 0 := congrFun hx i
      rw [star_mul']
      rw [← hBsymm, hxi, mul_zero]
    · intro hx
      funext i
      exact hx ((b i : N.toSubmodule) : Matrix n n ℂ)
        (b i).2
  have hsup : N.toSubmodule ⊔ Perp = ⊤ := by
    have hrank :=
      LinearMap.finrank_range_add_finrank_ker Ψ
    have hrange : finrank ℂ (LinearMap.range Ψ) ≤ k := by
      calc finrank ℂ (LinearMap.range Ψ)
          ≤ finrank ℂ (Fin k → ℂ) :=
            Submodule.finrank_le _
        _ = k := by
            rw [finrank_pi]
            simp
    have hkerdim : finrank ℂ Perp
        = finrank ℂ (LinearMap.ker Ψ) := by
      rw [hkerΨ]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      N.toSubmodule Perp
    rw [hdisj] at h1
    simp only [finrank_bot, add_zero] at h1
    have h2 := Submodule.finrank_le
      (N.toSubmodule ⊔ Perp)
    apply Submodule.eq_top_of_finrank_eq
    omega
  have hcompl : IsCompl N.toSubmodule Perp :=
    ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsup⟩
  -- the GNS-orthogonal conditional expectation
  set P : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
    N.toSubmodule.projection Perp hcompl with hPdef
  have hPmem : ∀ x, P x ∈ N :=
    fun x => Submodule.projection_apply_mem hcompl x
  have hPfix : ∀ a ∈ N, P a = a := fun a ha =>
    Submodule.projection_apply_of_mem_left hcompl ha
  have hPdefect : ∀ x, x - P x ∈ Perp := by
    intro x
    have hs :=
      Submodule.projection_add_projection_eq_self
        hcompl x
    rw [← hPdef] at hs
    have heq : x - P x = Perp.projection N.toSubmodule
        hcompl.symm x := by
      calc x - P x
          = (P x + Perp.projection N.toSubmodule
              hcompl.symm x) - P x := by rw [hs]
        _ = Perp.projection N.toSubmodule
              hcompl.symm x := by abel
    rw [heq]
    exact Submodule.projection_apply_mem hcompl.symm x
  have horth : ∀ (x a : Matrix n n ℂ), a ∈ N →
      (ρ * aᴴ * (x - P x)).trace = 0 := by
    intro x a ha
    exact (hPerpMem (x - P x)).mp (hPdefect x) a ha
  -- the unique-decomposition workhorse
  have huniq_dec : ∀ (z u : Matrix n n ℂ), u ∈ N →
      z - u ∈ Perp → P z = u := by
    intro z u huN hzu
    have h1 : P z - u ∈ N.toSubmodule :=
      Submodule.sub_mem _ (hPmem z) huN
    have h2 : P z - u ∈ Perp := by
      have heq : P z - u = (z - u) - (z - P z) := by
        abel
      rw [heq]
      exact Submodule.sub_mem _ hzu (hPdefect z)
    have h3 : P z - u ∈ N.toSubmodule ⊓ Perp :=
      Submodule.mem_inf.mpr ⟨h1, h2⟩
    rw [hdisj, Submodule.mem_bot] at h3
    exact sub_eq_zero.mp h3
  refine ⟨P, hPmem, hPfix, horth, ?_, ?_, ?_, ?_, ?_⟩
  · -- uniqueness
    intro Q hQmem hQorth
    apply LinearMap.ext
    intro x
    have hQdef : x - Q x ∈ Perp := by
      rw [hPerpMem]
      intro a ha
      exact hQorth x a ha
    exact (huniq_dec x (Q x) (hQmem x) hQdef).symm
  · -- state preservation
    intro x
    have h1 := horth x 1 (one_mem N)
    rw [Matrix.conjTranspose_one, Matrix.mul_one,
      Matrix.mul_sub, Matrix.trace_sub] at h1
    have h2 : (ρ * x).trace = (ρ * P x).trace :=
      sub_eq_zero.mp h1
    exact h2.symm
  · -- left module property
    intro x a ha
    apply huniq_dec
    · exact mul_mem ha (hPmem x)
    · rw [hPerpMem]
      intro m hm
      have hz : mᴴ * a = (aᴴ * m)ᴴ := by
        rw [Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
      have hstep : ρ * mᴴ * (a * x - a * P x)
          = ρ * (aᴴ * m)ᴴ * (x - P x) := by
        rw [← Matrix.mul_sub a, ← hz]
        simp only [Matrix.mul_assoc]
      rw [hℓapp, hstep]
      exact horth x (aᴴ * m) (mul_mem (hstar a ha) hm)
  · -- right module property (the modular step)
    intro x a ha
    apply huniq_dec
    · exact mul_mem (hPmem x) ha
    · rw [hPerpMem]
      intro m hm
      set w : Matrix n n ℂ := ρ⁻¹ * a * ρ with hw
      have hwN : w ∈ N := hinv a ha
      have hρw : a * ρ = ρ * w := by
        rw [hw, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv ρ hρu,
          Matrix.one_mul]
      rw [hℓapp]
      have hstep : ρ * mᴴ * (x * a - P x * a)
          = ρ * mᴴ * ((x - P x) * a) := by
        rw [Matrix.sub_mul]
      rw [hstep]
      calc (ρ * mᴴ * ((x - P x) * a)).trace
          = (a * (ρ * mᴴ * (x - P x))).trace := by
            rw [← Matrix.mul_assoc]
            exact Matrix.trace_mul_comm _ a
        _ = ((a * ρ) * (mᴴ * (x - P x))).trace := by
            simp only [Matrix.mul_assoc]
        _ = ((ρ * w) * (mᴴ * (x - P x))).trace := by
            rw [hρw]
        _ = (ρ * (m * wᴴ)ᴴ * (x - P x)).trace := by
            rw [Matrix.conjTranspose_mul,
              Matrix.conjTranspose_conjTranspose]
            simp only [Matrix.mul_assoc]
        _ = 0 :=
            horth x (m * wᴴ)
              (mul_mem hm (hstar w hwN))
  · -- the boxed complete Gram order
    intro ι _ v c
    set u : Matrix n n ℂ := ∑ j, c j • v j with hu
    have hgram : ∀ f : ι → Matrix n n ℂ,
        (∑ i, ∑ j, star (c i) * c j *
          (ρ * (f i)ᴴ * (f j)).trace)
        = ℓ (∑ i, c i • f i) (∑ j, c j • f j) := by
      intro f
      have hsecond : ∀ z : Matrix n n ℂ,
          ℓ z (∑ j, c j • f j)
          = ∑ j, c j * ℓ z (f j) := by
        intro z
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul]
        rfl
      have hfirst : ∀ y : Matrix n n ℂ,
          ℓ (∑ i, c i • f i) y
          = ∑ i, star (c i) * ℓ (f i) y := by
        intro y
        rw [hBsymm, hsecond, star_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [star_mul', ← hBsymm]
      rw [hfirst]
      apply Finset.sum_congr rfl
      intro i _
      rw [hsecond, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hℓapp]
      ring
    have hPu : ∑ j, c j • P (v j) = P u := by
      rw [hu, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul]
    rw [hgram v, hgram (fun i => P (v i)), hPu, ← hu]
    -- orthogonal Pythagoras
    set y : Matrix n n ℂ := u - P u with hy
    have hyPerp : y ∈ Perp := hPdefect u
    have hcross1 : ℓ (P u) y = 0 :=
      (hPerpMem y).mp hyPerp (P u) (hPmem u)
    have hcross2 : ℓ y (P u) = 0 := by
      rw [hBsymm, hcross1, star_zero]
    have hdecomp : ℓ u u = ℓ (P u) (P u) + ℓ y y := by
      have hu2 : u = P u + y := by
        rw [hy]
        abel
      have hadd2 : ∀ z : Matrix n n ℂ,
          ℓ z (P u + y) = ℓ z (P u) + ℓ z y :=
        fun z => map_add (ℓ z) _ _
      have hadd1 : ℓ (P u + y) (P u + y)
          = ℓ (P u) (P u + y) + ℓ y (P u + y) := by
        rw [hBsymm, hadd2, star_add, ← hBsymm,
          ← hBsymm]
      calc ℓ u u = ℓ (P u + y) (P u + y) := by
            rw [← hu2]
        _ = ℓ (P u) (P u) + ℓ (P u) y
            + (ℓ y (P u) + ℓ y y) := by
            rw [hadd1, hadd2, hadd2]
        _ = ℓ (P u) (P u) + ℓ y y := by
            rw [hcross1, hcross2]
            ring
    rw [hdecomp]
    have hynn := hBdiag_nonneg y
    rw [Complex.le_def] at hynn
    obtain ⟨h1, _⟩ := hynn
    rw [Complex.zero_re] at h1
    simp only [Complex.add_re]
    linarith

end NCG
