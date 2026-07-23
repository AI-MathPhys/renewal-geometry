/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.ModularClock
import NCG.Upstream.KMSDual

/-!
# Modular eigenoperator criteria and the affine renewal clock

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:primitive-transfer` — the averaged renewal transfer
  `Φ̄ = ∑ p_σ Φ_σ` and primitivity;
* `thm:modular-eigenoperator-criteria` — for a faithful state with
  spectral resolution `ρ = ∑ r_j P_j`, the flow, commutator, and
  multiplicative eigenoperator conditions are equivalent, and hold
  iff every nonvanishing spectral block satisfies
  `log r_j − log r_k = β`;
* `cor:canonical-anti-family-weight` — every elementary channel
  preserving the transfer's stationary weight has a unital (UCP)
  KMS/Petz dual relative to it;
* `thm:upstream-affine-clock` — grading commutation, one common
  modular exponent, and a scalar joint commutant force
  `H_ρ = β N + c 1` with `c` real (the affine modular clock), and
  spectrally `ρ = e^{βN}/Tr(e^{βN})`;
* `cor:beta-extraction` — the exact extraction formulas: the
  centred-trace formula for `β`, and the consecutive-shell ratio
  `e^β = (Tr(P_{n+1}ρ)/d_{n+1})/(Tr(P_nρ)/d_n)`.
-/

namespace NCG.Upstream

open NCG

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-! ## `def:primitive-transfer` -/

/-- **Definition `def:primitive-transfer`**: the averaged Heisenberg
renewal transfer `Φ̄ = ∑_σ p_σ Φ_σ`. -/
noncomputable def averagedTransfer {ι : Type*} [Fintype ι]
    (prob : ι → ℝ) (Φ : ι → (A →ₗ[ℂ] A)) : A →ₗ[ℂ] A :=
  ∑ σ, (prob σ : ℂ) • Φ σ

/-- **Definition `def:primitive-transfer` (primitivity)**: some
power of the (Schrödinger) transfer maps every nonzero positive
element to a strictly positive one. -/
def IsPrimitive [PartialOrder A] (T : A →ₗ[ℂ] A)
    (strictPos : A → Prop) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ ∀ X : A, 0 ≤ X → X ≠ 0 → strictPos (T ^ m • X)

/-! ## `cor:canonical-anti-family-weight` -/

section AntiFamily

variable [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [StarModule ℂ A]
variable (τ : A →ₗ[ℂ] ℂ) (σ σi : A)
variable (hσi : σ * σi = 1) (hiσ : σi * σ = 1)

include hσi hiσ in
/-- **Corollary `cor:canonical-anti-family-weight`**: relative to
the faithful stationary weight of the transfer law, every elementary
channel whose predual fixes the weight has a *unital* KMS/Petz
anti-renewal dual (`thm:canonical-anti-renewal` applies branchwise);
without channelwise stationarity the dual exists but need not be
unital — unitality is exactly stationarity. -/
theorem canonical_anti_family (Φs : A →ₗ[ℂ] A) :
    (antiDual σ σi Φs 1 = 1 ↔ Φs (σ * σ) = σ * σ) :=
  antiDual_unital_iff σ σi hσi hiσ

end AntiFamily

/-! ## `thm:modular-eigenoperator-criteria`: the spectral model -/

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (r : ι → ℝ) (P : ι → A)

/-- Orthogonal resolution of the identity. -/
structure IsSpectralResolution : Prop where
  orth : ∀ j k, P j * P k = if j = k then P j else 0
  total : ∑ j, P j = 1

variable {r P}

/-- Block decomposition `S = ∑_{jk} P_j S P_k`. -/
theorem block_decomposition (hP : IsSpectralResolution P) (S : A) :
    S = ∑ j, ∑ k, P j * S * P k := by
  have h2 : ∀ j, ∑ k, P j * S * P k = P j * S := by
    intro j
    rw [← Finset.mul_sum, hP.total, mul_one]
  rw [Finset.sum_congr rfl fun j _ => h2 j, ← Finset.sum_mul,
    hP.total, one_mul]

/-- Block extraction: multiplying by `P_a`, `P_b` isolates one
block of a double block sum. -/
theorem block_extract (hP : IsSpectralResolution P)
    (c : ι → ι → ℂ) (S : A) (a b : ι) :
    P a * (∑ j, ∑ k, c j k • (P j * S * P k)) * P b
      = c a b • (P a * S * P b) := by
  have hterm : ∀ j k, P a * (c j k • (P j * S * P k)) * P b
      = c j k • ((P a * P j) * S * (P k * P b)) := by
    intro j k
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    noncomm_ring
  calc P a * (∑ j, ∑ k, c j k • (P j * S * P k)) * P b
      = ∑ j, ∑ k, P a * (c j k • (P j * S * P k)) * P b := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ j, ∑ k, c j k • ((P a * P j) * S * (P k * P b)) :=
        Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => hterm j k
    _ = c a b • (P a * S * P b) := by
        rw [Finset.sum_eq_single a
          (fun j _ hj => Finset.sum_eq_zero fun k _ => by
            rw [hP.orth a j, if_neg (fun h => hj h.symm), zero_mul,
              zero_mul, smul_zero])
          (fun h => absurd (Finset.mem_univ a) h)]
        rw [Finset.sum_eq_single b
          (fun k _ hk => by
            rw [hP.orth k b, if_neg hk, mul_zero, smul_zero])
          (fun h => absurd (Finset.mem_univ b) h)]
        rw [hP.orth a a, if_pos rfl, hP.orth b b, if_pos rfl]

variable (r P) in
/-- The faithful state `ρ = ∑ r_j P_j`. -/
noncomputable def specState : A := ∑ j, ((r j : ℝ) : ℂ) • P j

variable (r P) in
/-- The modular Hamiltonian `H_ρ = log ρ = ∑ (log r_j) P_j`. -/
noncomputable def specHamiltonian : A :=
  ∑ j, ((Real.log (r j) : ℝ) : ℂ) • P j

variable (r P) in
/-- The modular flow `σ_t^ρ(a) = ρ^{it} a ρ^{-it}`, spectrally:
`∑_{jk} e^{it(log r_j − log r_k)} P_j a P_k`. -/
noncomputable def specFlow (t : ℝ) (a : A) : A :=
  ∑ j, ∑ k, Complex.exp (Complex.I * t
    * ((Real.log (r j) - Real.log (r k) : ℝ) : ℂ)) • (P j * a * P k)

/-- Left multiplication by a spectral sum, in block form. -/
theorem spectral_mul (hP : IsSpectralResolution P) (f : ι → ℂ)
    (S : A) :
    (∑ j, f j • P j) * S = ∑ j, ∑ k, f j • (P j * S * P k) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc]
  have h2 : P j * S = ∑ k, P j * S * P k := by
    rw [← Finset.mul_sum, hP.total, mul_one]
  conv_lhs => rw [h2]
  rw [Finset.smul_sum]

/-- Right multiplication by a spectral sum, in block form. -/
theorem mul_spectral (hP : IsSpectralResolution P) (f : ι → ℂ)
    (S : A) :
    S * (∑ k, f k • P k) = ∑ j, ∑ k, f k • (P j * S * P k) := by
  rw [Finset.mul_sum]
  have h1 : ∀ k, S * (f k • P k) = ∑ j, f k • (P j * S * P k) := by
    intro k
    rw [mul_smul_comm]
    have h2 : S * P k = ∑ j, P j * S * P k := by
      have h3 : S * P k = (∑ j, P j) * (S * P k) := by
        rw [hP.total, one_mul]
      rw [h3, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      noncomm_ring
    rw [h2, Finset.smul_sum]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]

/-- Equality of block sums is blockwise equality. -/
theorem block_sum_eq_iff (hP : IsSpectralResolution P) (S : A)
    (c d : ι → ι → ℂ) :
    (∑ j, ∑ k, c j k • (P j * S * P k))
        = (∑ j, ∑ k, d j k • (P j * S * P k))
      ↔ ∀ j k, c j k • (P j * S * P k) = d j k • (P j * S * P k) := by
  constructor
  · intro h j k
    have h2 := congrArg (fun X => P j * X * P k) h
    rw [block_extract hP c S j k, block_extract hP d S j k] at h2
    exact h2
  · intro h
    exact Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => h j k

/-- Scalar comparison on a block. -/
theorem block_smul_eq_iff [NoZeroSMulDivisors ℂ A] (c d : ℂ)
    (X : A) : c • X = d • X ↔ X = 0 ∨ c = d := by
  constructor
  · intro h
    have h2 : (c - d) • X = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact Or.inr (sub_eq_zero.mp h3)
    · exact Or.inl h3
  · rintro (h | h)
    · rw [h, smul_zero, smul_zero]
    · rw [h]

/-- Equal complex exponentials for all real times have equal
frequencies. -/
theorem exp_it_eq_iff {θ β : ℝ}
    (h : ∀ t : ℝ, Complex.exp (Complex.I * t * θ)
      = Complex.exp (Complex.I * t * β)) : θ = β := by
  by_contra hne
  have hd0 : θ - β ≠ 0 := sub_ne_zero.mpr hne
  have hsub : ((θ : ℂ) - β) ≠ 0 := by
    rw [show ((θ : ℂ) - β) = ((θ - β : ℝ) : ℂ) from by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr hd0
  have h1 := h (Real.pi / (θ - β))
  push_cast at h1
  have h2 : Complex.exp (Complex.I * ((Real.pi : ℂ) / ((θ : ℂ) - β)) * θ
      - Complex.I * ((Real.pi : ℂ) / ((θ : ℂ) - β)) * β) = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 : Complex.I * ((Real.pi : ℂ) / ((θ : ℂ) - β)) * θ
      - Complex.I * ((Real.pi : ℂ) / ((θ : ℂ) - β)) * β
      = (Real.pi : ℂ) * Complex.I := by
    calc Complex.I * ((Real.pi : ℂ) / ((θ : ℂ) - β)) * θ
          - Complex.I * ((Real.pi : ℂ) / ((θ : ℂ) - β)) * β
        = Complex.I * ((Real.pi : ℂ) / ((θ : ℂ) - β) * ((θ : ℂ) - β)) := by
          ring
      _ = Complex.I * (Real.pi : ℂ) := by
          rw [div_mul_cancel₀ _ hsub]
      _ = (Real.pi : ℂ) * Complex.I := by ring
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

variable [NoZeroSMulDivisors ℂ A]

/-- **Theorem `thm:modular-eigenoperator-criteria` ((ii) ↔ block)**:
`[H_ρ, S] = β S` iff every nonvanishing spectral block satisfies
`log r_j − log r_k = β`. -/
theorem criteria_commutator_iff_block (hP : IsSpectralResolution P)
    (S : A) (β : ℝ) :
    specHamiltonian r P * S - S * specHamiltonian r P
        = ((β : ℝ) : ℂ) • S
      ↔ ∀ j k, P j * S * P k ≠ 0 →
          Real.log (r j) - Real.log (r k) = β := by
  rw [specHamiltonian, spectral_mul hP, mul_spectral hP]
  rw [← Finset.sum_sub_distrib]
  have hj : ∀ j, ((∑ k, ((Real.log (r j) : ℝ) : ℂ) • (P j * S * P k))
        - ∑ k, ((Real.log (r k) : ℝ) : ℂ) • (P j * S * P k))
      = ∑ k, (((Real.log (r j) - Real.log (r k) : ℝ) : ℂ))
          • (P j * S * P k) := by
    intro j
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_smul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => hj j]
  rw [show (((β : ℝ) : ℂ) • S : A)
      = ∑ j, ∑ k, ((β : ℝ) : ℂ) • (P j * S * P k) from by
    conv_lhs => rw [block_decomposition hP S]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]]
  rw [block_sum_eq_iff hP]
  constructor
  · intro h j k hne
    rcases (block_smul_eq_iff _ _ _).mp (h j k) with h2 | h2
    · exact absurd h2 hne
    · exact_mod_cast h2
  · intro h j k
    by_cases hX : P j * S * P k = 0
    · rw [hX, smul_zero, smul_zero]
    · rw [h j k hX]

/-- **Theorem `thm:modular-eigenoperator-criteria` ((iii) ↔
block)**: `ρ S = e^β S ρ` iff every nonvanishing spectral block
satisfies `log r_j − log r_k = β`. -/
theorem criteria_multiplicative_iff_block
    (hP : IsSpectralResolution P) (hr : ∀ j, 0 < r j)
    (S : A) (β : ℝ) :
    IsModularEigen (specState r P) S β
      ↔ ∀ j k, P j * S * P k ≠ 0 →
          Real.log (r j) - Real.log (r k) = β := by
  unfold IsModularEigen
  rw [specState, spectral_mul hP, mul_spectral hP]
  rw [show ((Real.exp β : ℝ) : ℂ)
        • (∑ j, ∑ k, ((r k : ℝ) : ℂ) • (P j * S * P k))
      = ∑ j, ∑ k, ((Real.exp β * r k : ℝ) : ℂ)
          • (P j * S * P k) from by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul]
    congr 1
    push_cast
    ring]
  rw [block_sum_eq_iff hP]
  constructor
  · intro h j k hne
    rcases (block_smul_eq_iff _ _ _).mp (h j k) with h2 | h2
    · exact absurd h2 hne
    · have h3 : r j = Real.exp β * r k := by exact_mod_cast h2
      rw [h3, Real.log_mul (Real.exp_ne_zero β) (hr k).ne',
        Real.log_exp]
      ring
  · intro h j k
    by_cases hX : P j * S * P k = 0
    · rw [hX, smul_zero, smul_zero]
    · have h2 := h j k hX
      have h3 : r j = Real.exp β * r k := by
        have h4 : Real.log (r j) = β + Real.log (r k) := by
          linarith
        calc r j = Real.exp (Real.log (r j)) :=
              (Real.exp_log (hr j)).symm
          _ = Real.exp (β + Real.log (r k)) := by rw [h4]
          _ = Real.exp β * r k := by
              rw [Real.exp_add, Real.exp_log (hr k)]
      rw [show ((r j : ℝ) : ℂ) = ((Real.exp β * r k : ℝ) : ℂ) from
        by exact_mod_cast h3]

/-- **Theorem `thm:modular-eigenoperator-criteria` ((i) ↔ block)**:
`σ_t^ρ(S) = e^{itβ} S` for all `t` iff every nonvanishing spectral
block satisfies `log r_j − log r_k = β`. -/
theorem criteria_flow_iff_block (hP : IsSpectralResolution P)
    (S : A) (β : ℝ) :
    (∀ t : ℝ, specFlow r P t S
        = Complex.exp (Complex.I * t * β) • S)
      ↔ ∀ j k, P j * S * P k ≠ 0 →
          Real.log (r j) - Real.log (r k) = β := by
  have hrw : ∀ t : ℝ, (Complex.exp (Complex.I * t * β) • S
      = ∑ j, ∑ k, Complex.exp (Complex.I * t * β)
          • (P j * S * P k)) := by
    intro t
    conv_lhs => rw [block_decomposition hP S]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
  constructor
  · intro h j k hne
    refine exp_it_eq_iff fun t => ?_
    have h2 := h t
    rw [specFlow, hrw t, block_sum_eq_iff hP] at h2
    rcases (block_smul_eq_iff _ _ _).mp (h2 j k) with h3 | h3
    · exact absurd h3 hne
    · exact h3
  · intro h t
    rw [specFlow, hrw t, block_sum_eq_iff hP]
    intro j k
    by_cases hX : P j * S * P k = 0
    · rw [hX, smul_zero, smul_zero]
    · rw [h j k hX]

end Spectral

/-! ## `thm:upstream-affine-clock` -/

section AffineClock

variable [StarRing A] [StarModule ℂ A] [NoZeroSMulDivisors ℂ A]
  [Nontrivial A]

/-- **Theorem `thm:upstream-affine-clock` (the affine clock)**: a
common modular exponent on the graded resets with scalar joint
commutant forces `H_ρ = β N + c 1` with real `c`. -/
theorem upstream_affine_clock (H N : A) (hHsa : star H = H)
    (hNsa : star N = N) {ι' : Type*} (S : ι' → A) (β : ℝ)
    (hgrade : ∀ e, N * S e - S e * N = S e)
    (heig : ∀ e, H * S e - S e * H = ((β : ℝ) : ℂ) • S e)
    (hcommutant : ∀ X : A, (∀ e, X * S e = S e * X) →
      (∀ e, X * star (S e) = star (S e) * X) → ∃ c : ℂ, X = c • 1) :
    ∃ c : ℝ, H = ((β : ℝ) : ℂ) • N + ((c : ℝ) : ℂ) • 1 := by
  set X : A := H - ((β : ℝ) : ℂ) • N with hX
  have hXsa : star X = X := by
    rw [hX, star_sub, hHsa, star_smul, hNsa]
    congr 1
    rw [show star (((β : ℝ) : ℂ)) = ((β : ℝ) : ℂ) from by
      rw [Complex.star_def, Complex.conj_ofReal]]
  have hXcomm : ∀ e, X * S e = S e * X := by
    intro e
    have h1 := heig e
    have h2 := hgrade e
    have h3 : X * S e - S e * X
        = (H * S e - S e * H)
          - ((β : ℝ) : ℂ) • (N * S e - S e * N) := by
      rw [hX]
      rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub]
      abel
    rw [h1, h2, sub_self] at h3
    exact sub_eq_zero.mp h3
  have hXcommStar : ∀ e, X * star (S e) = star (S e) * X := by
    intro e
    have h1 := congrArg star (hXcomm e)
    rw [star_mul, star_mul, hXsa] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := hcommutant X hXcomm hXcommStar
  have hcreal : star c = c := by
    have h1 := congrArg star hc
    rw [hXsa, star_smul, star_one] at h1
    rw [hc] at h1
    have h2 : (star c - c) • (1 : A) = 0 := by
      rw [sub_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 one_ne_zero
  refine ⟨c.re, ?_⟩
  have hcre : c = ((c.re : ℝ) : ℂ) := by
    have := Complex.conj_eq_iff_re.mp hcreal
    exact this.symm
  rw [← hcre, ← hc, hX]
  abel

/-- **Theorem `thm:affine-clock` (weighted affine clock)**: with
depth-weighted grading `[N, S_e] = ℓ_e S_e` and matching modular
eigenvalue relation `[H, S_e] = β ℓ_e S_e` on every elementary reset
(general edge depths `ℓ_e`, as in the manuscript statement), a scalar
joint commutant forces `H = β N + c·1` with real `c`. -/
theorem upstream_affine_clock_weighted (H N : A) (hHsa : star H = H)
    (hNsa : star N = N) {ι' : Type*} (S : ι' → A) (β : ℝ) (ℓ : ι' → ℝ)
    (hgrade : ∀ e, N * S e - S e * N = ((ℓ e : ℝ) : ℂ) • S e)
    (heig : ∀ e, H * S e - S e * H = ((β * ℓ e : ℝ) : ℂ) • S e)
    (hcommutant : ∀ X : A, (∀ e, X * S e = S e * X) →
      (∀ e, X * star (S e) = star (S e) * X) → ∃ c : ℂ, X = c • 1) :
    ∃ c : ℝ, H = ((β : ℝ) : ℂ) • N + ((c : ℝ) : ℂ) • 1 := by
  set X : A := H - ((β : ℝ) : ℂ) • N with hX
  have hXsa : star X = X := by
    rw [hX, star_sub, hHsa, star_smul, hNsa]
    congr 1
    rw [show star (((β : ℝ) : ℂ)) = ((β : ℝ) : ℂ) from by
      rw [Complex.star_def, Complex.conj_ofReal]]
  have hXcomm : ∀ e, X * S e = S e * X := by
    intro e
    have h1 := heig e
    have h2 := hgrade e
    have h3 : X * S e - S e * X
        = (H * S e - S e * H)
          - ((β : ℝ) : ℂ) • (N * S e - S e * N) := by
      rw [hX]
      rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub]
      abel
    rw [h1, h2, smul_smul,
      show ((β : ℝ) : ℂ) * ((ℓ e : ℝ) : ℂ) = ((β * ℓ e : ℝ) : ℂ) from by
        push_cast; ring,
      sub_self] at h3
    exact sub_eq_zero.mp h3
  have hXcommStar : ∀ e, X * star (S e) = star (S e) * X := by
    intro e
    have h1 := congrArg star (hXcomm e)
    rw [star_mul, star_mul, hXsa] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := hcommutant X hXcomm hXcommStar
  have hcreal : star c = c := by
    have h1 := congrArg star hc
    rw [hXsa, star_smul, star_one] at h1
    rw [hc] at h1
    have h2 : (star c - c) • (1 : A) = 0 := by
      rw [sub_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 one_ne_zero
  refine ⟨c.re, ?_⟩
  have hcre : c = ((c.re : ℝ) : ℂ) := by
    have := Complex.conj_eq_iff_re.mp hcreal
    exact this.symm
  rw [← hcre, ← hc, hX]
  abel

end AffineClock

/-! ## `cor:beta-extraction` -/

section BetaExtraction

variable (τ : A →ₗ[ℂ] ℂ)

/-- **Corollary `cor:beta-extraction` (centred trace formula)**:
`β = τ((N − τ(N)1) log ρ)/τ((N − τ(N)1)²)`. -/
theorem beta_extraction_trace (hτ1 : τ 1 = 1) (H N : A) (β c : ℝ)
    (hclock : H = ((β : ℝ) : ℂ) • N + ((c : ℝ) : ℂ) • 1)
    (hden : τ ((N - τ N • 1) * (N - τ N • 1)) ≠ 0) :
    τ ((N - τ N • 1) * H) / τ ((N - τ N • 1) * (N - τ N • 1))
      = ((β : ℝ) : ℂ) := by
  set M : A := N - τ N • 1 with hM
  have hτM : τ M = 0 := by
    rw [hM, map_sub, map_smul, hτ1, smul_eq_mul, mul_one, sub_self]
  have hnum : τ (M * H) = ((β : ℝ) : ℂ) * τ (M * M) := by
    rw [hclock, mul_add, map_add, mul_smul_comm, map_smul,
      mul_smul_comm, map_smul, mul_one, hτM, smul_zero, add_zero]
    have hMN : M * N = M * M + τ N • M := by
      have h5 : M * N = M * (M + τ N • 1) := by
        congr 1
        rw [hM]
        abel
      rw [h5, mul_add, mul_smul_comm, mul_one]
    rw [hMN, map_add, map_smul, hτM, smul_zero, add_zero,
      smul_eq_mul]
  rw [hnum, mul_div_assoc, div_self hden, mul_one]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Corollary `cor:beta-extraction` (shell ratios)** /
**Theorem `thm:upstream-affine-clock` (normalized form)**: for
`ρ = Z⁻¹ ∑ e^{β n_j} Q_j` (the spectral form of
`e^{βN}/Tr e^{βN}`), the normalized shell traces of consecutive
levels have ratio exactly `e^β`. -/
theorem beta_extraction_shell (nval : ι → ℝ) (Q : ι → A)
    (hQ : IsSpectralResolution Q) (Z : ℝ) (hZ : (Z : ℂ) ≠ 0)
    (β : ℝ) (j1 j0 : ι)
    (hd1 : τ (Q j1) ≠ 0) (hd0 : τ (Q j0) ≠ 0)
    (hstep : nval j1 = nval j0 + 1) :
    (τ (Q j1 * ((Z : ℂ)⁻¹
        • ∑ j, ((Real.exp (β * nval j) : ℝ) : ℂ) • Q j)) / τ (Q j1))
      / (τ (Q j0 * ((Z : ℂ)⁻¹
        • ∑ j, ((Real.exp (β * nval j) : ℝ) : ℂ) • Q j)) / τ (Q j0))
      = ((Real.exp β : ℝ) : ℂ) := by
  have hval : ∀ a : ι, τ (Q a * ((Z : ℂ)⁻¹
      • ∑ j, ((Real.exp (β * nval j) : ℝ) : ℂ) • Q j))
      = (Z : ℂ)⁻¹ * ((Real.exp (β * nval a) : ℝ) : ℂ)
        * τ (Q a) := by
    intro a
    rw [mul_smul_comm, map_smul, Finset.mul_sum, map_sum]
    rw [Finset.sum_eq_single a
      (fun k _ hk => by
        rw [mul_smul_comm, map_smul, hQ.orth a k,
          if_neg (fun h => hk h.symm), map_zero, smul_zero])
      (fun h => absurd (Finset.mem_univ a) h)]
    rw [mul_smul_comm, map_smul, hQ.orth a a, if_pos rfl,
      smul_eq_mul, smul_eq_mul]
    ring
  rw [hval j1, hval j0]
  rw [hstep]
  have hexp0 : ((Real.exp (β * nval j0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hexp1 : ((Real.exp (β * (nval j0 + 1)) : ℝ) : ℂ)
      = ((Real.exp β : ℝ) : ℂ)
        * ((Real.exp (β * nval j0) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp1]
  field_simp

end BetaExtraction

end NCG.Upstream
