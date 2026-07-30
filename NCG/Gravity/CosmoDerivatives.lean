/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cosmological derivative identities and the one-crossing lemma
(GR_emergence, Phase 1)

* `flatness_attractor_hasDerivAt`, `log_omega_eq` —
  `cor:renewal-flatness-attractor`: with `Ω_k = -k/(a²H²)` and
  `ȧ = aH`, the exact identity `d/dt log|Ω_k| = -2H - 2Ḣ/H`;
* `comoving_matter_depletion`, `comoving_matter_deficit_nonneg`,
  `matter_density_le_free` — `thm:comoving-matter-depletion` and
  `cor:phantom-matter-deficit`;
* `berry_antihermitian` — `lem:berry-antiherm`;
* `constant_rate_energy_identity`, `phi_strictMonoOn` —
  `lem:constant-rate-energy`;
* `neg_after_zero_of_deriv_neg`, `pos_before_zero_of_deriv_neg`,
  `at_most_one_zero_of_deriv_neg`, `local_clock_one_crossing` —
  `prop:local-clock-one-crossing`: a differentiable function with
  strictly negative derivative at each of its zeros is negative just
  after and positive just before any zero (the `+ → -` crossing
  direction) and has at most one zero; applied to
  `Ḃ = S(t) - F(B)` with `S' < 0` and `F` differentiable.
-/

namespace NCG

open Real Filter Set Topology

/-! ## `cor:renewal-flatness-attractor` -/

/-- `cor:renewal-flatness-attractor`: with `Ω_k(t) = -k/(a²H²)` and
the FLRW relation `ȧ = aH`, one has the exact flatness-attractor
identity `d/dt log|Ω_k| = -2H - 2Ḣ/H`. -/
theorem flatness_attractor_hasDerivAt (k : ℝ)
    (a H : ℝ → ℝ) (t : ℝ) (H' : ℝ)
    (ha : HasDerivAt a (a t * H t) t) (hH : HasDerivAt H H' t)
    (ha0 : a t ≠ 0) (hH0 : H t ≠ 0) :
    HasDerivAt (fun s => Real.log (-k) - 2 * Real.log (a s)
        - 2 * Real.log (H s))
      (-2 * H t - 2 * H' / H t) t := by
  have h1 : HasDerivAt (fun s => Real.log (a s)) (a t * H t / a t) t :=
    ha.log ha0
  have h2 : HasDerivAt (fun s => Real.log (H s)) (H' / H t) t :=
    hH.log hH0
  have h4 : HasDerivAt (fun s => Real.log (-k) - 2 * Real.log (a s)
      - 2 * Real.log (H s))
      (0 - 2 * (a t * H t / a t) - 2 * (H' / H t)) t :=
    ((hasDerivAt_const t (Real.log (-k))).sub
      (h1.const_mul 2)).sub (h2.const_mul 2)
  have h5 : (0:ℝ) - 2 * (a t * H t / a t) - 2 * (H' / H t)
      = -2 * H t - 2 * H' / H t := by
    field_simp
    ring
  rw [← h5]
  exact h4

/-- Pointwise identity: `log|Ω_k| = log(-k) - 2log(a) - 2log(H)`
wherever `a, H ≠ 0` (`Real.log x = log |x|`, so signs are
immaterial). -/
theorem log_omega_eq (k av Hv : ℝ) (hk : k ≠ 0) (ha : av ≠ 0)
    (hH : Hv ≠ 0) :
    Real.log (-k / (av ^ 2 * Hv ^ 2))
      = Real.log (-k) - 2 * Real.log av - 2 * Real.log Hv := by
  rw [Real.log_div (by simpa using hk) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-! ## `thm:comoving-matter-depletion`, `cor:phantom-matter-deficit` -/

/-- `thm:comoving-matter-depletion`: for `ρ̇ + dHρ = -Q` and
`ȧ = aH`, the comoving matter obeys the exact integrated identity
`a(t₁)^d ρ(t₁) = a(t₀)^d ρ(t₀) - ∫ a^d Q`. -/
theorem comoving_matter_depletion (d : ℕ) (a rho Q H : ℝ → ℝ)
    (t0 t1 : ℝ)
    (ha : ∀ t, HasDerivAt a (a t * H t) t)
    (hrho : ∀ t, HasDerivAt rho (-(d * H t * rho t) - Q t) t)
    (hQ : Continuous Q) :
    a t1 ^ d * rho t1
      = a t0 ^ d * rho t0 - ∫ s in t0..t1, a s ^ d * Q s := by
  have hacont : Continuous a :=
    continuous_iff_continuousAt.mpr fun t => (ha t).continuousAt
  have hprod : ∀ t, HasDerivAt (fun s => a s ^ d * rho s)
      (-(a t ^ d * Q t)) t := by
    intro t
    have h1 : HasDerivAt (fun s => a s ^ d)
        ((d : ℕ) * a t ^ (d - 1) * (a t * H t)) t := (ha t).pow d
    have h2 := h1.mul (hrho t)
    have h3 : (d : ℕ) * a t ^ (d - 1) * (a t * H t) * rho t
        + a t ^ d * (-(d * H t * rho t) - Q t)
        = -(a t ^ d * Q t) := by
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd
        simp
      · have hpow : a t ^ (d - 1) * a t = a t ^ d := by
          rw [← pow_succ]
          congr 1
          omega
        linear_combination ((d : ℝ) * H t * rho t) * hpow
    rw [← h3]
    exact h2
  have hint : IntervalIntegrable (fun s => -(a s ^ d * Q s))
      MeasureTheory.volume t0 t1 :=
    (((hacont.pow d).mul hQ).neg).intervalIntegrable t0 t1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hprod t) hint
  rw [intervalIntegral.integral_neg] at hftc
  linarith [hftc]

/-- `cor:phantom-matter-deficit`: the comoving deficit
`ΔM = ∫ a^d Q` is nonnegative once the exchange is nonnegative —
every matter-to-deficiency episode leaves a sign-definite comoving
matter deficit. -/
theorem comoving_matter_deficit_nonneg (d : ℕ) (a Q : ℝ → ℝ)
    (t0 t1 : ℝ) (h01 : t0 ≤ t1)
    (hQ0 : ∀ s, 0 ≤ Q s) (ha0 : ∀ s, 0 ≤ a s) :
    0 ≤ ∫ s in t0..t1, a s ^ d * Q s := by
  apply intervalIntegral.integral_nonneg h01
  intro s _
  exact mul_nonneg (pow_nonneg (ha0 s) d) (hQ0 s)

/-- Comparison with noninteracting dust with the same expansion
history: `ρ(t₁) ≤ ρ_i (a_i/a(t₁))^d`. -/
theorem matter_density_le_free (d : ℕ) (a rho Q H : ℝ → ℝ)
    (t0 t1 : ℝ) (h01 : t0 ≤ t1)
    (ha : ∀ t, HasDerivAt a (a t * H t) t)
    (hrho : ∀ t, HasDerivAt rho (-(d * H t * rho t) - Q t) t)
    (hQ : Continuous Q) (hQ0 : ∀ s, 0 ≤ Q s) (ha0 : ∀ s, 0 ≤ a s)
    (hat1 : 0 < a t1) :
    rho t1 ≤ a t0 ^ d * rho t0 / a t1 ^ d := by
  have h1 := comoving_matter_depletion d a rho Q H t0 t1 ha hrho hQ
  have h2 := comoving_matter_deficit_nonneg d a Q t0 t1 h01 hQ0 ha0
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h1, h2]

/-! ## `lem:berry-antiherm` -/

/-- `lem:berry-antiherm`: for a `C¹` frame with constant pairwise
inner products (an orthonormal band frame), the Berry matrix
`𝒜_ab = ⟨u_a, u̇_b⟩` is anti-Hermitian: `𝒜_ab + conj 𝒜_ba = 0`.
Hence the Berry holonomy lies in `U(r)`. -/
theorem berry_antihermitian {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (u v : ℝ → H) (u' v' : H) (t : ℝ)
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t)
    (hconst : ∀ s, inner ℂ (u s) (v s) = inner ℂ (u t) (v t)) :
    inner ℂ (u t) v' + starRingEnd ℂ (inner ℂ (v t) u') = 0 := by
  have hderiv : HasDerivAt (fun s => inner ℂ (u s) (v s))
      (inner ℂ (u t) v' + inner ℂ u' (v t)) t := hu.inner ℂ hv
  have hconst' : HasDerivAt (fun s => inner ℂ (u s) (v s)) 0 t := by
    have heq : (fun s => inner ℂ (u s) (v s))
        = fun _ => inner ℂ (u t) (v t) := funext hconst
    rw [heq]
    exact hasDerivAt_const t _
  have hzero : inner ℂ (u t) v' + inner ℂ u' (v t) = 0 :=
    hderiv.unique hconst'
  rw [inner_conj_symm]
  exact hzero

/-! ## `lem:constant-rate-energy` -/

/-- `lem:constant-rate-energy` (energy identity): with
`L = λ(1 - √(1 - s/c²))` and `s = g(v,v)`, the autonomous Lagrangian
energy is `E = v·∂_vL - L = 2s·L'(s) - L = λ((1-s/c²)^{-1/2} - 1)
= λφ(s)`. -/
theorem constant_rate_energy_identity (lam c2 s : ℝ)
    (hc : 0 < c2) (_hs : 0 ≤ s) (hlt : s < c2) :
    2 * s * (lam / (2 * c2 * Real.sqrt (1 - s / c2)))
      - lam * (1 - Real.sqrt (1 - s / c2))
    = lam * ((Real.sqrt (1 - s / c2))⁻¹ - 1) := by
  have hpos : 0 < 1 - s / c2 := by
    rw [sub_pos, div_lt_one hc]
    exact hlt
  set w := Real.sqrt (1 - s / c2) with hw
  have hw0 : 0 < w := Real.sqrt_pos.mpr hpos
  have hwsq : w ^ 2 = 1 - s / c2 := Real.sq_sqrt hpos.le
  have hw' : w ≠ 0 := ne_of_gt hw0
  have hs_eq : s = c2 * (1 - w ^ 2) := by
    rw [hwsq]
    field_simp
    ring
  rw [hs_eq]
  field_simp
  ring

/-- `lem:constant-rate-energy` (monotonicity): the energy profile
`φ(s) = (1 - s/c²)^{-1/2} - 1` is strictly increasing on `[0, c²)`,
so the conserved energy pins the constant `g`-speed. -/
theorem phi_strictMonoOn (c2 : ℝ) (hc : 0 < c2) :
    StrictMonoOn (fun s => (Real.sqrt (1 - s / c2))⁻¹ - 1)
      (Set.Ico 0 c2) := by
  intro s1 hs1 s2 hs2 h12
  have hp1 : 0 < 1 - s1 / c2 := by
    rw [sub_pos, div_lt_one hc]
    exact hs1.2
  have hp2 : 0 < 1 - s2 / c2 := by
    rw [sub_pos, div_lt_one hc]
    exact hs2.2
  have hdiv : s1 / c2 < s2 / c2 := by gcongr
  have hkey : Real.sqrt (1 - s2 / c2) < Real.sqrt (1 - s1 / c2) :=
    Real.sqrt_lt_sqrt hp2.le (by linarith)
  have h2 : 0 < Real.sqrt (1 - s2 / c2) := Real.sqrt_pos.mpr hp2
  have hinv : (Real.sqrt (1 - s1 / c2))⁻¹
      < (Real.sqrt (1 - s2 / c2))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_lt_one_div_of_lt h2 hkey
  simp only []
  linarith

/-! ## `prop:local-clock-one-crossing` -/

/-- After a zero with negative derivative the function is negative
somewhere in every right-neighbourhood (the outgoing branch of the
`+ → -` crossing). -/
theorem neg_after_zero_of_deriv_neg {g : ℝ → ℝ} {t0 g0' : ℝ}
    (h0 : g t0 = 0) (hd : HasDerivAt g g0' t0) (hneg : g0' < 0)
    {b : ℝ} (hb : t0 < b) :
    ∃ u, u ∈ Set.Ioo t0 b ∧ g u < 0 := by
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hmono : 𝓝[>] t0 ≤ 𝓝[≠] t0 :=
    nhdsWithin_mono _ fun x hx => ne_of_gt hx
  have hlt : ∀ᶠ u in 𝓝[>] t0, slope g t0 u < 0 :=
    (hslope.mono_left hmono).eventually_lt_const hneg
  have hIoo : Set.Ioo t0 b ∈ 𝓝[>] t0 := Ioo_mem_nhdsGT hb
  obtain ⟨u, hu1, hu2⟩ := (hlt.and (Filter.eventually_mem_set.mpr hIoo)).exists
  refine ⟨u, hu2, ?_⟩
  have hden : 0 < u - t0 := sub_pos.mpr hu2.1
  rw [slope_def_field] at hu1
  rw [h0, sub_zero] at hu1
  by_contra hgu
  push Not at hgu
  exact absurd hu1 (not_lt.mpr (div_nonneg hgu hden.le))

/-- Before a zero with negative derivative the function is positive
somewhere in every left-neighbourhood (the incoming branch of the
`+ → -` crossing). -/
theorem pos_before_zero_of_deriv_neg {g : ℝ → ℝ} {t2 g2' : ℝ}
    (h0 : g t2 = 0) (hd : HasDerivAt g g2' t2) (hneg : g2' < 0)
    {a : ℝ} (ha : a < t2) :
    ∃ v, v ∈ Set.Ioo a t2 ∧ 0 < g v := by
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hmono : 𝓝[<] t2 ≤ 𝓝[≠] t2 :=
    nhdsWithin_mono _ fun x hx => ne_of_lt hx
  have hlt : ∀ᶠ v in 𝓝[<] t2, slope g t2 v < 0 :=
    (hslope.mono_left hmono).eventually_lt_const hneg
  have hIoo : Set.Ioo a t2 ∈ 𝓝[<] t2 := Ioo_mem_nhdsLT ha
  obtain ⟨v, hv1, hv2⟩ := (hlt.and (Filter.eventually_mem_set.mpr hIoo)).exists
  refine ⟨v, hv2, ?_⟩
  have hden : v - t2 < 0 := sub_neg.mpr hv2.2
  rw [slope_def_field, h0, sub_zero] at hv1
  by_contra hgv
  push Not at hgv
  have : 0 ≤ g v / (v - t2) := div_nonneg_iff.mpr (Or.inr ⟨hgv, hden.le⟩)
  exact absurd hv1 (not_lt.mpr this)

/-- `prop:local-clock-one-crossing` (abstract core): a continuous
function with strictly negative derivative at each of its zeros has
at most one zero. -/
theorem at_most_one_zero_of_deriv_neg {g g' : ℝ → ℝ}
    (hgc : Continuous g)
    (hd : ∀ t, g t = 0 → HasDerivAt g (g' t) t)
    (hneg : ∀ t, g t = 0 → g' t < 0) :
    ∀ t1 t2, g t1 = 0 → g t2 = 0 → t1 = t2 := by
  have key : ∀ t1 t2, t1 < t2 → g t1 = 0 → g t2 = 0 → False := by
    intro t1 t2 h12 h1 h2
    obtain ⟨u, hu, hgu⟩ :=
      neg_after_zero_of_deriv_neg h1 (hd t1 h1) (hneg t1 h1) h12
    obtain ⟨v, hv, hgv⟩ :=
      pos_before_zero_of_deriv_neg h2 (hd t2 h2) (hneg t2 h2) hu.2
    have huv : u < v := hv.1
    -- a zero exists between u and v by the IVT
    have hivt : ∃ w ∈ Set.Ioo u v, g w = 0 := by
      have h0mem : (0:ℝ) ∈ Set.Ioo (g u) (g v) := ⟨hgu, hgv⟩
      have := intermediate_value_Ioo huv.le hgc.continuousOn h0mem
      obtain ⟨w, hw, hw0⟩ := this
      exact ⟨w, hw, hw0⟩
    -- take the first zero after u
    set Z : Set ℝ := {t | t ∈ Set.Icc u v ∧ g t = 0} with hZ
    have hZclosed : IsClosed Z := by
      apply IsClosed.inter isClosed_Icc
      exact isClosed_eq hgc continuous_const
    have hZne : Z.Nonempty := by
      obtain ⟨w, hw, hw0⟩ := hivt
      exact ⟨w, ⟨hw.1.le, hw.2.le⟩, hw0⟩
    have hZbdd : BddBelow Z := ⟨u, fun t ht => ht.1.1⟩
    set T := sInf Z with hT
    have hTmem : T ∈ Z := hZclosed.csInf_mem hZne hZbdd
    have hTu : u < T := by
      rcases lt_or_eq_of_le hTmem.1.1 with h | h
      · exact h
      · exact absurd (h ▸ hTmem.2) (ne_of_lt hgu)
    -- g is negative on [u, T)
    have hgneg : ∀ t, t ∈ Set.Ico u T → g t < 0 := by
      intro t ht
      by_contra hge
      push Not at hge
      rcases eq_or_lt_of_le hge with h | h
      · -- t itself is a zero below the infimum
        have htZ : t ∈ Z := ⟨⟨ht.1, ht.2.le.trans hTmem.1.2⟩, h.symm⟩
        exact absurd (csInf_le hZbdd htZ) (not_le.mpr ht.2)
      · -- a zero strictly between u and t by the IVT
        have hut : u < t := by
          rcases eq_or_lt_of_le ht.1 with h' | h'
          · exact absurd (h' ▸ h) (not_lt.mpr hgu.le)
          · exact h'
        have h0mem : (0:ℝ) ∈ Set.Ioo (g u) (g t) := ⟨hgu, h⟩
        obtain ⟨w, hw, hw0⟩ :=
          intermediate_value_Ioo hut.le hgc.continuousOn h0mem
        have hwZ : w ∈ Z := by
          constructor
          · constructor
            · exact hw.1.le
            · exact (hw.2.le.trans ht.2.le).trans hTmem.1.2
          · exact hw0
        have := csInf_le hZbdd hwZ
        have hwT : w < T := lt_of_lt_of_le hw.2 ht.2.le
        exact absurd this (not_le.mpr hwT)
    -- the slope at T from the left is nonnegative, contradiction
    have hgT : g T = 0 := hTmem.2
    have hslope := hasDerivAt_iff_tendsto_slope.mp (hd T hgT)
    have hmono : 𝓝[<] T ≤ 𝓝[≠] T :=
      nhdsWithin_mono _ fun x hx => ne_of_lt hx
    have htend := hslope.mono_left hmono
    have hIoo : Set.Ioo u T ∈ 𝓝[<] T := Ioo_mem_nhdsLT hTu
    have hev : ∀ᶠ t in 𝓝[<] T, 0 ≤ slope g T t := by
      filter_upwards [Filter.eventually_mem_set.mpr hIoo] with t ht
      rw [slope_def_field, hgT, sub_zero]
      have hgt : g t < 0 := hgneg t ⟨ht.1.le, ht.2⟩
      have hden : t - T < 0 := sub_neg.mpr ht.2
      exact div_nonneg_iff.mpr (Or.inr ⟨hgt.le, hden.le⟩)
    have : (0:ℝ) ≤ g' T := ge_of_tendsto htend hev
    exact absurd this (not_le.mpr (hneg T hgT))
  intro t1 t2 h1 h2
  rcases lt_trichotomy t1 t2 with h | h | h
  · exact absurd (key t1 t2 h h1 h2) (fun f => f)
  · exact h
  · exact absurd (key t2 t1 h h2 h1) (fun f => f)

/-- `prop:local-clock-one-crossing`: for `Ḃ = S(t) - F(B)` with `S`
strictly decreasing (`S' < 0`) and `F` differentiable, the balance
derivative `Ḃ` has at most one zero; by
`pos_before_zero_of_deriv_neg` / `neg_after_zero_of_deriv_neg` any
such zero is a `+ → -` sign change. -/
theorem local_clock_one_crossing (S F B S' F' : ℝ → ℝ)
    (hB : ∀ t, HasDerivAt B (S t - F (B t)) t)
    (hS : ∀ t, HasDerivAt S (S' t) t)
    (hSneg : ∀ t, S' t < 0)
    (hF : ∀ x, HasDerivAt F (F' x) x) :
    ∀ t1 t2, S t1 - F (B t1) = 0 → S t2 - F (B t2) = 0 → t1 = t2 := by
  have hBc : Continuous B :=
    continuous_iff_continuousAt.mpr fun t => (hB t).continuousAt
  have hSc : Continuous S :=
    continuous_iff_continuousAt.mpr fun t => (hS t).continuousAt
  have hFc : Continuous F :=
    continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hgc : Continuous (fun t => S t - F (B t)) :=
    hSc.sub (hFc.comp hBc)
  have hd : ∀ t, HasDerivAt (fun t => S t - F (B t))
      (S' t - F' (B t) * (S t - F (B t))) t := by
    intro t
    exact (hS t).sub ((hF (B t)).comp t (hB t))
  exact at_most_one_zero_of_deriv_neg hgc
    (g' := fun t => S' t - F' (B t) * (S t - F (B t)))
    (fun t _ => hd t)
    (fun t h0 => by
      rw [h0, mul_zero, sub_zero]
      exact hSneg t)

end NCG
