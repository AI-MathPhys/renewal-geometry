/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Fermionic gap, spectral-flow, and gauge-line alternatives

Machinery for `thm:SMST-fermionic-phase-transport`.

* `reduced_gap_alternative` (**F1/F2**): along any sequence of finite Dirac operators, exactly one
  of: a uniform reduced gap `‖D_j u‖ ≥ γ > 0` on unit vectors orthogonal to the kernel, or unit
  vectors `u_k ⊥ ker D_{j_k}` with `‖D_{j_k} u_k‖ → 0`;
* `scalarizable_iff_stabilizer_trivial` (**QRP.12**): a `U(1)`-valued (more generally, commutative
  group valued) cocycle on one orbit `G ω₀` is a coboundary `a(g, ω) = b(g ω) b(ω)⁻¹` exactly when
  it is trivial on the stabilizer of `ω₀`; `scalarization_unique`: two scalarizations differ by a
  constant phase on the orbit (the residual edge cochain).
-/

open Filter Topology

namespace NCG
namespace FermionicPhaseTransport

set_option linter.unusedSectionVars false

/-! ### The reduced-gap alternative -/

section Gap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A uniform reduced gap `γ` along the family: `‖D_j u‖ ≥ γ` for every unit `u ⊥ ker D_j`. -/
def UniformReducedGap (D : ℕ → E →ₗ[ℂ] E) (γ : ℝ) : Prop :=
  ∀ j, ∀ u : E, ‖u‖ = 1 → u ∈ (LinearMap.ker (D j))ᗮ → γ ≤ ‖D j u‖

/-- A vanishing reduced singular value: unit vectors `u_k ⊥ ker D_{j_k}` with
`‖D_{j_k} u_k‖ → 0`. -/
def VanishingReducedGap (D : ℕ → E →ₗ[ℂ] E) : Prop :=
  ∃ (j : ℕ → ℕ) (u : ℕ → E), (∀ k, ‖u k‖ = 1) ∧ (∀ k, u k ∈ (LinearMap.ker (D (j k)))ᗮ) ∧
    Tendsto (fun k => ‖D (j k) (u k)‖) atTop (𝓝 0)

/-- **(F1)/(F2)**: exactly one of a uniform reduced gap or a vanishing reduced singular value. -/
theorem reduced_gap_alternative (D : ℕ → E →ₗ[ℂ] E) :
    ((∃ γ : ℝ, 0 < γ ∧ UniformReducedGap D γ) ∨ VanishingReducedGap D) ∧
      ¬ ((∃ γ : ℝ, 0 < γ ∧ UniformReducedGap D γ) ∧ VanishingReducedGap D) := by
  constructor
  · by_cases h : ∃ γ : ℝ, 0 < γ ∧ UniformReducedGap D γ
    · exact Or.inl h
    · right
      push Not at h
      -- for every `k` some `j` and unit `u ⊥ ker` with `‖D j u‖ < 1/(k+1)`
      have hk : ∀ k : ℕ, ∃ j, ∃ u : E, ‖u‖ = 1 ∧ u ∈ (LinearMap.ker (D j))ᗮ ∧
          ‖D j u‖ < 1 / ((k : ℝ) + 1) := by
        intro k
        have := h (1 / ((k : ℝ) + 1)) (by positivity)
        unfold UniformReducedGap at this
        push Not at this
        obtain ⟨j, u, hu, hker, hlt⟩ := this
        exact ⟨j, u, hu, hker, hlt⟩
      choose j u hu hker hlt using hk
      refine ⟨j, u, hu, hker, ?_⟩
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => (hlt k).le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
  · rintro ⟨⟨γ, hγ, hgap⟩, j, u, hu, hker, hlim⟩
    have := (hlim.eventually (gt_mem_nhds hγ)).exists
    obtain ⟨k, hk⟩ := this
    exact absurd (hgap (j k) (u k) (hu k) (hker k)) (not_le.mpr hk)

end Gap

/-! ### Gauge-line cocycles on an orbit -/

section Cocycle

variable {G Ω A : Type*} [Group G] [MulAction G Ω] [CommGroup A]

/-- The cocycle identity `a(g h, ω) = a(g, h ω) a(h, ω)`. -/
def IsCocycle (a : G → Ω → A) : Prop :=
  ∀ g h ω, a (g * h) ω = a g (h • ω) * a h ω

/-- A scalarization (coboundary trivialization) of `a` on the orbit of `ω₀`:
`a(g, ω) = b(g ω) b(ω)⁻¹` for `ω ∈ G ω₀`. -/
def IsScalarization (a : G → Ω → A) (ω₀ : Ω) (b : Ω → A) : Prop :=
  ∀ g, ∀ ω ∈ MulAction.orbit G ω₀, a g ω = b (g • ω) * (b ω)⁻¹

theorem IsCocycle.one_left {a : G → Ω → A} (ha : IsCocycle a) (ω : Ω) : a 1 ω = 1 := by
  have := ha 1 1 ω
  rw [one_mul, one_smul] at this
  exact (mul_left_cancel (a := a 1 ω) (by rw [mul_one]; exact this)).symm

/-- On the stabilizer the cocycle is determined by any scalarization: necessity in QRP.12. -/
theorem IsScalarization.stabilizer_trivial {a : G → Ω → A} {ω₀ : Ω} {b : Ω → A}
    (hb : IsScalarization a ω₀ b) {h : G} (hh : h ∈ MulAction.stabilizer G ω₀) :
    a h ω₀ = 1 := by
  have := hb h ω₀ (MulAction.mem_orbit_self ω₀)
  rw [MulAction.mem_stabilizer_iff.mp hh, mul_inv_cancel] at this
  exact this

/-- Cocycle values on `ω₀` only depend on the point `g ω₀` when the stabilizer acts trivially. -/
theorem IsCocycle.eq_of_smul_eq {a : G → Ω → A} (ha : IsCocycle a) {ω₀ : Ω}
    (hstab : ∀ h ∈ MulAction.stabilizer G ω₀, a h ω₀ = 1) {g g' : G} (hg : g • ω₀ = g' • ω₀) :
    a g ω₀ = a g' ω₀ := by
  have hmem : g'⁻¹ * g ∈ MulAction.stabilizer G ω₀ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hg, inv_smul_smul]
  have h1 := ha g' (g'⁻¹ * g) ω₀
  rw [mul_inv_cancel_left, MulAction.mem_stabilizer_iff.mp hmem, hstab _ hmem, mul_one] at h1
  exact h1

open Classical in
/-- The canonical scalarization `b(g ω₀) = a(g, ω₀)` (and `1` off the orbit). -/
noncomputable def canonicalScalarization (a : G → Ω → A) (ω₀ : Ω) (ω : Ω) : A :=
  if h : ω ∈ MulAction.orbit G ω₀ then a (Classical.choose (MulAction.mem_orbit_iff.mp h)) ω₀
  else 1

theorem canonicalScalarization_smul {a : G → Ω → A} (ha : IsCocycle a) {ω₀ : Ω}
    (hstab : ∀ h ∈ MulAction.stabilizer G ω₀, a h ω₀ = 1) (g : G) :
    canonicalScalarization a ω₀ (g • ω₀) = a g ω₀ := by
  have hmem : g • ω₀ ∈ MulAction.orbit G ω₀ := MulAction.mem_orbit _ g
  unfold canonicalScalarization
  rw [dif_pos hmem]
  exact ha.eq_of_smul_eq hstab (Classical.choose_spec (MulAction.mem_orbit_iff.mp hmem))

/-- **(QRP.12)**: a cocycle is scalarizable on the orbit of `ω₀` exactly when it is trivial on the
stabilizer of `ω₀`. -/
theorem scalarizable_iff_stabilizer_trivial {a : G → Ω → A} (ha : IsCocycle a) (ω₀ : Ω) :
    (∃ b : Ω → A, IsScalarization a ω₀ b) ↔ ∀ h ∈ MulAction.stabilizer G ω₀, a h ω₀ = 1 := by
  constructor
  · rintro ⟨b, hb⟩ h hh
    exact hb.stabilizer_trivial hh
  · intro hstab
    refine ⟨canonicalScalarization a ω₀, fun g ω hω => ?_⟩
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hω
    rw [← mul_smul, canonicalScalarization_smul ha hstab, canonicalScalarization_smul ha hstab,
      ha g k ω₀, mul_inv_cancel_right]

/-- **Residual edge cochain**: two scalarizations of the same cocycle differ by a constant phase
on the orbit. -/
theorem scalarization_unique {a : G → Ω → A} {ω₀ : Ω} {b b' : Ω → A}
    (hb : IsScalarization a ω₀ b) (hb' : IsScalarization a ω₀ b') :
    ∀ ω ∈ MulAction.orbit G ω₀, b' ω * (b ω)⁻¹ = b' ω₀ * (b ω₀)⁻¹ := by
  intro ω hω
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hω
  have h1 := hb g ω₀ (MulAction.mem_orbit_self ω₀)
  have h2 := hb' g ω₀ (MulAction.mem_orbit_self ω₀)
  have h0 : b (g • ω₀) * (b ω₀)⁻¹ = b' (g • ω₀) * (b' ω₀)⁻¹ := h1.symm.trans h2
  have h3 : b' (g • ω₀) = b (g • ω₀) * (b ω₀)⁻¹ * b' ω₀ := by
    rw [h0, inv_mul_cancel_right]
  rw [h3, mul_right_comm, mul_right_comm (b (g • ω₀)), mul_inv_cancel, one_mul, mul_comm]

end Cocycle

/-! ### Sign parity across transversal zeros -/

section Parity

/-- A continuous function without zeros on `[p, q]` has the same sign at both ends:
`0 < f p * f q`. -/
theorem mul_pos_of_no_zero {f : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q) (hf : ContinuousOn f (Set.Icc p q))
    (hz : ∀ t ∈ Set.Icc p q, f t ≠ 0) : 0 < f p * f q := by
  have hp : f p ≠ 0 := hz p ⟨le_rfl, hpq⟩
  have hq : f q ≠ 0 := hz q ⟨hpq, le_rfl⟩
  rcases lt_or_gt_of_ne hp with hp' | hp' <;> rcases lt_or_gt_of_ne hq with hq' | hq'
  · exact mul_pos_of_neg_of_neg hp' hq'
  · exfalso
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hpq hf ⟨hp'.le, hq'.le⟩
    exact hz c hc hc0
  · exfalso
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hpq hf ⟨hq'.le, hp'.le⟩
    exact hz c hc hc0
  · exact mul_pos hp' hq'

/-- Near a transversal zero `z` (`f z = 0`, `f' z = d ≠ 0`), the function changes sign:
`f (z - h) * f (z + h) < 0` for all small `h > 0`. -/
theorem exists_sign_change_of_hasDerivAt {f : ℝ → ℝ} {z d : ℝ} (hf : HasDerivAt f d z)
    (hz : f z = 0) (hd : d ≠ 0) :
    ∃ ε > 0, ∀ h, 0 < h → h < ε → f (z - h) * f (z + h) < 0 := by
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hf)
  have hev := hslope.eventually (Metric.ball_mem_nhds d (by positivity : 0 < |d| / 2))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε, hε, fun h hh hhε => ?_⟩
  have key : ∀ t, dist t z < ε → t ≠ z → 0 < (f t / (t - z)) * d := by
    intro t ht htz
    have := hball ht htz
    rw [slope_def_field, hz, sub_zero, Real.dist_eq] at this
    rcases lt_or_gt_of_ne hd with hd' | hd'
    · have : f t / (t - z) < 0 := by
        have := (abs_lt.mp this).2
        linarith [abs_of_neg hd']
      exact mul_pos_of_neg_of_neg this hd'
    · have : 0 < f t / (t - z) := by
        have := (abs_lt.mp this).1
        linarith [abs_of_pos hd']
      exact mul_pos this hd'
  have h1 := key (z + h) (by rw [Real.dist_eq]; simp [abs_of_pos hh, hhε]) (by linarith)
  have h2 := key (z - h) (by rw [Real.dist_eq]; simp [abs_of_pos hh, hhε]) (by linarith)
  rw [add_sub_cancel_left] at h1
  rw [sub_sub_cancel_left, div_neg] at h2
  -- `f (z+h) / h * d > 0` and `-(f (z-h) / h) * d > 0`
  have h3 : 0 < (f (z + h) / h * d) * (-(f (z - h) / h) * d) := mul_pos h1 h2
  have h4 : (f (z + h) / h * d) * (-(f (z - h) / h) * d)
      = -(f (z - h) * f (z + h)) * (d / h) ^ 2 := by
    field_simp
  rw [h4] at h3
  have h5 : 0 < (d / h) ^ 2 := by positivity
  nlinarith [h3, h5]

/-- **Sign parity across transversal zeros**: if `f` is continuous on `[a, b]`, vanishes on
`[a, b]` exactly at the points of a finite set `Z ⊆ (a, b)`, and every zero is transversal, then
`0 < (-1)^{|Z|} f(b) f(a)`. -/
theorem sign_parity (Z : Finset ℝ) :
    ∀ {f : ℝ → ℝ} {a b : ℝ}, a < b → ContinuousOn f (Set.Icc a b) → (↑Z : Set ℝ) ⊆ Set.Ioo a b →
      (∀ t ∈ Set.Icc a b, f t = 0 ↔ t ∈ Z) → (∀ z ∈ Z, ∃ d ≠ 0, HasDerivAt f d z) →
      0 < (-1 : ℝ) ^ Z.card * (f b * f a) := by
  induction Z using Finset.strongInduction with
  | H Z ih =>
    intro f a b hab hf hZ hzero htr
    rcases Z.eq_empty_or_nonempty with hZe | hZne
    · subst hZe
      simp only [Finset.card_empty, pow_zero, one_mul]
      rw [mul_comm]
      exact mul_pos_of_no_zero hab.le hf fun t ht h0 => by simpa using (hzero t ht).mp h0
    · -- the smallest zero
      set z := Z.min' hZne with hz
      have hzZ : z ∈ Z := Z.min'_mem hZne
      have hzIoo : z ∈ Set.Ioo a b := hZ hzZ
      have hzmin : ∀ w ∈ Z, z ≤ w := fun w hw => Z.min'_le w hw
      -- a point `c` strictly between `z` and the next zero (or `b`)
      obtain ⟨c, hzc, hcb, hcz⟩ : ∃ c, z < c ∧ c < b ∧ ∀ w ∈ Z, w ≠ z → c < w := by
        rcases (Z.erase z).eq_empty_or_nonempty with he | hne
        · refine ⟨(z + b) / 2, by linarith [hzIoo.2], by linarith [hzIoo.2], fun w hw hwz => ?_⟩
          exact absurd (Finset.mem_erase.mpr ⟨hwz, hw⟩) (by rw [he]; simp)
        · set z' := (Z.erase z).min' hne with hz'
          have hz'Z : z' ∈ Z.erase z := Finset.min'_mem _ hne
          have hz'gt : z < z' := lt_of_le_of_ne (hzmin z' (Finset.mem_of_mem_erase hz'Z))
            (Finset.ne_of_mem_erase hz'Z).symm
          have hz'b : z' < b := (hZ (Finset.mem_of_mem_erase hz'Z)).2
          refine ⟨(z + z') / 2, by linarith, by linarith, fun w hw hwz => ?_⟩
          have := Finset.min'_le (Z.erase z) w (Finset.mem_erase.mpr ⟨hwz, hw⟩)
          rw [← hz'] at this
          linarith
      -- sign change across the single zero `z` on `[a, c]`
      obtain ⟨d, hd, hfd⟩ := htr z hzZ
      have hfz : f z = 0 := (hzero z ⟨hzIoo.1.le, hzIoo.2.le⟩).mpr hzZ
      obtain ⟨ε, hε, hsc⟩ := exists_sign_change_of_hasDerivAt hfd hfz hd
      set h := min (ε / 2) (min ((z - a) / 2) ((c - z) / 2)) with hh
      have hh0 : 0 < h := lt_min (half_pos hε) (lt_min (by linarith [hzIoo.1]) (by linarith))
      have hhε : h < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
      have hha : a < z - h := by
        have := (min_le_right _ _).trans (min_le_left ((z - a) / 2) ((c - z) / 2)) |>.trans_eq'
          (rfl : h = h)
        have : h ≤ (z - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
        linarith
      have hhc : z + h < c := by
        have : h ≤ (c - z) / 2 := (min_le_right _ _).trans (min_le_right _ _)
        linarith
      have hleft : 0 < f a * f (z - h) := by
        refine mul_pos_of_no_zero (by linarith) (hf.mono (Set.Icc_subset_Icc le_rfl (by
          linarith [hzIoo.2]))) ?_
        intro t ht h0
        have htZ := (hzero t ⟨ht.1, by linarith [ht.2, hzIoo.2]⟩).mp h0
        have := hzmin t htZ
        linarith [ht.2]
      have hright : 0 < f (z + h) * f c := by
        refine mul_pos_of_no_zero (by linarith) (hf.mono (Set.Icc_subset_Icc (by linarith
          [hzIoo.1]) hcb.le)) ?_
        intro t ht h0
        have htZ := (hzero t ⟨by linarith [ht.1, hzIoo.1], by linarith [ht.2]⟩).mp h0
        have htz : t ≠ z := by intro h'; rw [h'] at ht; linarith [ht.1]
        have := hcz t htZ htz
        linarith [ht.2]
      have hmid := hsc h hh0 hhε
      have hac : f c * f a < 0 := by nlinarith [hleft, hright, hmid]
      -- induction on `[c, b]` with the remaining zeros
      have hsub : Z.erase z ⊂ Z := Finset.erase_ssubset hzZ
      have hih := ih (Z.erase z) hsub (f := f) (a := c) (b := b) hcb
        (hf.mono (Set.Icc_subset_Icc (hzIoo.1.le.trans hzc.le) le_rfl)) ?_ ?_ ?_
      · rw [Finset.card_erase_of_mem hzZ] at hih
        have hcard : Z.card = (Z.card - 1) + 1 := (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr
          hZne)).symm
        rw [hcard, pow_succ]
        nlinarith [hih, hac, sq_nonneg (f c)]
      · intro w hw
        have hwZ := Finset.mem_of_mem_erase hw
        exact ⟨hcz w hwZ (Finset.ne_of_mem_erase hw), (hZ hwZ).2⟩
      · intro t ht
        constructor
        · intro h0
          have htZ := (hzero t ⟨by linarith [ht.1, hzIoo.1], ht.2⟩).mp h0
          refine Finset.mem_erase.mpr ⟨?_, htZ⟩
          intro h'
          rw [h'] at ht
          linarith [ht.1]
        · intro hw
          exact (hzero t ⟨by linarith [ht.1, hzIoo.1], ht.2⟩).mpr (Finset.mem_of_mem_erase hw)
      · intro w hw
        exact htr w (Finset.mem_of_mem_erase hw)

end Parity

/-! ### Spectral flow and the determinant sign (QRP.10) -/

section SpectralFlow

variable {n : ℕ}

/-- The spectral flow of eigenvalue branches with transversal zero sets `Z i` and derivative
data `d i`: up-crossings minus down-crossings. -/
noncomputable def spectralFlow (Z : Fin n → Finset ℝ) (d : Fin n → ℝ → ℝ) : ℤ :=
  ∑ i, ((((Z i).filter fun z => 0 < d i z).card : ℤ) - (((Z i).filter fun z => d i z < 0).card : ℤ))

/-- The spectral flow has the parity of the total number of crossings. -/
theorem even_spectralFlow_iff (Z : Fin n → Finset ℝ) (d : Fin n → ℝ → ℝ)
    (hd : ∀ i, ∀ z ∈ Z i, d i z ≠ 0) :
    Even (spectralFlow Z d) ↔ Even (∑ i, (Z i).card) := by
  have hsplit : ∀ i, ((Z i).filter fun z => 0 < d i z).card +
      ((Z i).filter fun z => d i z < 0).card = (Z i).card := by
    intro i
    have h := Finset.card_filter_add_card_filter_not (s := Z i) (fun z => 0 < d i z)
    have hcongr : ((Z i).filter fun z => ¬ 0 < d i z) = (Z i).filter fun z => d i z < 0 := by
      refine Finset.filter_congr fun z hz => ?_
      constructor
      · intro hle
        exact lt_of_le_of_ne (not_lt.mp hle) (hd i z hz)
      · intro hlt
        exact not_lt.mpr hlt.le
    rw [hcongr] at h
    exact h
  have heq : spectralFlow Z d = ∑ i, ((((Z i).card : ℕ) : ℤ)
      - 2 * (((Z i).filter fun z => d i z < 0).card : ℤ)) := by
    unfold spectralFlow
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsplit i]
    push_cast
    ring
  rw [heq, Finset.sum_sub_distrib, ← Finset.mul_sum, Int.even_sub, ← Nat.cast_sum,
    Int.even_coe_nat]
  constructor
  · intro h
    exact h.mpr (even_two_mul _)
  · intro h
    exact ⟨fun _ => even_two_mul _, fun _ => h⟩

/-- The product of the parity-signed endpoint values is positive. -/
theorem prod_parity_pos {lam : Fin n → ℝ → ℝ} (Z : Fin n → Finset ℝ) (d : Fin n → ℝ → ℝ)
    (hcont : ∀ i, ContinuousOn (lam i) (Set.Icc 0 1)) (hZ : ∀ i, (↑(Z i) : Set ℝ) ⊆ Set.Ioo 0 1)
    (hzero : ∀ i, ∀ t ∈ Set.Icc 0 1, lam i t = 0 ↔ t ∈ Z i)
    (htr : ∀ i, ∀ z ∈ Z i, d i z ≠ 0 ∧ HasDerivAt (lam i) (d i z) z) :
    0 < (-1 : ℝ) ^ (∑ i, (Z i).card) * ((∏ i, lam i 1) * ∏ i, lam i 0) := by
  have h : ∀ i, 0 < (-1 : ℝ) ^ (Z i).card * (lam i 1 * lam i 0) := fun i =>
    sign_parity (Z i) one_pos (hcont i) (hZ i) (hzero i) fun z hz =>
      ⟨d i z, (htr i z hz).1, (htr i z hz).2⟩
  have := Finset.prod_pos fun i (_ : i ∈ Finset.univ) => h i
  rwa [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_mul_distrib] at this

/-- **(QRP.10)**: `sgn det H(1) = (-1)^{sf} sgn det H(0)`, stated as positivity of the endpoint
product exactly when the spectral flow is even, for a Hermitian path whose eigenvalue branches
`lam i` are continuous with transversal zero sets `Z i` in `(0, 1)`. -/
theorem det_sign_spectral_flow {H : ℝ → Matrix (Fin n) (Fin n) ℂ} {lam : Fin n → ℝ → ℝ}
    (hdet : ∀ t, (H t).det = ((∏ i, lam i t : ℝ) : ℂ)) (Z : Fin n → Finset ℝ) (d : Fin n → ℝ → ℝ)
    (hcont : ∀ i, ContinuousOn (lam i) (Set.Icc 0 1)) (hZ : ∀ i, (↑(Z i) : Set ℝ) ⊆ Set.Ioo 0 1)
    (hzero : ∀ i, ∀ t ∈ Set.Icc 0 1, lam i t = 0 ↔ t ∈ Z i)
    (htr : ∀ i, ∀ z ∈ Z i, d i z ≠ 0 ∧ HasDerivAt (lam i) (d i z) z) :
    (0 < ((H 1).det * (H 0).det).re ↔ Even (spectralFlow Z d)) ∧
      (H 1).det ≠ 0 ∧ (H 0).det ≠ 0 := by
  have hpos := prod_parity_pos Z d hcont hZ hzero htr
  have hre : ((H 1).det * (H 0).det).re = (∏ i, lam i 1) * ∏ i, lam i 0 := by
    rw [hdet, hdet, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hne : (∏ i, lam i 1) * ∏ i, lam i 0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  refine ⟨?_, ?_, ?_⟩
  · rw [hre, even_spectralFlow_iff Z d fun i z hz => (htr i z hz).1]
    rcases Nat.even_or_odd (∑ i, (Z i).card) with he | ho
    · rw [he.neg_one_pow, one_mul] at hpos
      exact ⟨fun _ => he, fun _ => hpos⟩
    · rw [ho.neg_one_pow, neg_one_mul, neg_pos] at hpos
      constructor
      · intro h; exact absurd hpos (not_lt.mpr h.le)
      · intro h; exact absurd h (Nat.not_even_iff_odd.mpr ho)
  · intro h
    rw [hdet] at h
    exact hne (by rw [mul_eq_zero]; left; exact_mod_cast h)
  · intro h
    rw [hdet] at h
    exact hne (by rw [mul_eq_zero]; right; exact_mod_cast h)

end SpectralFlow

end FermionicPhaseTransport
end NCG
