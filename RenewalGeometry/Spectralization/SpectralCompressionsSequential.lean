/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.CompactResolventStrongCofinalMarkedRenewalLimitExact
import RenewalGeometry.OperatorLimits.CompactResolventSpectralProjectionContractionExact
import RenewalGeometry.Spectralization.SpectralCompressionStrictQuasidiagonalEquivalenceExact

open NCG
/-!
# Strong and norm-multiplicative spectral compressions along sequences

Paper `predictive_spectral_geometry`, label `thm:spectral-compressions`.

* **Commutator form of quasidiagonality** (any C⋆-algebra, any star-closed subset `T`):
  `‖[P, a]‖` controls and is controlled by the two off-diagonal corners
  (`norm_commutator_le_corners`, `norm_corner_le_norm_commutator`), and norm
  multiplicativity of the compressions on `T` is equivalent to `‖[P_n, a]‖ → 0` for every
  `a ∈ T` (`normMultiplicativeOn_iff_commutatorDecayOn`).
* **Sequences of spectral screens** for a separable compact-resolvent spectral triple
  (`exists_monotone_screens`): finite sets `s_n` of resolvent eigenvalues, increasing, such
  that the finite-rank orthogonal spectral projections `P_n` increase and `P_n → I` strongly.
* **Compressed commutator identity** (`compressed_commutator_identity`,
  `eq:compressed-commutator-identity`): for `x ∈ P H`,
  `[D_n, a_n] x = P [D, π(a)] x` with `D_n = P D|_{PH}`, `a_n = P π(a)|_{PH}`.
* **Strong compression** (`spectral_compressions_strong`): the strong-convergence conditions
  `eq:strong-compression-topology` along the sequence, for every bounded operator (in particular
  `π(a)`, the bounded extension of `[D, π(a)]` and the resolvents `(D - z)⁻¹`) and every product
  defect.
* **Norm multiplicativity ↔ commutator decay on `A_D`** along any sequence of spectral screens
  (`normMultiplicative_iff_commutator_tendsto`), hence a norm-multiplicative
  spectral-compression sequence exists exactly for spectrally quasidiagonal triples
  (`hasNormMultiplicativeCompression_iff_spectrallyQuasidiagonal`).
-/

open Filter Topology Set

noncomputable section

namespace RenewalGeometry.SpectralCompression

/-! ### Commutators and off-diagonal corners in a C⋆-algebra -/

section CStar

variable {B X : Type*} [CStarAlgebra B]

/-- Norm multiplicativity of the compressions on a subset `T`. -/
def NormMultiplicativeOn (P : X → B) (l : Filter X) (T : Set B) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, Tendsto
    (fun n => ‖compress (P n) (a * b) - compress (P n) a * compress (P n) b‖) l (𝓝 0)

/-- Commutator decay `‖[P_n, a]‖ → 0` on a subset `T`. -/
def CommutatorDecayOn (P : X → B) (l : Filter X) (T : Set B) : Prop :=
  ∀ a ∈ T, Tendsto (fun n => ‖P n * a - a * P n‖) l (𝓝 0)

theorem commutator_eq_corners (P a : B) :
    P * a - a * P = P * a * (1 - P) - (1 - P) * a * P := by
  noncomm_ring

theorem one_sub_idempotent (P : B) (hP : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  rw [sub_mul, one_mul, mul_sub, mul_one, hP, sub_self, sub_zero]

theorem left_corner_eq (P a : B) (hP : P * P = P) :
    P * (P * a - a * P) * (1 - P) = P * a * (1 - P) := by
  have h1 : P * (P * a - a * P) = P * a - P * a * P := by
    rw [mul_sub, ← mul_assoc, hP, mul_assoc]
  rw [h1, sub_mul, mul_assoc (P * a) P (1 - P), mul_sub P 1 P, mul_one, hP, sub_self, mul_zero,
    sub_zero]

theorem right_corner_eq (P a : B) (hP : P * P = P) :
    (1 - P) * (P * a - a * P) * P = -((1 - P) * a * P) := by
  have h1 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have h2 : (1 - P) * (P * a - a * P) = -((1 - P) * a * P) := by
    rw [mul_sub, ← mul_assoc, h1, zero_mul, zero_sub, mul_assoc]
  rw [h2, neg_mul, mul_assoc ((1 - P) * a) P P, hP]

theorem norm_commutator_le_corners (P a : B) :
    ‖P * a - a * P‖ ≤ ‖P * a * (1 - P)‖ + ‖(1 - P) * a * P‖ := by
  rw [commutator_eq_corners]
  exact norm_sub_le _ _

theorem norm_corner_le_norm_commutator (P a : B) (hP : P * P = P) (hPstar : star P = P) :
    ‖P * a * (1 - P)‖ ≤ ‖P * a - a * P‖ ∧ ‖(1 - P) * a * P‖ ≤ ‖P * a - a * P‖ := by
  have hp := norm_le_one_of_selfAdjoint_idempotent P hP hPstar
  have hq := norm_le_one_of_selfAdjoint_idempotent (1 - P) (one_sub_idempotent P hP)
    (by rw [star_sub, star_one, hPstar])
  have hc := norm_nonneg (P * a - a * P)
  constructor
  · rw [← left_corner_eq P a hP]
    calc ‖P * (P * a - a * P) * (1 - P)‖ ≤ ‖P‖ * ‖P * a - a * P‖ * ‖1 - P‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖P * a - a * P‖ * 1 := by gcongr
      _ = ‖P * a - a * P‖ := by ring
  · have : ‖(1 - P) * a * P‖ = ‖(1 - P) * (P * a - a * P) * P‖ := by
      rw [right_corner_eq P a hP, norm_neg]
    rw [this]
    calc ‖(1 - P) * (P * a - a * P) * P‖ ≤ ‖1 - P‖ * ‖P * a - a * P‖ * ‖P‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖P * a - a * P‖ * 1 := by gcongr
      _ = ‖P * a - a * P‖ := by ring

/-- `‖[P_n, a]‖ → 0` iff both off-diagonal corners vanish in norm. -/
theorem commutator_tendsto_iff_corners (P : X → B) (l : Filter X) (a : B)
    (hP : ∀ n, P n * P n = P n) (hPstar : ∀ n, star (P n) = P n) :
    Tendsto (fun n => ‖P n * a - a * P n‖) l (𝓝 0) ↔
      Tendsto (fun n => ‖(1 - P n) * a * P n‖) l (𝓝 0) ∧
      Tendsto (fun n => ‖P n * a * (1 - P n)‖) l (𝓝 0) := by
  constructor
  · intro h
    exact ⟨squeeze_zero (fun n => norm_nonneg _)
        (fun n => (norm_corner_le_norm_commutator (P n) a (hP n) (hPstar n)).2) h,
      squeeze_zero (fun n => norm_nonneg _)
        (fun n => (norm_corner_le_norm_commutator (P n) a (hP n) (hPstar n)).1) h⟩
  · rintro ⟨h1, h2⟩
    have := h2.add h1
    rw [add_zero] at this
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => norm_commutator_le_corners (P n) a) this

/-- **Norm multiplicativity on a star-closed subset is commutator decay on it**
(the `A_D`-restricted form of `normMultiplicativeAlong_iff_quasidiagonalAlong`). -/
theorem normMultiplicativeOn_iff_commutatorDecayOn (P : X → B) (l : Filter X) (T : Set B)
    (hT : ∀ a ∈ T, star a ∈ T)
    (hP : ∀ n, P n * P n = P n) (hPstar : ∀ n, star (P n) = P n) :
    NormMultiplicativeOn P l T ↔ CommutatorDecayOn P l T := by
  constructor
  · intro hmul a ha
    rw [commutator_tendsto_iff_corners P l a hP hPstar]
    constructor
    · have hsq : Tendsto (fun n => ‖(1 - P n) * a * P n‖ ^ 2) l (𝓝 0) := by
        convert hmul (star a) (hT a ha) a ha using 1
        funext n
        exact (norm_compress_star_mul_defect (P n) a (hP n) (hPstar n)).symm
      have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
      change Tendsto (fun n => Real.sqrt (‖(1 - P n) * a * P n‖ ^ 2)) l
        (𝓝 (Real.sqrt 0)) at hsqrt
      simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
    · have hsq : Tendsto (fun n => ‖P n * a * (1 - P n)‖ ^ 2) l (𝓝 0) := by
        convert hmul a ha (star a) (hT a ha) using 1
        funext n
        exact (norm_compress_mul_star_defect (P n) a (hP n) (hPstar n)).symm
      have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
      change Tendsto (fun n => Real.sqrt (‖P n * a * (1 - P n)‖ ^ 2)) l
        (𝓝 (Real.sqrt 0)) at hsqrt
      simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  · intro hcd a _ b hb
    have hupper : Tendsto (fun n => ‖a‖ * ‖P n * b - b * P n‖) l (𝓝 0) := by
      simpa using (hcd b hb).const_mul ‖a‖
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hupper
    have hp := norm_le_one_of_selfAdjoint_idempotent (P n) (hP n) (hPstar n)
    have hcorner := (norm_corner_le_norm_commutator (P n) b (hP n) (hPstar n)).2
    calc ‖compress (P n) (a * b) - compress (P n) a * compress (P n) b‖
        ≤ ‖P n‖ * ‖a‖ * ‖(1 - P n) * b * P n‖ := norm_compression_defect_le (P n) a b (hP n)
      _ ≤ 1 * ‖a‖ * ‖P n * b - b * P n‖ := by gcongr
      _ = ‖a‖ * ‖P n * b - b * P n‖ := by ring

end CStar

end RenewalGeometry.SpectralCompression

namespace RenewalGeometry.SpectralCompressionsSequential

open RenewalGeometry.SpectralCompression
open RenewalGeometry.CompactResolventDiracSpectralScreensExact
open RenewalGeometry.CompactResolventStrongCofinalMarkedRenewalLimitExact
open RenewalGeometry.CompactResolventSpectralProjectionContractionExact
open RenewalGeometry.CompactNormalFiniteSpectralScreensExact

universe u

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Elementary properties of the spectral screens -/

theorem screen_idempotent (S : SpectralTriple A H) (s : Finset ℂ) :
    diracSpectralScreen S s * diracSpectralScreen S s = diracSpectralScreen S s := by
  have h := (diracSpectralScreen_isSymmetricProjection S s).isIdempotentElem
  ext x
  exact LinearMap.congr_fun h.eq x

theorem screen_star (S : SpectralTriple A H) (s : Finset ℂ) :
    star (diracSpectralScreen S s) = diracSpectralScreen S s :=
  ((diracSpectralScreen_isSymmetricProjection S s).isSymmetric.isSelfAdjoint).star_eq

theorem screen_apply_of_mem_range (S : SpectralTriple A H) (s : Finset ℂ) {x : H}
    (hx : x ∈ LinearMap.range (diracSpectralScreen S s).toLinearMap) :
    diracSpectralScreen S s x = x := by
  obtain ⟨y, rfl⟩ := hx
  show diracSpectralScreen S s (diracSpectralScreen S s y) = diracSpectralScreen S s y
  rw [← mul_apply_eq_comp, screen_idempotent]

theorem screen_mem_domain (S : SpectralTriple A H) (s : Finset ℂ) (y : H) :
    diracSpectralScreen S s y ∈ S.dirac.domain :=
  diracSpectralScreen_range_le_domain S s (LinearMap.mem_range_self _ y)

/-- The range of the screen is monotone in the eigenvalue set. -/
theorem screen_range_mono (S : SpectralTriple A H) {s t : Finset ℂ} (hst : s ⊆ t) :
    LinearMap.range (diracSpectralScreen S s).toLinearMap ≤
      LinearMap.range (diracSpectralScreen S t).toLinearMap := by
  have h1 := spectralScreen_range S.resolvent S.resolvent_isCompact (resolvent_injective S) s
  have h2 := spectralScreen_range S.resolvent S.resolvent_isCompact (resolvent_injective S) t
  change LinearMap.range (spectralScreen S.resolvent S.resolvent_isCompact
      (resolvent_injective S) s).toLinearMap ≤ LinearMap.range (spectralScreen S.resolvent
      S.resolvent_isCompact (resolvent_injective S) t).toLinearMap
  rw [h1, h2]
  exact spectralScreenSubspace_mono S.resolvent hst

/-- Monotone screens: `P_t P_s = P_s` for `s ⊆ t`. -/
theorem screen_mul_of_subset (S : SpectralTriple A H) {s t : Finset ℂ} (hst : s ⊆ t) :
    diracSpectralScreen S t * diracSpectralScreen S s = diracSpectralScreen S s := by
  ext x
  exact screen_apply_of_mem_range S t (screen_range_mono S hst (LinearMap.mem_range_self _ x))

/-! ### Extraction of an increasing sequence of screens (separable case) -/

/-- For a separable Hilbert space the strongly convergent net of finite spectral screens has an
increasing cofinal sequence along which `P_n → I` strongly. -/
theorem exists_monotone_screens [TopologicalSpace.SeparableSpace H] (S : SpectralTriple A H) :
    ∃ s : ℕ → Finset ℂ, Monotone s ∧
      ∀ x, Tendsto (fun n => diracSpectralScreen S (s n) x) atTop (𝓝 x) := by
  classical
  set d := TopologicalSpace.denseSeq H
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq H
  have hev : ∀ n : ℕ, ∀ᶠ t in (atTop : Filter (Finset ℂ)), ∀ k ∈ Finset.range (n + 1),
      dist (diracSpectralScreen S t (d k)) (d k) < 1 / ((n : ℝ) + 1) := by
    intro n
    rw [Filter.eventually_all_finset]
    intro k _
    exact (tendsto_diracSpectralScreen_apply S (d k)).eventually
      (Metric.ball_mem_nhds _ (by positivity))
  choose a ha using fun n => eventually_atTop.mp (hev n)
  let s : ℕ → Finset ℂ := fun n => Nat.rec (a 0) (fun m acc => acc ∪ a (m + 1)) n
  have hs_succ : ∀ n, s (n + 1) = s n ∪ a (n + 1) := fun n => rfl
  have hmono : Monotone s := monotone_nat_of_le_succ fun n => by
    rw [hs_succ]; exact Finset.subset_union_left
  have hge : ∀ n, a n ≤ s n := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => rw [hs_succ]; exact Finset.subset_union_right
  refine ⟨s, hmono, fun x => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := hd.exists_dist_lt x (by positivity : (0 : ℝ) < ε / 3)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < ε / 3)
  refine ⟨max k N, fun n hn => ?_⟩
  have hkn : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have h1 := ha n (s n) (hge n) k hkn
  have hNn : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (N : ℝ) ≤ n := by exact_mod_cast (le_of_max_le_right hn)
    linarith
  set P := diracSpectralScreen S (s n)
  have hPc : dist (P x) (P (d k)) ≤ dist x (d k) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_diracSpectralScreen_apply_le S (s n) _
  calc dist (P x) x ≤ dist (P x) (P (d k)) + dist (P (d k)) (d k) + dist (d k) x :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have := dist_comm (d k) x
        gcongr
        · exact lt_of_le_of_lt hPc hk
        · linarith
        · linarith
    _ = ε := by ring

/-! ### The compressed commutator identity -/

/-- **`eq:compressed-commutator-identity`**: for a finite spectral screen `P`, an element `a`
whose representative preserves the Dirac domain, and `x ∈ P H`,
`[D_n, a_n] x = P (D π(a) x - π(a) D x)`, where `D_n = P D|_{PH}` and `a_n = P π(a)|_{PH}`
(all compressed vectors lie in the domain since `P H ⊆ dom D`). -/
theorem compressed_commutator_identity (S : SpectralTriple A H) (s : Finset ℂ) (a : A)
    (hpres : ∀ y ∈ S.dirac.domain, S.rep a y ∈ S.dirac.domain) {x : H}
    (hx : x ∈ LinearMap.range (diracSpectralScreen S s).toLinearMap) :
    diracSpectralScreen S s
        (S.dirac ⟨diracSpectralScreen S s (S.rep a x), screen_mem_domain S s _⟩) -
      diracSpectralScreen S s (S.rep a (diracSpectralScreen S s
        (S.dirac ⟨x, diracSpectralScreen_range_le_domain S s hx⟩))) =
      diracSpectralScreen S s
        (S.dirac ⟨S.rep a x, hpres x (diracSpectralScreen_range_le_domain S s hx)⟩ -
          S.rep a (S.dirac ⟨x, diracSpectralScreen_range_le_domain S s hx⟩)) := by
  set P := diracSpectralScreen S s
  have hxD : x ∈ S.dirac.domain := diracSpectralScreen_range_le_domain S s hx
  have haxD : S.rep a x ∈ S.dirac.domain := hpres x hxD
  -- `D (P (a x)) = P (D (a x))`
  have h1 : S.dirac ⟨P (S.rep a x), screen_mem_domain S s _⟩ =
      P (S.dirac ⟨S.rep a x, haxD⟩) :=
    diracSpectralScreen_commutes_dirac S s ⟨S.rep a x, haxD⟩
  -- `P (D x) = D (P x) = D x`
  have hPx : P x = x := screen_apply_of_mem_range S s hx
  have h2 : P (S.dirac ⟨x, hxD⟩) = S.dirac ⟨x, hxD⟩ := by
    have := diracSpectralScreen_commutes_dirac S s ⟨x, hxD⟩
    rw [← this]
    congr 1
    exact Subtype.ext hPx
  rw [h1, h2, map_sub]
  congr 1
  show (P * P) _ = P _
  rw [screen_idempotent]

/-- The compressed commutator identity with the bounded extension `C` of `[D, π(a)]`:
`[D_n, a_n] = P C|_{PH}`. -/
theorem compressed_commutator_identity_of_extension (S : SpectralTriple A H) (s : Finset ℂ)
    (a : A) (hpres : ∀ y ∈ S.dirac.domain, S.rep a y ∈ S.dirac.domain) (C : H →L[ℂ] H)
    (hC : ∀ (y : S.dirac.domain) (hy : S.rep a y ∈ S.dirac.domain),
      S.dirac ⟨S.rep a y, hy⟩ - S.rep a (S.dirac y) = C y) {x : H}
    (hx : x ∈ LinearMap.range (diracSpectralScreen S s).toLinearMap) :
    diracSpectralScreen S s
        (S.dirac ⟨diracSpectralScreen S s (S.rep a x), screen_mem_domain S s _⟩) -
      diracSpectralScreen S s (S.rep a (diracSpectralScreen S s
        (S.dirac ⟨x, diracSpectralScreen_range_le_domain S s hx⟩))) =
      diracSpectralScreen S s (C x) := by
  rw [compressed_commutator_identity S s a hpres hx]
  congr 1
  exact hC ⟨x, _⟩ _

/-- Every element of the smooth algebra `A_D` preserves the Dirac domain. -/
theorem rep_mem_domain (S : SpectralTriple A H) {a : A} (ha : a ∈ S.smoothAlgebra) :
    ∀ y ∈ S.dirac.domain, S.rep a y ∈ S.dirac.domain :=
  (S.lipschitz a ha).choose

/-! ### Sequences of spectral screens and the two compression classes -/

/-- A sequence of finite spectral screens of `D` increasing to the identity: each `P_n` is the
orthogonal spectral projection of `D` onto finitely many eigenspaces, the ranges increase and
`P_n → I` strongly. -/
def IsScreenSequence (S : SpectralTriple A H) (P : ℕ → H →L[ℂ] H) : Prop :=
  (∀ n, ∃ s : Finset ℂ, P n = diracSpectralScreen S s) ∧
  (∀ n, P (n + 1) * P n = P n) ∧
  (∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))

/-- **Spectral quasidiagonality** (`eq:sqd`): a sequence of finite spectral screens `P_n ↑ I`
with `‖[P_n, π(a)]‖ → 0` for every `a ∈ A_D`. -/
def SpectrallyQuasidiagonal (S : SpectralTriple A H) : Prop :=
  ∃ P : ℕ → H →L[ℂ] H, IsScreenSequence S P ∧
    ∀ a ∈ S.smoothAlgebra, Tendsto (fun n => ‖P n * S.rep a - S.rep a * P n‖) atTop (𝓝 0)

/-- Existence of a **norm-multiplicative spectral-compression sequence**
(`eq:norm-multiplicative-compression`). -/
def HasNormMultiplicativeCompression (S : SpectralTriple A H) : Prop :=
  ∃ P : ℕ → H →L[ℂ] H, IsScreenSequence S P ∧
    ∀ a ∈ S.smoothAlgebra, ∀ b ∈ S.smoothAlgebra, Tendsto
      (fun n => ‖P n * S.rep (a * b) * P n - (P n * S.rep a * P n) * (P n * S.rep b * P n)‖)
      atTop (𝓝 0)

theorem IsScreenSequence.idempotent {S : SpectralTriple A H} {P : ℕ → H →L[ℂ] H}
    (hP : IsScreenSequence S P) (n : ℕ) : P n * P n = P n := by
  obtain ⟨s, hs⟩ := hP.1 n
  rw [hs]; exact screen_idempotent S s

theorem IsScreenSequence.star_eq {S : SpectralTriple A H} {P : ℕ → H →L[ℂ] H}
    (hP : IsScreenSequence S P) (n : ℕ) : star (P n) = P n := by
  obtain ⟨s, hs⟩ := hP.1 n
  rw [hs]; exact screen_star S s

/-- **Norm multiplicativity ↔ commutator decay on `A_D`** along any sequence of spectral
screens: `‖P_n π(ab) P_n - P_n π(a) P_n π(b) P_n‖ → 0` for all `a, b ∈ A_D` iff
`‖[P_n, π(a)]‖ → 0` for all `a ∈ A_D`. -/
theorem normMultiplicative_iff_commutator_tendsto (S : SpectralTriple A H)
    {P : ℕ → H →L[ℂ] H} (hP : IsScreenSequence S P) :
    (∀ a ∈ S.smoothAlgebra, ∀ b ∈ S.smoothAlgebra, Tendsto
      (fun n => ‖P n * S.rep (a * b) * P n - (P n * S.rep a * P n) * (P n * S.rep b * P n)‖)
      atTop (𝓝 0)) ↔
    ∀ a ∈ S.smoothAlgebra, Tendsto (fun n => ‖P n * S.rep a - S.rep a * P n‖) atTop (𝓝 0) := by
  have key := normMultiplicativeOn_iff_commutatorDecayOn P atTop (S.rep '' S.smoothAlgebra)
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨star a, star_mem ha, map_star S.rep a⟩)
    hP.idempotent hP.star_eq
  constructor
  · intro h a ha
    refine key.mp ?_ (S.rep a) ⟨a, ha, rfl⟩
    rintro _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩
    have := h a' ha' b' hb'
    simpa [compress, map_mul] using this
  · intro h a ha b hb
    have := key.mpr (by
      rintro _ ⟨a', ha', rfl⟩
      exact h a' ha') (S.rep a) ⟨a, ha, rfl⟩ (S.rep b) ⟨b, hb, rfl⟩
    simpa [compress, map_mul] using this

/-- **A norm-multiplicative spectral-compression sequence exists exactly for spectrally
quasidiagonal triples.** -/
theorem hasNormMultiplicativeCompression_iff_spectrallyQuasidiagonal (S : SpectralTriple A H) :
    HasNormMultiplicativeCompression S ↔ SpectrallyQuasidiagonal S := by
  constructor
  · rintro ⟨P, hP, h⟩
    exact ⟨P, hP, (normMultiplicative_iff_commutator_tendsto S hP).mp h⟩
  · rintro ⟨P, hP, h⟩
    exact ⟨P, hP, (normMultiplicative_iff_commutator_tendsto S hP).mpr h⟩

/-! ### Strong compression along a sequence -/

/-- **Strong spectral compressions** (`thm:spectral-compressions`, first clause): every
separable compact-resolvent spectral triple admits a sequence of finite-rank orthogonal spectral
projections `P_n ↑ I` of `D` (finitely many eigenspaces each), preserving the domain and
commuting with `D`, such that every bounded operator `T` (in particular `π(a)`, the bounded
extension of `[D, π(a)]`, and the resolvents `(D - z)⁻¹`) is recovered strongly by its
compressions `P_n T P_n`, and every product defect `P_n T P_n U P_n - P_n T U P_n` tends to zero
strongly (`eq:strong-compression-topology`). -/
theorem spectral_compressions_strong [TopologicalSpace.SeparableSpace H]
    (S : SpectralTriple A H) :
    ∃ P : ℕ → H →L[ℂ] H, IsScreenSequence S P ∧
      (∀ n, (P n).IsSymmetricProjection) ∧
      (∀ n, FiniteDimensional ℂ (LinearMap.range (P n).toLinearMap)) ∧
      (∀ n, LinearMap.range (P n).toLinearMap ≤ LinearMap.range (P (n + 1)).toLinearMap) ∧
      (∀ n (x : S.dirac.domain), ∃ h : P n (x : H) ∈ S.dirac.domain,
        S.dirac ⟨P n (x : H), h⟩ = P n (S.dirac x)) ∧
      (∀ (T : H →L[ℂ] H) x, Tendsto (fun n => P n (T (P n x))) atTop (𝓝 (T x))) ∧
      (∀ (T U : H →L[ℂ] H) x, Tendsto
        (fun n => P n (T (P n (P n (U (P n x))))) - P n (T (U (P n x)))) atTop (𝓝 0)) := by
  obtain ⟨s, hmono, hconv⟩ := exists_monotone_screens S
  set P : ℕ → H →L[ℂ] H := fun n => diracSpectralScreen S (s n)
  have hseq : IsScreenSequence S P :=
    ⟨fun n => ⟨s n, rfl⟩, fun n => screen_mul_of_subset S (hmono (Nat.le_succ n)), hconv⟩
  have hcomp : ∀ (T : H →L[ℂ] H) x, Tendsto (fun n => P n (T (P n x))) atTop (𝓝 (T x)) := by
    intro T x
    have h1 : Tendsto (fun n => T (P n x)) atTop (𝓝 (T x)) :=
      T.continuous.continuousAt.tendsto.comp (hconv x)
    -- `‖P_n y_n - y‖ ≤ ‖y_n - y‖ + ‖P_n y - y‖`
    rw [tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.mp (hconv (T x)))
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h1.add h2)
    calc ‖P n (T (P n x)) - T x‖ = ‖P n (T (P n x) - T x) + (P n (T x) - T x)‖ := by
          rw [map_sub]; abel_nf
      _ ≤ ‖P n (T (P n x) - T x)‖ + ‖P n (T x) - T x‖ := norm_add_le _ _
      _ ≤ ‖T (P n x) - T x‖ + ‖P n (T x) - T x‖ := by
          gcongr
          exact norm_diracSpectralScreen_apply_le S (s n) _
  refine ⟨P, hseq, fun n => diracSpectralScreen_isSymmetricProjection S (s n),
    fun n => diracSpectralScreen_range_finiteDimensional S (s n),
    fun n => screen_range_mono S (hmono (Nat.le_succ n)),
    fun n x => ⟨diracSpectralScreen_mem_domain S (s n) x,
      diracSpectralScreen_commutes_dirac S (s n) x⟩, hcomp, ?_⟩
  intro T U x
  have hU := hcomp U x
  -- `P_n T P_n (P_n U P_n x) → T (U x)`
  have hTU : Tendsto (fun n => P n (T (P n (P n (U (P n x)))))) atTop (𝓝 (T (U x))) := by
    have hPP : ∀ n y, P n (P n y) = P n y := fun n y => by
      show (P n * P n) y = P n y
      rw [hseq.idempotent]
    simp_rw [hPP]
    have h1 : Tendsto (fun n => T (P n (U (P n x)))) atTop (𝓝 (T (U x))) :=
      T.continuous.continuousAt.tendsto.comp hU
    rw [tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
    have h2 := tendsto_iff_norm_sub_tendsto_zero.mp (hconv (T (U x)))
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h1.add h2)
    calc ‖P n (T (P n (U (P n x)))) - T (U x)‖ =
          ‖P n (T (P n (U (P n x))) - T (U x)) + (P n (T (U x)) - T (U x))‖ := by
          rw [map_sub]; abel_nf
      _ ≤ ‖P n (T (P n (U (P n x))) - T (U x))‖ + ‖P n (T (U x)) - T (U x)‖ := norm_add_le _ _
      _ ≤ ‖T (P n (U (P n x))) - T (U x)‖ + ‖P n (T (U x)) - T (U x)‖ := by
          gcongr
          exact norm_diracSpectralScreen_apply_le S (s n) _
  have := hTU.sub (hcomp (T.comp U) x)
  simpa using this

/-- **`thm:spectral-compressions`** (packaged, for the NCG spectral-triple encoding): for every
separable compact-resolvent spectral triple,
1. a sequence of finite-rank orthogonal spectral projections `P_n ↑ I` with the strong
   convergence conditions exists (`spectral_compressions_strong`);
2. the compressed commutator identity holds on every screen for every `a ∈ A_D`;
3. along every sequence of spectral screens, norm multiplicativity on `A_D` is equivalent to
   `‖[P_n, π(a)]‖ → 0` for every `a ∈ A_D`;
4. a norm-multiplicative spectral-compression sequence exists iff the triple is spectrally
   quasidiagonal. -/
theorem spectral_compressions [TopologicalSpace.SeparableSpace H] (S : SpectralTriple A H) :
    (∃ P : ℕ → H →L[ℂ] H, IsScreenSequence S P ∧
      (∀ n, (P n).IsSymmetricProjection) ∧
      (∀ n, FiniteDimensional ℂ (LinearMap.range (P n).toLinearMap)) ∧
      (∀ n, LinearMap.range (P n).toLinearMap ≤ LinearMap.range (P (n + 1)).toLinearMap) ∧
      (∀ n (x : S.dirac.domain), ∃ h : P n (x : H) ∈ S.dirac.domain,
        S.dirac ⟨P n (x : H), h⟩ = P n (S.dirac x)) ∧
      (∀ (T : H →L[ℂ] H) x, Tendsto (fun n => P n (T (P n x))) atTop (𝓝 (T x))) ∧
      (∀ (T U : H →L[ℂ] H) x, Tendsto
        (fun n => P n (T (P n (P n (U (P n x))))) - P n (T (U (P n x)))) atTop (𝓝 0))) ∧
    (∀ (s : Finset ℂ) (a : A) (ha : a ∈ S.smoothAlgebra) (x : H)
      (hx : x ∈ LinearMap.range (diracSpectralScreen S s).toLinearMap),
      diracSpectralScreen S s
          (S.dirac ⟨diracSpectralScreen S s (S.rep a x), screen_mem_domain S s _⟩) -
        diracSpectralScreen S s (S.rep a (diracSpectralScreen S s
          (S.dirac ⟨x, diracSpectralScreen_range_le_domain S s hx⟩))) =
        diracSpectralScreen S s
          (S.dirac ⟨S.rep a x,
              rep_mem_domain S ha x (diracSpectralScreen_range_le_domain S s hx)⟩ -
            S.rep a (S.dirac ⟨x, diracSpectralScreen_range_le_domain S s hx⟩))) ∧
    (∀ P : ℕ → H →L[ℂ] H, IsScreenSequence S P →
      ((∀ a ∈ S.smoothAlgebra, ∀ b ∈ S.smoothAlgebra, Tendsto
        (fun n => ‖P n * S.rep (a * b) * P n - (P n * S.rep a * P n) * (P n * S.rep b * P n)‖)
        atTop (𝓝 0)) ↔
      ∀ a ∈ S.smoothAlgebra, Tendsto (fun n => ‖P n * S.rep a - S.rep a * P n‖) atTop (𝓝 0))) ∧
    (HasNormMultiplicativeCompression S ↔ SpectrallyQuasidiagonal S) :=
  ⟨spectral_compressions_strong S,
    fun s a ha x hx => compressed_commutator_identity S s a (rep_mem_domain S ha) hx,
    fun _ hP => normMultiplicative_iff_commutator_tendsto S hP,
    hasNormMultiplicativeCompression_iff_spectrallyQuasidiagonal S⟩

end RenewalGeometry.SpectralCompressionsSequential
