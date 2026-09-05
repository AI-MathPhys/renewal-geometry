/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HilbertSchmidtExact

/-!
# Chronological source first birth, common response, and dynamic-head promotion

Machinery for `thm:GT-source-terminal-nonduplication`.  The previously assembled sources are one
map `Sprev : E' →L[ℝ] H` (the synthesis `(S₁ ⋯ S_{j-1})`) with `M = ran Sprev` and projection
`P^src`; the current source is `S : E →L[ℝ] H`; the fresh source is `F = (I - P^src) S`.

* (JS.1) `F† F = G_jj - G_{j,<j} G_{<j,<j}† G_{<j,j} ⪰ 0` (`fresh_gram`, `fresh_gram_isPositive`),
  and fresh ranges are orthogonal to the previous synthesis (`fresh_orthogonal`);
* (JS.2) `(I - P^term) R P^src = 0` for `Y = R M` (`terminal_nonduplication`);
* (JS.3) the five-arm Hilbert–Schmidt decomposition for a contractive response and nested heads
  `K₋ ⊆ K₊` containing `Y` (`five_arm`);
* (JS.4) nested-head residuals `R†(I - Π₋)R = R†(Π₊ - Π₋)R + R†(I - Π₊)R` (`nested_residual_op`);
* (JS.6) `∑ⱼ ‖Fⱼ‖²_HS ≤ ‖S_{1:N}‖²_HS` (`sum_fresh_hsSq_le`).
-/

open ContinuousLinearMap Submodule NCG.MoorePenrose NCG.HilbertSchmidt
open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace SourceTerminal

variable {E E' H Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [CompleteSpace E'] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [CompleteSpace H] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [CompleteSpace Y]

variable (Sprev : E' →L[ℝ] H) (S : E →L[ℝ] H)

/-- The previous source range `M = ran (S₁ ⋯ S_{j-1})`. -/
noncomputable def prevRange : Submodule ℝ H := LinearMap.range Sprev.toLinearMap

/-- The fresh source `F = (I - P^src) S`. -/
noncomputable def fresh : E →L[ℝ] H := residual Sprev S

omit [FiniteDimensional ℝ E] [CompleteSpace E] [CompleteSpace E'] [FiniteDimensional ℝ H]
  [CompleteSpace H] in
/-- The fresh range is orthogonal to the previous synthesis. -/
theorem fresh_orthogonal (x : E) (y : E') : ⟪fresh Sprev S x, Sprev y⟫ = 0 :=
  residual_inner_eq_zero Sprev S x y

omit [FiniteDimensional ℝ E] [CompleteSpace E] [CompleteSpace E'] [FiniteDimensional ℝ H]
  [CompleteSpace H] in
/-- The fresh range is orthogonal to every earlier fresh range (which lies in the synthesis). -/
theorem fresh_orthogonal_of_mem (x : E) {v : H} (hv : v ∈ prevRange Sprev) :
    ⟪fresh Sprev S x, v⟫ = 0 := by
  obtain ⟨y, rfl⟩ := hv
  exact fresh_orthogonal Sprev S x y

omit [FiniteDimensional ℝ E] in
/-- **(JS.1)**: the fresh source Gram is the Moore–Penrose Schur innovation. -/
theorem fresh_gram :
    (fresh Sprev S)† ∘L fresh Sprev S
      = gram S - (crossGram Sprev S)† ∘L gramPinv Sprev ∘L crossGram Sprev S := by
  rw [show gram S = S† ∘L S from rfl, schur_innovation]
  refine ContinuousLinearMap.ext fun x => ?_
  refine ext_inner_right ℝ fun y => ?_
  rw [comp_apply, comp_apply, adjoint_inner_left, adjoint_inner_left]
  change ⟪fresh Sprev S x, fresh Sprev S y⟫ = ⟪fresh Sprev S x, S y⟫
  have h := fresh_orthogonal_of_mem Sprev S x ((prevRange Sprev).starProjection_apply_mem (S y))
  rw [show fresh Sprev S y = S y - (prevRange Sprev).starProjection (S y) from
    residual_apply _ _ _, inner_sub_right, h, sub_zero]

omit [FiniteDimensional ℝ E] [CompleteSpace E'] [FiniteDimensional ℝ H] in
theorem fresh_gram_isPositive : ((fresh Sprev S)† ∘L fresh Sprev S).IsPositive :=
  isPositive_adjoint_comp_self _

/-! ### (JS.2) -/

variable (R : H →L[ℝ] Y)

/-- The terminal image `Y_{j-1} = R M_{j-1}`. -/
noncomputable def termRange : Submodule ℝ Y := (prevRange Sprev).map (R : H →ₗ[ℝ] Y)

omit [FiniteDimensional ℝ E'] [CompleteSpace E'] [CompleteSpace H] [CompleteSpace Y] in
/-- **(JS.2)**: `(I - P^term) R P^src = 0`: an old source cannot create a new terminal direction. -/
theorem terminal_nonduplication (v : H) :
    R ((prevRange Sprev).starProjection v)
      - (termRange Sprev R).starProjection (R ((prevRange Sprev).starProjection v)) = 0 := by
  rw [sub_eq_zero, eq_comm, (termRange Sprev R).starProjection_eq_self_iff]
  exact ⟨_, (prevRange Sprev).starProjection_apply_mem v, rfl⟩

/-! ### (JS.3)–(JS.4): nested heads and the five-arm decomposition -/

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ Y] in
/-- **(JS.4)**: `R†(I - Π₋)R = R†(Π₊ - Π₋)R + R†(I - Π₊)R`. -/
theorem nested_residual_op (Pm Pp : Y →L[ℝ] Y) :
    R† ∘L (1 - Pm) ∘L R = R† ∘L (Pp - Pm) ∘L R + R† ∘L (1 - Pp) ∘L R := by
  have : (1 - Pm) = (Pp - Pm) + (1 - Pp) := by abel
  rw [this, add_comp, comp_add]

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ Y] in
/-- A contractive response has `I - R† R ⪰ 0`. -/
theorem one_sub_gram_isPositive (hR : ‖R‖ ≤ 1) : (1 - R† ∘L R).IsPositive := by
  refine ⟨?_, fun v => ?_⟩
  · have : IsSelfAdjoint (1 - R† ∘L R) :=
      (IsSelfAdjoint.one _).sub (isPositive_adjoint_comp_self R).isSelfAdjoint
    exact this.isSymmetric
  · rw [reApplyInnerSelf_apply, RCLike.re_to_real, sub_apply, one_apply_eq_self, inner_sub_left,
      comp_apply, adjoint_inner_left, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have h1 : ‖R v‖ ≤ ‖v‖ := by
      calc ‖R v‖ ≤ ‖R‖ * ‖v‖ := R.le_opNorm v
        _ ≤ 1 * ‖v‖ := by gcongr
        _ = ‖v‖ := one_mul _
    nlinarith [norm_nonneg (R v), norm_nonneg v]

omit [CompleteSpace E'] in
/-- Hilbert–Schmidt Pythagoras along the source projection: `‖S‖² = ‖P S‖² + ‖F‖²`. -/
theorem hsSq_source_split :
    hsSq S = hsSq ((prevRange Sprev).starProjection ∘L S) + hsSq (fresh Sprev S) := by
  have hdecomp : S = (prevRange Sprev).starProjection ∘L S + fresh Sprev S := by
    ext x
    simp only [add_apply, comp_apply, fresh, residual_apply, prevRange]
    abel
  have horth : ((prevRange Sprev).starProjection ∘L S)† ∘L fresh Sprev S = 0 := by
    ext x
    rw [zero_apply]
    refine ext_inner_right ℝ fun y => ?_
    rw [comp_apply, adjoint_inner_left, inner_zero_left, comp_apply]
    exact fresh_orthogonal_of_mem Sprev S x ((prevRange Sprev).starProjection_apply_mem (S y))
  conv_lhs => rw [hdecomp]
  exact hsSq_add_of_adjoint_comp_eq_zero horth

/-- Hilbert–Schmidt Pythagoras along three mutually orthogonal projections summing to `I`. -/
theorem hsSq_three_arms {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [CompleteSpace W] (Pm Pp : W →L[ℝ] W)
    (hm : IsSelfAdjoint Pm) (hp : IsSelfAdjoint Pp) (hmm : Pm ∘L Pm = Pm) (hpp : Pp ∘L Pp = Pp)
    (hmp : Pm ∘L Pp = Pm) (A : E →L[ℝ] W) :
    hsSq A = hsSq (Pm ∘L A) + hsSq ((Pp - Pm) ∘L A) + hsSq ((1 - Pp) ∘L A) := by
  have e1 : Pp ∘L A = Pm ∘L A + (Pp - Pm) ∘L A := by
    rw [sub_comp]; abel
  have e2 : A = Pp ∘L A + (1 - Pp) ∘L A := by
    rw [sub_comp, one_def, id_comp]; abel
  have h1 : (Pm ∘L A)† ∘L ((Pp - Pm) ∘L A) = 0 := by
    rw [adjoint_comp, isSelfAdjoint_iff'.mp hm]
    have : Pm ∘L (Pp - Pm) = 0 := by rw [comp_sub, hmp, hmm, sub_self]
    rw [← comp_assoc, comp_assoc (A†), this, comp_zero, zero_comp]
  have h2 : (Pp ∘L A)† ∘L ((1 - Pp) ∘L A) = 0 := by
    rw [adjoint_comp, isSelfAdjoint_iff'.mp hp]
    have : Pp ∘L (1 - Pp) = 0 := by rw [comp_sub, one_def, comp_id, hpp, sub_self]
    rw [← comp_assoc, comp_assoc (A†), this, comp_zero, zero_comp]
  calc hsSq A = hsSq (Pp ∘L A + (1 - Pp) ∘L A) := by rw [← e2]
    _ = hsSq (Pp ∘L A) + hsSq ((1 - Pp) ∘L A) := hsSq_add_of_adjoint_comp_eq_zero h2
    _ = hsSq (Pm ∘L A + (Pp - Pm) ∘L A) + hsSq ((1 - Pp) ∘L A) := by rw [← e1]
    _ = hsSq (Pm ∘L A) + hsSq ((Pp - Pm) ∘L A) + hsSq ((1 - Pp) ∘L A) := by
        rw [hsSq_add_of_adjoint_comp_eq_zero h1]

omit [CompleteSpace E'] in
/-- **(JS.3)**: the five-arm Hilbert–Schmidt decomposition of the current source for a
contractive response and nested terminal heads `Π₋ ≤ Π₊`. -/
theorem five_arm (hR : ‖R‖ ≤ 1) (Pm Pp : Y →L[ℝ] Y)
    (hm : IsSelfAdjoint Pm) (hp : IsSelfAdjoint Pp) (hmm : Pm ∘L Pm = Pm) (hpp : Pp ∘L Pp = Pp)
    (hmp : Pm ∘L Pp = Pm) :
    hsSq S = hsSq ((prevRange Sprev).starProjection ∘L S)
      + hsSq (Pm ∘L (R ∘L fresh Sprev S))
      + hsSq ((Pp - Pm) ∘L (R ∘L fresh Sprev S))
      + hsSq ((1 - Pp) ∘L (R ∘L fresh Sprev S))
      + hsSq (PositiveSqrt.sqrt (1 - R† ∘L R) (one_sub_gram_isPositive R hR) ∘L fresh Sprev S) := by
  rw [hsSq_source_split Sprev S,
    hsSq_eq_hsSq_comp_add_sqrt R (one_sub_gram_isPositive R hR) (fresh Sprev S),
    hsSq_three_arms Pm Pp hm hp hmm hpp hmp (R ∘L fresh Sprev S)]
  ring

/-! ### (JS.6): the fresh sources are dominated by the assembled synthesis -/

omit [CompleteSpace E'] in
/-- `‖F‖²_HS ≤ ‖S‖²_HS`: the fresh source is dominated by the current source. -/
theorem hsSq_fresh_le : hsSq (fresh Sprev S) ≤ hsSq S := by
  rw [hsSq_source_split Sprev S]
  exact le_add_of_nonneg_left (hsSq_nonneg _)

/-! ### (JS.5): the irreducible fresh source action -/

/-- The fresh range `Ran Fⱼ`. -/
noncomputable def freshRange : Submodule ℝ H := LinearMap.range (fresh Sprev S).toLinearMap

/-- The fresh source with codomain restricted to its range. -/
noncomputable def freshRes : E →L[ℝ] freshRange Sprev S :=
  (fresh Sprev S).codRestrict (freshRange Sprev S) fun x => LinearMap.mem_range_self _ x

/-- `Lⱼ = (I - Π₊) ℛ |_{Ran Fⱼ}`. -/
noncomputable def irrMap (Pp : Y →L[ℝ] Y) : freshRange Sprev S →L[ℝ] Y :=
  ((1 - Pp) ∘L R) ∘L (freshRange Sprev S).subtypeL

/-- `qⱼ = Lⱼ Fⱼ`. -/
noncomputable def irrSource (Pp : Y →L[ℝ] Y) : E →L[ℝ] Y :=
  irrMap Sprev S R Pp ∘L freshRes Sprev S

omit [FiniteDimensional ℝ E] [CompleteSpace E] [CompleteSpace E'] [FiniteDimensional ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ Y] [CompleteSpace Y] in
theorem irrSource_eq (Pp : Y →L[ℝ] Y) :
    irrSource Sprev S R Pp = (1 - Pp) ∘L (R ∘L fresh Sprev S) := rfl

/-- The irreducible fresh source action `dⱼ^bi = Tr[qⱼ† Cⱼ† qⱼ]` with `Cⱼ = Lⱼ Lⱼ†`. -/
noncomputable def irrAction (Pp : Y →L[ℝ] Y) : ℝ :=
  LinearMap.trace ℝ E (((irrSource Sprev S R Pp)† ∘L gramPinv ((irrMap Sprev S R Pp)†)
    ∘L irrSource Sprev S R Pp : E →L[ℝ] E) : E →ₗ[ℝ] E)

omit [CompleteSpace E'] in
theorem hsSq_freshRes : hsSq (freshRes Sprev S) = hsSq (fresh Sprev S) := by
  rw [hsSq_eq_sum (stdOrthonormalBasis ℝ E), hsSq_eq_sum (stdOrthonormalBasis ℝ E)]
  rfl

omit [CompleteSpace E'] in
/-- **(JS.5)**: the Hilbert–Schmidt Thomson principle — `dⱼ^bi = min_{Lⱼ H = qⱼ} ‖H‖²_HS`,
attained, and at most `‖Fⱼ‖²_HS`. -/
theorem irrAction_eq_min (Pp : Y →L[ℝ] Y) :
    ∃ H₀ : E →L[ℝ] freshRange Sprev S,
      irrMap Sprev S R Pp ∘L H₀ = irrSource Sprev S R Pp ∧
      hsSq H₀ = irrAction Sprev S R Pp ∧
      (∀ K : E →L[ℝ] freshRange Sprev S,
        irrMap Sprev S R Pp ∘L K = irrSource Sprev S R Pp → hsSq H₀ ≤ hsSq K) ∧
      irrAction Sprev S R Pp ≤ hsSq (fresh Sprev S) := by
  have hQ : ∀ x, irrSource Sprev S R Pp x
      ∈ LinearMap.range (irrMap Sprev S R Pp).toLinearMap := fun x => ⟨freshRes Sprev S x, rfl⟩
  refine ⟨minNormLift (irrMap Sprev S R Pp) (irrSource Sprev S R Pp), comp_minNormLift _ _ hQ,
    hsSq_minNormLift _ _ hQ, fun _ hK => hsSq_minNormLift_le _ _ hK, ?_⟩
  rw [irrAction, ← hsSq_minNormLift _ _ hQ, ← hsSq_freshRes]
  exact hsSq_minNormLift_le _ _ rfl

omit [CompleteSpace E'] in
theorem irrAction_le_hsSq_fresh (Pp : Y →L[ℝ] Y) :
    irrAction Sprev S R Pp ≤ hsSq (fresh Sprev S) :=
  (irrAction_eq_min Sprev S R Pp).choose_spec.2.2.2

/-! ### Chronological families and (JS.6) -/

section Family

variable {N : ℕ} {V : Fin N → Type*} [∀ j, NormedAddCommGroup (V j)]
  [∀ j, InnerProductSpace ℝ (V j)] [∀ j, FiniteDimensional ℝ (V j)] [∀ j, CompleteSpace (V j)]

/-- The completely assembled synthesis `S_{1:N} = (S₁ ⋯ S_N) : ⊕ⱼ Vⱼ → H`. -/
noncomputable def assembled (S : ∀ j, V j →L[ℝ] H) : PiLp 2 V →L[ℝ] H :=
  ∑ j, S j ∘L PiLp.proj 2 V j

omit [FiniteDimensional ℝ H] [CompleteSpace H] [∀ j, FiniteDimensional ℝ (V j)]
  [∀ j, CompleteSpace (V j)] in
theorem assembled_single (S : ∀ j, V j →L[ℝ] H) (j : Fin N) (v : V j) :
    assembled S (PiLp.single 2 j v) = S j v := by
  simp only [assembled, _root_.sum_apply, comp_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

omit [FiniteDimensional ℝ H] in
/-- `‖S_{1:N}‖²_HS = ∑ⱼ ‖Sⱼ‖²_HS`. -/
theorem hsSq_assembled (S : ∀ j, V j →L[ℝ] H) : hsSq (assembled S) = ∑ j, hsSq (S j) := by
  rw [hsSq_eq_sum (Pi.orthonormalBasis fun j => stdOrthonormalBasis ℝ (V j)), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsSq_eq_sum (stdOrthonormalBasis ℝ (V j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.orthonormalBasis_apply]
  exact congrArg (fun v => ‖v‖ ^ 2) (assembled_single S j (stdOrthonormalBasis ℝ (V j) i))

/-- The previous synthesis `(S₁ ⋯ S_{j-1})`. -/
noncomputable def prevSynth (S : ∀ j, V j →L[ℝ] H) (j : Fin N) :
    PiLp 2 (fun k : Fin j => V (Fin.castLE j.isLt.le k)) →L[ℝ] H :=
  assembled fun k : Fin j => S (Fin.castLE j.isLt.le k)

omit [FiniteDimensional ℝ H] [CompleteSpace H] [∀ j, FiniteDimensional ℝ (V j)]
  [∀ j, CompleteSpace (V j)] in
theorem range_le_prevRange (S : ∀ j, V j →L[ℝ] H) {k j : Fin N} (hkj : k < j) :
    LinearMap.range (S k).toLinearMap ≤ prevRange (prevSynth S j) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨PiLp.single 2 ⟨k, hkj⟩ x,
    assembled_single (fun i : Fin j => S (Fin.castLE j.isLt.le i)) ⟨k, hkj⟩ x⟩

omit [FiniteDimensional ℝ H] [CompleteSpace H] [∀ j, FiniteDimensional ℝ (V j)]
  [∀ j, CompleteSpace (V j)] in
theorem prevRange_mono (S : ∀ j, V j →L[ℝ] H) {k j : Fin N} (hkj : k ≤ j) :
    prevRange (prevSynth S k) ≤ prevRange (prevSynth S j) := by
  rintro _ ⟨x, rfl⟩
  change assembled _ x ∈ _
  simp only [assembled, _root_.sum_apply, comp_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact range_le_prevRange S (lt_of_lt_of_le (Fin.lt_def.mpr i.isLt) hkj) ⟨_, rfl⟩

omit [CompleteSpace H] [∀ j, CompleteSpace (V j)] in
theorem fresh_mem_prevRange (S : ∀ j, V j →L[ℝ] H) {k j : Fin N} (hkj : k < j) (x : V k) :
    fresh (prevSynth S k) (S k) x ∈ prevRange (prevSynth S j) := by
  rw [fresh, residual_apply]
  exact Submodule.sub_mem _ (range_le_prevRange S hkj ⟨x, rfl⟩)
    (prevRange_mono S hkj.le ((prevRange (prevSynth S k)).starProjection_apply_mem _))

omit [CompleteSpace H] [∀ j, CompleteSpace (V j)] in
/-- **(JS.1, second clause)**: the fresh ranges of a chronological family are mutually
orthogonal. -/
theorem fresh_orthogonal_family (S : ∀ j, V j →L[ℝ] H) {k j : Fin N} (hkj : k < j)
    (x : V j) (y : V k) :
    ⟪fresh (prevSynth S j) (S j) x, fresh (prevSynth S k) (S k) y⟫ = 0 :=
  fresh_orthogonal_of_mem _ _ x (fresh_mem_prevRange S hkj y)

/-- `∑ⱼ ‖Fⱼ‖²_HS ≤ ‖S_{1:N}‖²_HS`. -/
theorem sum_fresh_hsSq_le (S : ∀ j, V j →L[ℝ] H) :
    ∑ j, hsSq (fresh (prevSynth S j) (S j)) ≤ hsSq (assembled S) := by
  rw [hsSq_assembled]
  exact Finset.sum_le_sum fun j _ => hsSq_fresh_le _ _

/-- **(JS.6)**: `∑ⱼ dⱼ^bi ≤ ∑ⱼ ‖Fⱼ‖²_HS ≤ ‖S_{1:N}‖²_HS`. -/
theorem sum_irrAction_le (S : ∀ j, V j →L[ℝ] H) (R : H →L[ℝ] Y) (Pp : Y →L[ℝ] Y) :
    ∑ j, irrAction (prevSynth S j) (S j) R Pp ≤ ∑ j, hsSq (fresh (prevSynth S j) (S j)) ∧
      ∑ j, hsSq (fresh (prevSynth S j) (S j)) ≤ hsSq (assembled S) :=
  ⟨Finset.sum_le_sum fun _ _ => irrAction_le_hsSq_fresh _ _ R Pp, sum_fresh_hsSq_le S⟩

/-- **`thm:GT-source-terminal-nonduplication`** for a chronological family `Sⱼ : Vⱼ → H`, one
contractive common response `ℛ : H → Y`, and protocol-fixed nested heads `Π₋ ≤ Π₊`:
(JS.1) the fresh Grams are the Moore–Penrose Schur innovations and the fresh ranges are
mutually orthogonal; (JS.2) `(I - P^term) ℛ P^src = 0`; (JS.3) the five-arm decomposition;
(JS.4) the nested-head residual identity; (JS.5) the Thomson principle for `dⱼ^bi`;
(JS.6) `∑ dⱼ^bi ≤ ∑ ‖Fⱼ‖² ≤ ‖S_{1:N}‖²`. -/
theorem source_terminal_nonduplication (S : ∀ j, V j →L[ℝ] H) (R : H →L[ℝ] Y) (hR : ‖R‖ ≤ 1)
    (Pm Pp : Y →L[ℝ] Y) (hm : IsSelfAdjoint Pm) (hp : IsSelfAdjoint Pp)
    (hmm : Pm ∘L Pm = Pm) (hpp : Pp ∘L Pp = Pp) (hmp : Pm ∘L Pp = Pm) :
    (∀ j, (fresh (prevSynth S j) (S j))† ∘L fresh (prevSynth S j) (S j)
        = gram (S j) - (crossGram (prevSynth S j) (S j))† ∘L gramPinv (prevSynth S j)
            ∘L crossGram (prevSynth S j) (S j)) ∧
      (∀ j, ((fresh (prevSynth S j) (S j))† ∘L fresh (prevSynth S j) (S j)).IsPositive) ∧
      (∀ {k j : Fin N}, k < j → ∀ (x : V j) (y : V k),
        ⟪fresh (prevSynth S j) (S j) x, fresh (prevSynth S k) (S k) y⟫ = 0) ∧
      (∀ j (v : H), R ((prevRange (prevSynth S j)).starProjection v)
        - (termRange (prevSynth S j) R).starProjection
            (R ((prevRange (prevSynth S j)).starProjection v)) = 0) ∧
      (∀ j, hsSq (S j) = hsSq ((prevRange (prevSynth S j)).starProjection ∘L S j)
        + hsSq (Pm ∘L (R ∘L fresh (prevSynth S j) (S j)))
        + hsSq ((Pp - Pm) ∘L (R ∘L fresh (prevSynth S j) (S j)))
        + hsSq ((1 - Pp) ∘L (R ∘L fresh (prevSynth S j) (S j)))
        + hsSq (PositiveSqrt.sqrt (1 - R† ∘L R) (one_sub_gram_isPositive R hR)
            ∘L fresh (prevSynth S j) (S j))) ∧
      R† ∘L (1 - Pm) ∘L R = R† ∘L (Pp - Pm) ∘L R + R† ∘L (1 - Pp) ∘L R ∧
      (∀ j, ∃ H₀ : V j →L[ℝ] freshRange (prevSynth S j) (S j),
        irrMap (prevSynth S j) (S j) R Pp ∘L H₀ = irrSource (prevSynth S j) (S j) R Pp ∧
        hsSq H₀ = irrAction (prevSynth S j) (S j) R Pp ∧
        (∀ K : V j →L[ℝ] freshRange (prevSynth S j) (S j),
          irrMap (prevSynth S j) (S j) R Pp ∘L K = irrSource (prevSynth S j) (S j) R Pp →
            hsSq H₀ ≤ hsSq K) ∧
        irrAction (prevSynth S j) (S j) R Pp ≤ hsSq (fresh (prevSynth S j) (S j))) ∧
      ∑ j, irrAction (prevSynth S j) (S j) R Pp ≤ ∑ j, hsSq (fresh (prevSynth S j) (S j)) ∧
      ∑ j, hsSq (fresh (prevSynth S j) (S j)) ≤ hsSq (assembled S) :=
  ⟨fun _ => fresh_gram _ _, fun _ => fresh_gram_isPositive _ _,
    fun hkj x y => fresh_orthogonal_family S hkj x y, fun _ v => terminal_nonduplication _ R v,
    fun _ => five_arm _ _ R hR Pm Pp hm hp hmm hpp hmp, nested_residual_op R Pm Pp,
    fun _ => irrAction_eq_min _ _ R Pp, (sum_irrAction_le S R Pp).1, (sum_irrAction_le S R Pp).2⟩

end Family

end SourceTerminal
end NCG
