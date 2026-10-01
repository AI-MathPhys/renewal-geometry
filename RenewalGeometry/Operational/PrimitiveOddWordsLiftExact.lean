/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.OddChoiOccurrenceExact
import RenewalGeometry.Operational.SpectatorProduct

/-!
# Primitive odd alternative and the microscopic odd-lift ambiguity
  (`cor:primitive-odd-alternative`, `cth:microscopic-odd-lift`)

Spacetime–gauge duality manuscript, `app:odd-occurrence` and `app:microscopic-odd-lift`.

## `cor:primitive-odd-alternative`

A finite alphabet `Σ` of CP letters `Φ_a = ∑ K_{a,i} · K_{a,i}ᴴ` (finite Kraus families),
the profile `m_odd(Σ) = ∑_a μ_J(Φ_a)` (`oddProfile`), and an autonomous word grammar whose
steps are letters or maps from a set `W` of passive writers / initializations, each of
which is grading even (has a Kraus family commuting with `J`, `HasEvenKraus`).  Then
`m_odd(Σ) = 0` iff every admissible word has zero odd Choi mass, iff every Kraus
resolution of every admissible word commutes with `J` (`primitive_odd_alternative`);
and `m_odd(Σ) > 0` forces a letter with nonzero cross-sign corner
(`primitive_odd_support`).

## `cth:microscopic-odd-lift`

Visible carrier `m` (dimension `d = card m`), spectator `ℂ²` with grading `σ_z`,
`U_θ = cos θ · 1 + i sin θ · σ_x`, lifted map `id ⊗ Ad_{U_θ}` with Kraus operator
`1 ⊗ₖ U_θ` (`oddLift`).  Discarding the spectator gives the identity channel
(`partialTrace_oddLift`, `oddLift_visible_channel`), every visible multitime word is
unchanged (`partialTrace_liftedWord`), but `μ_{Z ⊗ σ_z}(id ⊗ Ad_{U_θ}) = 2 d sin²θ`
for any visible grading `Z` (`oddChoiMass_oddLift`), while the visible active mass of the
identity channel is `0` (`activeCrossSignMass_id`).  Packaged as `microscopic_odd_lift`.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace RenewalGeometry
namespace PrimitiveOddWords

open OddChoiOccurrence

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A linear map is grading even (in the Kraus sense) when it has a finite Kraus family all
of whose directions commute with the grading `J`. -/
def HasEvenKraus (J : Matrix n n ℂ) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (K : κ → Matrix n n ℂ),
    (∀ X, Φ X = ∑ b, K b * X * (K b)ᴴ) ∧ ∀ b, K b * J = J * K b

theorem hasEvenKraus_id (J : Matrix n n ℂ) : HasEvenKraus J LinearMap.id :=
  ⟨Unit, inferInstance, fun _ => 1, fun X => by simp, fun _ => by simp⟩

/-- Products of grading-even Kraus directions are grading even. -/
theorem hasEvenKraus_comp {J : Matrix n n ℂ} {Φ Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΦ : HasEvenKraus J Φ) (hΨ : HasEvenKraus J Ψ) : HasEvenKraus J (Ψ ∘ₗ Φ) := by
  obtain ⟨κ, _, K, hK, hKc⟩ := hΦ
  obtain ⟨κ', _, K', hK', hK'c⟩ := hΨ
  refine ⟨κ × κ', inferInstance, fun p => K' p.2 * K p.1, fun X => ?_, fun p => ?_⟩
  · rw [LinearMap.comp_apply, hK, hK', Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  · simp only
    rw [Matrix.mul_assoc, hKc, ← Matrix.mul_assoc, hK'c, Matrix.mul_assoc]

theorem oddChoiMass_eq_zero_of_hasEvenKraus {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (h : HasEvenKraus J Φ) : oddChoiMass J Φ = 0 := by
  obtain ⟨κ, _, K, hK, hKc⟩ := h
  exact ((oddChoiMass_eq_zero_iff hJh hJ Φ K hK).2.2).mpr hKc

/-- The resolved word map of a list of steps (the first step acts first). -/
def wordMap (steps : List (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  steps.foldr (fun f acc => acc ∘ₗ f) LinearMap.id

theorem wordMap_singleton (f : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : wordMap [f] = f := by
  simp [wordMap]

section Alphabet

variable {Sig : Type*} [Fintype Sig] {ι : Sig → Type} [∀ a, Fintype (ι a)]

/-- The alphabet profile `m_odd(Σ) = ∑_a μ_J(Φ_a)` (`eq:primitive-odd-profile`). -/
noncomputable def oddProfile (J : Matrix n n ℂ) (K : ∀ a, ι a → Matrix n n ℂ) : ℂ :=
  ∑ a, oddChoiMass J (krausLin (K a))

/-- Admissible autonomous words: every step is a letter of the alphabet or one of the
(grading-even) passive writers / initializations `W`. -/
def Admissible (K : ∀ a, ι a → Matrix n n ℂ) (W : Set (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ))
    (steps : List (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)) : Prop :=
  ∀ f ∈ steps, (∃ a, f = krausLin (K a)) ∨ f ∈ W

theorem oddChoiMass_letter_eq {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    (K : ∀ a, ι a → Matrix n n ℂ) (a : Sig) :
    oddChoiMass J (krausLin (K a)) = ((∑ i, hsSq (gradeOdd J (K a i)) : ℝ) : ℂ) :=
  oddChoiMass_eq_sum_hsSq_odd hJh hJ _ (K a) (fun X => krausLin_apply (K a) X)

theorem oddProfile_eq {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    (K : ∀ a, ι a → Matrix n n ℂ) :
    oddProfile J K = ((∑ a, ∑ i, hsSq (gradeOdd J (K a i)) : ℝ) : ℂ) := by
  rw [oddProfile, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun a _ => oddChoiMass_letter_eq hJh hJ K a

theorem oddProfile_nonneg {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    (K : ∀ a, ι a → Matrix n n ℂ) : 0 ≤ oddProfile J K := by
  rw [oddProfile_eq hJh hJ]
  exact Complex.zero_le_real.mpr
    (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => hsSq_nonneg _)

theorem oddProfile_eq_zero_iff {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    (K : ∀ a, ι a → Matrix n n ℂ) :
    oddProfile J K = 0 ↔ ∀ a, oddChoiMass J (krausLin (K a)) = 0 := by
  rw [oddProfile_eq hJh hJ, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => Finset.sum_nonneg fun i _ => hsSq_nonneg _)]
  simp only [Finset.mem_univ, true_implies, oddChoiMass_letter_eq hJh hJ K,
    Complex.ofReal_eq_zero]

theorem admissible_hasEvenKraus {J : Matrix n n ℂ} {K : ∀ a, ι a → Matrix n n ℂ}
    {W : Set (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)} (hW : ∀ f ∈ W, HasEvenKraus J f)
    (hletters : ∀ a, HasEvenKraus J (krausLin (K a))) :
    ∀ steps, Admissible K W steps → HasEvenKraus J (wordMap steps) := by
  intro steps
  induction steps with
  | nil => intro _; exact hasEvenKraus_id J
  | cons f rest ih =>
    intro hadm
    have hf : HasEvenKraus J f := by
      rcases hadm f List.mem_cons_self with ⟨a, rfl⟩ | hfW
      · exact hletters a
      · exact hW f hfW
    have hrest := ih (fun g hg => hadm g (List.mem_cons_of_mem f hg))
    simpa [wordMap, List.foldr] using hasEvenKraus_comp hf hrest

/-- **`cor:primitive-odd-alternative`, `eq:primitive-odd-stop`.**  With grading-even passive
writers and initializations `W`, `m_odd(Σ) = 0` iff every admissible finite word has zero
odd Choi mass, iff every Kraus resolution of every admissible word consists of
grading-even directions (commuting with `J`). -/
theorem primitive_odd_alternative {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    (K : ∀ a, ι a → Matrix n n ℂ) (W : Set (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ))
    (hW : ∀ f ∈ W, HasEvenKraus J f) :
    (oddProfile J K = 0 ↔
      ∀ steps, Admissible K W steps → oddChoiMass J (wordMap steps) = 0) ∧
    (oddProfile J K = 0 ↔
      ∀ steps, Admissible K W steps → ∀ (κ : Type) [Fintype κ] (K' : κ → Matrix n n ℂ),
        (∀ X, wordMap steps X = ∑ b, K' b * X * (K' b)ᴴ) → ∀ b, K' b * J = J * K' b) := by
  have hfwd : oddProfile J K = 0 → ∀ steps, Admissible K W steps →
      HasEvenKraus J (wordMap steps) := by
    intro h0
    refine admissible_hasEvenKraus hW fun a => ?_
    have ha := (oddProfile_eq_zero_iff hJh hJ K).mp h0 a
    exact ⟨ι a, inferInstance, K a, fun X => krausLin_apply (K a) X,
      ((oddChoiMass_eq_zero_iff hJh hJ _ (K a) (fun X => krausLin_apply (K a) X)).2.2).mp ha⟩
  have hletter : ∀ a, Admissible K W [krausLin (K a)] := by
    intro a f hf
    rw [List.mem_singleton] at hf
    exact Or.inl ⟨a, hf⟩
  refine ⟨⟨fun h0 steps hadm => oddChoiMass_eq_zero_of_hasEvenKraus hJh hJ (hfwd h0 steps hadm),
    fun h => (oddProfile_eq_zero_iff hJh hJ K).mpr fun a => ?_⟩,
    ⟨fun h0 steps hadm κ _ K' hK' => ?_, fun h => (oddProfile_eq_zero_iff hJh hJ K).mpr
      fun a => ?_⟩⟩
  · simpa [wordMap_singleton] using h [krausLin (K a)] (hletter a)
  · exact ((oddChoiMass_eq_zero_iff hJh hJ _ K' hK').2.2).mp
      (oddChoiMass_eq_zero_of_hasEvenKraus hJh hJ (hfwd h0 steps hadm))
  · have hc := h [krausLin (K a)] (hletter a) (ι a) (K a)
      (fun X => by rw [wordMap_singleton, krausLin_apply])
    exact ((oddChoiMass_eq_zero_iff hJh hJ _ (K a) (fun X => krausLin_apply (K a) X)).2.2).mpr hc

/-- **`cor:primitive-odd-alternative`, support clause.**  If `m_odd(Σ) > 0`, some letter has
positive odd Choi mass and one of its Kraus directions has a nonzero cross-sign corner
`P₋ K P₊` or `P₊ K P₋`. -/
theorem primitive_odd_support {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    (K : ∀ a, ι a → Matrix n n ℂ) (hpos : 0 < oddProfile J K) :
    ∃ a, 0 < oddChoiMass J (krausLin (K a)) ∧ ∃ i,
      ActiveOddLift.gradingMinus J * K a i * ActiveOddLift.gradingPlus J ≠ 0 ∨
      ActiveOddLift.gradingPlus J * K a i * ActiveOddLift.gradingMinus J ≠ 0 := by
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
  have hpa : 0 < oddChoiMass J (krausLin (K a)) :=
    lt_of_le_of_ne (oddChoiMass_nonneg hJh hJ _ (K a) (fun X => krausLin_apply (K a) X))
      (Ne.symm ha)
  refine ⟨a, hpa, ?_⟩
  rw [oddChoiMass_eq_sum_hsSq_corners hJh hJ _ (K a) (fun X => krausLin_apply (K a) X)] at ha
  have ha' : (∑ i, (hsSq (ActiveOddLift.gradingMinus J * K a i * ActiveOddLift.gradingPlus J)
      + hsSq (ActiveOddLift.gradingPlus J * K a i * ActiveOddLift.gradingMinus J))) ≠ 0 := by
    intro h; apply ha; rw [h, Complex.ofReal_zero]
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha'
  refine ⟨i, ?_⟩
  by_contra hcon
  push_neg at hcon
  apply hi
  rw [hcon.1, hcon.2]
  simp [hsSq]

end Alphabet

end PrimitiveOddWords
namespace MicroscopicOddLift

open OddChoiOccurrence

/-- Pauli `σ_x`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `σ_z`, the spectator grading. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `U_θ = cos θ · 1 + i sin θ · σ_x`. -/
noncomputable def liftUnitary (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos θ : ℂ) • 1 + (Complex.I * Real.sin θ) • pauliX

theorem liftUnitary_eq (θ : ℝ) :
    liftUnitary θ = !![(Real.cos θ : ℂ), Complex.I * Real.sin θ;
      Complex.I * Real.sin θ, (Real.cos θ : ℂ)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [liftUnitary, pauliX]

theorem liftUnitary_conjTranspose (θ : ℝ) :
    (liftUnitary θ)ᴴ = !![(Real.cos θ : ℂ), -(Complex.I * Real.sin θ);
      -(Complex.I * Real.sin θ), (Real.cos θ : ℂ)] := by
  rw [liftUnitary_eq]
  generalize Real.cos θ = c
  generalize Real.sin θ = s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Complex.conj_ofReal]

theorem cos_sq_add_sin_sq_complex (θ : ℝ) :
    (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq θ

theorem liftUnitary_conjTranspose_mul (θ : ℝ) : (liftUnitary θ)ᴴ * liftUnitary θ = 1 := by
  have hcs := cos_sq_add_sin_sq_complex θ
  rw [liftUnitary_conjTranspose, liftUnitary_eq, Matrix.mul_fin_two, Matrix.one_fin_two]
  generalize (Real.cos θ : ℂ) = c at hcs ⊢
  generalize (Real.sin θ : ℂ) = s at hcs ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | linear_combination hcs - s ^ 2 * Complex.I_sq
    | ring

theorem liftUnitary_mul_conjTranspose (θ : ℝ) : liftUnitary θ * (liftUnitary θ)ᴴ = 1 := by
  have hcs := cos_sq_add_sin_sq_complex θ
  rw [liftUnitary_conjTranspose, liftUnitary_eq, Matrix.mul_fin_two, Matrix.one_fin_two]
  generalize (Real.cos θ : ℂ) = c at hcs ⊢
  generalize (Real.sin θ : ℂ) = s at hcs ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | linear_combination hcs - s ^ 2 * Complex.I_sq
    | ring

theorem trace_pauliZ_conj (θ : ℝ) :
    (pauliZ * liftUnitary θ * pauliZ * (liftUnitary θ)ᴴ).trace
      = 2 * ((Real.cos θ : ℂ) ^ 2 - (Real.sin θ : ℂ) ^ 2) := by
  rw [liftUnitary_conjTranspose, liftUnitary_eq, pauliZ]
  generalize (Real.cos θ : ℂ) = c
  generalize (Real.sin θ : ℂ) = s
  simp only [Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  linear_combination ((2 : ℂ) * s ^ 2) * Complex.I_sq

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The spectator lift `id ⊗ Ad_{U_θ}` on `m × Fin 2`, with unique Kraus operator
`1 ⊗ₖ U_θ`. -/
noncomputable def oddLift (m : Type*) [Fintype m] [DecidableEq m] (θ : ℝ) :
    Matrix (m × Fin 2) (m × Fin 2) ℂ →ₗ[ℂ] Matrix (m × Fin 2) (m × Fin 2) ℂ :=
  krausLin (fun _ : Unit => (1 : Matrix m m ℂ) ⊗ₖ liftUnitary θ)

theorem oddLift_apply (θ : ℝ) (X : Matrix (m × Fin 2) (m × Fin 2) ℂ) :
    oddLift m θ X = ((1 : Matrix m m ℂ) ⊗ₖ liftUnitary θ) * X *
      ((1 : Matrix m m ℂ) ⊗ₖ liftUnitary θ)ᴴ := by
  simp [oddLift, krausLin_apply]

/-- Discarding a spectator after conjugation by `1 ⊗ W`, `Wᴴ W = 1`, leaves the partial
trace unchanged. -/
theorem partialTrace_conj_one_kronecker {k : Type*} [Fintype k] [DecidableEq k]
    (W : Matrix k k ℂ) (hW : Wᴴ * W = 1) (X : Matrix (m × k) (m × k) ℂ) :
    partialTraceRight (((1 : Matrix m m ℂ) ⊗ₖ W) * X * ((1 : Matrix m m ℂ) ⊗ₖ W)ᴴ)
      = partialTraceRight X := by
  ext a b
  have hW' : ∀ r t, ∑ s, star (W s r) * W s t = (1 : Matrix k k ℂ) r t := by
    intro r t; rw [← hW, Matrix.mul_apply]; rfl
  have h1 : ∀ s q, (((1 : Matrix m m ℂ) ⊗ₖ W) * X) (a, s) q = ∑ t, W s t * X (a, t) q := by
    intro s q
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp [Matrix.kroneckerMap_apply, Matrix.one_apply]
  have h2 : ∀ (Y : Matrix (m × k) (m × k) ℂ) s,
      (Y * ((1 : Matrix m m ℂ) ⊗ₖ W)ᴴ) (a, s) (b, s) = ∑ r, Y (a, s) (b, r) * star (W s r) := by
    intro Y s
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.mul_apply,
      Fintype.sum_prod_type]
    simp [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_apply]
  simp only [partialTraceRight, Matrix.of_apply, h2, h1, Finset.sum_mul]
  calc ∑ s, ∑ r, ∑ t, W s t * X (a, t) (b, r) * star (W s r)
      = ∑ t, ∑ r, ∑ s, X (a, t) (b, r) * (star (W s r) * W s t) := by
        rw [OddChoiOccurrence.sum3_reverse]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun r _ =>
          Finset.sum_congr rfl fun s _ => ?_
        ring
    _ = ∑ t, X (a, t) (b, t) := by
        simp_rw [← Finset.mul_sum, hW', Matrix.one_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Discarding the spectator after the lift gives back the discarded input. -/
theorem partialTrace_oddLift (θ : ℝ) (X : Matrix (m × Fin 2) (m × Fin 2) ℂ) :
    partialTraceRight (oddLift m θ X) = partialTraceRight X := by
  rw [oddLift_apply, partialTrace_conj_one_kronecker _ (liftUnitary_conjTranspose_mul θ)]

/-- **Visible identity channel**: `Tr_S[(id ⊗ Ψ_θ)(ρ ⊗ σ)] = ρ` for every spectator state
with `Tr σ = 1`, for every `θ`. -/
theorem oddLift_visible_channel (θ : ℝ) (ρ : Matrix m m ℂ) (σ : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ.trace = 1) : partialTraceRight (oddLift m θ (ρ ⊗ₖ σ)) = ρ := by
  rw [partialTrace_oddLift]
  ext i j
  simp only [partialTraceRight, Matrix.of_apply, Matrix.kroneckerMap_apply]
  rw [← Finset.mul_sum]
  have : ∑ x, σ x x = σ.trace := rfl
  rw [this, hσ, mul_one]

/-- A visible operation `V ⊗ id` commutes with discarding the spectator. -/
theorem partialTrace_kroneckerLift_id {k : Type*} [Fintype k] [DecidableEq k]
    (V : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix (m × k) (m × k) ℂ) :
    partialTraceRight (ActiveOddLift.kroneckerLift V LinearMap.id X) = V (partialTraceRight X) := by
  rw [ActiveOddLift.linearMap_apply_eq_sum V (partialTraceRight X)]
  ext a b
  simp only [partialTraceRight, ActiveOddLift.kroneckerLift, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    LinearMap.id_apply, Matrix.single_apply, smul_eq_mul]
  simp only [and_self, ite_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_and, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- The visible multitime word: visible operations `V₁, V₂, …` (first acts first). -/
def visibleWord (Vs : List (Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ)) : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
  Vs.foldr (fun V acc => acc ∘ₗ V) LinearMap.id

/-- The lifted multitime word: each visible operation `V ⊗ id` is followed by the lifted
primitive step `id ⊗ Ψ_θ`. -/
noncomputable def liftedWord (θ : ℝ) (Vs : List (Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ)) :
    Matrix (m × Fin 2) (m × Fin 2) ℂ →ₗ[ℂ] Matrix (m × Fin 2) (m × Fin 2) ℂ :=
  Vs.foldr (fun V acc => acc ∘ₗ (oddLift m θ ∘ₗ ActiveOddLift.kroneckerLift V LinearMap.id))
    LinearMap.id

/-- **Visible multitime words are unchanged**: after discarding the spectator, every lifted
word equals the visible word applied to the discarded input, independently of `θ`. -/
theorem partialTrace_liftedWord (θ : ℝ) :
    ∀ (Vs : List (Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ)) (X : Matrix (m × Fin 2) (m × Fin 2) ℂ),
      partialTraceRight (liftedWord θ Vs X) = visibleWord Vs (partialTraceRight X) := by
  intro Vs
  induction Vs with
  | nil => intro X; rfl
  | cons V rest ih =>
    intro X
    have e1 : liftedWord θ (V :: rest) X
        = liftedWord θ rest (oddLift m θ (ActiveOddLift.kroneckerLift V LinearMap.id X)) := rfl
    have e2 : visibleWord (V :: rest) (partialTraceRight X)
        = visibleWord rest (V (partialTraceRight X)) := rfl
    rw [e1, e2, ih, partialTrace_oddLift, partialTrace_kroneckerLift_id]

/-- **`eq:microscopic-odd-lift-family`**: for any visible grading `Z` (`Z * Z = 1`) and
`Z̃ = Z ⊗ σ_z`, `μ_{Z̃}(id ⊗ Ad_{U_θ}) = 2 d sin²θ` with `d = card m`. -/
theorem oddChoiMass_oddLift (θ : ℝ) (Z : Matrix m m ℂ) (hZ : Z * Z = 1) :
    oddChoiMass (Z ⊗ₖ pauliZ) (oddLift m θ)
      = 2 * (Fintype.card m : ℂ) * (Real.sin θ : ℂ) ^ 2 := by
  have hcs := cos_sq_add_sin_sq_complex θ
  rw [oddChoiMass_eq_half_trace, oddLift_apply, oddLift_apply, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_one, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    liftUnitary_mul_conjTranspose, Matrix.trace_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  simp only [Matrix.mul_one, Matrix.one_mul, hZ, Matrix.trace_one, Fintype.card_fin]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_pauliZ_conj]
  linear_combination (-(Fintype.card m : ℂ)) * hcs

/-- The visible active cross-sign mass of the identity channel vanishes. -/
theorem activeCrossSignMass_id (Z : Matrix m m ℂ) (hZ : Z * Z = 1) :
    ActiveOddLift.activeCrossSignMass Z LinearMap.id = 0 := by
  rw [ActiveOddLift.activeCrossSignMass, LinearMap.id_apply, LinearMap.id_apply,
    gradingMinus_mul_gradingPlus hZ, gradingPlus_mul_gradingMinus hZ, Matrix.trace_zero,
    add_zero]

/-- **`cth:microscopic-odd-lift`** (packaged).  For every `θ`, the lift `id ⊗ Ad_{U_θ}`
(i) leaves the discarded spectator marginal unchanged, (ii) induces the visible identity
channel, (iii) leaves every visible multitime word unchanged, yet (iv) has odd Choi mass
`2 d sin²θ` relative to `Z ⊗ σ_z`, while (v) the visible active mass is `0`. -/
theorem microscopic_odd_lift (θ : ℝ) (Z : Matrix m m ℂ) (hZ : Z * Z = 1) :
    (∀ X, partialTraceRight (oddLift m θ X) = partialTraceRight X) ∧
    (∀ (ρ : Matrix m m ℂ) (σ : Matrix (Fin 2) (Fin 2) ℂ), σ.trace = 1 →
      partialTraceRight (oddLift m θ (ρ ⊗ₖ σ)) = ρ) ∧
    (∀ (Vs : List (Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ)) X,
      partialTraceRight (liftedWord θ Vs X) = visibleWord Vs (partialTraceRight X)) ∧
    oddChoiMass (Z ⊗ₖ pauliZ) (oddLift m θ)
      = 2 * (Fintype.card m : ℂ) * (Real.sin θ : ℂ) ^ 2 ∧
    ActiveOddLift.activeCrossSignMass Z LinearMap.id = 0 :=
  ⟨partialTrace_oddLift θ, oddLift_visible_channel θ, partialTrace_liftedWord θ,
    oddChoiMass_oddLift θ Z hZ, activeCrossSignMass_id Z hZ⟩

end MicroscopicOddLift

end RenewalGeometry
