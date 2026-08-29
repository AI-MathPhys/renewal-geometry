/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HilbertLimitBoundedAction

/-!
# Uniform gaps for a compatible Hilbert direct-limit family

This supplies the family layer of the manuscript's exact uniform-gap theorem.
Finite-stage transitions and fixed-space projections act on an increasing
Hilbert filtration and intertwine its isometric inclusions into the completed
carrier.  The transient limit norm is then exactly the least upper bound of
the *finite-stage transient norms*, not merely of restrictions named after one
already constructed operator.
-/

open Filter

namespace NCG
namespace CompatibleHilbertDirectLimitGap

variable {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The transient compression associated with a transition and its fixed-space
projection. -/
def transient {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T E : K →L[ℂ] K) : K →L[ℂ] K :=
  (1 - E) * (T * (1 - E))

/-- Isometric inclusion of an earlier stage into a later stage of a monotone
filtration. -/
def stageInclusion (S : ℕ → Submodule ℂ H) (hmono : Monotone S)
    {n m : ℕ} (hnm : n ≤ m) : S n →L[ℂ] S m :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨x.1, hmono hnm x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun x => by simp)

@[simp] theorem stageInclusion_coe
    (S : ℕ → Submodule ℂ H) (hmono : Monotone S)
    {n m : ℕ} (hnm : n ≤ m) (x : S n) :
    ((stageInclusion S hmono hnm x : S m) : H) = x := rfl

/-- Intertwining with the completed carrier implies the ordinary pairwise
compatibility equations along every cutoff inclusion. -/
theorem pairwise_compatibility_of_limit_intertwining
    (S : ℕ → Submodule ℂ H) (hmono : Monotone S)
    (A : (n : ℕ) → ContinuousLinearMap (RingHom.id ℂ) (S n) (S n))
    (Alimit : H →L[ℂ] H)
    (hA : ∀ n (x : S n), ((A n x : S n) : H) = Alimit x)
    {n m : ℕ} (hnm : n ≤ m) :
    (stageInclusion S hmono hnm).comp (A n) =
      (A m).comp (stageInclusion S hmono hnm) := by
  ext x
  change ((A n x : S n) : H) =
    ((A m (stageInclusion S hmono hnm x) : S m) : H)
  exact (hA n x).trans
    (hA m (stageInclusion S hmono hnm x)).symm

/-- The norm of a stage operator is unchanged by its isometric inclusion in
the completed Hilbert carrier. -/
theorem norm_subtype_comp (S : Submodule ℂ H) (A : S →L[ℂ] S) :
    ‖S.subtypeL.comp A‖ = ‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro x
    simpa using A.le_opNorm x
  · apply ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _)
    intro x
    simpa using (S.subtypeL.comp A).le_opNorm x

/-- Exact norm passage for a genuinely compatible finite-stage family. -/
theorem compatible_family_norm_isLUB
    (S : ℕ → Submodule ℂ H) (hmono : Monotone S)
    (hdense : Dense ((⨆ n, S n : Submodule ℂ H) : Set H))
    (A : (n : ℕ) → ContinuousLinearMap (RingHom.id ℂ) (S n) (S n))
    (Alimit : H →L[ℂ] H)
    (hA : ∀ n (x : S n), ((A n x : S n) : H) = Alimit x) :
    IsLUB (Set.range fun n => ‖A n‖) ‖Alimit‖ := by
  have hbase := (uniform_gap_limit S hmono hdense Alimit).1
  convert hbase using 1
  ext ρ
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have heq : Alimit.comp (S n).subtypeL = (S n).subtypeL.comp (A n) := by
      ext x
      exact (hA n x).symm
    change ‖Alimit.comp (S n).subtypeL‖ = ‖A n‖
    rw [heq, norm_subtype_comp]
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have heq : Alimit.comp (S n).subtypeL = (S n).subtypeL.comp (A n) := by
      ext x
      exact (hA n x).symm
    change ‖A n‖ = ‖Alimit.comp (S n).subtypeL‖
    rw [heq, norm_subtype_comp]

/-- Transition and projection intertwining separately implies intertwining of
their transient compressions. -/
theorem transient_intertwines
    (S : ℕ → Submodule ℂ H)
    (T E : (n : ℕ) → ContinuousLinearMap (RingHom.id ℂ) (S n) (S n))
    (Tlimit Elimit : H →L[ℂ] H)
    (hT : ∀ n (x : S n), ((T n x : S n) : H) = Tlimit x)
    (hE : ∀ n (x : S n), ((E n x : S n) : H) = Elimit x) :
    ∀ n (x : S n),
      ((transient (T n) (E n) x : S n) : H) =
        transient Tlimit Elimit x := by
  intro n x
  simp only [transient, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    Submodule.coe_sub]
  have hy : ((x - E n x : S n) : H) = (x : H) - Elimit x := by
    rw [Submodule.coe_sub, hE]
  rw [hE n (T n (x - E n x)), hT n (x - E n x), hy]

/-- Full compatible-family form of the exact uniform-gap theorem: transient
norm equality, the equivalent uniform finite-stage bound, limit power decay,
and pairwise cutoff compatibility all appear in one certificate. -/
theorem uniform_gap_compatible_family
    (S : ℕ → Submodule ℂ H) (hmono : Monotone S)
    (hdense : Dense ((⨆ n, S n : Submodule ℂ H) : Set H))
    (T E : (n : ℕ) → ContinuousLinearMap (RingHom.id ℂ) (S n) (S n))
    (Tlimit Elimit : H →L[ℂ] H)
    (hT : ∀ n (x : S n), ((T n x : S n) : H) = Tlimit x)
    (hE : ∀ n (x : S n), ((E n x : S n) : H) = Elimit x)
    (hEid : Elimit * Elimit = Elimit) (hTE : Tlimit * Elimit = Elimit)
    (hET : Elimit * Tlimit = Elimit) :
    IsLUB (Set.range fun n => ‖transient (T n) (E n)‖)
      ‖transient Tlimit Elimit‖
    ∧ (∀ γ₀ : ℝ,
        ‖transient Tlimit Elimit‖ ≤ 1 - γ₀ ↔
          ∀ n, ‖transient (T n) (E n)‖ ≤ 1 - γ₀)
    ∧ (∀ γ₀ : ℝ, ‖transient Tlimit Elimit‖ ≤ 1 - γ₀ →
        ∀ k : ℕ, 1 ≤ k →
          ‖(Tlimit ^ k : H →L[ℂ] H) - Elimit‖ ≤ (1 - γ₀) ^ k)
    ∧ (∀ {n m : ℕ} (hnm : n ≤ m),
        (stageInclusion S hmono hnm).comp (T n) =
          (T m).comp (stageInclusion S hmono hnm)
        ∧ (stageInclusion S hmono hnm).comp (E n) =
          (E m).comp (stageInclusion S hmono hnm)) := by
  have htrans := transient_intertwines S T E Tlimit Elimit hT hE
  have hlub := compatible_family_norm_isLUB S hmono hdense
    (fun n => transient (T n) (E n)) (transient Tlimit Elimit) htrans
  refine ⟨hlub, ?_, ?_, ?_⟩
  · intro γ₀
    constructor
    · intro h n
      exact (hlub.1 ⟨n, rfl⟩).trans h
    · intro h
      exact hlub.2 (fun ρ hρ => by obtain ⟨n, rfl⟩ := hρ; exact h n)
  · intro γ₀ hgap
    have hlimit := (uniform_gap_limit S hmono hdense Tlimit).2.1
      Elimit γ₀ hEid hTE hET
    exact hlimit.2 (by rw [← hlimit.1]; exact hgap)
  · intro n m hnm
    exact ⟨pairwise_compatibility_of_limit_intertwining
      S hmono T Tlimit hT hnm,
      pairwise_compatibility_of_limit_intertwining
        S hmono E Elimit hE hnm⟩

end CompatibleHilbertDirectLimitGap
end NCG
