/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact marked-monodromy descent and the determinant-line shadow

Paper `predictive_spectral_geometry`, labels

* `thm:supp-monodromy-descent` (exact marked-monodromy descent): for a
  surjection `q : F →* F̄` of fundamental groups and a marked monodromy
  `ρ : F →* G`, a factorisation `ρ = ρ̄ ∘ q` exists and is unique iff
  `ker q ≤ ker ρ` (`RenewalGeometry.monodromy_descends_iff`); the descended
  representation is gauge covariant (`monodromyDescent_conj`) and functorial
  under composed contractions (`monodromyDescent_comp_surjective`); a line
  character can descend while the full packet does not
  (`detCharacter_descends_but_monodromy_does_not`).
* `cth:supp-det-no-frame` (a trivial determinant line need not trivialise the
  packet): the `SU(2)` element `g = diag(e^{iθ}, e^{-iθ})` is unitary with
  `det g = 1`, commutes with the zero Dirac operator and the scalar algebra,
  and is not the identity when `θ ∉ 2πℤ`; the one-cycle monodromy it generates
  has trivial determinant-line holonomy but is a nontrivial homomorphism
  (`RenewalGeometry.oneCycleMonodromy_det_trivial`,
  `RenewalGeometry.oneCycleMonodromy_ne_one`).

The fundamental group of a graph is modelled abstractly by a group `F`; on the
one-cycle graph it is `Multiplicative ℤ` and the contraction of the cycle to
a point is the trivial surjection `Multiplicative ℤ →* Unit`.
-/

open Matrix

namespace RenewalGeometry

section Descent

variable {F F₁ F₂ G : Type*} [Group F] [Group F₁] [Group F₂] [Group G]

/-- **Theorem `thm:supp-monodromy-descent` (existence and uniqueness).**
For a surjective `q : F →* F₁` and a monodromy `ρ : F →* G`, there is a unique
`ρ̄ : F₁ →* G` with `ρ = ρ̄ ∘ q` if and only if `ker q ≤ ker ρ`. -/
theorem monodromy_descends_iff (q : F →* F₁) (hq : Function.Surjective q)
    (ρ : F →* G) :
    (∃! ρbar : F₁ →* G, ρ = ρbar.comp q) ↔ q.ker ≤ ρ.ker := by
  constructor
  · rintro ⟨ρbar, hρ, -⟩ x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [hρ, MonoidHom.comp_apply, hx, map_one]
  · intro h
    refine ⟨q.liftOfSurjective hq ⟨ρ, h⟩, ?_, ?_⟩
    · exact (MonoidHom.liftOfRightInverse_comp q _ _ ⟨ρ, h⟩).symm
    · intro ρ' hρ'
      exact MonoidHom.eq_liftOfRightInverse q _ _ ρ h ρ' hρ'.symm

/-- The descended marked monodromy `ρ̄` of `thm:supp-monodromy-descent`, defined
under the kernel condition `ker q ≤ ker ρ`. -/
noncomputable def monodromyDescent (q : F →* F₁) (hq : Function.Surjective q)
    (ρ : F →* G) (h : q.ker ≤ ρ.ker) : F₁ →* G :=
  q.liftOfSurjective hq ⟨ρ, h⟩

/-- The descended monodromy factors the original one: `ρ = ρ̄ ∘ q_*`
(equation `eq:supp-monodromy-factor`). -/
theorem monodromyDescent_comp (q : F →* F₁) (hq : Function.Surjective q)
    (ρ : F →* G) (h : q.ker ≤ ρ.ker) :
    (monodromyDescent q hq ρ h).comp q = ρ :=
  MonoidHom.liftOfRightInverse_comp q _ _ ⟨ρ, h⟩

/-- Uniqueness of the descended monodromy (surjectivity of `q_*`). -/
theorem monodromyDescent_unique (q : F →* F₁) (hq : Function.Surjective q)
    (ρ : F →* G) (h : q.ker ≤ ρ.ker) (ρ' : F₁ →* G) (hρ' : ρ'.comp q = ρ) :
    ρ' = monodromyDescent q hq ρ h :=
  MonoidHom.eq_liftOfRightInverse q _ _ ρ h ρ' hρ'

/-- A gauge change (conjugation by `g ∈ G`) preserves the kernel condition. -/
theorem ker_le_ker_conj_comp (q : F →* F₁) (ρ : F →* G) (h : q.ker ≤ ρ.ker)
    (g : G) : q.ker ≤ ((MulAut.conj g).toMonoidHom.comp ρ).ker := by
  intro x hx
  have hx' := h hx
  rw [MonoidHom.mem_ker] at hx' ⊢
  simp [hx']

/-- **Gauge independence of `[ρ̄]` (`thm:supp-monodromy-descent`).** Conjugating
the monodromy by a frame change `g` conjugates its descent by the same `g`, so
the conjugacy class of the descended monodromy is gauge independent. -/
theorem monodromyDescent_conj (q : F →* F₁) (hq : Function.Surjective q)
    (ρ : F →* G) (h : q.ker ≤ ρ.ker) (g : G) :
    monodromyDescent q hq ((MulAut.conj g).toMonoidHom.comp ρ)
        (ker_le_ker_conj_comp q ρ h g)
      = (MulAut.conj g).toMonoidHom.comp (monodromyDescent q hq ρ h) := by
  symm
  apply monodromyDescent_unique
  rw [MonoidHom.comp_assoc, monodromyDescent_comp]

/-- Under a two-stage contraction `q₂ ∘ q₁`, the kernel condition for the
composite implies the kernel condition for the first stage. -/
theorem ker_le_ker_of_comp (q₁ : F →* F₁) (q₂ : F₁ →* F₂) (ρ : F →* G)
    (h : (q₂.comp q₁).ker ≤ ρ.ker) : q₁.ker ≤ ρ.ker := by
  intro x hx
  apply h
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [MonoidHom.comp_apply, hx, map_one]

/-- Under a two-stage contraction, the descended monodromy of the first stage
satisfies the kernel condition for the second stage. -/
theorem ker_le_ker_monodromyDescent (q₁ : F →* F₁) (hq₁ : Function.Surjective q₁)
    (q₂ : F₁ →* F₂) (ρ : F →* G) (h : (q₂.comp q₁).ker ≤ ρ.ker) :
    q₂.ker ≤ (monodromyDescent q₁ hq₁ ρ (ker_le_ker_of_comp q₁ q₂ ρ h)).ker := by
  intro y hy
  obtain ⟨x, rfl⟩ := hq₁ y
  rw [MonoidHom.mem_ker] at hy ⊢
  have hx : x ∈ (q₂.comp q₁).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]; exact hy
  have := h hx
  rw [MonoidHom.mem_ker] at this
  have hc := congrArg (fun φ : F →* G => φ x)
    (monodromyDescent_comp q₁ hq₁ ρ (ker_le_ker_of_comp q₁ q₂ ρ h))
  simp only [MonoidHom.comp_apply] at hc
  rw [hc, this]

/-- **Functoriality of descent (`thm:supp-monodromy-descent`).** Descending
along `q₁` and then along `q₂` equals descending along the composite
contraction `q₂ ∘ q₁`. -/
theorem monodromyDescent_comp_surjective (q₁ : F →* F₁)
    (hq₁ : Function.Surjective q₁) (q₂ : F₁ →* F₂) (hq₂ : Function.Surjective q₂)
    (ρ : F →* G) (h : (q₂.comp q₁).ker ≤ ρ.ker) :
    monodromyDescent q₂ hq₂ (monodromyDescent q₁ hq₁ ρ (ker_le_ker_of_comp q₁ q₂ ρ h))
        (ker_le_ker_monodromyDescent q₁ hq₁ q₂ ρ h)
      = monodromyDescent (q₂.comp q₁) (hq₂.comp hq₁) ρ h := by
  apply monodromyDescent_unique
  rw [← MonoidHom.comp_assoc, monodromyDescent_comp, monodromyDescent_comp]

/-- A line character `χ : G →* L` of a descended monodromy satisfies the
descended kernel condition (the easy direction of the character remark in
`thm:supp-monodromy-descent`). -/
theorem ker_le_ker_character_comp {L : Type*} [Group L] (q : F →* F₁)
    (ρ : F →* G) (h : q.ker ≤ ρ.ker) (χ : G →* L) :
    q.ker ≤ (χ.comp ρ).ker := by
  intro x hx
  have hx' := h hx
  rw [MonoidHom.mem_ker] at hx' ⊢
  rw [MonoidHom.comp_apply, hx', map_one]

end Descent

section SU2

open Complex

/-- The `SU(2)` monodromy `g = diag(e^{iθ}, e^{-iθ})` of
`eq:supp-SU2-monodromy`. -/
noncomputable def su2DiagonalMonodromy (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![exp (θ * I), exp (-(θ * I))]

/-- The determinant of `diag(e^{iθ}, e^{-iθ})` is one: the determinant-line
holonomy of `cth:supp-det-no-frame` is trivial. -/
theorem det_su2DiagonalMonodromy (θ : ℝ) : (su2DiagonalMonodromy θ).det = 1 := by
  unfold su2DiagonalMonodromy
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp [← Complex.exp_add]

/-- `diag(e^{iθ}, e^{-iθ})` is unitary. -/
theorem su2DiagonalMonodromy_mem_unitaryGroup (θ : ℝ) :
    su2DiagonalMonodromy θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  unfold su2DiagonalMonodromy
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [← Complex.exp_conj, ← Complex.exp_add]

/-- `diag(e^{iθ}, e^{-iθ})` commutes with the zero Dirac operator. -/
theorem su2DiagonalMonodromy_comm_zero (θ : ℝ) :
    su2DiagonalMonodromy θ * (0 : Matrix (Fin 2) (Fin 2) ℂ)
      = (0 : Matrix (Fin 2) (Fin 2) ℂ) * su2DiagonalMonodromy θ := by
  simp

/-- `diag(e^{iθ}, e^{-iθ})` commutes with the scalar algebra `ℂ·1`. -/
theorem su2DiagonalMonodromy_comm_scalar (θ : ℝ) (c : ℂ) :
    su2DiagonalMonodromy θ * (c • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * su2DiagonalMonodromy θ := by
  simp

/-- For `θ ∉ 2πℤ` the monodromy `diag(e^{iθ}, e^{-iθ})` is not the identity. -/
theorem su2DiagonalMonodromy_ne_one (θ : ℝ) (hθ : ∀ n : ℤ, θ ≠ 2 * Real.pi * n) :
    su2DiagonalMonodromy θ ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [su2DiagonalMonodromy] at h00
  rw [Complex.exp_eq_one_iff] at h00
  obtain ⟨n, hn⟩ := h00
  apply hθ n
  have hI : (θ : ℂ) * I = ((2 * Real.pi * n : ℝ) : ℂ) * I := by
    rw [hn]; push_cast; ring
  have := mul_right_cancel₀ Complex.I_ne_zero hI
  exact_mod_cast this

/-- The `SU(2)` monodromy as an element of the unitary group `U(2)`, which is
the marked automorphism group of a scalar-algebra, zero-Dirac, multiplicity-two
packet. -/
noncomputable def su2DiagonalMonodromyUnitary (θ : ℝ) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨su2DiagonalMonodromy θ, su2DiagonalMonodromy_mem_unitaryGroup θ⟩

/-- The determinant-line character `det : U(n) → ℂˣ`. -/
noncomputable def detCharacter (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix.unitaryGroup n ℂ →* ℂˣ :=
  (Units.map (Matrix.detMonoidHom : Matrix n n ℂ →* ℂ)).comp Unitary.toUnits

/-- The value of the determinant character is the determinant. -/
theorem detCharacter_apply_val {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) : ((detCharacter n) U : ℂ) = (U : Matrix n n ℂ).det := by
  simp [detCharacter, Matrix.coe_detMonoidHom]

/-- The marked monodromy of the one-cycle graph (`π₁ = ℤ`) sending the
generator to `diag(e^{iθ}, e^{-iθ})`. -/
noncomputable def oneCycleMonodromy (θ : ℝ) :
    Multiplicative ℤ →* Matrix.unitaryGroup (Fin 2) ℂ :=
  zpowersHom _ (su2DiagonalMonodromyUnitary θ)

/-- **Proposition `cth:supp-det-no-frame` (trivial line holonomy).** The
determinant-line holonomy of the one-cycle `SU(2)` monodromy is trivial. -/
theorem oneCycleMonodromy_det_trivial (θ : ℝ) :
    (detCharacter (Fin 2)).comp (oneCycleMonodromy θ) = 1 := by
  refine MonoidHom.ext fun n => ?_
  have h1 : (detCharacter (Fin 2)) (su2DiagonalMonodromyUnitary θ) = 1 := by
    apply Units.ext
    rw [detCharacter_apply_val]
    exact det_su2DiagonalMonodromy θ
  simp [oneCycleMonodromy, h1]

/-- **Proposition `cth:supp-det-no-frame` (nontrivial monodromy).** For
`θ ∉ 2πℤ` the one-cycle monodromy is a nontrivial homomorphism, so the marked
Hilbert bundle is not globally trivialisable although its determinant line is. -/
theorem oneCycleMonodromy_ne_one (θ : ℝ) (hθ : ∀ n : ℤ, θ ≠ 2 * Real.pi * n) :
    oneCycleMonodromy θ ≠ 1 := by
  intro h
  have h1 := congrArg (fun φ : Multiplicative ℤ →* Matrix.unitaryGroup (Fin 2) ℂ =>
    (φ (Multiplicative.ofAdd 1) : Matrix (Fin 2) (Fin 2) ℂ)) h
  simp [oneCycleMonodromy, su2DiagonalMonodromyUnitary] at h1
  exact su2DiagonalMonodromy_ne_one θ hθ h1

/-- The contraction of the one-cycle graph to a point, on fundamental groups. -/
def oneCycleCollapse : Multiplicative ℤ →* Unit := 1

/-- The collapse map is surjective. -/
theorem oneCycleCollapse_surjective : Function.Surjective oneCycleCollapse :=
  fun _ => ⟨1, rfl⟩

/-- **Character remark of `thm:supp-monodromy-descent`.** Along the collapse
of the one cycle, the determinant character of the `SU(2)` monodromy satisfies
the descended kernel condition, while the full marked monodromy does not
(for `θ ∉ 2πℤ`): line descent does not imply packet descent. -/
theorem detCharacter_descends_but_monodromy_does_not (θ : ℝ)
    (hθ : ∀ n : ℤ, θ ≠ 2 * Real.pi * n) :
    oneCycleCollapse.ker ≤ ((detCharacter (Fin 2)).comp (oneCycleMonodromy θ)).ker ∧
      ¬ oneCycleCollapse.ker ≤ (oneCycleMonodromy θ).ker := by
  constructor
  · intro x _
    rw [MonoidHom.mem_ker, oneCycleMonodromy_det_trivial]
  · intro h
    apply oneCycleMonodromy_ne_one θ hθ
    refine MonoidHom.ext fun x => ?_
    have hx : x ∈ oneCycleCollapse.ker := by
      rw [MonoidHom.mem_ker]; rfl
    have := h hx
    rw [MonoidHom.mem_ker] at this
    rw [this]
    rfl

end SU2

end RenewalGeometry
