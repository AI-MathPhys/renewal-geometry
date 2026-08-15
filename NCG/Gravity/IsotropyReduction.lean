/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Isotropy reduction (exact)

Exact formalization of `lem:isotropy-reduction`: for spatially
homogeneous isotropic data, every isotropy-invariant symmetric
2-tensor has perfect-fluid form
`S = ρ·u⊗u + p·h`, and a divergence-free pure-trace tensor
`S = f·g` has constant `f`.

Model and derivations:

* the spacetime index is `Unit ⊕ Fin d` (time ⊕ space); the
  isotropy group acts on the spatial block, and its invariance
  is instantiated at the coordinate sign flips and permutations
  (special cases of the `SO(d)` invariance — the proof uses
  exactly the manuscript's "no invariant spatial vectors"
  argument);
* `invariant_vector_zero` / `invariant_matrix_scalar`: the
  representation-theoretic core — a sign-flip-invariant vector
  vanishes, and a sign-flip- and permutation-invariant matrix
  is scalar (with the scalar identified as `trace/d`);
* `isotropy_perfect_fluid`: the boxed perfect-fluid form — the
  mixed block vanishes and the spatial block is `p·h`, giving
  `S = ρ·u⊗u + p·h` with `ρ = S(u,u)`;
* `divergence_free_scalar_const`: in a flat chart with constant
  invertible metric, `∇^μ(f g_{μν}) = ∂_ν f`, so a
  divergence-free pure-trace tensor has `∂f = 0` and `f` is
  constant (`is_const_of_fderiv_eq_zero`).
-/

open Matrix

namespace NCG
namespace Isotropy

/-! ### The representation-theoretic core -/

/-- A vector invariant under all coordinate sign flips
vanishes. -/
theorem invariant_vector_zero {d : ℕ} (v : Fin d → ℝ)
    (hsign : ∀ ε : Fin d → ℝ,
      (∀ i, ε i = 1 ∨ ε i = -1) → ∀ i, ε i * v i = v i) :
    v = 0 := by
  funext i
  have hε : ∀ j, (if j = i then (-1 : ℝ) else 1) = 1
      ∨ (if j = i then (-1 : ℝ) else 1) = -1 := by
    intro j
    by_cases h : j = i <;> simp [h]
  have h := hsign (fun j => if j = i then (-1 : ℝ) else 1) hε i
  simp at h
  have : v i = 0 := by linarith
  simpa using this

/-- A symmetric matrix invariant under coordinate sign flips and
permutations is scalar, with scalar `trace/d`. -/
theorem invariant_matrix_scalar {d : ℕ} (hd : 0 < d)
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hsign : ∀ ε : Fin d → ℝ,
      (∀ i, ε i = 1 ∨ ε i = -1) →
      ∀ i j, ε i * ε j * M i j = M i j)
    (hperm : ∀ σ : Equiv.Perm (Fin d),
      ∀ i j, M (σ i) (σ j) = M i j) :
    M = (Matrix.trace M / d) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    have hε : ∀ k, (if k = i then (-1 : ℝ) else 1) = 1
        ∨ (if k = i then (-1 : ℝ) else 1) = -1 := by
      intro k
      by_cases h : k = i <;> simp [h]
    have h := hsign (fun k => if k = i then (-1 : ℝ) else 1)
      hε i j
    simp [Ne.symm hij] at h
    linarith
  have hdiag : ∀ i j, M i i = M j j := by
    intro i j
    have h := hperm (Equiv.swap i j) i i
    rw [Equiv.swap_apply_left] at h
    exact h.symm
  -- identify the scalar
  obtain ⟨i₀⟩ := Fin.pos_iff_nonempty.mp hd
  have htr : Matrix.trace M = d * M i₀ i₀ := by
    rw [Matrix.trace]
    have : ∀ i, Matrix.diag M i = M i₀ i₀ := fun i =>
      hdiag i i₀
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp [mul_comm]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [htr]
    have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    simp [hdiag i i₀]
    field_simp
  · rw [hoff i j hij]
    simp [hij]

/-! ### The perfect-fluid form -/

/-- The spacetime index: time ⊕ space. -/
abbrev STIndex (d : ℕ) : Type := Unit ⊕ Fin d

/-- Extension of a spatial sign vector by `1` on the time
coordinate. -/
def extSign {d : ℕ} (ε : Fin d → ℝ) : STIndex d → ℝ
  | Sum.inl _ => 1
  | Sum.inr i => ε i

/-- Extension of a spatial permutation by the identity on the
time coordinate. -/
def extPerm {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    STIndex d → STIndex d
  | Sum.inl u => Sum.inl u
  | Sum.inr i => Sum.inr (σ i)

/-- The tensor `u ⊗ u` for the unit normal `u`. -/
def uuT (d : ℕ) : Matrix (STIndex d) (STIndex d) ℝ :=
  fun a b => match a, b with
  | Sum.inl _, Sum.inl _ => 1
  | _, _ => 0

/-- The spatial projector `h`. -/
def hProj (d : ℕ) : Matrix (STIndex d) (STIndex d) ℝ :=
  fun a b => match a, b with
  | Sum.inr i, Sum.inr j => if i = j then 1 else 0
  | _, _ => 0

/-- **Isotropy reduction** (`lem:isotropy-reduction`, boxed
form): every isotropy-invariant symmetric 2-tensor has
perfect-fluid form `S = ρ·u⊗u + p·h` with `ρ = S(u,u)`. -/
theorem isotropy_perfect_fluid {d : ℕ} (hd : 0 < d)
    (S : Matrix (STIndex d) (STIndex d) ℝ)
    (hsign : ∀ ε : Fin d → ℝ,
      (∀ i, ε i = 1 ∨ ε i = -1) →
      ∀ a b, extSign ε a * extSign ε b * S a b = S a b)
    (hperm : ∀ σ : Equiv.Perm (Fin d),
      ∀ a b, S (extPerm σ a) (extPerm σ b) = S a b) :
    ∃ ρ p : ℝ, S = ρ • uuT d + p • hProj d := by
  obtain ⟨i₀⟩ := Fin.pos_iff_nonempty.mp hd
  refine ⟨S (Sum.inl ()) (Sum.inl ()),
    S (Sum.inr i₀) (Sum.inr i₀), ?_⟩
  -- the mixed block vanishes
  have hmixflip : ∀ (a : STIndex d) (i : Fin d),
      (∀ ε : Fin d → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) →
        extSign ε a = 1) →
      S a (Sum.inr i) = 0 ∧ S (Sum.inr i) a = 0 := by
    intro a i ha
    have hε : ∀ k, (if k = i then (-1 : ℝ) else 1) = 1
        ∨ (if k = i then (-1 : ℝ) else 1) = -1 := by
      intro k
      by_cases h : k = i <;> simp [h]
    constructor
    · have h := hsign (fun k => if k = i then (-1 : ℝ) else 1)
        hε a (Sum.inr i)
      rw [ha _ hε] at h
      simp [extSign] at h
      linarith
    · have h := hsign (fun k => if k = i then (-1 : ℝ) else 1)
        hε (Sum.inr i) a
      rw [ha _ hε] at h
      simp [extSign] at h
      linarith
  -- spatial off-diagonal vanishes
  have hspoff : ∀ i j : Fin d, i ≠ j →
      S (Sum.inr i) (Sum.inr j) = 0 := by
    intro i j hij
    have hε : ∀ k, (if k = i then (-1 : ℝ) else 1) = 1
        ∨ (if k = i then (-1 : ℝ) else 1) = -1 := by
      intro k
      by_cases h : k = i <;> simp [h]
    have h := hsign (fun k => if k = i then (-1 : ℝ) else 1)
      hε (Sum.inr i) (Sum.inr j)
    simp [extSign, Ne.symm hij] at h
    linarith
  -- spatial diagonal constant
  have hspdiag : ∀ i : Fin d,
      S (Sum.inr i) (Sum.inr i)
        = S (Sum.inr i₀) (Sum.inr i₀) := by
    intro i
    have h := hperm (Equiv.swap i i₀) (Sum.inr i) (Sum.inr i)
    simp only [extPerm, Equiv.swap_apply_left] at h
    exact h.symm
  -- assemble
  funext a b
  match a, b with
  | Sum.inl u, Sum.inl u' =>
    simp [uuT, hProj, Matrix.add_apply, Matrix.smul_apply]
  | Sum.inl u, Sum.inr i =>
    have h := (hmixflip (Sum.inl u) i
      (fun ε _ => rfl)).1
    simp [uuT, hProj, Matrix.add_apply, Matrix.smul_apply, h]
  | Sum.inr i, Sum.inl u =>
    have h := (hmixflip (Sum.inl u) i
      (fun ε _ => rfl)).2
    simp [uuT, hProj, Matrix.add_apply, Matrix.smul_apply, h]
  | Sum.inr i, Sum.inr j =>
    by_cases hij : i = j
    · subst hij
      simp [uuT, hProj, Matrix.add_apply, Matrix.smul_apply,
        hspdiag i]
    · simp [uuT, hProj, Matrix.add_apply, Matrix.smul_apply,
        hij, hspoff i j hij]

/-! ### The divergence-free pure-trace clause -/

/-- **The second clause**: in a flat chart with constant
invertible metric, `∇^μ(f·g_{μν}) = ∂_ν f`, so a
divergence-free pure-trace tensor has constant scalar. -/
theorem divergence_free_scalar_const {m : ℕ}
    (g : Matrix (Fin m) (Fin m) ℝ) [Invertible g]
    (f : (Fin m → ℝ) → ℝ) (hf : Differentiable ℝ f)
    (hdiv : ∀ x : Fin m → ℝ, ∀ ν : Fin m,
      (∑ μ, fderiv ℝ f x (Pi.single μ 1) * g μ ν) = 0)
    (x y : Fin m → ℝ) : f x = f y := by
  have hzero : ∀ x : Fin m → ℝ, fderiv ℝ f x = 0 := by
    intro x
    -- the gradient row vector annihilates the invertible metric
    have hrow : (fun μ => fderiv ℝ f x (Pi.single μ 1)) ᵥ* g
        = 0 := by
      funext ν
      simpa [Matrix.vecMul, dotProduct] using hdiv x ν
    have hgrad : (fun μ => fderiv ℝ f x (Pi.single μ 1))
        = 0 := by
      have h := congrArg (fun v => v ᵥ* g⁻¹) hrow
      simpa [Matrix.vecMul_vecMul,
        Matrix.mul_inv_of_invertible] using h
    -- a linear functional vanishing on the coordinate basis
    have hv' : ∀ v : Fin m → ℝ,
        (∑ μ, v μ • Pi.single μ (1 : ℝ)) = v := by
      intro v
      funext j
      rw [Finset.sum_apply]
      have : ∀ μ, (v μ • Pi.single μ (1 : ℝ)) j
          = if j = μ then v μ else 0 := by
        intro μ
        by_cases h : j = μ <;> simp [h]
      rw [Finset.sum_congr rfl fun μ _ => this μ]
      simp
    ext v
    have hrepr : v = ∑ μ, v μ • Pi.single μ (1 : ℝ) :=
      (hv' v).symm
    rw [hrepr, map_sum]
    have hterm : ∀ μ ∈ Finset.univ,
        fderiv ℝ f x (v μ • Pi.single μ 1) = 0 := by
      intro μ _
      rw [map_smul]
      have := congrFun hgrad μ
      simp only [Pi.zero_apply] at this
      simp [this]
    rw [Finset.sum_congr rfl hterm]
    simp
  exact is_const_of_fderiv_eq_zero hf hzero x y

end Isotropy
end NCG
