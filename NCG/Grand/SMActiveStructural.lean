/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.ActiveResidualAlgebra

/-!
# Unconditional active finite structural Standard Model
  (`thm:SM-active-SM-I`, Gran-Tensor manuscript)

The assembly layer of the active finite structural Standard
Model on top of the two-control reconstruction
(`thm:SM-active-residual-algebra`, formalized in
`ActiveResidualAlgebra.lean`): the boxed odd-orbit tight-frame
identities (SM.0o), the Clifford-flip scalar mechanism behind
`p_Cl = 1` (SM.0p), and the structural generation count.

* `Bedge`: the odd root seeds `B_e = P_e ⊗ D₀` obtained by
  tensoring the six `K₄` edge projectors with the normalized
  grading-odd incidence operator `D₀` (`D₀^*D₀ = D₀D₀^* = I`).
* `odd_orbit_tight_left` / `odd_orbit_tight_right`:
  `∑_e B_e^* B_e = ∑_e B_e B_e^* = 2 (Π_G ⊗ I)` where `Π_G` is
  the orthogonal projection onto the cut carrier `G` — the
  boxed `∑ B_e^* B_e = ∑ B_e B_e^* = 2I` of (SM.0o) read on
  `G ⊗ H` (`odd_orbit_tight_apply` gives the literal `2I`
  action on every mean-zero simple tensor).
* `odd_orbit_span`: `∑_e B_e = 2 (Π_G ⊗ D₀)`, i.e.
  `I_G ⊗ D₀ = ½ ∑_e B_e` — the complete odd full-cell
  generator lies in the one-seed orbit span.
* `clifford_flip`: an anticommuting unitary axis flips the
  total grading, `(Jσ)(Jσ) = -I` — the algebraic mechanism
  behind the normalized Clifford occurrence scalar
  `p_Cl = 1` (SM.0p) via the proved Clifford-twirl record.
* `generation_rank`: the mean-zero endpoint quotient — the
  only matter multiplicity carrier — has dimension exactly
  three: the future-visible structural generation number.

Items (S1)–(S3) of the theorem are the proved records
`thm:SM-active-residual-algebra`, `thm:SM-group`, and
`thm:SM-anomaly-forced-weights`; the CAR/incidence and
finite-Dirac clauses are the proved records
`thm:SMST-monoidal-CAR` and `thm:SMST-generator-projections`;
the faithfulness/orthogonality of the endpoint and loop
triplets is the proved record
`thm:SMST-record-native-generations`.
-/

open Matrix
open scoped Kronecker

namespace NCG
namespace SMActive

open NCG.ActiveResidual

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The odd root seed of an edge: the edge projector tensored
with the normalized grading-odd incidence operator. -/
noncomputable def Bedge (D0 : Matrix H H ℂ) (i j : V) :
    Matrix (V × H) (V × H) ℂ :=
  Pedge i j ⊗ₖ D0

/-- The cut-vector has squared length `2`. -/
theorem cutVec_dot (i j : V) (hij : i ≠ j) :
    ∑ h : V, cutVec i j h * cutVec i j h = 2 := by
  have hterm : ∀ h : V, cutVec i j h * cutVec i j h
      = (if h = j then (1:ℂ) else 0)
        + (if h = i then (1:ℂ) else 0) := by
    intro h
    show ((if h = j then (1:ℂ) else 0)
        - (if h = i then (1:ℂ) else 0))
      * ((if h = j then (1:ℂ) else 0)
        - (if h = i then (1:ℂ) else 0)) = _
    by_cases h1 : h = j
    · by_cases h2 : h = i
      · exact absurd (h2.symm.trans h1) hij
      · rw [if_pos h1, if_neg h2]
        norm_num
    · by_cases h2 : h = i
      · rw [if_neg h1, if_pos h2]
        norm_num
      · rw [if_neg h1, if_neg h2]
        norm_num
  rw [Finset.sum_congr rfl fun h _ => hterm h,
    Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ j),
    if_pos (Finset.mem_univ i)]
  norm_num

theorem cutVec_star (i j x : V) :
    star (cutVec i j x) = cutVec i j x := by
  have h : ∀ (c : Prop) [Decidable c],
      star (if c then (1:ℂ) else 0)
        = if c then (1:ℂ) else 0 := by
    intro c _
    by_cases hc : c <;> simp [hc]
  show star ((if x = j then (1:ℂ) else 0)
      - (if x = i then (1:ℂ) else 0))
    = (if x = j then (1:ℂ) else 0)
      - (if x = i then (1:ℂ) else 0)
  rw [star_sub, h, h]

theorem Pedge_herm (i j : V) : (Pedge i j)ᴴ = Pedge i j := by
  ext x y
  simp only [Pedge, Matrix.conjTranspose_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    star_mul', cutVec_star, star_inv₀, star_ofNat]
  ring

theorem Pedge_idem (i j : V) (hij : i ≠ j) :
    Pedge i j * Pedge i j = Pedge i j := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Pedge, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  calc ∑ h : V, (2:ℂ)⁻¹ * (cutVec i j x * cutVec i j h)
        * ((2:ℂ)⁻¹ * (cutVec i j h * cutVec i j y))
      = ((2:ℂ)⁻¹ * (2:ℂ)⁻¹ * (cutVec i j x * cutVec i j y))
        * ∑ h : V, cutVec i j h * cutVec i j h := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun h _ => by ring
    _ = (2:ℂ)⁻¹ * (cutVec i j x * cutVec i j y) := by
        rw [cutVec_dot i j hij]
        ring

theorem Bedge_dagger_Bedge (D0 : Matrix H H ℂ)
    (hDl : D0ᴴ * D0 = 1) (i j : V) (hij : i ≠ j) :
    (Bedge D0 i j)ᴴ * Bedge D0 i j
      = Pedge i j ⊗ₖ (1 : Matrix H H ℂ) := by
  rw [Bedge, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Pedge_herm,
    Pedge_idem i j hij, hDl]

theorem Bedge_Bedge_dagger (D0 : Matrix H H ℂ)
    (hDr : D0 * D0ᴴ = 1) (i j : V) (hij : i ≠ j) :
    Bedge D0 i j * (Bedge D0 i j)ᴴ
      = Pedge i j ⊗ₖ (1 : Matrix H H ℂ) := by
  rw [Bedge, Matrix.conjTranspose_kronecker, Pedge_herm,
    ← Matrix.mul_kronecker_mul, Pedge_idem i j hij, hDr]

/-- **(SM.0o), left tight frame**: the odd seeds satisfy
`∑_e B_e^* B_e = 2 (Π_G ⊗ I)` — twice the identity of the
matter carrier `G ⊗ H`. -/
theorem odd_orbit_tight_left (D0 : Matrix H H ℂ)
    (hDl : D0ᴴ * D0 = 1) :
    (Bedge D0 0 1)ᴴ * Bedge D0 0 1
      + (Bedge D0 0 2)ᴴ * Bedge D0 0 2
      + (Bedge D0 0 3)ᴴ * Bedge D0 0 3
      + (Bedge D0 1 2)ᴴ * Bedge D0 1 2
      + (Bedge D0 1 3)ᴴ * Bedge D0 1 3
      + (Bedge D0 2 3)ᴴ * Bedge D0 2 3
    = ((2:ℂ) • ((1 : Matrix V V ℂ)
        - (4:ℂ)⁻¹ • Matrix.of (fun _ _ => (1:ℂ))))
      ⊗ₖ (1 : Matrix H H ℂ) := by
  rw [Bedge_dagger_Bedge D0 hDl 0 1 (by decide),
    Bedge_dagger_Bedge D0 hDl 0 2 (by decide),
    Bedge_dagger_Bedge D0 hDl 0 3 (by decide),
    Bedge_dagger_Bedge D0 hDl 1 2 (by decide),
    Bedge_dagger_Bedge D0 hDl 1 3 (by decide),
    Bedge_dagger_Bedge D0 hDl 2 3 (by decide),
    ← Matrix.add_kronecker, ← Matrix.add_kronecker,
    ← Matrix.add_kronecker, ← Matrix.add_kronecker,
    ← Matrix.add_kronecker, edge_projector_sum]

/-- **(SM.0o), right tight frame**:
`∑_e B_e B_e^* = 2 (Π_G ⊗ I)`. -/
theorem odd_orbit_tight_right (D0 : Matrix H H ℂ)
    (hDr : D0 * D0ᴴ = 1) :
    Bedge D0 0 1 * (Bedge D0 0 1)ᴴ
      + Bedge D0 0 2 * (Bedge D0 0 2)ᴴ
      + Bedge D0 0 3 * (Bedge D0 0 3)ᴴ
      + Bedge D0 1 2 * (Bedge D0 1 2)ᴴ
      + Bedge D0 1 3 * (Bedge D0 1 3)ᴴ
      + Bedge D0 2 3 * (Bedge D0 2 3)ᴴ
    = ((2:ℂ) • ((1 : Matrix V V ℂ)
        - (4:ℂ)⁻¹ • Matrix.of (fun _ _ => (1:ℂ))))
      ⊗ₖ (1 : Matrix H H ℂ) := by
  rw [Bedge_Bedge_dagger D0 hDr 0 1 (by decide),
    Bedge_Bedge_dagger D0 hDr 0 2 (by decide),
    Bedge_Bedge_dagger D0 hDr 0 3 (by decide),
    Bedge_Bedge_dagger D0 hDr 1 2 (by decide),
    Bedge_Bedge_dagger D0 hDr 1 3 (by decide),
    Bedge_Bedge_dagger D0 hDr 2 3 (by decide),
    ← Matrix.add_kronecker, ← Matrix.add_kronecker,
    ← Matrix.add_kronecker, ← Matrix.add_kronecker,
    ← Matrix.add_kronecker, edge_projector_sum]

omit [Fintype H] [DecidableEq H] in
/-- **(SM.0o), orbit span**: `I_G ⊗ D₀ = ½ ∑_e B_e` — the
complete odd full-cell generator is in the one-seed orbit
span. -/
theorem odd_orbit_span (D0 : Matrix H H ℂ) :
    Bedge D0 0 1 + Bedge D0 0 2 + Bedge D0 0 3
      + Bedge D0 1 2 + Bedge D0 1 3 + Bedge D0 2 3
    = (2:ℂ) • (((1 : Matrix V V ℂ)
        - (4:ℂ)⁻¹ • Matrix.of (fun _ _ => (1:ℂ)))
      ⊗ₖ D0) := by
  rw [Bedge, Bedge, Bedge, Bedge, Bedge, Bedge,
    ← Matrix.add_kronecker, ← Matrix.add_kronecker,
    ← Matrix.add_kronecker, ← Matrix.add_kronecker,
    ← Matrix.add_kronecker, edge_projector_sum,
    Matrix.smul_kronecker]

/-- Kronecker products act factorwise on simple tensors. -/
theorem kron_mulVec_simple {m n : Type} [Fintype m]
    [Fintype n] (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (x : m → ℂ) (ψ : n → ℂ) :
    (A ⊗ₖ B) *ᵥ (fun p => x p.1 * ψ p.2)
      = fun p => (A *ᵥ x) p.1 * (B *ᵥ ψ) p.2 := by
  funext p
  obtain ⟨i, k⟩ := p
  simp only [Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The tight frame acts as literal `2I` on every mean-zero
simple tensor of the matter carrier. -/
theorem odd_orbit_tight_apply (D0 : Matrix H H ℂ)
    (hDl : D0ᴴ * D0 = 1) (x : V → ℂ)
    (hx : ∑ v, x v = 0) (ψ : H → ℂ) :
    ((Bedge D0 0 1)ᴴ * Bedge D0 0 1
      + (Bedge D0 0 2)ᴴ * Bedge D0 0 2
      + (Bedge D0 0 3)ᴴ * Bedge D0 0 3
      + (Bedge D0 1 2)ᴴ * Bedge D0 1 2
      + (Bedge D0 1 3)ᴴ * Bedge D0 1 3
      + (Bedge D0 2 3)ᴴ * Bedge D0 2 3) *ᵥ
      (fun p => x p.1 * ψ p.2)
    = (2:ℂ) • fun p => x p.1 * ψ p.2 := by
  rw [odd_orbit_tight_left D0 hDl, kron_mulVec_simple,
    Matrix.one_mulVec]
  have h2 : ((2:ℂ) • ((1 : Matrix V V ℂ)
      - (4:ℂ)⁻¹ • Matrix.of (fun _ _ => (1:ℂ)))) *ᵥ x
      = (2:ℂ) • x := by
    rw [← edge_projector_sum]
    exact edge_projector_sum_apply x hx
  rw [h2]
  funext p
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **(SM.0p) mechanism**: an anticommuting unitary axis
flips the total grading: `(Jσ)(Jσ) = -I`.  Combined with the
proved Clifford-twirl record this gives the normalized
Clifford occurrence scalar `p_Cl = 1`. -/
theorem clifford_flip {n : Type} [Fintype n] [DecidableEq n]
    (J σ : Matrix n n ℂ) (hanti : J * σ = -(σ * J))
    (hJ : J * J = 1) (hσ : σ * σ = 1) :
    (J * σ) * (J * σ) = -1 := by
  calc (J * σ) * (J * σ)
      = J * ((σ * J) * σ) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = J * (-(J * σ) * σ) := by
        rw [show σ * J = -(J * σ) from by
          rw [hanti, neg_neg]]
    _ = -((J * J) * (σ * σ)) := by
        rw [Matrix.neg_mul, Matrix.mul_neg,
          Matrix.mul_assoc, Matrix.mul_assoc]
    _ = -1 := by rw [hJ, hσ, Matrix.one_mul]

/-- The sum functional on the endpoint register. -/
def sumF : (V → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ v, x v
  map_add' x y := Finset.sum_add_distrib
  map_smul' c x := by
    simp [Finset.mul_sum]

/-- **The structural generation number is three**: the
mean-zero endpoint quotient `G` — the only matter
multiplicity carrier (`trace Q_G = 3` in the residual
algebra) — has dimension exactly three. -/
theorem generation_rank :
    Module.finrank ℂ (LinearMap.ker sumF) = 3 := by
  have hsurj : Function.Surjective sumF := by
    intro c
    exact ⟨fun _ => c / 4, by
      simp [sumF, Finset.sum_const]
      ring⟩
  have hrange : Module.finrank ℂ (LinearMap.range sumF)
      = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  have htotal := LinearMap.finrank_range_add_finrank_ker sumF
  rw [hrange, Module.finrank_fintype_fun_eq_card] at htotal
  simp only [Fintype.card_fin] at htotal
  omega

end SMActive
end NCG
