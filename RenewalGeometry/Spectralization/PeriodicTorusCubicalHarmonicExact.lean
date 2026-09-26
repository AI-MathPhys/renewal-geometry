/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.CellularModularHodgeExact
/-!
# Harmonic one-cochains of the periodic three-torus

This file covers the worked example of `cor:supp-modular-trichotomy` of
`papers/predictive_spectral_geometry`: the cubical cochain complex of the periodic
`n × n × n` lattice (the discrete three-torus `(ℤ/nℤ)³`) has a three-dimensional space of
harmonic one-cochains, spanned by the three axis-constant cochains.

We build the complex `C⁰ →d₀ C¹ →d₁ C²` with

* vertices `V n = Fin 3 → ZMod n`, edges `V n × Fin 3`, faces `V n × {(i, j) | i < j}`;
* `d₀ φ (v, i) = φ (v + eᵢ) - φ v`;
* `d₁ a (v, (i, j)) = a (v, i) + a (v + eᵢ, j) - a (v + eⱼ, i) - a (v, j)`,

prove `d₁ ∘ d₀ = 0`, compute the coboundary adjoint `d₀* a v = ∑ᵢ (a (v - eᵢ, i) - a (v, i))`,
and show `dim ℋ¹ = 3` (`finrank_harmonicSpace_eq_three`) via the energy identity: a harmonic
one-cochain has each axis component invariant under all three unit translations, hence constant.
The packaged statement `modular_trichotomy_three_torus` combines this with
`CellularModularHodge.modular_trichotomy`.
-/

open scoped InnerProductSpace
open Finset

namespace RenewalGeometry
namespace PeriodicTorusCubical

/-- Vertices of the periodic `n × n × n` cubical lattice (`cor:supp-modular-trichotomy`). -/
abbrev V (n : ℕ) : Type := Fin 3 → ZMod n

/-- The unit lattice vector along axis `i` (`cor:supp-modular-trichotomy`). -/
def e (n : ℕ) (i : Fin 3) : V n := Pi.single i 1

/-- Oriented faces of a cube: ordered axis pairs `(i, j)` with `i < j`
(`cor:supp-modular-trichotomy`). -/
abbrev Face : Type := {p : Fin 3 × Fin 3 // p.1 < p.2}

/-- Zero-cochains (vertex functions) of the periodic lattice (`cor:supp-modular-trichotomy`). -/
abbrev C₀ (n : ℕ) [NeZero n] : Type := EuclideanSpace ℝ (V n)

/-- One-cochains (edge functions) of the periodic lattice (`cor:supp-modular-trichotomy`). -/
abbrev C₁ (n : ℕ) [NeZero n] : Type := EuclideanSpace ℝ (V n × Fin 3)

/-- Two-cochains (face functions) of the periodic lattice (`cor:supp-modular-trichotomy`). -/
abbrev C₂ (n : ℕ) [NeZero n] : Type := EuclideanSpace ℝ (V n × Face)

variable (n : ℕ) [NeZero n]

/-- The vertex coboundary `d₀ φ (v, i) = φ (v + eᵢ) - φ v` (`cor:supp-modular-trichotomy`). -/
noncomputable def d₀ : C₀ n →ₗ[ℝ] C₁ n where
  toFun φ := WithLp.toLp 2 fun x => φ (x.1 + e n x.2) - φ x.1
  map_add' φ ψ := by
    ext x
    simp only [PiLp.add_apply]
    ring
  map_smul' c φ := by
    ext x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The edge coboundary `d₁ a (v, (i, j)) = a (v, i) + a (v + eᵢ, j) - a (v + eⱼ, i) - a (v, j)`
(`cor:supp-modular-trichotomy`). -/
noncomputable def d₁ : C₁ n →ₗ[ℝ] C₂ n where
  toFun a := WithLp.toLp 2 fun x =>
    a (x.1, x.2.1.1) + a (x.1 + e n x.2.1.1, x.2.1.2) - a (x.1 + e n x.2.1.2, x.2.1.1) -
      a (x.1, x.2.1.2)
  map_add' a b := by
    ext x
    simp only [PiLp.add_apply]
    ring
  map_smul' c a := by
    ext x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The explicit coboundary adjoint `d₀* a v = ∑ᵢ (a (v - eᵢ, i) - a (v, i))`
(`cor:supp-modular-trichotomy`). -/
noncomputable def divergence : C₁ n →ₗ[ℝ] C₀ n where
  toFun a := WithLp.toLp 2 fun v => ∑ i, (a (v - e n i, i) - a (v, i))
  map_add' a b := by
    ext v
    simp only [PiLp.add_apply, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  map_smul' c a := by
    ext v
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring

variable {n}

theorem d₀_apply (φ : C₀ n) (x : V n × Fin 3) : d₀ n φ x = φ (x.1 + e n x.2) - φ x.1 := rfl

theorem d₁_apply (a : C₁ n) (x : V n × Face) :
    d₁ n a x = a (x.1, x.2.1.1) + a (x.1 + e n x.2.1.1, x.2.1.2) -
      a (x.1 + e n x.2.1.2, x.2.1.1) - a (x.1, x.2.1.2) := rfl

theorem divergence_apply (a : C₁ n) (v : V n) :
    divergence n a v = ∑ i, (a (v - e n i, i) - a (v, i)) := rfl

/-- `d₁ ∘ d₀ = 0` for the cubical complex of the periodic lattice
(`cor:supp-modular-trichotomy`). -/
theorem d₁_comp_d₀ : d₁ n ∘ₗ d₀ n = 0 := by
  ext φ x
  simp only [LinearMap.comp_apply, d₁_apply, d₀_apply, LinearMap.zero_apply, PiLp.zero_apply]
  rw [add_right_comm x.1 (e n x.2.1.1) (e n x.2.1.2)]
  ring

/-! ### Translation reindexing -/

/-- Reindexing a sum over `V n` by the translation `v ↦ v - eⱼ`
(`cor:supp-modular-trichotomy`). -/
theorem sum_shift_mul (f g : V n → ℝ) (j : Fin 3) :
    ∑ v, f (v + e n j) * g v = ∑ v, f v * g (v - e n j) := by
  rw [← Equiv.sum_comp (Equiv.subRight (e n j)) (fun v => f (v + e n j) * g v)]
  simp only [Equiv.subRight_apply, sub_add_cancel]

/-- Summation by parts on the periodic lattice (`cor:supp-modular-trichotomy`). -/
theorem sum_shift_sub_mul (f g : V n → ℝ) (j : Fin 3) :
    ∑ v, (f (v + e n j) - f v) * g v = ∑ v, f v * (g (v - e n j) - g v) := by
  simp only [sub_mul, mul_sub, sum_sub_distrib, sum_shift_mul]

/-- The coboundary adjoint is the divergence: `d₀* a v = ∑ᵢ (a (v - eᵢ, i) - a (v, i))`
(`cor:supp-modular-trichotomy`). -/
theorem adjoint_d₀_eq : LinearMap.adjoint (d₀ n) = divergence n := by
  have h : d₀ n = LinearMap.adjoint (divergence n) := by
    rw [LinearMap.eq_adjoint_iff]
    intro φ a
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
    change ∑ x : V n × Fin 3, a x * (φ (x.1 + e n x.2) - φ x.1) =
      ∑ v, (∑ i, (a (v - e n i, i) - a (v, i))) * φ v
    rw [Fintype.sum_prod_type, sum_comm]
    simp only [sum_mul]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    calc ∑ v, a (v, i) * (φ (v + e n i) - φ v)
        = ∑ v, (φ (v + e n i) - φ v) * a (v, i) := sum_congr rfl fun v _ => mul_comm _ _
      _ = ∑ v, φ v * (a (v - e n i, i) - a (v, i)) := sum_shift_sub_mul φ (fun v => a (v, i)) i
      _ = ∑ v, (a (v - e n i, i) - a (v, i)) * φ v := sum_congr rfl fun v _ => mul_comm _ _
  rw [h, LinearMap.adjoint_adjoint]

/-- Explicit coboundary adjoint `d₀* a v = ∑ᵢ (a (v - eᵢ, i) - a (v, i))`
(`cor:supp-modular-trichotomy`). -/
theorem adjoint_d₀_apply (a : C₁ n) (v : V n) :
    LinearMap.adjoint (d₀ n) a v = ∑ i, (a (v - e n i, i) - a (v, i)) := by
  rw [adjoint_d₀_eq, divergence_apply]

/-! ### The axis-constant cochains -/

variable (n) in
/-- The axis-constant one-cochain `εᵢ (v, j) = δᵢⱼ` (`cor:supp-modular-trichotomy`). -/
noncomputable def axisCochain (i : Fin 3) : C₁ n :=
  WithLp.toLp 2 fun x => if x.2 = i then 1 else 0

theorem axisCochain_apply (i : Fin 3) (x : V n × Fin 3) :
    axisCochain n i x = if x.2 = i then 1 else 0 := rfl

/-- The axis-constant cochains are harmonic (`cor:supp-modular-trichotomy`). -/
theorem axisCochain_mem_harmonicSpace (i : Fin 3) :
    axisCochain n i ∈ CellularModularHodge.harmonicSpace (d₀ n) (d₁ n) := by
  rw [CellularModularHodge.mem_harmonicSpace_iff]
  constructor
  · ext x
    simp only [d₁_apply, axisCochain_apply, PiLp.zero_apply]
    ring
  · ext v
    simp only [adjoint_d₀_apply, axisCochain_apply, sub_self, sum_const_zero, PiLp.zero_apply]

/-- The axis-constant cochains are linearly independent (`cor:supp-modular-trichotomy`). -/
theorem linearIndependent_axisCochain : LinearIndependent ℝ (axisCochain n) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have := congrArg (fun a : C₁ n => a (0, i)) hg
  simpa [WithLp.ofLp_sum, Finset.sum_apply, axisCochain_apply] using this

/-! ### Every harmonic cochain is axis-constant -/

/-- The curl identity for all axis pairs, extracted from `d₁ a = 0`
(`cor:supp-modular-trichotomy`). -/
theorem curl_eq_of_d₁_eq_zero {a : C₁ n} (ha : d₁ n a = 0) (v : V n) (i j : Fin 3) :
    a (v + e n j, i) - a (v, i) = a (v + e n i, j) - a (v, j) := by
  have key : ∀ {i j : Fin 3}, i < j →
      a (v, i) + a (v + e n i, j) - a (v + e n j, i) - a (v, j) = 0 := fun {i j} hij => by
    have := congrArg (fun b : C₂ n => b (v, ⟨(i, j), hij⟩)) ha
    simpa [d₁_apply] using this
  rcases lt_trichotomy i j with hij | rfl | hji
  · linear_combination -key hij
  · ring
  · linear_combination key hji

/-- The divergence identity extracted from `d₀* a = 0` (`cor:supp-modular-trichotomy`). -/
theorem div_eq_of_adjoint_eq_zero {a : C₁ n} (ha : LinearMap.adjoint (d₀ n) a = 0) (v : V n) :
    ∑ j, (a (v - e n j, j) - a (v, j)) = 0 := by
  have := congrArg (fun b : C₀ n => b v) ha
  simpa [adjoint_d₀_apply] using this

/-- The energy identity: for a harmonic one-cochain, the Dirichlet energy of each axis
component vanishes (`cor:supp-modular-trichotomy`). -/
theorem energy_eq_zero {a : C₁ n}
    (hcurl : ∀ v i j, a (v + e n j, i) - a (v, i) = a (v + e n i, j) - a (v, j))
    (hdiv : ∀ v, ∑ j, (a (v - e n j, j) - a (v, j)) = 0) (i : Fin 3) :
    ∑ v, ∑ j, (a (v + e n j, i) - a (v, i)) ^ 2 = 0 := by
  calc ∑ v, ∑ j, (a (v + e n j, i) - a (v, i)) ^ 2
      = ∑ v, ∑ j, (a (v + e n j, i) - a (v, i)) * (a (v + e n i, j) - a (v, j)) := by
        refine sum_congr rfl fun v _ => sum_congr rfl fun j _ => ?_
        rw [sq, ← hcurl v i j]
    _ = ∑ j, ∑ v, (a (v + e n j, i) - a (v, i)) * (a (v + e n i, j) - a (v, j)) := sum_comm
    _ = ∑ j, ∑ v, a (v, i) *
          ((a (v - e n j + e n i, j) - a (v - e n j, j)) - (a (v + e n i, j) - a (v, j))) := by
        refine sum_congr rfl fun j _ => ?_
        exact sum_shift_sub_mul (fun v => a (v, i)) (fun v => a (v + e n i, j) - a (v, j)) j
    _ = ∑ v, a (v, i) *
          ∑ j, ((a (v - e n j + e n i, j) - a (v - e n j, j)) - (a (v + e n i, j) - a (v, j))) := by
        rw [sum_comm]
        simp only [mul_sum]
    _ = 0 := by
        refine sum_eq_zero fun v _ => ?_
        have h : ∑ j, ((a (v - e n j + e n i, j) - a (v - e n j, j)) -
            (a (v + e n i, j) - a (v, j))) =
            (∑ j, (a (v + e n i - e n j, j) - a (v + e n i, j))) -
              ∑ j, (a (v - e n j, j) - a (v, j)) := by
          rw [← sum_sub_distrib]
          refine sum_congr rfl fun j _ => ?_
          rw [sub_add_eq_add_sub]
          ring
        rw [h, hdiv, hdiv, sub_zero, mul_zero]

/-- A function on the periodic lattice invariant under the three unit translations is
constant (`cor:supp-modular-trichotomy`). -/
theorem eq_apply_zero_of_forall_add_e {f : V n → ℝ} (hf : ∀ v j, f (v + e n j) = f v)
    (v : V n) : f v = f 0 := by
  have hk : ∀ (k : ℕ) (w : V n) (j : Fin 3), f (w + k • e n j) = f w := by
    intro k
    induction k with
    | zero => intro w j; simp
    | succ k ih =>
      intro w j
      rw [succ_nsmul, ← add_assoc, hf, ih]
  have hv : v = 0 + (v 0).val • e n 0 + (v 1).val • e n 1 + (v 2).val • e n 2 := by
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, zero_add]
    fin_cases k <;> simp [e, -ZMod.natCast_val, ZMod.natCast_zmod_val]
  rw [hv, hk, hk, hk]

/-- Every harmonic one-cochain has translation-invariant axis components
(`cor:supp-modular-trichotomy`). -/
theorem apply_add_e_eq_of_mem_harmonicSpace {a : C₁ n}
    (ha : a ∈ CellularModularHodge.harmonicSpace (d₀ n) (d₁ n)) (v : V n) (i j : Fin 3) :
    a (v + e n j, i) = a (v, i) := by
  rw [CellularModularHodge.mem_harmonicSpace_iff] at ha
  have hE := energy_eq_zero (curl_eq_of_d₁_eq_zero ha.1) (div_eq_of_adjoint_eq_zero ha.2) i
  rw [sum_eq_zero_iff_of_nonneg (fun v _ => sum_nonneg fun j _ => sq_nonneg _)] at hE
  have := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp (hE v (mem_univ v)) j
    (mem_univ j)
  rw [sq_eq_zero_iff, sub_eq_zero] at this
  exact this

/-- Every harmonic one-cochain is a combination of the axis-constant cochains
(`cor:supp-modular-trichotomy`). -/
theorem eq_sum_axisCochain_of_mem_harmonicSpace {a : C₁ n}
    (ha : a ∈ CellularModularHodge.harmonicSpace (d₀ n) (d₁ n)) :
    a = ∑ i, a (0, i) • axisCochain n i := by
  ext ⟨v, i⟩
  have hconst : ∀ v i, a (v, i) = a (0, i) := fun v i =>
    eq_apply_zero_of_forall_add_e (f := fun w => a (w, i))
      (fun w j => apply_add_e_eq_of_mem_harmonicSpace ha w i j) v
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
    axisCochain_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true]
  exact hconst v i

/-- The harmonic space is spanned by the three axis-constant cochains
(`cor:supp-modular-trichotomy`). -/
theorem harmonicSpace_eq_span :
    CellularModularHodge.harmonicSpace (d₀ n) (d₁ n) =
      Submodule.span ℝ (Set.range (axisCochain n)) := by
  refine le_antisymm (fun a ha => ?_) (Submodule.span_le.mpr ?_)
  · rw [eq_sum_axisCochain_of_mem_harmonicSpace ha]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rintro _ ⟨i, rfl⟩
    exact axisCochain_mem_harmonicSpace i

/-- **`cor:supp-modular-trichotomy` (three-torus example).**  The harmonic one-cochains of the
periodic `n × n × n` cubical lattice form a three-dimensional space. -/
theorem finrank_harmonicSpace_eq_three :
    Module.finrank ℝ (CellularModularHodge.harmonicSpace (d₀ n) (d₁ n)) = 3 := by
  rw [harmonicSpace_eq_span, finrank_span_eq_card linearIndependent_axisCochain, Fintype.card_fin]

/-- **`cor:supp-modular-trichotomy` on the periodic three-torus.**  Every one-cochain `a` of the
periodic `n × n × n` cubical lattice satisfies the trichotomy (M1)–(M3) of
`CellularModularHodge.modular_trichotomy`, and the space of flat, gauge-inequivalent-to-zero
holonomies `ℋ¹` is exactly three-dimensional (one global holonomy per axis). -/
theorem modular_trichotomy_three_torus :
    (∀ a : C₁ n,
      CellularModularHodge.curvature (d₁ n) a ≠ 0 ∨
      (CellularModularHodge.curvature (d₁ n) a = 0 ∧
        CellularModularHodge.harmonicPart (d₀ n) (d₁ n) a ≠ 0) ∨
      (CellularModularHodge.curvature (d₁ n) a = 0 ∧
        CellularModularHodge.harmonicPart (d₀ n) (d₁ n) a = 0 ∧ ∃ φ : C₀ n, a = d₀ n φ)) ∧
    Module.finrank ℝ (CellularModularHodge.harmonicSpace (d₀ n) (d₁ n)) = 3 :=
  ⟨fun a => CellularModularHodge.modular_trichotomy d₁_comp_d₀ a, finrank_harmonicSpace_eq_three⟩

end PeriodicTorusCubical
end RenewalGeometry
