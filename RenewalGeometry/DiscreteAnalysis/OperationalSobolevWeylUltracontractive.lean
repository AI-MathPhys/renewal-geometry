/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.OperationalSobolevWeylFiniteGraph

/-!
# Ultracontractivity of the mean-zero heat semigroup on a finite weighted graph
  (`lem:supp-nash-counting`, `eq:supp-ultracontractive`; emergent-spacetime manuscript)

On the finite weighted graph `G_X` (`def:supp-spatial-dirichlet`), `P_{0,X}` is the orthogonal
projection of `L²(μ_X)` onto mean-zero functions and `T_X(t) = e^{-tΔ_X^{sp}} P_{0,X}`.  Here
`e^{-tΔ}` is the concrete Markov heat action `heatApply` of the graph and `P₀ f = f - ⟨f⟩_μ`.

* `meanZeroHeat_eq_kernel` — `T(t) f(u) = Σ_v μ(v) K⁰_t(u, v) f(v)` with the `μ`-kernel
  `K⁰_t(u, v) = Σ_{λ_j > 0} e^{-tλ_j} φ_j(u) φ_j(v)` (`meanZeroHeatKernel`): the heat kernel is
  `μ(v)(K⁰_t(u,v) + V^{-1})` and the stationary part is annihilated by `P₀`;
* `meanZeroHeatKernel_sq_le` — the semigroup/self-adjointness identity
  `K⁰_t(u,v) = ⟨col_u(t/2), col_v(t/2)⟩_μ` in spectral form and Cauchy–Schwarz:
  `K⁰_t(u,v)² ≤ ‖col_u(t/2)‖²_μ ‖col_v(t/2)‖²_μ`;
* `abs_meanZeroHeatKernel_le` — with the proved column decay
  `‖col_v(t/2)‖²_μ ≤ 4 (3C_S/(2t))^{3/2}` (Nash, `FiniteHeatColumn.l2_decay`),
  `sup_{u,v} |K⁰_t(u,v)| ≤ 4 (3C_S/(2t))^{3/2}`;
* `meanZeroHeat_ultracontractive` — **`eq:supp-ultracontractive`**:
  `‖T_X(t) f‖_∞ ≤ 4 (3C_S/(2t))^{3/2} ‖f‖_{L¹(μ)}` for every `f` and `t > 0`, i.e.
  `‖T_X(t)‖_{L¹ → L^∞} ≤ 4 (3C_S/(2t))^{3/2}`, with `C_S = 128 D_*/(I_*)²`.
-/

open scoped BigOperators

noncomputable section

namespace RenewalGeometry
namespace FiniteWeightedGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : FiniteWeightedGraph V)

/-- The mean-zero projection `P₀ f = f - ⟨f⟩_μ`, `⟨f⟩_μ = Σ μ f / μ(V)`. -/
def meanZeroProjection (f : V → ℝ) (v : V) : ℝ :=
  f v - (∑ u, G.mass u * f u) / G.volume

/-- The mean-zero heat semigroup `T(t) = e^{-tΔ} P₀` (`def:supp-spatial-dirichlet`). -/
def meanZeroHeat (t : ℝ) (f : V → ℝ) : V → ℝ :=
  G.heatApply t (G.meanZeroProjection f)

/-- The `μ`-kernel of `T(t)`: `K⁰_t(u, v) = Σ_{λ_j > 0} e^{-tλ_j} φ_j(u) φ_j(v)`. -/
def meanZeroHeatKernel (t : ℝ) (u v : V) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
    Real.exp (-t * G.eigenvalue j) * G.eigenfunction j u * G.eigenfunction j v

theorem meanZeroProjection_mass_sum (f : V → ℝ) :
    ∑ v, G.mass v * G.meanZeroProjection f v = 0 := by
  unfold meanZeroProjection
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  change (∑ v, G.mass v * f v) - G.volume * ((∑ u, G.mass u * f u) / G.volume) = 0
  field_simp [G.volume_pos.ne']
  ring

theorem meanZeroHeatKernel_eq_column (t : ℝ) (u v : V) :
    G.meanZeroHeatKernel t u v = G.positiveHeatColumn v t u := by
  unfold meanZeroHeatKernel positiveHeatColumn
  refine Finset.sum_congr rfl fun j _ => by ring

theorem meanZeroHeatKernel_eq_column' (t : ℝ) (u v : V) :
    G.meanZeroHeatKernel t u v = G.positiveHeatColumn u t v := rfl

/-- `Σ_v μ(v) K⁰_t(u, v) = 0`: the kernel is mean-zero in each variable. -/
theorem meanZeroHeatKernel_mass_sum (t : ℝ) (u : V) :
    ∑ v, G.mass v * G.meanZeroHeatKernel t u v = 0 := by
  simp_rw [G.meanZeroHeatKernel_eq_column']
  exact G.positiveHeatColumn_mean_zero u t

/-- **The `μ`-kernel representation** `T(t) f(u) = Σ_v μ(v) K⁰_t(u, v) f(v)`. -/
theorem meanZeroHeat_eq_kernel
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    (t : ℝ) (ht : 0 ≤ t) (f : V → ℝ) (u : V) :
    G.meanZeroHeat t f u = ∑ v, G.mass v * G.meanZeroHeatKernel t u v * f v := by
  have hker : ∀ x, G.heatKernel t u x =
      G.mass x * (G.meanZeroHeatKernel t u x + (G.volume)⁻¹) := fun x => by
    rw [G.meanZeroHeatKernel_eq_column, G.positiveHeatColumn_eq_heatKernel_sub_stationary I D h
      Vstar hI hD hh hVstar hvolume hdegree hcut x u t ht]
    field_simp [(G.mass_pos x).ne']
    ring
  set c : ℝ := (∑ w, G.mass w * f w) / G.volume with hc
  unfold meanZeroHeat heatApply
  simp_rw [hker]
  have h1 : ∑ x, G.mass x * (G.meanZeroHeatKernel t u x + (G.volume)⁻¹) *
      G.meanZeroProjection f x =
      ∑ x, G.mass x * G.meanZeroHeatKernel t u x * G.meanZeroProjection f x +
        (G.volume)⁻¹ * ∑ x, G.mass x * G.meanZeroProjection f x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h1, G.meanZeroProjection_mass_sum, mul_zero, add_zero]
  have h2 : ∑ x, G.mass x * G.meanZeroHeatKernel t u x * G.meanZeroProjection f x =
      ∑ x, G.mass x * G.meanZeroHeatKernel t u x * f x -
        c * ∑ x, G.mass x * G.meanZeroHeatKernel t u x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by unfold meanZeroProjection; rw [← hc]; ring
  rw [h2, G.meanZeroHeatKernel_mass_sum, mul_zero, sub_zero]

theorem positiveHeatColumnL2Sq_nonneg (v : V) (t : ℝ) : 0 ≤ G.positiveHeatColumnL2Sq v t := by
  unfold positiveHeatColumnL2Sq
  exact Finset.sum_nonneg fun j _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- Semigroup/self-adjointness and Cauchy–Schwarz:
`K⁰_t(u, v)² ≤ ‖col_u(t/2)‖²_μ ‖col_v(t/2)‖²_μ`. -/
theorem meanZeroHeatKernel_sq_le (t : ℝ) (u v : V) :
    G.meanZeroHeatKernel t u v ^ 2 ≤
      G.positiveHeatColumnL2Sq u (t / 2) * G.positiveHeatColumnL2Sq v (t / 2) := by
  set P := Finset.univ.filter (fun j => 0 < G.eigenvalue j)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq P
    (fun j => Real.exp (-(t / 2) * G.eigenvalue j) * G.eigenfunction j u)
    (fun j => Real.exp (-(t / 2) * G.eigenvalue j) * G.eigenfunction j v)
  have hexp : ∀ j, Real.exp (-(t / 2) * G.eigenvalue j) * Real.exp (-(t / 2) * G.eigenvalue j) =
      Real.exp (-t * G.eigenvalue j) := fun j => by
    rw [← Real.exp_add]; congr 1; ring
  have hexp2 : ∀ j, Real.exp (-(t / 2) * G.eigenvalue j) ^ 2 =
      Real.exp (-2 * (t / 2) * G.eigenvalue j) := fun j => by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hlhs : G.meanZeroHeatKernel t u v = ∑ j ∈ P,
      (Real.exp (-(t / 2) * G.eigenvalue j) * G.eigenfunction j u) *
        (Real.exp (-(t / 2) * G.eigenvalue j) * G.eigenfunction j v) := by
    unfold meanZeroHeatKernel
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hexp j]; ring
  have hu : G.positiveHeatColumnL2Sq u (t / 2) =
      ∑ j ∈ P, (Real.exp (-(t / 2) * G.eigenvalue j) * G.eigenfunction j u) ^ 2 := by
    unfold positiveHeatColumnL2Sq
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, hexp2 j]
  have hv : G.positiveHeatColumnL2Sq v (t / 2) =
      ∑ j ∈ P, (Real.exp (-(t / 2) * G.eigenvalue j) * G.eigenfunction j v) ^ 2 := by
    unfold positiveHeatColumnL2Sq
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, hexp2 j]
  rw [hlhs, hu, hv]
  exact hcs

/-- A nontrivial graph satisfying the cut/degree hypotheses has `D > 0` (otherwise the `L⁶`
Sobolev inequality would kill a nonzero positive eigenfunction). -/
theorem degreeConstant_pos [Nontrivial V]
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A) : 0 < D := by
  by_contra hnot
  have hDzero : D = 0 := le_antisymm (le_of_not_gt hnot) hD
  let v0 : V := Classical.choice inferInstance
  obtain ⟨j, hjpos, hjne⟩ := G.exists_positive_eigenfunction_nonzero
    I D h Vstar hI hD hh hVstar hvolume hdegree hcut v0
  have hsob := finite_meanZero_L6_sobolev G.mass
    (fun u => (G.mass_pos u).le) G.conductance G.conductance_nonneg
    G.conductance_symm (G.eigenfunction j) (G.eigenfunction_mean_zero hjpos)
    I D h hI hD hh hdegree hcut
  rw [hDzero] at hsob
  norm_num at hsob
  have hterm : G.mass v0 * G.eigenfunction j v0 ^ 6 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun u _ =>
      mul_nonneg (G.mass_pos u).le (by positivity))).mp
        (le_antisymm hsob (Finset.sum_nonneg fun u _ =>
          mul_nonneg (G.mass_pos u).le (by positivity)))
        v0 (Finset.mem_univ v0)
  have hp6 : G.eigenfunction j v0 ^ 6 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (G.mass_pos v0).ne'
  exact hjne (by
    by_contra hne
    exact (pow_ne_zero 6 hne) hp6)

/-- **Kernel bound**: `sup_{u,v} |K⁰_t(u, v)| ≤ 4 (3C_S/(2t))^{3/2}`, `C_S = 128 D/I²`. -/
theorem abs_meanZeroHeatKernel_le
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    (t : ℝ) (ht : 0 < t) (u v : V) :
    |G.meanZeroHeatKernel t u v| ≤ 4 * (3 * (128 * D / I ^ 2) / (2 * t)) ^ ((3 : ℝ) / 2) := by
  have hB0 : 0 ≤ 4 * (3 * (128 * D / I ^ 2) / (2 * t)) ^ ((3 : ℝ) / 2) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)
  cases subsingleton_or_nontrivial V with
  | inl hsub =>
      have hzero : ∀ j : V, G.eigenvalue j = 0 := by
        intro j
        obtain ⟨z, hz⟩ := G.exists_zero_eigenvalue
        exact congrArg G.eigenvalue (Subsingleton.elim j z) |>.trans hz
      have : G.meanZeroHeatKernel t u v = 0 := by
        unfold meanZeroHeatKernel
        simp [hzero]
      rw [this, abs_zero]
      exact hB0
  | inr hnon =>
      have hDpos := G.degreeConstant_pos I D h Vstar hI hD hh hVstar hvolume hdegree hcut
      have hCS : 0 < 128 * D / I ^ 2 := by positivity
      set B := 4 * (3 * (128 * D / I ^ 2) / (2 * t)) ^ ((3 : ℝ) / 2) with hB
      have hcol : ∀ w, G.positiveHeatColumnL2Sq w (t / 2) ≤ B := fun w => by
        have := (G.positiveHeatColumnCertificate I D h Vstar hI hD hh hVstar hvolume hdegree
          hcut w).l2_decay hCS (t / 2) (by positivity) (by
            change (0 : ℝ) < 2; norm_num)
        have hst : 3 * (128 * D / I ^ 2) / (4 * (t / 2)) = 3 * (128 * D / I ^ 2) / (2 * t) := by
          ring
        have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
        simpa [positiveHeatColumnCertificate, hst, hB, h4] using this
      have hsq : G.meanZeroHeatKernel t u v ^ 2 ≤ B * B :=
        (G.meanZeroHeatKernel_sq_le t u v).trans
          (mul_le_mul (hcol u) (hcol v) (G.positiveHeatColumnL2Sq_nonneg v _) hB0)
      calc |G.meanZeroHeatKernel t u v| ≤ Real.sqrt (B * B) := Real.abs_le_sqrt hsq
        _ = B := Real.sqrt_mul_self hB0

/-- **`eq:supp-ultracontractive`**: under the hypotheses of `lem:supp-l6-poincare`, for every
`t > 0`, every `f` and every vertex `u`,
`|T_X(t) f(u)| ≤ 4 (3C_S/(2t))^{3/2} Σ_v μ(v) |f(v)|`, i.e.
`‖T_X(t)‖_{L¹(μ) → L^∞} ≤ 4 (3C_S/(2t))^{3/2}` with `C_S = 128 D_*/(I_*)²`. -/
theorem meanZeroHeat_ultracontractive
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    (t : ℝ) (ht : 0 < t) (f : V → ℝ) (u : V) :
    |G.meanZeroHeat t f u| ≤
      4 * (3 * (128 * D / I ^ 2) / (2 * t)) ^ ((3 : ℝ) / 2) * ∑ v, G.mass v * |f v| := by
  rw [G.meanZeroHeat_eq_kernel I D h Vstar hI hD hh hVstar hvolume hdegree hcut t ht.le f u]
  set B := 4 * (3 * (128 * D / I ^ 2) / (2 * t)) ^ ((3 : ℝ) / 2)
  calc |∑ v, G.mass v * G.meanZeroHeatKernel t u v * f v|
      ≤ ∑ v, |G.mass v * G.meanZeroHeatKernel t u v * f v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, B * (G.mass v * |f v|) := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [abs_mul, abs_mul, abs_of_pos (G.mass_pos v)]
        have hk := G.abs_meanZeroHeatKernel_le I D h Vstar hI hD hh hVstar hvolume hdegree hcut
          t ht u v
        calc G.mass v * |G.meanZeroHeatKernel t u v| * |f v|
            ≤ G.mass v * B * |f v| := by
              have := (G.mass_pos v).le
              gcongr
          _ = B * (G.mass v * |f v|) := by ring
    _ = B * ∑ v, G.mass v * |f v| := by rw [Finset.mul_sum]

/-- The two-vertex graph with unit masses and unit conductance (non-vacuity witness). -/
def twoVertexGraph : FiniteWeightedGraph (Fin 2) where
  mass := fun _ => 1
  conductance := fun u v => if u = v then 0 else 1
  mass_pos := fun _ => one_pos
  conductance_nonneg := fun u v => by split_ifs <;> norm_num
  conductance_symm := fun u v => by
    by_cases h : u = v
    · subst h; rfl
    · simp [h, Ne.symm h]

theorem twoVertexGraph_cut (A : Finset (Fin 2)) :
    (1 : ℝ) * min (∑ v ∈ A, twoVertexGraph.mass v) (∑ v ∈ Aᶜ, twoVertexGraph.mass v) ^
        ((2 : ℝ) / 3) ≤ 1 * finiteCutCapacity twoVertexGraph.conductance A := by
  have hA : A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = Finset.univ := by
    revert A; decide
  rcases hA with rfl | rfl | rfl | rfl <;>
    simp [twoVertexGraph, finiteCutCapacity, Real.zero_rpow, Finset.compl_singleton]

/-- Non-vacuity of `meanZeroHeat_ultracontractive`: its hypotheses hold on the (nontrivial)
two-vertex graph with `I = D = h = 1`, `V_* = 2`. -/
example (t : ℝ) (ht : 0 < t) (f : Fin 2 → ℝ) (u : Fin 2) :
    |twoVertexGraph.meanZeroHeat t f u| ≤
      4 * (3 * (128 * 1 / 1 ^ 2) / (2 * t)) ^ ((3 : ℝ) / 2) *
        ∑ v, twoVertexGraph.mass v * |f v| :=
  twoVertexGraph.meanZeroHeat_ultracontractive 1 1 1 2 one_pos zero_le_one one_pos (by norm_num)
    (by simp [volume, twoVertexGraph])
    (fun v => by fin_cases v <;> simp [twoVertexGraph, Fin.sum_univ_two])
    twoVertexGraph_cut t ht f u

end FiniteWeightedGraph
end RenewalGeometry
