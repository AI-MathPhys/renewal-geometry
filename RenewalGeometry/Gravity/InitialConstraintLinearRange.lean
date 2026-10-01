/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridSampling

/-!
# The linearised initial constraint map and its range inverse
  (`lem:supp-initial-range`, linear half; `eq:supp-initial-phase-derivative`,
  `eq:supp-initial-linear-map`, `eq:supp-initial-right-inverse`, `eq:supp-initial-rank`;
  emergent-spacetime manuscript, supplement)

On the periodic grid `(ℤ/N)³` (`h = 1/N`, `d = N³`), with complexified fields and `Sym₃`
coordinates `(11, 22, 33, 12, 13, 23)` (`sym6`, `idx6`):

* `delta`: the odd phase derivative `δ_i`, the Fourier multiplier `i κ_i(k)`,
  `κ_i(k) = 2h⁻¹ sin(π h k_i)` (`kap`), with `|κ|² ≥ 16` off the zero mode
  (`sixteen_le_kapSq`).
* `Lh`: the linear initial constraint map
  `L_h(u, π) = (δ_iδ_j u_{ij} - Σ_i δ_i² tr u, -2 δ_j π^{ij})` (`eq:supp-initial-linear-map`).
* `Rh`: the range inverse `R_h(f, m) = (½(Ω_h²)⁻¹ f I, ½ 𝓛_h^{vec} 𝒟_h⁻¹ m)`
  (`eq:supp-initial-right-inverse`), with the Sherman–Morrison symbol
  `𝒟_h(k)⁻¹ = |κ|⁻²(I - κκᵀ/(4|κ|²))` of `𝒟_h(k) = |κ|² I + κκᵀ/3`.
* `Lh_Rh`: `L_h R_h = I` on mean-zero targets; `Lh_mem_meanZero`: `P_0 L_h = 0`;
  `range_Lh`: `range L_h` is exactly the mean-zero target space.
* `rank_Lh` (`eq:supp-initial-rank`): `rank L_h = 4d - 4`, `dim ker L_h = 8d + 4`.
* `Rh_bound`: `‖R_h y‖²_{H^{r+2} × H^{r+1}} ≤ C_r ‖y‖²_{H^r}` with `C_r` independent of `N`
  (per-mode bounds `scalar_mode_bound`, `vector_mode_bound`: orders `-2` and `-1`).

This is the linear half of `lem:supp-initial-range`; the nonlinear range equation needs the
constraint calculus of `lem:supp-initial-calculus` (open).
-/

open Finset ComplexConjugate
open scoped BigOperators Real

namespace RenewalGeometry.InitialConstraintLinearRange

open PeriodicGridSobolev PeriodicGridSobolev.Sampling LatticeTorusPlancherel

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### The odd phase derivative -/

/-- The phase symbol `κ_i(k) = 2 h⁻¹ sin(π h k_i)` on the signed frequency cube. -/
noncomputable def kap (i : Fin 3) (k : Grid N) : ℝ := 2 * N * Real.sin (π * freq i k / N)

/-- `|κ|² = Σ_i κ_i²`, the symbol of `Ω_h² = -Σ_i δ_i²`. -/
noncomputable def kapSq (k : Grid N) : ℝ := ∑ i, kap i k ^ 2

theorem kap_zero (i : Fin 3) : kap i (0 : Grid N) = 0 := by
  simp [kap, freq]

theorem kapSq_zero : kapSq (0 : Grid N) = 0 := by simp [kapSq, kap_zero]

theorem abs_kap_eq (i : Fin 3) (k : Grid N) : |kap i k| = ‖sym i k‖ := by
  rw [norm_sym_eq, kap, abs_mul, abs_mul, abs_two, Nat.abs_cast]
  ring

theorem kap_sq_eq (i : Fin 3) (k : Grid N) : kap i k ^ 2 = ‖sym i k‖ ^ 2 := by
  rw [← abs_kap_eq, sq_abs]

theorem sixteen_le_kapSq {k : Grid N} (hk : k ≠ 0) : 16 ≤ kapSq k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have hf : freq i k ≠ 0 := by
    simp only [freq]; rwa [Ne, ZMod.valMinAbs_eq_zero]
  have h1 : (1 : ℝ) ≤ (freq i k : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ freq i k ^ 2 := by
      have := Int.one_le_abs hf
      nlinarith [sq_abs (freq i k)]
    exact_mod_cast this
  have h2 := sq_le_norm_sym_sq i k
  rw [← kap_sq_eq] at h2
  have h3 : kap i k ^ 2 ≤ kapSq k :=
    single_le_sum (f := fun j => kap j k ^ 2) (fun _ _ => sq_nonneg _) (mem_univ i)
  nlinarith

theorem kapSq_ne_zero {k : Grid N} (hk : k ≠ 0) : kapSq k ≠ 0 := by
  have := sixteen_le_kapSq hk; linarith

/-! ### Fourier multipliers as linear maps -/

/-- The Fourier multiplier with symbol `m`. -/
noncomputable def fmult (m : Grid N → ℂ) : Module.End ℂ (Grid N → ℂ) where
  toFun u x := ∑ k, latticeChar k x * (m k * dft u k)
  map_add' u v := by
    funext x
    simp only [Pi.add_apply, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [dft_add]; ring
  map_smul' c u := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [dft_smul, smul_eq_mul]; ring

/-- The DFT at a fixed frequency, as a linear functional. -/
noncomputable def dftL (k : Grid N) : (Grid N → ℂ) →ₗ[ℂ] ℂ where
  toFun u := dft u k
  map_add' u v := dft_add u v k
  map_smul' c u := by rw [dft_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]

theorem dftL_apply (k : Grid N) (u : Grid N → ℂ) : dftL k u = dft u k := rfl

theorem dftL_fmult (m : Grid N → ℂ) (u : Grid N → ℂ) (k : Grid N) :
    dftL k (fmult m u) = m k * dftL k u :=
  dft_synth (fun k => m k * dft u k) k

theorem eq_of_dftL_eq {u v : Grid N → ℂ} (h : ∀ k, dftL k u = dftL k v) : u = v :=
  eq_of_dft_eq h

/-- The odd phase derivative `δ_i` (`eq:supp-initial-phase-derivative`):
`(δ_i u)^(k) = i κ_i(k) û(k)`. -/
noncomputable def delta (i : Fin 3) : Module.End ℂ (Grid N → ℂ) :=
  fmult fun k => Complex.I * (kap i k : ℂ)

theorem dftL_delta (i : Fin 3) (u : Grid N → ℂ) (k : Grid N) :
    dftL k (delta i u) = Complex.I * (kap i k : ℂ) * dftL k u :=
  dftL_fmult _ u k

/-! ### Symmetric tensor fields -/

/-- Coordinates of a symmetric `3 × 3` tensor: `(11, 22, 33, 12, 13, 23)`. -/
def sym6 (i j : Fin 3) : Fin 6 := ![![0, 3, 4], ![3, 1, 5], ![4, 5, 2]] i j

/-- The entry `(i, j)` of a coordinate index (`sym6 (idx6 a).1 (idx6 a).2 = a`). -/
def idx6 (a : Fin 6) : Fin 3 × Fin 3 := ![(0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2)] a

/-- Initial records `X = (u, π)`: a pair of complexified `Sym₃`-valued grid fields. -/
abbrev Dom (N : ℕ) := (Fin 6 → Grid N → ℂ) × (Fin 6 → Grid N → ℂ)

/-- Constraint targets `(f, m) ∈ H_h(ℝ ⊕ ℝ³)` (complexified). -/
abbrev Tgt (N : ℕ) := (Grid N → ℂ) × (Fin 3 → Grid N → ℂ)

/-- Coordinate projection of a `Sym₃` field. -/
noncomputable def pr (a : Fin 6) : (Fin 6 → Grid N → ℂ) →ₗ[ℂ] (Grid N → ℂ) := LinearMap.proj a

/-- Coordinate projection of a vector field. -/
noncomputable def pr3 (j : Fin 3) : (Fin 3 → Grid N → ℂ) →ₗ[ℂ] (Grid N → ℂ) := LinearMap.proj j

/-- The scalar (Hamiltonian) row `δ_i δ_j u_{ij} - Σ_i δ_i² tr u`. -/
noncomputable def rowS : (Fin 6 → Grid N → ℂ) →ₗ[ℂ] (Grid N → ℂ) :=
  (∑ i, ∑ j, delta i ∘ₗ delta j ∘ₗ pr (sym6 i j)) -
    ∑ i, delta i ∘ₗ delta i ∘ₗ (pr 0 + pr 1 + pr 2)

/-- The vector (momentum) row `-2 δ_j π^{ij}`. -/
noncomputable def rowV : (Fin 6 → Grid N → ℂ) →ₗ[ℂ] (Fin 3 → Grid N → ℂ) :=
  LinearMap.pi fun i => (-2 : ℂ) • ∑ j, delta j ∘ₗ pr (sym6 i j)

/-- **The linearised initial constraint map** `L_h(u, π) = (δ_iδ_j u_{ij} - Σ_i δ_i² tr u,
-2 δ_j π^{ij})` (`eq:supp-initial-linear-map`). -/
noncomputable def Lh : Dom N →ₗ[ℂ] Tgt N := rowS.prodMap rowV

/-! ### The range inverse -/

/-- `½ (Ω_h²)⁻¹` on mean-zero scalars. -/
noncomputable def scalarInv : Module.End ℂ (Grid N → ℂ) :=
  fmult fun k => ((2 * kapSq k : ℝ) : ℂ)⁻¹

/-- `𝒟_h⁻¹`, symbol `|κ|⁻²(I - κκᵀ/(4|κ|²))` (Sherman–Morrison inverse of
`|κ|² I + κκᵀ/3`), component `i`. -/
noncomputable def Dinv (i : Fin 3) : (Fin 3 → Grid N → ℂ) →ₗ[ℂ] (Grid N → ℂ) :=
  ∑ j, fmult (fun k => (((kapSq k)⁻¹ * ((if i = j then 1 else 0) -
      kap i k * kap j k / (4 * kapSq k)) : ℝ) : ℂ)) ∘ₗ pr3 j

/-- `½ 𝓛_h^{vec} Y`, the component `(i, j)`:
`½(δ_i Y_j + δ_j Y_i - ⅔ δ_{ij} δ_k Y_k)`. -/
noncomputable def halfLvec (i j : Fin 3) : (Fin 3 → Grid N → ℂ) →ₗ[ℂ] (Grid N → ℂ) :=
  (2 : ℂ)⁻¹ • (delta i ∘ₗ Dinv j + delta j ∘ₗ Dinv i -
    (if i = j then (2 / 3 : ℂ) else 0) • ∑ k, delta k ∘ₗ Dinv k)

/-- **The range inverse** `R_h(f, m) = (½(Ω_h²)⁻¹ f I, ½ 𝓛_h^{vec} 𝒟_h⁻¹ m)`
(`eq:supp-initial-right-inverse`). -/
noncomputable def Rh : Tgt N →ₗ[ℂ] Dom N :=
  (LinearMap.pi fun a : Fin 6 => if (a : ℕ) < 3 then scalarInv else 0).prodMap
    (LinearMap.pi fun a : Fin 6 => halfLvec (idx6 a).1 (idx6 a).2)

/-- The four spatial means `P_0 (f, m) = (f̂(0), m̂(0))`. -/
noncomputable def meanMap : Tgt N →ₗ[ℂ] ℂ × (Fin 3 → ℂ) :=
  (dftL 0).prodMap (LinearMap.pi fun i => dftL 0 ∘ₗ pr3 i)

/-- Mean-zero targets. -/
noncomputable def meanZero (N : ℕ) [NeZero N] : Submodule ℂ (Tgt N) := LinearMap.ker meanMap


/-! ### Fourier symbols of the rows -/

theorem dftL_rowS (u : Fin 6 → Grid N → ℂ) (k : Grid N) :
    dftL k (rowS u) = (∑ i, ∑ j, (Complex.I * kap i k) * (Complex.I * kap j k) *
        dftL k (u (sym6 i j))) -
      ∑ i, (Complex.I * kap i k) * (Complex.I * kap i k) *
        (dftL k (u 0) + dftL k (u 1) + dftL k (u 2)) := by
  simp only [rowS, LinearMap.sub_apply, LinearMap.sum_apply, map_sub, map_sum,
    LinearMap.comp_apply, dftL_delta, LinearMap.add_apply, pr, LinearMap.proj_apply, map_add]
  congr 1
  · refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_; ring
  · refine sum_congr rfl fun i _ => ?_; ring

theorem dftL_rowV (p : Fin 6 → Grid N → ℂ) (i : Fin 3) (k : Grid N) :
    dftL k (rowV p i) = -2 * ∑ j, (Complex.I * kap j k) * dftL k (p (sym6 i j)) := by
  simp only [rowV, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, LinearMap.comp_apply, dftL_delta, pr,
    LinearMap.proj_apply, smul_eq_mul]

theorem dftL_scalarInv (f : Grid N → ℂ) (k : Grid N) :
    dftL k (scalarInv f) = ((2 * kapSq k : ℝ) : ℂ)⁻¹ * dftL k f :=
  dftL_fmult _ f k

theorem dftL_Dinv (i : Fin 3) (m : Fin 3 → Grid N → ℂ) (k : Grid N) :
    dftL k (Dinv i m) = ∑ j, (((kapSq k)⁻¹ * ((if i = j then 1 else 0) -
      kap i k * kap j k / (4 * kapSq k)) : ℝ) : ℂ) * dftL k (m j) := by
  simp only [Dinv, LinearMap.sum_apply, map_sum, LinearMap.comp_apply,
    dftL_fmult, pr3, LinearMap.proj_apply]

theorem dftL_halfLvec (i j : Fin 3) (m : Fin 3 → Grid N → ℂ) (k : Grid N) :
    dftL k (halfLvec i j m) = (2 : ℂ)⁻¹ * ((Complex.I * kap i k) * dftL k (Dinv j m) +
      (Complex.I * kap j k) * dftL k (Dinv i m) - (if i = j then (2 / 3 : ℂ) else 0) *
        ∑ l, (Complex.I * kap l k) * dftL k (Dinv l m)) := by
  simp only [halfLvec, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.sum_apply, map_smul, map_sub, map_add, map_sum,
    LinearMap.comp_apply, dftL_delta, smul_eq_mul]

theorem mem_meanZero (y : Tgt N) :
    y ∈ meanZero N ↔ dftL 0 y.1 = 0 ∧ ∀ i, dftL 0 (y.2 i) = 0 := by
  simp only [meanZero, LinearMap.mem_ker, meanMap, LinearMap.prodMap_apply, Prod.mk_eq_zero,
    LinearMap.pi_apply, LinearMap.comp_apply, pr3, LinearMap.proj_apply]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i => congrFun h2 i⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, funext h2⟩

/-- `L_h` takes values in mean-zero targets (`P_0 L_h = 0`). -/
theorem Lh_mem_meanZero (x : Dom N) : Lh x ∈ meanZero N := by
  rw [mem_meanZero]
  refine ⟨?_, fun i => ?_⟩
  · simp only [Lh, LinearMap.prodMap_apply]
    rw [dftL_rowS]; simp [kap_zero]
  · simp only [Lh, LinearMap.prodMap_apply]
    rw [dftL_rowV]; simp [kap_zero]

/-- **Right inverse** (`lem:supp-initial-range`): `L_h R_h = I` on mean-zero targets. -/
theorem Lh_Rh {y : Tgt N} (hy : y ∈ meanZero N) : Lh (Rh y) = y := by
  rw [mem_meanZero] at hy
  obtain ⟨hf, hm⟩ := hy
  obtain ⟨f, m⟩ := y
  simp only at hf hm
  simp only [Lh, Rh, LinearMap.prodMap_apply]
  refine Prod.ext ?_ ?_
  · refine eq_of_dftL_eq fun k => ?_
    simp only
    rw [dftL_rowS]
    by_cases hk : k = 0
    · subst hk; simp [kap_zero, hf]
    · have hK := kapSq_ne_zero hk
      simp only [LinearMap.pi_apply, Fin.sum_univ_three, sym6]
      simp [dftL_scalarInv]
      have hK' : ((kapSq k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hK
      have e : ((kapSq k : ℝ) : ℂ) = (kap 0 k : ℂ) ^ 2 + (kap 1 k : ℂ) ^ 2 + (kap 2 k : ℂ) ^ 2 := by
        simp [kapSq, Fin.sum_univ_three]
      field_simp
      rw [e]
      ring_nf
      rw [Complex.I_sq]
      ring
  · funext i
    refine eq_of_dftL_eq fun k => ?_
    rw [dftL_rowV]
    by_cases hk : k = 0
    · subst hk; simp [kap_zero, hm]
    · have hK := kapSq_ne_zero hk
      have hK' : ((kapSq k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hK
      have e : ((kapSq k : ℝ) : ℂ) = (kap 0 k : ℂ) ^ 2 + (kap 1 k : ℂ) ^ 2 + (kap 2 k : ℂ) ^ 2 := by
        simp [kapSq, Fin.sum_univ_three]
      simp only [LinearMap.pi_apply, Fin.sum_univ_three, sym6, idx6, dftL_halfLvec, dftL_Dinv]
      fin_cases i <;> simp <;> push_cast <;> field_simp <;> rw [e] <;> ring_nf <;>
        simp only [Complex.I_sq] <;> ring_nf


/-! ### Range, rank and kernel -/

/-- `range L_h` is exactly the mean-zero target space. -/
theorem range_Lh : LinearMap.range (Lh (N := N)) = meanZero N := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩; exact Lh_mem_meanZero x
  · intro y hy; exact ⟨Rh y, Lh_Rh hy⟩

theorem finrank_grid_fun : Module.finrank ℂ (Grid N → ℂ) = N ^ 3 := by
  rw [Module.finrank_fintype_fun_eq_card]; simp [ZMod.card]

theorem finrank_Tgt : Module.finrank ℂ (Tgt N) = 4 * N ^ 3 := by
  rw [Module.finrank_prod]
  simp [Module.finrank_pi_fintype, ZMod.card]
  ring

theorem finrank_Dom : Module.finrank ℂ (Dom N) = 12 * N ^ 3 := by
  rw [Module.finrank_prod]
  simp [Module.finrank_pi_fintype, ZMod.card]
  ring

theorem dftL_zero_const (c : ℂ) : dftL 0 (fun _ : Grid N => c) = c := by
  have hn : ((N : ℂ) ^ 3) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp only [dftL_apply, dft, smul_eq_mul]
  have h0 : ∀ x : Grid N, latticeChar 0 x = 1 := by
    intro x; rw [latticeChar_comm]; exact latticeChar_zero_right x
  simp only [h0, map_one, one_mul, sum_const, card_univ, nsmul_eq_mul]
  have : (Fintype.card (Grid N) : ℂ) = (N : ℂ) ^ 3 := by simp [ZMod.card]
  rw [this]; field_simp

theorem meanMap_surjective : Function.Surjective (meanMap (N := N)) := by
  rintro ⟨c, v⟩
  refine ⟨(fun _ => c, fun i _ => v i), ?_⟩
  simp only [meanMap, LinearMap.prodMap_apply, dftL_zero_const]
  refine Prod.ext rfl (funext fun i => ?_)
  simp [pr3, dftL_zero_const]

/-- The mean-zero target space has dimension `4d - 4`, `d = N³`. -/
theorem finrank_meanZero : Module.finrank ℂ (meanZero N) = 4 * N ^ 3 - 4 := by
  have h := LinearMap.finrank_range_add_finrank_ker (meanMap (N := N))
  rw [LinearMap.range_eq_top.mpr meanMap_surjective, finrank_top, Module.finrank_prod,
    Module.finrank_fin_fun, Module.finrank_self, finrank_Tgt] at h
  have h2 : Module.finrank ℂ (LinearMap.ker (meanMap (N := N))) = 4 * N ^ 3 - 4 := by omega
  exact h2

/-- **Rank and kernel** (`eq:supp-initial-rank`): with `d = N³`,
`rank L_h = 4d - 4` and `dim ker L_h = 8d + 4`. -/
theorem rank_Lh :
    Module.finrank ℂ (LinearMap.range (Lh (N := N))) = 4 * N ^ 3 - 4 ∧
      Module.finrank ℂ (LinearMap.ker (Lh (N := N))) = 8 * N ^ 3 + 4 := by
  have hr : Module.finrank ℂ (LinearMap.range (Lh (N := N))) = 4 * N ^ 3 - 4 := by
    rw [range_Lh, finrank_meanZero]
  refine ⟨hr, ?_⟩
  have h := LinearMap.finrank_range_add_finrank_ker (Lh (N := N))
  rw [hr, finrank_Dom] at h
  have hN : 1 ≤ N ^ 3 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne N))
  omega


/-! ### The uniform bound on the range inverse -/

theorem kap_sq_le_kapSq (i : Fin 3) (k : Grid N) : kap i k ^ 2 ≤ kapSq k :=
  single_le_sum (f := fun j => kap j k ^ 2) (fun _ _ => sq_nonneg _) (mem_univ i)

theorem kapSq_nonneg (k : Grid N) : 0 ≤ kapSq k := sum_nonneg fun _ _ => sq_nonneg _

/-- `⟨κ⟩² = 1 + |κ|²`. -/
noncomputable def gbr (k : Grid N) : ℝ := 1 + kapSq k

theorem one_le_gbr (k : Grid N) : 1 ≤ gbr k := by
  have := kapSq_nonneg k; unfold gbr; linarith

theorem norm_dsym_sq_kap (α : Fin 3 → ℕ) (k : Grid N) :
    ‖dsym α k‖ ^ 2 = (kap 0 k ^ 2) ^ α 0 * (kap 1 k ^ 2) ^ α 1 * (kap 2 k ^ 2) ^ α 2 := by
  rw [norm_dsym_sq, kap_sq_eq, kap_sq_eq, kap_sq_eq]

theorem gridWeight_le_gbr (t : ℕ) (k : Grid N) :
    gridWeight t k ≤ ((multiIndices t).card : ℝ) * gbr k ^ t := by
  have hB := one_le_gbr k
  have hc : ∀ i, kap i k ^ 2 ≤ gbr k := fun i => by
    have := kap_sq_le_kapSq i k; unfold gbr; linarith
  unfold gridWeight
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun α hα => ?_
  rw [norm_dsym_sq_kap]
  calc (kap 0 k ^ 2) ^ α 0 * (kap 1 k ^ 2) ^ α 1 * (kap 2 k ^ 2) ^ α 2
      ≤ gbr k ^ α 0 * gbr k ^ α 1 * gbr k ^ α 2 :=
        mul_le_mul (mul_le_mul (pow_le_pow_left₀ (sq_nonneg _) (hc 0) _)
          (pow_le_pow_left₀ (sq_nonneg _) (hc 1) _) (by positivity) (by positivity))
          (pow_le_pow_left₀ (sq_nonneg _) (hc 2) _) (by positivity) (by positivity)
    _ = gbr k ^ deg α := by rw [deg, pow_add, pow_add]
    _ ≤ gbr k ^ t := pow_le_pow_right₀ hB (mem_multiIndices.mp hα)

theorem norm_dsym_le_gridWeight {t : ℕ} {α : Fin 3 → ℕ} (h : deg α ≤ t) (k : Grid N) :
    ‖dsym α k‖ ^ 2 ≤ gridWeight t k :=
  single_le_sum (f := fun β => ‖dsym β k‖ ^ 2) (fun β _ => sq_nonneg _) (mem_multiIndices.mpr h)

theorem gbr_pow_le_gridWeight (t : ℕ) (k : Grid N) : gbr k ^ t ≤ 4 ^ t * gridWeight t k := by
  have hsingle : ∀ i, (kap i k ^ 2) ^ t ≤ gridWeight t k := by
    intro i
    have h := norm_dsym_le_gridWeight (t := t) (α := Pi.single i t) (by rw [deg_single]) k
    rw [norm_dsym_sq_kap] at h
    fin_cases i <;> simpa using h
  have hzero : 1 ≤ gridWeight t k := by
    have h := norm_dsym_le_gridWeight (t := t) (α := 0) (by simp [deg]) k
    rw [norm_dsym_sq_kap] at h
    simpa using h
  set a := kap 0 k ^ 2
  set b := kap 1 k ^ 2
  set c := kap 2 k ^ 2
  set m : ℝ := max 1 (max a (max b c))
  have hbr : gbr k = 1 + a + b + c := by simp [gbr, kapSq, Fin.sum_univ_three, a, b, c]; ring
  have ha : a ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hb : b ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hc : c ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hle : gbr k ≤ 4 * m := by rw [hbr]; have := le_max_left 1 (max a (max b c)); linarith
  have hmT : m ^ t ≤ gridWeight t k := by
    rcases max_choice 1 (max a (max b c)) with h | h
    · rw [show m = 1 from h, one_pow]; exact hzero
    · rw [show m = _ from h]
      rcases max_choice a (max b c) with h' | h'
      · rw [h']; exact hsingle 0
      · rw [h']
        rcases max_choice b c with h'' | h''
        · rw [h'']; exact hsingle 1
        · rw [h'']; exact hsingle 2
  calc gbr k ^ t ≤ (4 * m) ^ t := pow_le_pow_left₀ (le_trans zero_le_one (one_le_gbr k)) hle t
    _ = 4 ^ t * m ^ t := mul_pow _ _ _
    _ ≤ 4 ^ t * gridWeight t k := by gcongr

theorem gridWeight_add_le (r t : ℕ) (k : Grid N) :
    gridWeight (r + t) k ≤
      ((multiIndices (r + t)).card : ℝ) * 4 ^ r * gbr k ^ t * gridWeight r k := by
  have h1 := gridWeight_le_gbr (r + t) k
  have h2 := gbr_pow_le_gridWeight r k
  have hg : 0 ≤ gbr k ^ t := pow_nonneg (le_trans zero_le_one (one_le_gbr k)) t
  calc gridWeight (r + t) k ≤ ((multiIndices (r + t)).card : ℝ) * gbr k ^ (r + t) := h1
    _ = ((multiIndices (r + t)).card : ℝ) * gbr k ^ t * gbr k ^ r := by rw [pow_add]; ring
    _ ≤ ((multiIndices (r + t)).card : ℝ) * gbr k ^ t * (4 ^ r * gridWeight r k) := by
        gcongr
    _ = _ := by ring

theorem gbr_le_of_ne_zero {k : Grid N} (hk : k ≠ 0) : gbr k ≤ 17 / 16 * kapSq k := by
  have := sixteen_le_kapSq hk; unfold gbr; linarith

/-- Per-mode bound for `½(Ω_h²)⁻¹`: order `-2`. -/
theorem scalar_mode_bound (r : ℕ) (k : Grid N) :
    gridWeight (r + 2) k * ‖((2 * kapSq k : ℝ) : ℂ)⁻¹‖ ^ 2 ≤
      (((multiIndices (r + 2)).card : ℝ) * 4 ^ r * (17 / 16) ^ 2 / 4) * gridWeight r k := by
  by_cases hk : k = 0
  · subst hk; rw [kapSq_zero]; simp only [mul_zero, Complex.ofReal_zero, inv_zero, norm_zero]
    have : 0 ≤ gridWeight r (0 : Grid N) := gridWeight_nonneg r 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity
  · have hK := sixteen_le_kapSq hk
    have hKp : 0 < kapSq k := by linarith
    have hg := gridWeight_add_le r 2 k
    have hgb := gbr_le_of_ne_zero hk
    have hgw := gridWeight_nonneg r k
    have hnorm : ‖((2 * kapSq k : ℝ) : ℂ)⁻¹‖ ^ 2 = (4 * kapSq k ^ 2)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), inv_pow]
      ring
    rw [hnorm]
    have hgb2 : gbr k ^ 2 ≤ (17 / 16 * kapSq k) ^ 2 :=
      pow_le_pow_left₀ (le_trans zero_le_one (one_le_gbr k)) hgb 2
    set c := ((multiIndices (r + 2)).card : ℝ)
    have hc : 0 ≤ c := Nat.cast_nonneg _
    calc gridWeight (r + 2) k * (4 * kapSq k ^ 2)⁻¹
        ≤ (c * 4 ^ r * gbr k ^ 2 * gridWeight r k) * (4 * kapSq k ^ 2)⁻¹ := by gcongr
      _ ≤ (c * 4 ^ r * (17 / 16 * kapSq k) ^ 2 * gridWeight r k) * (4 * kapSq k ^ 2)⁻¹ := by
          gcongr
      _ = _ := by field_simp

/-- Per-mode bound for `½ 𝓛_h^{vec} 𝒟_h⁻¹`: order `-1`. -/
theorem vector_mode_bound (r : ℕ) (i j : Fin 3) (m : Fin 3 → Grid N → ℂ) (k : Grid N) :
    gridWeight (r + 1) k * ‖dftL k (halfLvec i j m)‖ ^ 2 ≤
      (((multiIndices (r + 1)).card : ℝ) * 4 ^ r * (17 / 16) * (75 / 4)) *
        (gridWeight r k * ∑ l, ‖dftL k (m l)‖ ^ 2) := by
  set c := ((multiIndices (r + 1)).card : ℝ)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hgw := gridWeight_nonneg r k
  have hsum0 : 0 ≤ ∑ l, ‖dftL k (m l)‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  by_cases hk : k = 0
  · subst hk
    have : dftL 0 (halfLvec i j m) = 0 := by
      rw [dftL_halfLvec]; simp [kap_zero]
    rw [this, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity
  have hK := sixteen_le_kapSq hk
  have hKp : 0 < kapSq k := by linarith
  set K := kapSq k
  set μ := ∑ l, ‖dftL k (m l)‖
  have hμ : 0 ≤ μ := sum_nonneg fun _ _ => norm_nonneg _
  have hκ : ∀ l, |kap l k| ≤ Real.sqrt K := fun l =>
    Real.abs_le_sqrt (kap_sq_le_kapSq l k)
  have hcoef : ∀ l l', |K⁻¹ * ((if l = l' then 1 else 0) - kap l k * kap l' k / (4 * K))| ≤
      5 / 4 * K⁻¹ := by
    intro l l'
    have h1 : |kap l k * kap l' k| ≤ K := by
      rw [abs_mul]
      have := kap_sq_le_kapSq l k; have := kap_sq_le_kapSq l' k
      nlinarith [sq_abs (kap l k), sq_abs (kap l' k), abs_nonneg (kap l k),
        abs_nonneg (kap l' k), sq_nonneg (|kap l k| - |kap l' k|)]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hKp)]
    have h2 : |(if l = l' then (1 : ℝ) else 0) - kap l k * kap l' k / (4 * K)| ≤ 5 / 4 := by
      refine (abs_sub _ _).trans ?_
      have h3 : |(if l = l' then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      have h4 : |kap l k * kap l' k / (4 * K)| ≤ 1 / 4 := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 4 * K), div_le_iff₀ (by linarith)]
        linarith
      linarith
    nlinarith [inv_pos.mpr hKp]
  have hX : ∀ l, ‖dftL k (Dinv l m)‖ ≤ 5 / 4 * K⁻¹ * μ := by
    intro l
    rw [dftL_Dinv]
    refine (norm_sum_le _ _).trans ?_
    rw [show μ = ∑ l', ‖dftL k (m l')‖ from rfl, mul_sum]
    refine sum_le_sum fun l' _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hcoef l l') (norm_nonneg _)
  set β := 5 / 4 * K⁻¹ * μ
  have hβ : 0 ≤ β := by positivity
  have hIk : ∀ l (z : ℂ), ‖Complex.I * (kap l k : ℂ) * z‖ ≤ Real.sqrt K * β ∨
      ‖dftL k (Dinv l m)‖ ≠ ‖z‖ := by
    intro l z
    by_cases hz : ‖dftL k (Dinv l m)‖ = ‖z‖
    · left
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, ← hz]
      exact mul_le_mul (hκ l) (hX l) (norm_nonneg _) (Real.sqrt_nonneg _)
    · right; exact hz
  have hterm : ∀ l l', ‖Complex.I * (kap l k : ℂ) * dftL k (Dinv l' m)‖ ≤ Real.sqrt K * β := by
    intro l l'
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hκ l) (hX l') (norm_nonneg _) (Real.sqrt_nonneg _)
  have hhalf : ‖dftL k (halfLvec i j m)‖ ≤ 2 * Real.sqrt K * β := by
    rw [dftL_halfLvec, norm_mul]
    have hn2 : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by simp
    rw [hn2]
    have hsum : ‖∑ l, Complex.I * (kap l k : ℂ) * dftL k (Dinv l m)‖ ≤ 3 * (Real.sqrt K * β) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ l, ‖Complex.I * (kap l k : ℂ) * dftL k (Dinv l m)‖ ≤ ∑ _l : Fin 3, Real.sqrt K * β :=
            sum_le_sum fun l _ => hterm l l
        _ = 3 * (Real.sqrt K * β) := by simp
    have hcoef3 : ‖(if i = j then (2 / 3 : ℂ) else 0)‖ ≤ 2 / 3 := by
      split_ifs
      · simp only [norm_div, Complex.norm_ofNat]; norm_num
      · norm_num
    have htri := norm_sub_le (Complex.I * (kap i k : ℂ) * dftL k (Dinv j m) +
      Complex.I * (kap j k : ℂ) * dftL k (Dinv i m))
      ((if i = j then (2 / 3 : ℂ) else 0) * ∑ l, Complex.I * (kap l k : ℂ) * dftL k (Dinv l m))
    have hadd := norm_add_le (Complex.I * (kap i k : ℂ) * dftL k (Dinv j m))
      (Complex.I * (kap j k : ℂ) * dftL k (Dinv i m))
    have hmul : ‖(if i = j then (2 / 3 : ℂ) else 0) *
        ∑ l, Complex.I * (kap l k : ℂ) * dftL k (Dinv l m)‖ ≤ 2 / 3 * (3 * (Real.sqrt K * β)) := by
      rw [norm_mul]
      exact mul_le_mul hcoef3 hsum (norm_nonneg _) (by norm_num)
    have := hterm i j; have := hterm j i
    have hs0 : 0 ≤ Real.sqrt K * β := mul_nonneg (Real.sqrt_nonneg _) hβ
    nlinarith
  have hsq : ‖dftL k (halfLvec i j m)‖ ^ 2 ≤ 25 / 4 * K⁻¹ * μ ^ 2 := by
    have h0 : 0 ≤ 2 * Real.sqrt K * β := by positivity
    calc ‖dftL k (halfLvec i j m)‖ ^ 2 ≤ (2 * Real.sqrt K * β) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hhalf 2
      _ = 4 * K * β ^ 2 := by rw [mul_pow, mul_pow, Real.sq_sqrt hKp.le]; ring
      _ = 25 / 4 * K⁻¹ * μ ^ 2 := by simp only [β]; field_simp; ring
  have hμ2 : μ ^ 2 ≤ 3 * ∑ l, ‖dftL k (m l)‖ ^ 2 := by
    simp only [μ, Fin.sum_univ_three]
    nlinarith [sq_nonneg (‖dftL k (m 0)‖ - ‖dftL k (m 1)‖),
      sq_nonneg (‖dftL k (m 0)‖ - ‖dftL k (m 2)‖), sq_nonneg (‖dftL k (m 1)‖ - ‖dftL k (m 2)‖)]
  have hg := gridWeight_add_le r 1 k
  have hgb := gbr_le_of_ne_zero hk
  rw [pow_one] at hg
  calc gridWeight (r + 1) k * ‖dftL k (halfLvec i j m)‖ ^ 2
      ≤ (c * 4 ^ r * gbr k * gridWeight r k) * (25 / 4 * K⁻¹ * (3 * ∑ l, ‖dftL k (m l)‖ ^ 2)) := by
        refine mul_le_mul hg (hsq.trans ?_) (sq_nonneg _) (by
          have := le_trans zero_le_one (one_le_gbr k); positivity)
        gcongr
    _ ≤ (c * 4 ^ r * (17 / 16 * K) * gridWeight r k) *
          (25 / 4 * K⁻¹ * (3 * ∑ l, ‖dftL k (m l)‖ ^ 2)) := by gcongr
    _ = _ := by field_simp; ring

/-- The norm of `P^r = H^{r+2}(Sym₃) × H^{r+1}(Sym₃)` (squared, coordinatewise). -/
noncomputable def sobP (r : ℕ) (x : Dom N) : ℝ :=
  ∑ a, sobSq (r + 2) (x.1 a) + ∑ a, sobSq (r + 1) (x.2 a)

/-- The norm of `𝒴^r = H^r(ℝ ⊕ ℝ³)` (squared, coordinatewise). -/
noncomputable def sobY (r : ℕ) (y : Tgt N) : ℝ := sobSq r y.1 + ∑ i, sobSq r (y.2 i)

/-- **Uniform bound on the range inverse** (`lem:supp-initial-range`): there is `C_r`,
independent of the cutoff, with `‖R_h y‖²_{𝒫^r} ≤ C_r ‖y‖²_{𝒴^r}`. -/
theorem Rh_bound (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (y : Tgt N), sobP r (Rh y) ≤ C * sobY r y := by
  set Cs := ((multiIndices (r + 2)).card : ℝ) * 4 ^ r * (17 / 16) ^ 2 / 4
  set Cv := ((multiIndices (r + 1)).card : ℝ) * 4 ^ r * (17 / 16) * (75 / 4)
  have hCs : 0 ≤ Cs := by positivity
  have hCv : 0 ≤ Cv := by positivity
  refine ⟨3 * Cs + 6 * Cv, by positivity, fun N _ y => ?_⟩
  obtain ⟨f, m⟩ := y
  have hscal : sobSq (r + 2) (scalarInv f) ≤ Cs * sobSq r f := by
    rw [sobSq_eq_weight, sobSq_eq_weight, mul_sum]
    refine sum_le_sum fun k _ => ?_
    have h := scalar_mode_bound r k
    rw [show dft (scalarInv f) k = dftL k (scalarInv f) from rfl, dftL_scalarInv, norm_mul,
      mul_pow, ← mul_assoc]
    have := sq_nonneg ‖dftL k f‖
    calc gridWeight (r + 2) k * ‖((2 * kapSq k : ℝ) : ℂ)⁻¹‖ ^ 2 * ‖dftL k f‖ ^ 2
        ≤ Cs * gridWeight r k * ‖dftL k f‖ ^ 2 := mul_le_mul_of_nonneg_right h this
      _ = Cs * (gridWeight r k * ‖dft f k‖ ^ 2) := by rw [dftL_apply]; ring
  have hvec : ∀ i j, sobSq (r + 1) (halfLvec i j m) ≤ Cv * ∑ l, sobSq r (m l) := by
    intro i j
    rw [sobSq_eq_weight]
    simp only [sobSq_eq_weight, mul_sum]
    rw [sum_comm]
    refine sum_le_sum fun k _ => ?_
    have h := vector_mode_bound r i j m k
    refine h.trans (le_of_eq ?_)
    simp only [mul_sum, dftL_apply]
    refine sum_congr rfl fun l _ => ?_
    ring
  have hsP : sobP r (Rh (f, m)) =
      ∑ a : Fin 6, sobSq (r + 2) ((if (a : ℕ) < 3 then scalarInv else 0) f) +
        ∑ a : Fin 6, sobSq (r + 1) (halfLvec (idx6 a).1 (idx6 a).2 m) := rfl
  rw [hsP]
  have h1 : ∑ a : Fin 6, sobSq (r + 2) ((if (a : ℕ) < 3 then scalarInv else 0) f) ≤
      3 * (Cs * sobSq r f) := by
    have h0 : sobSq (r + 2) ((0 : Module.End ℂ (Grid N → ℂ)) f) = 0 := by
      simp [sobSq, gridNormSq, Dα]
    have hval : ∀ a : Fin 6, sobSq (r + 2) ((if (a : ℕ) < 3 then scalarInv else 0) f) ≤
        (if (a : ℕ) < 3 then 1 else 0) * (Cs * sobSq r f) := by
      intro a
      split_ifs with h
      · rw [one_mul]; exact hscal
      · rw [zero_mul, h0]
    refine (sum_le_sum fun a _ => hval a).trans (le_of_eq ?_)
    rw [← sum_mul]
    congr 1
    simp [Fin.sum_univ_six]
    exact_mod_cast (by decide : (Finset.univ.filter (fun x : Fin 6 => (x : ℕ) < 3)).card = 3)
  have h2 : ∑ a : Fin 6, sobSq (r + 1) (halfLvec (idx6 a).1 (idx6 a).2 m) ≤
      6 * (Cv * ∑ l, sobSq r (m l)) := by
    calc ∑ a : Fin 6, sobSq (r + 1) (halfLvec (idx6 a).1 (idx6 a).2 m)
        ≤ ∑ _a : Fin 6, Cv * ∑ l, sobSq r (m l) := sum_le_sum fun a _ => hvec _ _
      _ = 6 * (Cv * ∑ l, sobSq r (m l)) := by simp
  have hf0 := sobSq_nonneg r f
  have hm0 : 0 ≤ ∑ l, sobSq r (m l) := sum_nonneg fun l _ => sobSq_nonneg r _
  simp only [sobY]
  nlinarith

end RenewalGeometry.InitialConstraintLinearRange
