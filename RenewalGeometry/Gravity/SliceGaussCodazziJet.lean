/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.HarmonicGaugeCovectorJet

/-!
# Gauss–Codazzi and the harmonic initial slice at jet level
  (`lem:supp-open-initial-gauge`, `eq:supp-open-harmonic-initial`, `eq:main-open-data-class`;
  emergent-spacetime manuscript)

A **unit-lapse, zero-shift slice jet** (`SliceData`) consists of the spatial metric 2-jet
`(γ, γ⁻¹, ∂γ, ∂∂γ)`, the extrinsic curvature `K` with its spatial jet `∂K`, the free time
derivatives of lapse and shift `v₀₀ = ∂_t g₀₀`, `v₀ᵢ = ∂_t g₀ᵢ` with their spatial jets, and an
arbitrary symmetric acceleration `w = ∂_t² g`.  `SliceData.jet` is the space-time metric 3-jet
with `g₀₀ = -1`, `g₀ᵢ = 0`, `gᵢⱼ = γᵢⱼ`, `∂_t gᵢⱼ = -2Kᵢⱼ` (third jet zero; only 2-jet quantities
are used here); `SliceData.spatial` is the spatial 3-jet.

* `gauss` — the **Gauss equation** `R⁽⁴⁾_{likj} = R⁽³⁾_{likj} + K_{kl}K_{ji} - K_{jl}K_{ki}` on
  spatial indices; `codazzi` — the mixed components `R⁽⁴⁾_{k0ji}` in terms of `∂K` and `Γ⁽³⁾`;
* `einM_zero_zero` — **Hamiltonian constraint**: `G₀₀ = ½(R(γ) + (tr_γ K)² - |K|²_γ)`;
* `einM_zero_succ` — **momentum constraint**: `G₀ᵢ = -(∇_γ^j K_{ji} - ∂ᵢ tr_γ K)`;
  in particular `G_{0b}` of the slice jet does not involve the acceleration `w`;
* `gcUp_zero`, `gcUp_succ` — the gauge covector at the slice:
  `c⁰ = ½(v₀₀ + γ^{ij}v_{ij})`, `cⁱ = -γ^{ij}v_{0j} + γ^{jk}Γ⁽³⁾ⁱ_{jk}` (with `v_{ij} = -2K_{ij}`);
* `gc_harmonicInit` — for the harmonic initialization `eq:supp-open-harmonic-initial`
  (`v₀₀ = 2 tr_γ K`, `v₀ᵢ = γ^{jk}(∂_jγ_{ki} - ½∂ᵢγ_{jk})`) the gauge covector vanishes exactly;
* `hM_zero_eq` — on the slice the coefficient of `∂_t c_b` in `𝓗_{0b}` is `½`: for every covector
  1-jet, `𝓗_{0b} = ½ ∂_t c_b + (tangential derivatives of c) + (Γ c)` explicitly.
-/

open Finset Matrix
open scoped BigOperators

namespace RenewalGeometry.ContractedBianchiJet

noncomputable section

set_option linter.unusedSectionVars false

/-- The `4 × 4` matrix with blocks `a` (time-time), `b` (time-space) and `C` (space-space). -/
def sliceMat (a : ℝ) (b : Fin 3 → ℝ) (C : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => Fin.cases (Fin.cases a b ν) (fun i => Fin.cases (b i) (fun j => C i j) ν) μ

@[simp] theorem sliceMat_zero_zero (a : ℝ) (b : Fin 3 → ℝ) (C : Matrix (Fin 3) (Fin 3) ℝ) :
    sliceMat a b C 0 0 = a := rfl

@[simp] theorem sliceMat_zero_succ (a : ℝ) (b : Fin 3 → ℝ) (C : Matrix (Fin 3) (Fin 3) ℝ)
    (j : Fin 3) : sliceMat a b C 0 j.succ = b j := rfl

@[simp] theorem sliceMat_succ_zero (a : ℝ) (b : Fin 3 → ℝ) (C : Matrix (Fin 3) (Fin 3) ℝ)
    (i : Fin 3) : sliceMat a b C i.succ 0 = b i := rfl

@[simp] theorem sliceMat_succ_succ (a : ℝ) (b : Fin 3 → ℝ) (C : Matrix (Fin 3) (Fin 3) ℝ)
    (i j : Fin 3) : sliceMat a b C i.succ j.succ = C i j := rfl

theorem sliceMat_transpose (a : ℝ) (b : Fin 3 → ℝ) (C : Matrix (Fin 3) (Fin 3) ℝ) :
    (sliceMat a b C)ᵀ = sliceMat a b Cᵀ := by
  ext μ ν
  refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;> simp

/-- Data of a unit-lapse, zero-shift slice jet. -/
structure SliceData where
  γ : Matrix (Fin 3) (Fin 3) ℝ
  γi : Matrix (Fin 3) (Fin 3) ℝ
  dγ : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ
  ddγ : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) ℝ
  K : Matrix (Fin 3) (Fin 3) ℝ
  dK : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ
  v00 : ℝ
  v0 : Fin 3 → ℝ
  dv00 : Fin 3 → ℝ
  dv0 : Fin 3 → Fin 3 → ℝ
  w : Matrix (Fin 4) (Fin 4) ℝ

/-- Validity of slice data: `γ γ⁻¹ = 1`, symmetric matrices, commuting spatial derivatives. -/
structure SliceData.Valid (S : SliceData) : Prop where
  γγi : S.γ * S.γi = 1
  γ_symm : S.γᵀ = S.γ
  γi_symm : S.γiᵀ = S.γi
  dγ_symm : ∀ k, (S.dγ k)ᵀ = S.dγ k
  ddγ_symm : ∀ k l, (S.ddγ k l)ᵀ = S.ddγ k l
  ddγ_comm : ∀ k l, S.ddγ k l = S.ddγ l k
  K_symm : S.Kᵀ = S.K
  dK_symm : ∀ k, (S.dK k)ᵀ = S.dK k
  w_symm : S.wᵀ = S.w

namespace SliceData

variable (S : SliceData)

/-- The spatial metric 3-jet `(γ, γ⁻¹, ∂γ, ∂∂γ, 0)`. -/
def spatial : Jet3 (Fin 3) := ⟨S.γ, S.γi, S.dγ, S.ddγ, fun _ _ _ => 0⟩

/-- The time-space block of the mixed second jet `∂_k ∂_t g`. -/
def dtk (k : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ := sliceMat (S.dv00 k) (S.dv0 k) ((-2 : ℝ) • S.dK k)

/-- The space-time metric 3-jet of the slice (unit lapse, zero shift, `∂_t γ = -2K`). -/
def jet : Jet3 (Fin 4) where
  g := sliceMat (-1) 0 S.γ
  G := sliceMat (-1) 0 S.γi
  dg := fun a => Fin.cases (sliceMat S.v00 S.v0 ((-2 : ℝ) • S.K)) (fun k => sliceMat 0 0 (S.dγ k)) a
  ddg := fun a b => Fin.cases (Fin.cases S.w (fun l => S.dtk l) b)
    (fun k => Fin.cases (S.dtk k) (fun l => sliceMat 0 0 (S.ddγ k l)) b) a
  dddg := fun _ _ _ => 0

@[simp] theorem jet_g : S.jet.g = sliceMat (-1) 0 S.γ := rfl
@[simp] theorem jet_G : S.jet.G = sliceMat (-1) 0 S.γi := rfl
@[simp] theorem jet_dg_zero : S.jet.dg 0 = sliceMat S.v00 S.v0 ((-2 : ℝ) • S.K) := rfl
@[simp] theorem jet_dg_succ (k : Fin 3) : S.jet.dg k.succ = sliceMat 0 0 (S.dγ k) := rfl
@[simp] theorem jet_ddg_zero_zero : S.jet.ddg 0 0 = S.w := rfl
@[simp] theorem jet_ddg_zero_succ (l : Fin 3) : S.jet.ddg 0 l.succ = S.dtk l := rfl
@[simp] theorem jet_ddg_succ_zero (k : Fin 3) : S.jet.ddg k.succ 0 = S.dtk k := rfl
@[simp] theorem jet_ddg_succ_succ (k l : Fin 3) :
    S.jet.ddg k.succ l.succ = sliceMat 0 0 (S.ddγ k l) := rfl

theorem mat_apply_symm {m : Type*} {A : Matrix m m ℝ} (h : Aᵀ = A) (i j : m) : A i j = A j i := by
  conv_lhs => rw [← h]
  rfl

theorem Valid.spatial {S : SliceData} (hS : S.Valid) : S.spatial.Valid where
  gG := hS.γγi
  g_symm := hS.γ_symm
  G_symm := hS.γi_symm
  dg_symm := hS.dγ_symm
  ddg_symm := hS.ddγ_symm
  ddg_comm := hS.ddγ_comm
  dddg_symm := fun _ _ _ => by ext; rfl
  dddg_comm1 := fun _ _ _ => rfl
  dddg_comm2 := fun _ _ _ => rfl

theorem sliceMat_mul (a a' : ℝ) (C C' : Matrix (Fin 3) (Fin 3) ℝ) :
    sliceMat a 0 C * sliceMat a' 0 C' = sliceMat (a * a') 0 (C * C') := by
  ext μ ν
  refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem Valid.jet {S : SliceData} (hS : S.Valid) : S.jet.Valid where
  gG := by
    rw [jet_g, jet_G, sliceMat_mul, hS.γγi]
    have h0 : ∀ j : Fin 3, (0 : Fin 4) ≠ j.succ := fun j => (Fin.succ_ne_zero j).symm
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
      simp [Matrix.one_apply, Fin.succ_ne_zero, Fin.succ_inj, h0]
  g_symm := by rw [jet_g, sliceMat_transpose, hS.γ_symm]
  G_symm := by rw [jet_G, sliceMat_transpose, hS.γi_symm]
  dg_symm := fun a => by
    refine Fin.cases ?_ (fun k => ?_) a
    · rw [jet_dg_zero, sliceMat_transpose, Matrix.transpose_smul, hS.K_symm]
    · rw [jet_dg_succ, sliceMat_transpose, hS.dγ_symm]
  ddg_symm := fun a b => by
    refine Fin.cases ?_ (fun k => ?_) a <;> refine Fin.cases ?_ (fun l => ?_) b
    · rw [jet_ddg_zero_zero, hS.w_symm]
    · rw [jet_ddg_zero_succ, dtk, sliceMat_transpose, Matrix.transpose_smul, hS.dK_symm]
    · rw [jet_ddg_succ_zero, dtk, sliceMat_transpose, Matrix.transpose_smul, hS.dK_symm]
    · rw [jet_ddg_succ_succ, sliceMat_transpose, hS.ddγ_symm]
  ddg_comm := fun a b => by
    refine Fin.cases ?_ (fun k => ?_) a <;> refine Fin.cases ?_ (fun l => ?_) b
    · rfl
    · rfl
    · rfl
    · rw [jet_ddg_succ_succ, jet_ddg_succ_succ, hS.ddγ_comm]
  dddg_symm := fun _ _ _ => by ext; rfl
  dddg_comm1 := fun _ _ _ => rfl
  dddg_comm2 := fun _ _ _ => rfl

/-! ### Entry tables of the lowered Christoffel jets on the slice -/

variable {S}

theorem low_succ_succ_succ (k l i : Fin 3) :
    S.jet.low k.succ l.succ i.succ = S.spatial.low k l i := by
  simp [Jet3.low, spatial]

theorem low_succ_zero_succ (k l : Fin 3) : S.jet.low k.succ 0 l.succ = S.K k l := by
  simp [Jet3.low]

theorem low_succ_succ_zero (m i : Fin 3) : S.jet.low i.succ m.succ 0 = -S.K m i := by
  simp [Jet3.low]

theorem low_succ_zero_zero (i : Fin 3) : S.jet.low i.succ 0 0 = 0 := by
  simp [Jet3.low]

theorem dlow_succ_succ_succ_succ (k j l i : Fin 3) :
    S.jet.dlow k.succ j.succ l.succ i.succ = S.spatial.dlow k j l i := by
  simp [Jet3.dlow, spatial]

theorem dlow_succ_succ_succ_zero (j i k : Fin 3) :
    S.jet.dlow j.succ i.succ k.succ 0 = -S.dK j k i := by
  simp [Jet3.dlow, dtk]

/-- `G`-contraction on the slice: `Σ_{ρσ} G^{ρσ} f ρ σ = -f 0 0 + Σ_{ij} γ^{ij} f i j`. -/
theorem sum_G (f : Fin 4 → Fin 4 → ℝ) :
    ∑ ρ, ∑ σ, S.jet.G ρ σ * f ρ σ = -f 0 0 + ∑ i, ∑ j, S.γi i j * f i.succ j.succ := by
  simp only [Fin.sum_univ_succ (n := 3), jet_G, sliceMat_zero_zero, sliceMat_zero_succ,
    sliceMat_succ_zero, sliceMat_succ_succ, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, neg_one_mul]

end SliceData


/-! ### Lowered curvature on the slice: Gauss and Codazzi -/

namespace Jet3

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem lowT_chr_apply (J : Jet3 n) (a b κ σ : n) :
    ((J.low a)ᵀ * J.chr b) κ σ = ∑ ρ, ∑ l, J.G ρ l * (J.low a ρ κ * J.low b l σ) := by
  simp only [chr, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem lowRiem_apply (J : Jet3 n) (a b κ σ : n) :
    J.lowRiem a b κ σ = J.dlow a b κ σ - J.dlow b a κ σ
      - ∑ ρ, ∑ l, J.G ρ l * (J.low a ρ κ * J.low b l σ)
      + ∑ ρ, ∑ l, J.G ρ l * (J.low b ρ κ * J.low a l σ) := by
  simp only [lowRiem, Matrix.add_apply, Matrix.sub_apply, lowT_chr_apply]

/-- `Ric_{sb} = G^{lκ} R_{κ s l b}` (lowered Riemann). -/
theorem ricM_eq_lowRiem {J : Jet3 n} (hv : J.Valid) (s b : n) :
    J.ricM s b = ∑ l, ∑ κ, J.G l κ * J.lowRiem l b κ s := by
  simp only [ricM, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : J.riem l b = J.G * J.lowRiem l b := by
    rw [← metric_mul_riem hv, ← Matrix.mul_assoc, hv.Gg, Matrix.one_mul]
  rw [this, Matrix.mul_apply]

theorem lowRiem_self (J : Jet3 n) (a : n) : J.lowRiem a a = 0 := by
  unfold lowRiem; abel

theorem lowRiem_apply_antisymm {J : Jet3 n} (hv : J.Valid) (a b κ σ : n) :
    J.lowRiem a b κ σ = -J.lowRiem a b σ κ := by
  have h := congrFun (congrFun (lowRiem_antisymm hv a b) σ) κ
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  linarith

theorem lowRiem_swap (J : Jet3 n) (a b : n) : J.lowRiem a b = -J.lowRiem b a := by
  unfold lowRiem; abel

theorem scal_eq_sum (J : Jet3 n) : J.scal = ∑ s, ∑ b, J.G s b * J.ricM s b := by
  rw [scal, sum_sum_mul_eq_trace]

end Jet3

namespace SliceData

variable {S : SliceData}

/-- **The Gauss equation** on the slice:
`R⁽⁴⁾_{l i k j} = R⁽³⁾_{l i k j} + K_{kl}K_{ji} - K_{jl}K_{ki}`. -/
theorem gauss (k j l i : Fin 3) :
    S.jet.lowRiem k.succ j.succ l.succ i.succ =
      S.spatial.lowRiem k j l i + S.K k l * S.K j i - S.K j l * S.K k i := by
  rw [Jet3.lowRiem_apply, Jet3.lowRiem_apply, sum_G, sum_G]
  simp only [dlow_succ_succ_succ_succ, low_succ_zero_succ, low_succ_succ_succ]
  simp only [spatial]
  ring

/-- **The Codazzi relation** on the slice:
`R⁽⁴⁾_{k 0 j i} = -∂_jK_{ki} + ∂_iK_{kj} + γ^{ab}Γ_{a,jk}K_{bi} - γ^{ab}Γ_{a,ik}K_{bj}`. -/
theorem codazzi (j i k : Fin 3) :
    S.jet.lowRiem j.succ i.succ k.succ 0 =
      -S.dK j k i + S.dK i k j + ∑ a, ∑ b, S.γi a b * (S.spatial.low j a k * S.K b i)
        - ∑ a, ∑ b, S.γi a b * (S.spatial.low i a k * S.K b j) := by
  rw [Jet3.lowRiem_apply, sum_G, sum_G]
  simp only [dlow_succ_succ_succ_zero, low_succ_zero_succ, low_succ_succ_succ, low_succ_succ_zero,
    low_succ_zero_zero]
  simp only [mul_neg, mul_zero, neg_zero, zero_add]
  simp only [Finset.sum_neg_distrib]
  ring

theorem ricM_zero_zero (hS : S.Valid) :
    S.jet.ricM 0 0 = ∑ i, ∑ j, S.γi i j * S.jet.lowRiem i.succ 0 j.succ 0 := by
  rw [Jet3.ricM_eq_lowRiem hS.jet, sum_G (fun l κ => S.jet.lowRiem l 0 κ 0), Jet3.lowRiem_self]
  simp

theorem ricM_succ_succ (hS : S.Valid) (i j : Fin 3) :
    S.jet.ricM i.succ j.succ = -S.jet.lowRiem 0 j.succ 0 i.succ +
      ∑ k, ∑ l, S.γi k l * S.jet.lowRiem k.succ j.succ l.succ i.succ := by
  rw [Jet3.ricM_eq_lowRiem hS.jet, sum_G (fun l κ => S.jet.lowRiem l j.succ κ i.succ)]

theorem ricM_zero_succ (hS : S.Valid) (i : Fin 3) :
    S.jet.ricM 0 i.succ = ∑ j, ∑ k, S.γi j k * S.jet.lowRiem j.succ i.succ k.succ 0 := by
  rw [Jet3.ricM_eq_lowRiem hS.jet, sum_G (fun l κ => S.jet.lowRiem l i.succ κ 0)]
  have : S.jet.lowRiem 0 i.succ 0 0 = 0 := by
    have := Jet3.lowRiem_apply_antisymm hS.jet 0 i.succ 0 0
    linarith
  rw [this, neg_zero, zero_add]

theorem scal_slice :
    S.jet.scal = -S.jet.ricM 0 0 + ∑ i, ∑ j, S.γi i j * S.jet.ricM i.succ j.succ := by
  rw [Jet3.scal_eq_sum, sum_G (fun s b => S.jet.ricM s b)]

/-- The trace `tr_γ K = γ^{ij}K_{ij}`. -/
def trK (S : SliceData) : ℝ := ∑ i, ∑ j, S.γi i j * S.K i j

/-- `|K|²_γ = γ^{ik}γ^{jl}K_{ij}K_{kl}`. -/
def normK2 (S : SliceData) : ℝ := ∑ i, ∑ j, ∑ k, ∑ l, S.γi i k * S.γi j l * S.K i j * S.K k l

/-- The Hamiltonian constraint expression `R(γ) + (tr_γ K)² - |K|²_γ`. -/
def hamC (S : SliceData) : ℝ := S.spatial.scal + S.trK ^ 2 - S.normK2

/-- **Hamiltonian constraint at jet level**: on a unit-lapse zero-shift slice jet,
`G₀₀ = ½(R(γ) + (tr_γ K)² - |K|²_γ)`, independently of the acceleration and of the time
derivatives of lapse and shift. -/
theorem einM_zero_zero (hS : S.Valid) : S.jet.einM 0 0 = (1 / 2 : ℝ) * S.hamC := by
  have hγi : ∀ i j, S.γi i j = S.γi j i := mat_apply_symm hS.γi_symm
  have hK : ∀ i j, S.K i j = S.K j i := mat_apply_symm hS.K_symm
  set A := ∑ i, ∑ j, S.γi i j * S.jet.lowRiem i.succ 0 j.succ 0 with hAdef
  set B := ∑ i, ∑ j, S.γi i j * ∑ k, ∑ l, S.γi k l * S.jet.lowRiem k.succ j.succ l.succ i.succ
    with hBdef
  -- the acceleration terms cancel
  have hA : ∑ i, ∑ j, S.γi i j * S.jet.lowRiem 0 j.succ 0 i.succ = A := by
    rw [hAdef, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hγi j i, Jet3.lowRiem_swap, Matrix.neg_apply,
      Jet3.lowRiem_apply_antisymm hS.jet j.succ 0 0 i.succ]
    ring
  have hE : S.jet.einM 0 0 = S.jet.ricM 0 0 + (1 / 2 : ℝ) * S.jet.scal := by
    simp only [Jet3.einM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, jet_g,
      sliceMat_zero_zero]
    ring
  have hsum : ∑ i, ∑ j, S.γi i j * S.jet.ricM i.succ j.succ = -A + B := by
    simp only [ricM_succ_succ hS, mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [hA]
  -- the spatial part, by the Gauss equation
  have t0 : ∑ i, ∑ j, ∑ k, ∑ l, S.γi i j * (S.γi k l * S.spatial.lowRiem k j l i) =
      S.spatial.scal := by
    rw [Jet3.scal_eq_sum]
    simp only [Jet3.ricM_eq_lowRiem hS.spatial, Finset.mul_sum]
    rfl
  have t1 : ∑ i, ∑ j, ∑ k, ∑ l, S.γi i j * (S.γi k l * (S.K k l * S.K j i)) = S.trK ^ 2 := by
    rw [trK, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hK j i]; ring
  have t2 : ∑ i, ∑ j, ∑ k, ∑ l, S.γi i j * (S.γi k l * (S.K j l * S.K k i)) = S.normK2 := by
    rw [normK2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    rw [hK k i]; ring
  have hB : B = S.hamC := by
    have e : ∀ i j k l, S.γi i j * (S.γi k l * S.jet.lowRiem k.succ j.succ l.succ i.succ) =
        S.γi i j * (S.γi k l * S.spatial.lowRiem k j l i) +
          S.γi i j * (S.γi k l * (S.K k l * S.K j i)) -
          S.γi i j * (S.γi k l * (S.K j l * S.K k i)) := by
      intro i j k l; rw [gauss]; ring
    rw [hBdef]
    simp only [Finset.mul_sum, e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [t0, t1, t2, hamC]
  rw [hE, scal_slice, hsum, ricM_zero_zero hS, ← hAdef, hB]
  ring


/-- `∂ᵢ tr_γ K = ∂ᵢγ^{jk} K_{jk} + γ^{jk} ∂ᵢK_{jk}`. -/
def dtrK (S : SliceData) (i : Fin 3) : ℝ :=
  ∑ j, ∑ k, (S.spatial.dG i j k * S.K j k + S.γi j k * S.dK i j k)

/-- `∇_γ^j K_{ji} = γ^{jk}(∂_k K_{ji} - Γ^n_{kj}K_{ni} - Γ^n_{ki}K_{jn})`. -/
def divK (S : SliceData) (i : Fin 3) : ℝ :=
  ∑ j, ∑ k, S.γi j k * (S.dK k j i - ∑ m, S.spatial.chr k m j * S.K m i -
    ∑ m, S.spatial.chr k m i * S.K j m)

/-- The momentum constraint expression `∇_γ^j K_{ji} - ∂ᵢ tr_γ K`. -/
def momC (S : SliceData) (i : Fin 3) : ℝ := S.divK i - S.dtrK i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem codazzi_contract (hS : S.Valid) (i : Fin 3) :
    ∑ j, ∑ k, S.γi j k * (-S.dK j k i + S.dK i k j +
      ∑ a, ∑ b, S.γi a b * (S.spatial.low j a k * S.K b i) -
      ∑ a, ∑ b, S.γi a b * (S.spatial.low i a k * S.K b j)) = -S.momC i := by
  have hγi : ∀ a b, S.γi a b = S.γi b a := mat_apply_symm hS.γi_symm
  have hK : ∀ a b, S.K a b = S.K b a := mat_apply_symm hS.K_symm
  have hdK : ∀ c a b, S.dK c a b = S.dK c b a := fun c => mat_apply_symm (hS.dK_symm c)
  have hdγ : ∀ c a b, S.dγ c a b = S.dγ c b a := fun c => mat_apply_symm (hS.dγ_symm c)
  have g10 := hγi 1 0
  have g20 := hγi 2 0
  have g21 := hγi 2 1
  have k10 := hK 1 0
  have k20 := hK 2 0
  have k21 := hK 2 1
  have dk10 := fun c => hdK c 1 0
  have dk20 := fun c => hdK c 2 0
  have dk21 := fun c => hdK c 2 1
  have dg10 := fun c => hdγ c 1 0
  have dg20 := fun c => hdγ c 2 0
  have dg21 := fun c => hdγ c 2 1
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  all_goals
  simp only [momC, divK, dtrK, spatial, Jet3.chr, Jet3.low, Jet3.dG, Matrix.mul_apply,
    Matrix.neg_apply, Matrix.of_apply, Fin.sum_univ_three]
  all_goals
  simp only [g10, g20, g21, k10, k20, k21, dk10, dk20, dk21, dg10, dg20, dg21]
  all_goals ring

/-- **Momentum constraint at jet level**: on a unit-lapse zero-shift slice jet,
`G₀ᵢ = -(∇_γ^j K_{ji} - ∂ᵢ tr_γ K)`, independently of the acceleration and of the time
derivatives of lapse and shift. -/
theorem einM_zero_succ (hS : S.Valid) (i : Fin 3) : S.jet.einM 0 i.succ = -S.momC i := by
  have hE : S.jet.einM 0 i.succ = S.jet.ricM 0 i.succ := by
    simp only [Jet3.einM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, jet_g,
      sliceMat_zero_succ, Pi.zero_apply, mul_zero, sub_zero]
  rw [hE, ricM_zero_succ hS, ← codazzi_contract hS i]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [codazzi]


/-! ### The gauge covector and the harmonic-defect tensor on the slice -/

theorem chr_zero_zero_zero : S.jet.chr 0 0 0 = -(1 / 2 : ℝ) * S.v00 := by
  simp only [Jet3.chr, Matrix.mul_apply, Fin.sum_univ_succ (n := 3), jet_G, sliceMat_zero_zero,
    sliceMat_zero_succ, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  simp [Jet3.low]

theorem chr_succ_zero_succ (i j : Fin 3) : S.jet.chr i.succ 0 j.succ = -S.K i j := by
  simp only [Jet3.chr, Matrix.mul_apply, Fin.sum_univ_succ (n := 3), jet_G, sliceMat_zero_zero,
    sliceMat_zero_succ, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    low_succ_zero_succ]
  ring

theorem low_zero_succ_zero (l : Fin 3) : S.jet.low 0 l.succ 0 = S.v0 l := by
  simp [Jet3.low]; ring

theorem chr_zero_succ_zero (k : Fin 3) :
    S.jet.chr 0 k.succ 0 = ∑ l, S.γi k l * S.v0 l := by
  simp only [Jet3.chr, Matrix.mul_apply, Fin.sum_univ_succ (n := 3), jet_G, sliceMat_succ_zero,
    sliceMat_succ_succ, Pi.zero_apply, zero_mul, zero_add, low_zero_succ_zero]

theorem chr_succ_succ_succ (i k j : Fin 3) :
    S.jet.chr i.succ k.succ j.succ = S.spatial.chr i k j := by
  simp only [Jet3.chr, Matrix.mul_apply, Fin.sum_univ_succ (n := 3), jet_G, sliceMat_succ_zero,
    sliceMat_succ_succ, Pi.zero_apply, zero_mul, zero_add, low_succ_succ_succ]
  rfl

/-- `c⁰ = ½(v₀₀ + γ^{ij}v_{ij}) = ½ v₀₀ - tr_γ K` on the slice. -/
theorem gcUp_zero : S.jet.gcUp 0 = (1 / 2 : ℝ) * S.v00 - S.trK := by
  rw [Jet3.gcUp, sum_G (fun a b => S.jet.chr a 0 b), chr_zero_zero_zero]
  simp only [chr_succ_zero_succ, trK, mul_neg, Finset.sum_neg_distrib]
  ring

/-- `cⁱ = -γ^{ij}v_{0j} + γ^{jk}Γ⁽³⁾ⁱ_{jk}` on the slice. -/
theorem gcUp_succ (k : Fin 3) :
    S.jet.gcUp k.succ = -∑ l, S.γi k l * S.v0 l + ∑ i, ∑ j, S.γi i j * S.spatial.chr i k j := by
  rw [Jet3.gcUp, sum_G (fun a b => S.jet.chr a k.succ b), chr_zero_succ_zero]
  simp only [chr_succ_succ_succ]

/-- The harmonic initialization `eq:supp-open-harmonic-initial`:
`v₀₀ = 2 tr_γ K`, `v₀ᵢ = γ^{jk}(∂_jγ_{ki} - ½∂ᵢγ_{jk})`. -/
def HarmonicInit (S : SliceData) : Prop :=
  S.v00 = 2 * S.trK ∧ ∀ l, S.v0 l = ∑ j, ∑ k, S.γi j k * (S.dγ j k l - (1 / 2 : ℝ) * S.dγ l j k)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **The harmonic initialization makes the gauge covector vanish exactly** (`c^μ = 0`). -/
theorem gcUp_harmonicInit (hS : S.Valid) (hH : S.HarmonicInit) (μ : Fin 4) : S.jet.gcUp μ = 0 := by
  have hγi : ∀ a b, S.γi a b = S.γi b a := mat_apply_symm hS.γi_symm
  have hdγ : ∀ c a b, S.dγ c a b = S.dγ c b a := fun c => mat_apply_symm (hS.dγ_symm c)
  have g10 := hγi 1 0
  have g20 := hγi 2 0
  have g21 := hγi 2 1
  have dg10 := fun c => hdγ c 1 0
  have dg20 := fun c => hdγ c 2 0
  have dg21 := fun c => hdγ c 2 1
  refine Fin.cases ?_ (fun k => ?_) μ
  · rw [gcUp_zero, hH.1]; ring
  · rw [gcUp_succ]
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    all_goals
    simp only [hH.2, spatial, Jet3.chr, Jet3.low, Matrix.mul_apply, Matrix.of_apply,
      Fin.sum_univ_three]
    all_goals simp only [g10, g20, g21, dg10, dg20, dg21]
    all_goals ring

/-- The lowered gauge covector `c_b = g_{bμ}c^μ` vanishes for the harmonic initialization. -/
theorem gc_harmonicInit (hS : S.Valid) (hH : S.HarmonicInit) (b : Fin 4) : S.jet.gc b = 0 := by
  simp [Jet3.gc, gcUp_harmonicInit hS hH]

/-- **Coefficient `½` of `∂_t c₀` in `𝓗₀₀`** on the slice, for every covector 1-jet `(c, ∂c)`:
`𝓗₀₀ = ½ ∂_t c₀ + ½ γ^{ij}∂ᵢc_j - ½(Γ^l_{00}c_l + γ^{ij}Γ^l_{ij}c_l)`. -/
theorem hM_zero_zero (c : Fin 4 → ℝ) (dc : Matrix (Fin 4) (Fin 4) ℝ) :
    S.jet.hM c dc 0 0 = (1 / 2 : ℝ) * dc 0 0 + (1 / 2 : ℝ) * ∑ i, ∑ j, S.γi i j * dc i.succ j.succ
      - (1 / 2 : ℝ) * (∑ l, S.jet.chr 0 l 0 * c l +
        ∑ i, ∑ j, S.γi i j * ∑ l, S.jet.chr i.succ l j.succ * c l) := by
  simp only [Jet3.hM, Jet3.trN, ← Jet3.sum_sum_mul_eq_trace, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul, jet_g, sliceMat_zero_zero]
  rw [sum_G (fun s a => S.jet.nc c dc s a)]
  simp only [Jet3.nc, Jet3.chrC, Matrix.sub_apply, Matrix.of_apply, mul_sub,
    Finset.sum_sub_distrib]
  ring

/-- **Coefficient `½` of `∂_t c_k` in `𝓗₀ₖ`** on the slice, for every covector 1-jet:
`𝓗₀ₖ = ½ ∂_t c_k + ½ ∂_k c₀ - Γ^l_{0k}c_l`. -/
theorem hM_zero_succ (hS : S.Valid) (c : Fin 4 → ℝ) (dc : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 3) :
    S.jet.hM c dc 0 k.succ = (1 / 2 : ℝ) * dc 0 k.succ + (1 / 2 : ℝ) * dc k.succ 0
      - ∑ l, S.jet.chr 0 l k.succ * c l := by
  simp only [Jet3.hM, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul, jet_g, sliceMat_zero_succ, Pi.zero_apply, mul_zero,
    sub_zero, Jet3.nc, Jet3.chrC, Matrix.of_apply]
  have : ∑ l, S.jet.chr k.succ l 0 * c l = ∑ l, S.jet.chr 0 l k.succ * c l :=
    Finset.sum_congr rfl fun l _ => by rw [Jet3.chr_apply_comm hS.jet]
  rw [this]
  ring



/-! ### Non-vacuity: the flat slice -/

/-- The flat slice: `γ = 1`, `K = 0`, all jets zero (harmonic initialization holds). -/
def flatSlice : SliceData :=
  ⟨1, 1, fun _ => 0, fun _ _ => 0, 0, fun _ => 0, 0, fun _ => 0, fun _ => 0, fun _ _ => 0, 0⟩

theorem flatSlice_valid : flatSlice.Valid where
  γγi := by simp [flatSlice]
  γ_symm := by simp [flatSlice]
  γi_symm := by simp [flatSlice]
  dγ_symm := fun _ => by simp [flatSlice]
  ddγ_symm := fun _ _ => by simp [flatSlice]
  ddγ_comm := fun _ _ => rfl
  K_symm := by simp [flatSlice]
  dK_symm := fun _ => by simp [flatSlice]
  w_symm := by simp [flatSlice]

theorem flatSlice_harmonicInit : flatSlice.HarmonicInit := by
  refine ⟨?_, fun l => ?_⟩ <;> simp [flatSlice, trK]

example : flatSlice.jet.gc 0 = 0 := gc_harmonicInit flatSlice_valid flatSlice_harmonicInit 0
example : flatSlice.jet.einM 0 0 = (1 / 2 : ℝ) * flatSlice.hamC := einM_zero_zero flatSlice_valid

end SliceData

end

end RenewalGeometry.ContractedBianchiJet
