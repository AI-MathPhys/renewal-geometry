/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.HarmonicDefectForcingExact
import RenewalGeometry.Gravity.SpinorProlongationJet

/-!
# Rows of the gauge-defect-aware actual-jet equation (`prop:actual-jet-writer`)

Einstein–Standard-Model action-closure manuscript, `prop:actual-jet-writer`
(`eq:actual-jet-writer`, `eq:actual-jet-gauge-forcing`), on the foliated chart with adapted frame
`e_0 = N⁻¹(∂_t - βʲ∂_j)`, `e_a = e_aʲ∂_j` (`eq:actual-jet-adapted-frame`).  Everything is exact
algebra on jets at one point (the convention of `lem:harmonic-defect-forcing`); coordinates are
`Fin 4` with `0` the time coordinate and `j.succ` the spatial ones.

## The first-order wave reduction (metric rows)

For a field `u` with jets `(du, ddu)` and frame-derivative jets `de γ A μ = ∂_γ(e_A{}^μ)`, put
`p = e_0u`, `q_a = e_au` (`pJ`, `qJ`) and their coordinate jets (`dpJ`, `dqJ`, product rule).

* `head_row`, `spatial_of_q` — `∂_tu = Np + βʲ∂_ju` and `∂_ju = Σ_a (e⁻¹)_jᵃ q_a`: the head
  equation is algebraic in the state.
* **`p_row`** — `∂_tp - βʲ∂_jp - N e_aʲ∂_jq_a = N(-g^{αβ}∂_α∂_βu + L_p)` for an adapted frame
  (`g^{αβ} = -e_0^αe_0^β + Σ_a e_a^αe_a^β`), `L_p` linear in `∂u` with coefficients the frame jets.
* **`q_row`** — `∂_tq_a - βʲ∂_jq_a - N e_aʲ∂_jp = N L_{q,a}` (Schwarz symmetry), `L_q` likewise.
* **`metric_p_row`** — for `u = g_{μν}`, with `lem:harmonic-defect-forcing`
  (`HarmonicDefect.off_harmonic_metric_wave`), the metric `p`-row is
  `∂_tp - βʲ∂_jp - N e_aʲ∂_jq_a = N(L_p - 2𝓠 + 2κ(T - ½g trT) + 2Λg) + 2N𝓔^{tr} + 𝔊`,
  with the gauge forcing `𝔊 = -2N∇_{(μ}C_{ν)}`.
* **`gaugeForce_eq`** (`eq:actual-jet-gauge-forcing`) — `𝔊 = 𝒥_C C + 𝒥_C^0 ∂_tC + Σ_j 𝒥_C^j ∂_jC`
  with `∂C` the actual derivative jet of the harmonic defect, `𝒥_C^μ` depending only on `(N, g)`
  (`Jd`) and `𝒥_C` only on `(N, g, ∂g)` (`JC`); `gaugeForce_zero`: `C = 0`, `∂C = 0` ⇒ `𝔊 = 0`.
* `waveSym`, `waveSym_symm` — the principal matrices `A^j` of the `(p, q)` block are symmetric.

## The Dirac rows

* **`dirac_head_row`** — from `eq:normal-spinor-jet`: in coordinates,
  `∂_tΨ - βʲ∂_jΨ - N Σ_a e_aʲ c_0c_a ∂_jΨ = N(c_0Σ_a c_aω_a - ω_0 - c_0𝓜)Ψ - N c_0 r_D`.
* **`prolonged_row`** — the tangential prolonged rows: if `Σ_b ε_b c_b ∇²_{ba}Ψ = R_a`
  (`eq:spinor-prolongation`, right side `R_a`), then `∇²_{0a}Ψ = c_0Σ_i c_i∇²_{ia}Ψ - c_0R_a`:
  the same principal matrices `c_0c_i`, the residual entering only through `R_a`.
* `herm_c0ca`, `realify_symm` — `c_0c_a` is Hermitian (for `c_0` Hermitian, `c_a`
  anti-Hermitian, anticommuting), the realification of a Hermitian matrix is symmetric, and the
  transposed (dual-row) matrices are Hermitian (`herm_transpose`).
-/

namespace RenewalGeometry.ActualJetWriter

open Finset HarmonicDefect

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Adapted frame -/

/-- Lapse `N > 0`, shift `βʲ` and spatial frame `e_aʲ` of the adapted frame
`e_0 = N⁻¹(∂_t - βʲ∂_j)`, `e_a = e_aʲ∂_j` (`eq:actual-jet-adapted-frame`). -/
structure AdaptedFrame where
  N : ℝ
  β : Fin 3 → ℝ
  E : Fin 3 → Fin 3 → ℝ
  N_pos : 0 < N

namespace AdaptedFrame

variable (F : AdaptedFrame)

/-- The frame components `e_A{}^μ` (`A = 0` normal, `A = a.succ` spatial). -/
def fr (A μ : Fin 4) : ℝ :=
  Fin.cases (Fin.cases F.N⁻¹ (fun j => -(F.β j / F.N)) μ)
    (fun a => Fin.cases 0 (fun j => F.E a j) μ) A

@[simp] theorem fr_zero_zero : F.fr 0 0 = F.N⁻¹ := rfl
@[simp] theorem fr_zero_succ (j : Fin 3) : F.fr 0 j.succ = -(F.β j / F.N) := rfl
@[simp] theorem fr_succ_zero (a : Fin 3) : F.fr a.succ 0 = 0 := rfl
@[simp] theorem fr_succ_succ (a j : Fin 3) : F.fr a.succ j.succ = F.E a j := rfl

/-- The frame is adapted to (orthonormal for) the inverse metric:
`g^{μν} = -e_0^μe_0^ν + Σ_a e_a^μe_a^ν`. -/
def IsAdapted (gi : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ μ ν, gi μ ν = -(F.fr 0 μ * F.fr 0 ν) + ∑ a : Fin 3, F.fr a.succ μ * F.fr a.succ ν

theorem N_ne : F.N ≠ 0 := F.N_pos.ne'

/-- `N e_0(f) = ∂_tf - βʲ∂_jf`. -/
theorem N_e0 (df : Fin 4 → ℝ) :
    F.N * ∑ μ, F.fr 0 μ * df μ = df 0 - ∑ j, F.β j * df j.succ := by
  rw [Fin.sum_univ_succ, mul_add, Finset.mul_sum]
  simp only [fr_zero_zero, fr_zero_succ]
  rw [← mul_assoc, mul_inv_cancel₀ F.N_ne, one_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp [F.N_ne]

/-- `e_a(f) = e_aʲ∂_jf`. -/
theorem e_a (a : Fin 3) (df : Fin 4 → ℝ) :
    ∑ μ, F.fr a.succ μ * df μ = ∑ j, F.E a j * df j.succ := by
  rw [Fin.sum_univ_succ]; simp

/-! ### The first-order wave reduction of a field -/

/-- `p = e_0u`. -/
def pJ (du : Fin 4 → ℝ) : ℝ := ∑ β, F.fr 0 β * du β

/-- `q_a = e_au`. -/
def qJ (du : Fin 4 → ℝ) (a : Fin 3) : ℝ := ∑ β, F.fr a.succ β * du β

/-- `∂_γp = ∂_γ(e_0^β)∂_βu + e_0^β∂_γ∂_βu`. -/
def dpJ (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ) (ddu : Fin 4 → Fin 4 → ℝ)
    (γ : Fin 4) : ℝ :=
  ∑ β, (de γ 0 β * du β + F.fr 0 β * ddu γ β)

/-- `∂_γq_a = ∂_γ(e_a^β)∂_βu + e_a^β∂_γ∂_βu`. -/
def dqJ (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ) (ddu : Fin 4 → Fin 4 → ℝ)
    (γ : Fin 4) (a : Fin 3) : ℝ :=
  ∑ β, (de γ a.succ β * du β + F.fr a.succ β * ddu γ β)

/-- The lower-order term of the `p`-row: `L_p = (e_0(e_0^β) - Σ_a e_a(e_a^β))∂_βu`. -/
def Lp (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ) : ℝ :=
  ∑ β, (∑ α, F.fr 0 α * de α 0 β - ∑ a : Fin 3, ∑ α, F.fr a.succ α * de α a.succ β) * du β

/-- The lower-order term of the `q_a`-row: `L_{q,a} = [e_0, e_a]^β∂_βu`. -/
def Lq (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ) (a : Fin 3) : ℝ :=
  ∑ β, (∑ α, (F.fr 0 α * de α a.succ β - F.fr a.succ α * de α 0 β)) * du β

/-- **Head equation**: `∂_tu = Np + βʲ∂_ju`. -/
theorem head_row (du : Fin 4 → ℝ) : du 0 = F.N * F.pJ du + ∑ j, F.β j * du j.succ := by
  rw [pJ, F.N_e0]; ring

/-- The spatial derivatives are algebraic in `q`: `∂_ju = Σ_a (e⁻¹)_jᵃ q_a` whenever
`Σ_a (e⁻¹)_jᵃ e_aᵏ = δ_jᵏ`. -/
theorem spatial_of_q (Einv : Fin 3 → Fin 3 → ℝ)
    (hinv : ∀ j k, ∑ a, Einv j a * F.E a k = if j = k then 1 else 0) (du : Fin 4 → ℝ)
    (j : Fin 3) : du j.succ = ∑ a, Einv j a * F.qJ du a := by
  simp only [qJ, F.e_a, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hinv]
  simp

/-- `N e_0` of the coordinate jets. -/
theorem N_e0_jet (h : Fin 4 → ℝ) : h 0 - ∑ j, F.β j * h j.succ = F.N * ∑ α, F.fr 0 α * h α :=
  (F.N_e0 h).symm

theorem sum_fr_dpJ (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ)
    (ddu : Fin 4 → Fin 4 → ℝ) (A : Fin 4) (B : Fin 4) :
    ∑ α, F.fr A α * ∑ β, (de α B β * du β + F.fr B β * ddu α β) =
      ∑ β, (∑ α, F.fr A α * de α B β) * du β +
        ∑ α, ∑ β, F.fr A α * F.fr B β * ddu α β := by
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
    ring
  · refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    ring

/-- `Σ_a Σ_j e_aʲ ∂_jq_a` in frame form. -/
theorem sum_E_dqJ (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ) (ddu : Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ j, F.E a j * F.dqJ de du ddu j.succ a =
      ∑ a : Fin 3, (∑ β, (∑ α, F.fr a.succ α * de α a.succ β) * du β +
        ∑ α, ∑ β, F.fr a.succ α * F.fr a.succ β * ddu α β) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← F.e_a a (fun γ => F.dqJ de du ddu γ a)]
  exact F.sum_fr_dpJ de du ddu a.succ a.succ

/-- **The `p`-row** of the first-order wave reduction, for an adapted frame:
`∂_tp - βʲ∂_jp - N e_aʲ∂_jq_a = N(-g^{αβ}∂_α∂_βu + L_p)`. -/
theorem p_row (gi : Fin 4 → Fin 4 → ℝ) (hadapt : F.IsAdapted gi)
    (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ) (ddu : Fin 4 → Fin 4 → ℝ) :
    F.dpJ de du ddu 0 - ∑ j, F.β j * F.dpJ de du ddu j.succ -
        F.N * ∑ a, ∑ j, F.E a j * F.dqJ de du ddu j.succ a =
      F.N * (-(∑ α, ∑ β, gi α β * ddu α β) + F.Lp de du) := by
  unfold IsAdapted at hadapt
  rw [F.N_e0_jet (F.dpJ de du ddu), F.sum_E_dqJ]
  have hP := F.sum_fr_dpJ de du ddu 0 0
  simp only [dpJ]
  rw [hP, Finset.sum_add_distrib]
  have hg : ∑ α, ∑ β, gi α β * ddu α β = -(∑ α, ∑ β, F.fr 0 α * F.fr 0 β * ddu α β) +
      ∑ a : Fin 3, ∑ α, ∑ β, F.fr a.succ α * F.fr a.succ β * ddu α β := by
    simp only [hadapt, add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_mul]
    congr 1
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_comm
  have hL : F.Lp de du = ∑ β, (∑ α, F.fr 0 α * de α 0 β) * du β -
      ∑ a : Fin 3, ∑ β, (∑ α, F.fr a.succ α * de α a.succ β) * du β := by
    unfold Lp
    simp only [sub_mul, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_mul]
  rw [hg, hL]
  ring

/-- **The `q`-row** of the first-order wave reduction (Schwarz symmetry of `ddu`):
`∂_tq_a - βʲ∂_jq_a - N e_aʲ∂_jp = N L_{q,a}`. -/
theorem q_row (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (du : Fin 4 → ℝ) (ddu : Fin 4 → Fin 4 → ℝ)
    (hs : ∀ α β, ddu α β = ddu β α) (a : Fin 3) :
    F.dqJ de du ddu 0 a - ∑ j, F.β j * F.dqJ de du ddu j.succ a -
        F.N * ∑ j, F.E a j * F.dpJ de du ddu j.succ =
      F.N * F.Lq de du a := by
  rw [F.N_e0_jet (fun γ => F.dqJ de du ddu γ a), ← F.e_a a (F.dpJ de du ddu)]
  have h1 := F.sum_fr_dpJ de du ddu 0 a.succ
  have h2 := F.sum_fr_dpJ de du ddu a.succ 0
  simp only [dpJ, dqJ] at h1 h2 ⊢
  rw [h1, h2]
  have hsym : ∑ α, ∑ β, F.fr 0 α * F.fr a.succ β * ddu α β =
      ∑ α, ∑ β, F.fr a.succ α * F.fr 0 β * ddu α β := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [hs]; ring
  have hL : F.Lq de du a = ∑ β, (∑ α, F.fr 0 α * de α a.succ β) * du β -
      ∑ β, (∑ α, F.fr a.succ α * de α 0 β) * du β := by
    unfold Lq
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← sub_mul, ← Finset.sum_sub_distrib]
  rw [hsym, hL]
  ring

end AdaptedFrame

/-! ### The metric rows and the harmonic-defect forcing -/

section Metric

open AdaptedFrame

variable (F : AdaptedFrame) (g gi : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
  (ddg : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)

/-- The harmonic defect `C^l = g^{αβ}Γ^l_{αβ}`. -/
def C (l : Fin 4) : ℝ := cUp gi (chr gi dg) l

/-- Its actual derivative jet `∂_αC^l` (from the metric 2-jet). -/
def dC (α l : Fin 4) : ℝ := dcUp gi (dginv gi dg) (chr gi dg) (dchr gi dg ddg) α l

/-- The coefficient of `∂_αC^l` in `-2N∇_{(μ}C_{ν)}`: `-N(δ_α^μ g_{νl} + δ_α^ν g_{μl})` — it depends
only on the lapse and the metric (`𝒥_C^0` for `α = 0`, `𝒥_C^j` for `α = j`). -/
def Jd (α μ ν l : Fin 4) : ℝ :=
  -F.N * ((if α = μ then g ν l else 0) + (if α = ν then g μ l else 0))

/-- The coefficient of `C^l` in `-2N∇_{(μ}C_{ν)}`:
`-N(∂_μg_{νl} + ∂_νg_{μl}) + 2N Γ^k_{μν}g_{kl}` — it depends only on `(N, g, ∂g)`. -/
def JC (μ ν l : Fin 4) : ℝ :=
  -F.N * (dg μ ν l + dg ν μ l) + 2 * F.N * ∑ k, chr gi dg k μ ν * g k l

/-- The gauge-forcing entry of the metric `p`-row, `𝔊_{μν} = -2N∇_{(μ}C_{ν)}`. -/
def gaugeForce (μ ν : Fin 4) : ℝ := -2 * F.N * symDefect g gi dg ddg μ ν

theorem chr_symm (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (l μ ν : Fin 4) :
    chr gi dg l μ ν = chr gi dg l ν μ := by
  unfold chr
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hdg σ μ ν]; ring

/-- `∇_μC_ν = Σ_l (∂_μg_{νl}C^l + g_{νl}∂_μC^l) - Σ_m (Σ_l Γ^l_{μν}g_{lm})C^m`. -/
theorem nablaDefect_eq (μ ν : Fin 4) :
    nablaDefect g gi dg ddg μ ν =
      ∑ l, (dg μ ν l * C gi dg l + g ν l * dC gi dg ddg μ l) -
        ∑ m, (∑ l, chr gi dg l μ ν * g l m) * C gi dg m := by
  unfold nablaDefect nablaC cDown C dC
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem sum_Jd (μ ν l : Fin 4) :
    ∑ α, Jd F g α μ ν l * dC gi dg ddg α l =
      -F.N * (g ν l * dC gi dg ddg μ l + g μ l * dC gi dg ddg ν l) := by
  unfold Jd
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- **`eq:actual-jet-gauge-forcing`** (single-sum form):
`𝔊_{μν} = Σ_l (𝒥_C(μν,l) C^l + Σ_α 𝒥_C^α(μν,l) ∂_αC^l)`. -/
theorem gaugeForce_eq' (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (μ ν : Fin 4) :
    gaugeForce F g gi dg ddg μ ν =
      ∑ l, (JC F g gi dg μ ν l * C gi dg l + ∑ α, Jd F g α μ ν l * dC gi dg ddg α l) := by
  have e : gaugeForce F g gi dg ddg μ ν =
      -F.N * ∑ l, ((dg μ ν l * C gi dg l + g ν l * dC gi dg ddg μ l) +
        (dg ν μ l * C gi dg l + g μ l * dC gi dg ddg ν l)) +
      F.N * ∑ m, ((∑ l, chr gi dg l μ ν * g l m) * C gi dg m +
        (∑ l, chr gi dg l ν μ * g l m) * C gi dg m) := by
    unfold gaugeForce symDefect
    rw [nablaDefect_eq, nablaDefect_eq]
    simp only [Finset.sum_add_distrib]
    ring
  rw [e, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sum_Jd]
  unfold JC
  have hΓ : ∑ k, chr gi dg k ν μ * g k l = ∑ k, chr gi dg k μ ν * g k l :=
    Finset.sum_congr rfl fun k _ => by rw [chr_symm gi dg hdg k ν μ]
  rw [hΓ]
  ring

/-- **`eq:actual-jet-gauge-forcing`.**  The gauge forcing is linear in the actual harmonic
defect and its first derivatives:
`𝔊_{μν} = Σ_l 𝒥_C(μν,l) C^l + Σ_l 𝒥_C^0(μν,l) ∂_tC^l + Σ_j Σ_l 𝒥_C^j(μν,l) ∂_jC^l`, where
`𝒥_C^0 = Jd 0`, `𝒥_C^j = Jd j.succ` depend only on `(N, g)` and `𝒥_C = JC` on `(N, g, ∂g)`. -/
theorem gaugeForce_eq (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (μ ν : Fin 4) :
    gaugeForce F g gi dg ddg μ ν =
      ∑ l, JC F g gi dg μ ν l * C gi dg l + ∑ l, Jd F g 0 μ ν l * dC gi dg ddg 0 l +
        ∑ j : Fin 3, ∑ l, Jd F g j.succ μ ν l * dC gi dg ddg j.succ l := by
  rw [gaugeForce_eq' F g gi dg ddg hdg, Finset.sum_add_distrib, add_assoc]
  congr 1
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Fin.sum_univ_succ (fun α => Jd F g α μ ν l * dC gi dg ddg α l)

/-- The gauge forcing vanishes when the harmonic defect and its first derivatives vanish
(`C = 0` recovers the exactly harmonic system). -/
theorem gaugeForce_zero (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (hC : ∀ l, C gi dg l = 0) (hdC : ∀ α l, dC gi dg ddg α l = 0) (μ ν : Fin 4) :
    gaugeForce F g gi dg ddg μ ν = 0 := by
  rw [gaugeForce_eq' F g gi dg ddg hdg]
  simp [hC, hdC]

/-- The `∂C`-coefficients depend on the metric and the lapse only. -/
theorem Jd_depends (F' : AdaptedFrame) (hN : F.N = F'.N) (α μ ν l : Fin 4) :
    Jd F g α μ ν l = Jd F' g α μ ν l := by
  unfold Jd; rw [hN]

/-- **The metric `p`-row with harmonic-defect forcing.**  For `u = g_{μν}` with its 2-jet, an
adapted frame, any stress `T` and constants `Λ, κ`, in four dimensions:
`∂_tp - βʲ∂_jp - N e_aʲ∂_jq_a = N(L_p - 2𝓠_{μν} + 2κ(T - ½g trT)_{μν} + 2Λg_{μν})
  + 2N𝓔^{tr}_{μν} + 𝔊_{μν}`. -/
theorem metric_p_row (hadapt : F.IsAdapted gi) (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hs1 : ∀ α β μ ν, ddg α β μ ν = ddg β α μ ν) (hs2 : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ)
    (de : Fin 4 → Fin 4 → Fin 4 → ℝ) (T : Fin 4 → Fin 4 → ℝ) (Λ κ : ℝ) (μ ν : Fin 4) :
    F.dpJ de (fun α => dg α μ ν) (fun α β => ddg α β μ ν) 0 -
        ∑ j, F.β j * F.dpJ de (fun α => dg α μ ν) (fun α β => ddg α β μ ν) j.succ -
        F.N * ∑ a, ∑ j, F.E a j * F.dqJ de (fun α => dg α μ ν) (fun α β => ddg α β μ ν) j.succ a =
      F.N * (F.Lp de (fun α => dg α μ ν) - 2 * qRem g gi dg μ ν +
          2 * κ * traceRev g gi T μ ν + 2 * Λ * g μ ν) +
        2 * F.N * traceRev g gi (fun a b => einstein g gi dg ddg a b + Λ * g a b - κ * T a b) μ ν +
        gaugeForce F g gi dg ddg μ ν := by
  rw [F.p_row gi hadapt]
  have h := off_harmonic_metric_wave g gi dg ddg hgi hinv hs1 hs2 (by simp) T Λ κ μ ν
  unfold waveOp at h
  unfold gaugeForce
  linear_combination (2 * F.N) * h

end Metric

end

end RenewalGeometry.ActualJetWriter
