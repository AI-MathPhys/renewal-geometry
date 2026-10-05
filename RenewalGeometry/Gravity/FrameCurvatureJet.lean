/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.SpinorProlongationJet
import RenewalGeometry.Gravity.HarmonicDefectForcingExact

/-!
# Frame curvature from coordinate curvature on jets (`prop:actual-jet-writer`, clause (c2))

Einstein–Standard-Model action-closure manuscript, `prop:actual-jet-writer` ("For the tangential
spinor jets use `prop:spinor-prolongation`.  The contracted curvature there is the physical Ricci
tensor, so `eq:trace-reversal-residual` eliminates it").  The moving-frame Levi-Civita jets of
`SpinorProlongation.LCJet` are built from the jets of an actual orthonormal frame of an actual
metric, and their frame Riemann and Ricci tensors are identified with the coordinate ones of
`HarmonicDefect` (`lem:harmonic-defect-forcing`).

Everything is exact finite algebra on jets at one point, over arbitrary finite coordinate and
frame index types.  Data: a metric 2-jet `(g, g⁻¹, ∂g, ∂²g)` and a frame 2-jet
`(e_A{}^μ, ∂_γe_A{}^μ, ∂_δ∂_γe_A{}^μ)`; the jet relations are the identities satisfied by the
jets of smooth fields: symmetry of second derivatives, `g g⁻¹ = 1`, orthonormality
`g(e_A, e_B) = ε_Aδ_{AB}` together with its first and second derivatives, and completeness
`g^{μν} = Σ_A ε_A e_A{}^μe_A{}^ν`.

## Main results

* `cv2_comm` — the **Ricci identity for vector jets**
  `∇_δ∇_γV^μ - ∇_γ∇_δV^μ = R^μ{}_{σδγ}V^σ` (symmetric connection symbols).
* `metric_compat`, `metric_compat2` — `∂g = Γ·g + g·Γ` for the Levi-Civita symbols and its
  derivative (`∂²g` through `∂Γ = HarmonicDefect.dchr`).
* `dipg_eq`, `ddipg_eq` — first and second product-rule derivatives of `g(X, Y)` in covariant
  form.
* `FrameJet` — the frame jet; `FrameJet.G` the connection coefficients
  `G_{ABC} = g(∇_{e_A}e_B, e_C)`, `FrameJet.dG` their frame derivatives (product rule);
  `G_anti`, `dG_anti` (metric compatibility, from the orthonormality jets).
* **`rawRm_eq`** — the frame Riemann tensor of `SpinorProlongation.LCJet` (the same formula)
  equals the frame components of the coordinate Riemann tensor:
  `Rm_{abxy} = e_a{}^δe_b{}^γe_x{}^σe_y{}^ν g_{μν}R^μ{}_{σδγ}`.
* `jacobi` and **`FrameJet.toLCJet`** — the Jacobi identity of the frame (from the coordinate
  first Bianchi identity), hence the frame jet is an `LCJet`.
* **`ricciOf_eq`** — `Ric_{ab} = Σ_c ε_c Rm_{cabc} = e_a{}^μe_b{}^ν R_{μν}` with `R_{μν}` the
  coordinate Ricci tensor `HarmonicDefect.ricci` of the metric 2-jet.
* **`frame_trace_reversal`** — consequently, in four dimensions, for every stress `T`,
  `Ric_{ab} = κ T^{tr}(e_a, e_b) + Λ ε_aδ_{ab} + 𝓔^{tr}(e_a, e_b)` (`eq:trace-reversal-residual`
  in the moving frame).
* `bracket_eq`, **`frameF_eq`** — `[e_a, e_b] = Σ_c Λ_{ab}{}^ce_c`, and the frame gauge curvature
  of the twisted connection is `ρ(F(e_a, e_b))`.
* `hψ_frame` — the frame commutator relation of `prop:spinor-prolongation` holds for the frame
  jets of a spinor computed from its coordinate jets.
-/

namespace RenewalGeometry.FrameCurvature

open Finset HarmonicDefect SpinorProlongation TwistedHalfRicci

noncomputable section

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Covariant derivatives of vector jets -/

/-- `∇_γV^μ = ∂_γV^μ + Γ^μ_{γσ}V^σ` (`dV γ μ = ∂_γV^μ`). -/
def cv1 (Γ : n → n → n → ℝ) (V : n → ℝ) (dV : n → n → ℝ) (γ μ : n) : ℝ :=
  dV γ μ + ∑ σ, Γ μ γ σ * V σ

/-- `∂_δ(∇_γV^μ)` by the product rule (`dΓ δ μ γ σ = ∂_δΓ^μ_{γσ}`, `ddV δ γ μ = ∂_δ∂_γV^μ`). -/
def dcv1 (Γ : n → n → n → ℝ) (dΓ : n → n → n → n → ℝ) (V : n → ℝ) (dV : n → n → ℝ)
    (ddV : n → n → n → ℝ) (δ γ μ : n) : ℝ :=
  ddV δ γ μ + ∑ σ, (dΓ δ μ γ σ * V σ + Γ μ γ σ * dV δ σ)

/-- `∇_δ∇_γV^μ = ∂_δ(∇_γV^μ) + Γ^μ_{δλ}∇_γV^λ - Γ^λ_{δγ}∇_λV^μ`. -/
def cv2 (Γ : n → n → n → ℝ) (dΓ : n → n → n → n → ℝ) (V : n → ℝ) (dV : n → n → ℝ)
    (ddV : n → n → n → ℝ) (δ γ μ : n) : ℝ :=
  dcv1 Γ dΓ V dV ddV δ γ μ + ∑ l, Γ μ δ l * cv1 Γ V dV γ l - ∑ l, Γ l δ γ * cv1 Γ V dV l μ

/-- The coordinate Riemann tensor `R^λ{}_{σγρ} = ∂_γΓ^λ_{ρσ} - ∂_ρΓ^λ_{γσ} + Γ^λ_{γκ}Γ^κ_{ρσ}
- Γ^λ_{ρκ}Γ^κ_{γσ}` of a connection jet. -/
def rie (Γ : n → n → n → ℝ) (dΓ : n → n → n → n → ℝ) (l σ γ ρ : n) : ℝ :=
  dΓ γ l ρ σ - dΓ ρ l γ σ + ∑ κ, (Γ l γ κ * Γ κ ρ σ - Γ l ρ κ * Γ κ γ σ)

/-- **Ricci identity for vector jets**: for symmetric connection symbols and a symmetric second
jet, `∇_δ∇_γV^μ - ∇_γ∇_δV^μ = R^μ{}_{σδγ}V^σ`. -/
theorem cv2_comm {Γ : n → n → n → ℝ} (dΓ : n → n → n → n → ℝ) (V : n → ℝ) (dV : n → n → ℝ)
    {ddV : n → n → n → ℝ} (hΓ : ∀ l μ ν, Γ l μ ν = Γ l ν μ)
    (hV : ∀ δ γ μ, ddV δ γ μ = ddV γ δ μ) (δ γ μ : n) :
    cv2 Γ dΓ V dV ddV δ γ μ - cv2 Γ dΓ V dV ddV γ δ μ = ∑ σ, rie Γ dΓ μ σ δ γ * V σ := by
  have h1 : ∑ l, Γ l δ γ * cv1 Γ V dV l μ = ∑ l, Γ l γ δ * cv1 Γ V dV l μ :=
    Finset.sum_congr rfl fun l _ => by rw [hΓ l δ γ]
  have h2 : ∑ l, Γ μ δ l * cv1 Γ V dV γ l = ∑ σ, Γ μ δ σ * dV γ σ +
      ∑ σ, ∑ κ, Γ μ δ κ * Γ κ γ σ * V σ := by
    unfold cv1
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun κ _ => ?_
    ring
  have h3 : ∑ l, Γ μ γ l * cv1 Γ V dV δ l = ∑ σ, Γ μ γ σ * dV δ σ +
      ∑ σ, ∑ κ, Γ μ γ κ * Γ κ δ σ * V σ := by
    unfold cv1
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun κ _ => ?_
    ring
  have hR : ∑ σ, rie Γ dΓ μ σ δ γ * V σ = ∑ σ, (dΓ δ μ γ σ * V σ - dΓ γ μ δ σ * V σ) +
      (∑ σ, ∑ κ, Γ μ δ κ * Γ κ γ σ * V σ - ∑ σ, ∑ κ, Γ μ γ κ * Γ κ δ σ * V σ) := by
    unfold rie
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Finset.sum_sub_distrib, add_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun κ _ => by ring
  unfold cv2 dcv1
  rw [h1, h2, h3, hR, hV δ γ μ]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-! ### Levi-Civita connection jets: metric compatibility -/

section MetricCompat

variable (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ)

/-- Lowering the first index of the Christoffel symbols:
`Σ_l g_{νl}Γ^l_{γμ} = ½(∂_γg_{νμ} + ∂_μg_{νγ} - ∂_νg_{γμ})`. -/
theorem lower_chr (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0) (ν γ μ : n) :
    ∑ l, g ν l * chr gi dg l γ μ = (1 / 2) * (dg γ ν μ + dg μ ν γ - dg ν γ μ) := by
  unfold chr
  have : ∑ l, g ν l * ((1 / 2) * ∑ σ, gi l σ * (dg γ σ μ + dg μ σ γ - dg σ γ μ)) =
      (1 / 2) * ∑ σ, (∑ l, g ν l * gi l σ) * (dg γ σ μ + dg μ σ γ - dg σ γ μ) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [this]
  simp only [hinv, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **Metric compatibility** of the Levi-Civita symbols:
`∂_γg_{μν} = Σ_l (g_{νl}Γ^l_{γμ} + g_{μl}Γ^l_{γν})`. -/
theorem metric_compat (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (γ μ ν : n) :
    dg γ μ ν = ∑ l, (g ν l * chr gi dg l γ μ + g μ l * chr gi dg l γ ν) := by
  rw [Finset.sum_add_distrib, lower_chr g gi dg hinv, lower_chr g gi dg hinv]
  rw [hdg γ ν μ, hdg μ ν γ, hdg ν γ μ, hdg ν μ γ]
  ring

/-- `Σ_l g_{νl}∂_δg^{lσ} = -Σ_b ∂_δg_{νb}g^{bσ}`. -/
theorem lower_dginv (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0) (δ ν σ : n) :
    ∑ l, g ν l * dginv gi dg δ l σ = -∑ b, dg δ ν b * gi b σ := by
  unfold dginv
  have : ∑ l, g ν l * -∑ a, ∑ b, gi l a * dg δ a b * gi b σ =
      -∑ a, (∑ l, g ν l * gi l a) * ∑ b, dg δ a b * gi b σ := by
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [this]
  simp only [hinv, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Lowering the derivative jet of the Christoffel symbols:
`Σ_l (∂_δg_{νl}Γ^l_{γμ} + g_{νl}∂_δΓ^l_{γμ}) = ½(∂_δ∂_γg_{νμ} + ∂_δ∂_μg_{νγ} - ∂_δ∂_νg_{γμ})`. -/
theorem lower_dchr (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (δ ν γ μ : n) :
    ∑ l, (dg δ ν l * chr gi dg l γ μ + g ν l * dchr gi dg ddg δ l γ μ) =
      (1 / 2) * (ddg δ γ ν μ + ddg δ μ ν γ - ddg δ ν γ μ) := by
  have h2 : ∑ l, g ν l * dchr2 gi ddg δ l γ μ =
      (1 / 2) * (ddg δ γ ν μ + ddg δ μ ν γ - ddg δ ν γ μ) := by
    unfold dchr2
    have : ∑ l, g ν l * ((1 / 2) * ∑ σ, gi l σ *
        (ddg δ γ σ μ + ddg δ μ σ γ - ddg δ σ γ μ)) =
        (1 / 2) * ∑ σ, (∑ l, g ν l * gi l σ) * (ddg δ γ σ μ + ddg δ μ σ γ - ddg δ σ γ μ) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [this]
    simp only [hinv, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h1 : ∑ l, g ν l * dchr1 gi dg δ l γ μ = -∑ b, dg δ ν b * chr gi dg b γ μ := by
    unfold dchr1
    have : ∑ l, g ν l * ((1 / 2) * ∑ σ, dginv gi dg δ l σ *
        (dg γ σ μ + dg μ σ γ - dg σ γ μ)) =
        (1 / 2) * ∑ σ, (∑ l, g ν l * dginv gi dg δ l σ) * (dg γ σ μ + dg μ σ γ - dg σ γ μ) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [this]
    simp only [lower_dginv g gi dg hinv]
    unfold chr
    simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum, mul_neg]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  unfold dchr
  simp only [mul_add, Finset.sum_add_distrib]
  rw [h1, h2]
  ring

/-- **Second-order metric compatibility** (the derivative of `metric_compat`):
`∂_δ∂_γg_{μν} = Σ_l (∂_δg_{νl}Γ^l_{γμ} + g_{νl}∂_δΓ^l_{γμ} + ∂_δg_{μl}Γ^l_{γν} + g_{μl}∂_δΓ^l_{γν})`. -/
theorem metric_compat2 (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hddg : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ) (δ γ μ ν : n) :
    ddg δ γ μ ν = ∑ l, (dg δ ν l * chr gi dg l γ μ + g ν l * dchr gi dg ddg δ l γ μ) +
      ∑ l, (dg δ μ l * chr gi dg l γ ν + g μ l * dchr gi dg ddg δ l γ ν) := by
  rw [lower_dchr g gi dg ddg hinv, lower_dchr g gi dg ddg hinv]
  rw [hddg δ γ ν μ, hddg δ μ ν γ, hddg δ ν μ γ]
  ring

/-- The first derivative jet of the Christoffel symbols is symmetric in its lower indices. -/
theorem dchr_symm (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (hddg : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ) (δ l μ ν : n) :
    dchr gi dg ddg δ l μ ν = dchr gi dg ddg δ l ν μ := by
  unfold dchr dchr1 dchr2
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hdg σ μ ν]; ring
  · congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hddg δ σ μ ν]; ring

end MetricCompat

/-! ### Product-rule derivatives of the metric pairing -/

section Pairing

/-- `g(X, Y) = Σ g_{μν}X^μY^ν`. -/
def ipg (g : n → n → ℝ) (X Y : n → ℝ) : ℝ := ∑ μ, ∑ ν, g μ ν * X μ * Y ν

/-- `∂_δ(g(X, Y))` by the product rule. -/
def dipg (g : n → n → ℝ) (dg : n → n → n → ℝ) (X : n → ℝ) (dX : n → n → ℝ) (Y : n → ℝ)
    (dY : n → n → ℝ) (δ : n) : ℝ :=
  ∑ μ, ∑ ν, (dg δ μ ν * X μ * Y ν + g μ ν * dX δ μ * Y ν + g μ ν * X μ * dY δ ν)

/-- `∂_δ∂_γ(g(X, Y))` by the product rule. -/
def ddipg (g : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) (X : n → ℝ)
    (dX : n → n → ℝ) (ddX : n → n → n → ℝ) (Y : n → ℝ) (dY : n → n → ℝ) (ddY : n → n → n → ℝ)
    (δ γ : n) : ℝ :=
  ∑ μ, ∑ ν, (ddg δ γ μ ν * X μ * Y ν + dg γ μ ν * dX δ μ * Y ν + dg γ μ ν * X μ * dY δ ν +
    (dg δ μ ν * dX γ μ * Y ν + g μ ν * ddX δ γ μ * Y ν + g μ ν * dX γ μ * dY δ ν) +
    (dg δ μ ν * X μ * dY γ ν + g μ ν * dX δ μ * dY γ ν + g μ ν * X μ * ddY δ γ ν))

theorem ipg_add_left (g : n → n → ℝ) (X X' Y : n → ℝ) :
    ipg g (fun μ => X μ + X' μ) Y = ipg g X Y + ipg g X' Y := by
  unfold ipg; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun μ _ => by rw [← Finset.sum_add_distrib]; congr 1; ext ν; ring

theorem ipg_sum_left {κ : Type*} (s : Finset κ) (g : n → n → ℝ) (c : κ → ℝ) (X : κ → n → ℝ)
    (Y : n → ℝ) : ipg g (fun μ => ∑ i ∈ s, c i * X i μ) Y = ∑ i ∈ s, c i * ipg g (X i) Y := by
  unfold ipg
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem ipg_sum_right {κ : Type*} (s : Finset κ) (g : n → n → ℝ) (X : n → ℝ) (c : κ → ℝ)
    (Y : κ → n → ℝ) : ipg g X (fun ν => ∑ i ∈ s, c i * Y i ν) = ∑ i ∈ s, c i * ipg g X (Y i) := by
  unfold ipg
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem ipg_comm (g : n → n → ℝ) (hg : ∀ a b, g a b = g b a) (X Y : n → ℝ) :
    ipg g X Y = ipg g Y X := by
  unfold ipg
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [hg]; ring

/-- `Σ_{μν} (Σ_l (g_{νl}Γ^l_{δμ} + g_{μl}Γ^l_{δν})) X^μY^ν = g(ΓX, Y) + g(X, ΓY)`. -/
theorem sum_compat_pair (g : n → n → ℝ) (hg : ∀ a b, g a b = g b a) (Γ : n → n → n → ℝ)
    (X Y : n → ℝ) (δ : n) :
    ∑ μ, ∑ ν, (∑ l, (g ν l * Γ l δ μ + g μ l * Γ l δ ν)) * X μ * Y ν =
      ipg g (fun μ => ∑ σ, Γ μ δ σ * X σ) Y + ipg g X (fun ν => ∑ σ, Γ ν δ σ * Y σ) := by
  unfold ipg
  have hA : ∑ μ, ∑ ν, (∑ l, g ν l * Γ l δ μ) * X μ * Y ν =
      ∑ μ, ∑ ν, g μ ν * (∑ σ, Γ μ δ σ * X σ) * Y ν := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [sum3_rev]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    rw [hg b a]; ring
  have hB : ∑ μ, ∑ ν, (∑ l, g μ l * Γ l δ ν) * X μ * Y ν =
      ∑ μ, ∑ ν, g μ ν * X μ * (∑ σ, Γ ν δ σ * Y σ) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ν _ => ?_
    ring
  rw [← hA, ← hB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_add_distrib]; ring

/-- **First derivative of the metric pairing in covariant form**: if `∂g = Γ·g + g·Γ`, then
`∂_δ g(X, Y) = g(∇_δX, Y) + g(X, ∇_δY)`. -/
theorem dipg_eq (g : n → n → ℝ) (hg : ∀ a b, g a b = g b a) (dg : n → n → n → ℝ)
    (Γ : n → n → n → ℝ) (hcomp : ∀ γ μ ν, dg γ μ ν = ∑ l, (g ν l * Γ l γ μ + g μ l * Γ l γ ν))
    (X : n → ℝ) (dX : n → n → ℝ) (Y : n → ℝ) (dY : n → n → ℝ) (δ : n) :
    dipg g dg X dX Y dY δ = ipg g (fun μ => cv1 Γ X dX δ μ) Y + ipg g X (fun ν => cv1 Γ Y dY δ ν) := by
  have e1 : ipg g (fun μ => cv1 Γ X dX δ μ) Y =
      ipg g (fun μ => dX δ μ) Y + ipg g (fun μ => ∑ σ, Γ μ δ σ * X σ) Y :=
    ipg_add_left g _ _ Y
  have e2 : ipg g X (fun ν => cv1 Γ Y dY δ ν) =
      ipg g X (fun ν => dY δ ν) + ipg g X (fun ν => ∑ σ, Γ ν δ σ * Y σ) := by
    rw [ipg_comm g hg, ipg_comm g hg X, ipg_comm g hg X]
    exact ipg_add_left g _ _ X
  have hs := sum_compat_pair g hg Γ X Y δ
  have hd : ∑ μ, ∑ ν, dg δ μ ν * X μ * Y ν =
      ∑ μ, ∑ ν, (∑ l, (g ν l * Γ l δ μ + g μ l * Γ l δ ν)) * X μ * Y ν :=
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by rw [hcomp δ μ ν]
  rw [e1, e2]
  unfold dipg
  simp only [Finset.sum_add_distrib]
  rw [hd, hs]
  unfold ipg
  ring

theorem ipg_add_right (g : n → n → ℝ) (X Y Y' : n → ℝ) :
    ipg g X (fun ν => Y ν + Y' ν) = ipg g X Y + ipg g X Y' := by
  unfold ipg; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun μ _ => by rw [← Finset.sum_add_distrib]; congr 1; ext ν; ring

theorem dipg_split (g : n → n → ℝ) (dg : n → n → n → ℝ) (X : n → ℝ) (dX : n → n → ℝ)
    (Y : n → ℝ) (dY : n → n → ℝ) (δ : n) :
    dipg g dg X dX Y dY δ = ipg (dg δ) X Y + ipg g (dX δ) Y + ipg g X (dY δ) := by
  unfold dipg ipg; simp only [Finset.sum_add_distrib]

theorem ddipg_split (g : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ)
    (X : n → ℝ) (dX : n → n → ℝ) (ddX : n → n → n → ℝ) (Y : n → ℝ) (dY : n → n → ℝ)
    (ddY : n → n → n → ℝ) (δ γ : n) :
    ddipg g dg ddg X dX ddX Y dY ddY δ γ = ipg (ddg δ γ) X Y + ipg (dg γ) (dX δ) Y +
      ipg (dg γ) X (dY δ) + (ipg (dg δ) (dX γ) Y + ipg g (ddX δ γ) Y + ipg g (dX γ) (dY δ)) +
      (ipg (dg δ) X (dY γ) + ipg g (dX δ) (dY γ) + ipg g X (ddY δ γ)) := by
  unfold ddipg ipg; simp only [Finset.sum_add_distrib]

/-- **Second derivative of the metric pairing**: if `∂g = Γ·g + g·Γ` and `∂²g` is its derivative
(`metric_compat2`), then the product-rule second derivative `∂_δ∂_γ g(X, Y)` equals the
product-rule derivative of `g(∇_γX, Y) + g(X, ∇_γY)` (with `∂_δ∇_γ` from `dcv1`). -/
theorem ddipg_eq (g : n → n → ℝ) (hg : ∀ a b, g a b = g b a) (dg : n → n → n → ℝ)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (ddg : n → n → n → n → ℝ) (Γ : n → n → n → ℝ)
    (dΓ : n → n → n → n → ℝ)
    (hcomp : ∀ γ μ ν, dg γ μ ν = ∑ l, (g ν l * Γ l γ μ + g μ l * Γ l γ ν))
    (hcomp2 : ∀ δ γ μ ν, ddg δ γ μ ν = ∑ l, (dg δ ν l * Γ l γ μ + g ν l * dΓ δ l γ μ) +
      ∑ l, (dg δ μ l * Γ l γ ν + g μ l * dΓ δ l γ ν))
    (X : n → ℝ) (dX : n → n → ℝ) (ddX : n → n → n → ℝ) (Y : n → ℝ) (dY : n → n → ℝ)
    (ddY : n → n → n → ℝ) (δ γ : n) :
    ddipg g dg ddg X dX ddX Y dY ddY δ γ =
      dipg g dg (cv1 Γ X dX γ) (fun δ μ => dcv1 Γ dΓ X dX ddX δ γ μ) Y dY δ +
        dipg g dg X dX (cv1 Γ Y dY γ) (fun δ ν => dcv1 Γ dΓ Y dY ddY δ γ ν) δ := by
  have hdgs : ∀ a b, dg δ a b = dg δ b a := fun a b => hdg δ a b
  -- the `∂²g` term
  have hT1 : ipg (ddg δ γ) X Y = ipg (dg δ) (fun μ => ∑ σ, Γ μ γ σ * X σ) Y +
      ipg (dg δ) X (fun ν => ∑ σ, Γ ν γ σ * Y σ) +
      (ipg g (fun μ => ∑ σ, dΓ δ μ γ σ * X σ) Y + ipg g X (fun ν => ∑ σ, dΓ δ ν γ σ * Y σ)) := by
    rw [← sum_compat_pair (dg δ) hdgs Γ X Y γ,
      ← sum_compat_pair g hg (fun l _ μ => dΓ δ l γ μ) X Y γ]
    unfold ipg
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hcomp2 δ γ μ ν]
    simp only [Finset.sum_add_distrib]
    ring
  have hT2 : ipg (dg γ) (dX δ) Y = ipg g (fun μ => ∑ σ, Γ μ γ σ * dX δ σ) Y +
      ipg g (dX δ) (fun ν => ∑ σ, Γ ν γ σ * Y σ) := by
    rw [← sum_compat_pair g hg Γ (dX δ) Y γ]
    unfold ipg
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by rw [hcomp γ μ ν]
  have hT3 : ipg (dg γ) X (dY δ) = ipg g (fun μ => ∑ σ, Γ μ γ σ * X σ) (dY δ) +
      ipg g X (fun ν => ∑ σ, Γ ν γ σ * dY δ σ) := by
    rw [← sum_compat_pair g hg Γ X (dY δ) γ]
    unfold ipg
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by rw [hcomp γ μ ν]
  have hcX : cv1 Γ X dX γ = fun μ => dX γ μ + ∑ σ, Γ μ γ σ * X σ := rfl
  have hcY : cv1 Γ Y dY γ = fun ν => dY γ ν + ∑ σ, Γ ν γ σ * Y σ := rfl
  have hdX : (fun μ => dcv1 Γ dΓ X dX ddX δ γ μ) = fun μ => ddX δ γ μ +
      (∑ σ, dΓ δ μ γ σ * X σ + ∑ σ, Γ μ γ σ * dX δ σ) := by
    funext μ; unfold dcv1; rw [Finset.sum_add_distrib]
  have hdY : (fun ν => dcv1 Γ dΓ Y dY ddY δ γ ν) = fun ν => ddY δ γ ν +
      (∑ σ, dΓ δ ν γ σ * Y σ + ∑ σ, Γ ν γ σ * dY δ σ) := by
    funext ν; unfold dcv1; rw [Finset.sum_add_distrib]
  rw [ddipg_split, dipg_split, dipg_split, hT1, hT2, hT3, hdX, hdY, hcX, hcY]
  rw [ipg_add_left (dg δ) (dX γ), ipg_add_left g (dX γ), ipg_add_right (dg δ) X (dY γ),
    ipg_add_right g (dX δ) (dY γ), ipg_add_left g (ddX δ γ), ipg_add_left g,
    ipg_add_right g X (ddY δ γ), ipg_add_right g X]
  ring

end Pairing

/-! ### Frame jets -/

/-- Symmetry of the Christoffel symbols in their lower indices. -/
theorem chr_symm' (gi : n → n → ℝ) (dg : n → n → n → ℝ) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (l μ ν : n) : chr gi dg l μ ν = chr gi dg l ν μ := by
  unfold chr
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hdg σ μ ν]; ring

variable (n) in
/-- **The 2-jet of an orthonormal frame of a metric** at one point: metric 2-jet
`(g, g⁻¹, ∂g, ∂²g)`, frame `e_A{}^μ` with signs `ε_A`, frame derivative jets `∂_γe_A{}^μ`,
`∂_δ∂_γe_A{}^μ`.  The relations are those of the jets of smooth fields: symmetric second
derivatives, `g g⁻¹ = 1`, orthonormality `g(e_A, e_B) = ε_Aδ_{AB}` with its first and second
derivatives (`orth1`, `orth2`, product rule), and completeness `g^{μν} = Σ_A ε_Ae_A{}^μe_A{}^ν`. -/
structure FrameJet (ι : Type*) [Fintype ι] [DecidableEq ι] where
  g : n → n → ℝ
  gi : n → n → ℝ
  dg : n → n → n → ℝ
  ddg : n → n → n → n → ℝ
  ε : ι → ℝ
  e : ι → n → ℝ
  de : n → ι → n → ℝ
  dde : n → n → ι → n → ℝ
  g_symm : ∀ a b, g a b = g b a
  gi_symm : ∀ a b, gi a b = gi b a
  hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0
  dg_symm : ∀ α μ ν, dg α μ ν = dg α ν μ
  ddg_symm1 : ∀ α β μ ν, ddg α β μ ν = ddg β α μ ν
  ddg_symm2 : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ
  dde_symm : ∀ δ γ A μ, dde δ γ A μ = dde γ δ A μ
  sign_sq : ∀ A, ε A ^ 2 = 1
  orth : ∀ A B, ipg g (e A) (e B) = if A = B then ε A else 0
  compl : ∀ μ ν, gi μ ν = ∑ A, ε A * e A μ * e A ν
  orth1 : ∀ γ A B, dipg g dg (e A) (fun γ μ => de γ A μ) (e B) (fun γ μ => de γ B μ) γ = 0
  orth2 : ∀ δ γ A B, ddipg g dg ddg (e A) (fun γ μ => de γ A μ) (fun δ γ μ => dde δ γ A μ)
    (e B) (fun γ μ => de γ B μ) (fun δ γ μ => dde δ γ B μ) δ γ = 0

namespace FrameJet

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FrameJet n ι)

/-- The Levi-Civita symbols of the metric jet. -/
def Γ : n → n → n → ℝ := chr F.gi F.dg

/-- Their derivative jet. -/
def dΓ : n → n → n → n → ℝ := dchr F.gi F.dg F.ddg

theorem Γ_symm (l μ ν : n) : F.Γ l μ ν = F.Γ l ν μ := chr_symm' F.gi F.dg F.dg_symm l μ ν

theorem dΓ_symm (δ l μ ν : n) : F.dΓ δ l μ ν = F.dΓ δ l ν μ :=
  dchr_symm F.gi F.dg F.ddg F.dg_symm F.ddg_symm2 δ l μ ν

theorem compat (γ μ ν : n) : F.dg γ μ ν = ∑ l, (F.g ν l * F.Γ l γ μ + F.g μ l * F.Γ l γ ν) :=
  metric_compat F.g F.gi F.dg F.hinv F.dg_symm γ μ ν

theorem compat2 (δ γ μ ν : n) : F.ddg δ γ μ ν =
    ∑ l, (F.dg δ ν l * F.Γ l γ μ + F.g ν l * F.dΓ δ l γ μ) +
      ∑ l, (F.dg δ μ l * F.Γ l γ ν + F.g μ l * F.dΓ δ l γ ν) :=
  metric_compat2 F.g F.gi F.dg F.ddg F.hinv F.ddg_symm2 δ γ μ ν

/-- `∇_γe_A{}^μ`. -/
def Ne (A : ι) (γ μ : n) : ℝ := cv1 F.Γ (F.e A) (fun γ μ => F.de γ A μ) γ μ

/-- `∂_δ∇_γe_A{}^μ`. -/
def dNe (A : ι) (δ γ μ : n) : ℝ :=
  dcv1 F.Γ F.dΓ (F.e A) (fun γ μ => F.de γ A μ) (fun δ γ μ => F.dde δ γ A μ) δ γ μ

/-- `∇_δ∇_γe_A{}^μ`. -/
def NNe (A : ι) (δ γ μ : n) : ℝ :=
  cv2 F.Γ F.dΓ (F.e A) (fun γ μ => F.de γ A μ) (fun δ γ μ => F.dde δ γ A μ) δ γ μ

/-- `P_{γBC} = g(∇_γe_B, e_C)`. -/
def P (γ : n) (B C : ι) : ℝ := ipg F.g (F.Ne B γ) (F.e C)

/-- **The connection coefficients** `G_{ABC} = g(∇_{e_A}e_B, e_C)`. -/
def G (A B C : ι) : ℝ := ∑ γ, F.e A γ * F.P γ B C

/-- `∂_δP_{γBC}` (product rule). -/
def dP (δ γ : n) (B C : ι) : ℝ :=
  dipg F.g F.dg (F.Ne B γ) (fun δ μ => F.dNe B δ γ μ) (F.e C) (fun δ μ => F.de δ C μ) δ

/-- `∂_δG_{ABC}` (product rule). -/
def dGc (δ : n) (A B C : ι) : ℝ := ∑ γ, (F.de δ A γ * F.P γ B C + F.e A γ * F.dP δ γ B C)

/-- **The frame derivatives** `e_D(G_{ABC}) = e_D{}^δ∂_δG_{ABC}`. -/
def dG (D A B C : ι) : ℝ := ∑ δ, F.e D δ * F.dGc δ A B C

/-- **Frame expansion**: `X^μ = Σ_C ε_C g(X, e_C) e_C{}^μ`. -/
theorem expand (X : n → ℝ) (μ : n) : X μ = ∑ C, F.ε C * ipg F.g X (F.e C) * F.e C μ := by
  have h : ∑ C, F.ε C * ipg F.g X (F.e C) * F.e C μ =
      ∑ α, X α * ∑ β, F.g α β * F.gi β μ := by
    unfold ipg
    simp only [F.compl, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    refine Finset.sum_congr rfl fun C _ => ?_
    ring
  rw [h]
  simp only [F.hinv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `∇_{e_A}e_B = Σ_C ε_C G_{ABC} e_C`. -/
theorem Ne_expand (A B : ι) (μ : n) :
    ∑ γ, F.e A γ * F.Ne B γ μ = ∑ C, F.ε C * F.G A B C * F.e C μ := by
  rw [F.expand (fun μ => ∑ γ, F.e A γ * F.Ne B γ μ) μ]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [ipg_sum_left]
  rfl

/-- The first derivative of the pairing of two frame vectors in covariant form. -/
theorem dipg_frame (γ : n) (A B : ι) :
    dipg F.g F.dg (F.e A) (fun γ μ => F.de γ A μ) (F.e B) (fun γ μ => F.de γ B μ) γ =
      F.P γ A B + F.P γ B A := by
  rw [dipg_eq F.g F.g_symm F.dg F.Γ F.compat]
  unfold P
  rw [ipg_comm F.g F.g_symm (F.e A)]
  rfl

/-- **Metric compatibility of the frame connection**: `G_{ABC} = -G_{ACB}`. -/
theorem G_anti (A B C : ι) : F.G A C B = -F.G A B C := by
  have h : ∀ γ, F.P γ B C + F.P γ C B = 0 := fun γ => by
    rw [← F.dipg_frame γ B C]; exact F.orth1 γ B C
  unfold G
  rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun γ _ => ?_
  rw [← mul_add, add_comm, h γ, mul_zero]

/-- `∂_δP_{γBC} = g(∇_δ∇_γe_B, e_C) + Γ^λ_{δγ}P_{λBC} + g(∇_γe_B, ∇_δe_C)`. -/
theorem dP_eq (δ γ : n) (B C : ι) :
    F.dP δ γ B C = ipg F.g (F.NNe B δ γ) (F.e C) + ∑ l, F.Γ l δ γ * F.P l B C +
      ipg F.g (F.Ne B γ) (F.Ne C δ) := by
  unfold dP
  rw [dipg_eq F.g F.g_symm F.dg F.Γ F.compat]
  have h : cv1 F.Γ (F.Ne B γ) (fun δ μ => F.dNe B δ γ μ) δ =
      fun μ => F.NNe B δ γ μ + ∑ l, F.Γ l δ γ * F.Ne B l μ := by
    funext μ
    simp only [cv1, NNe, cv2, Ne, dNe]
    ring
  rw [h, ipg_add_left, ipg_sum_left]
  rfl

/-- The derivative of the connection coefficients in covariant form:
`∂_δG_{ABC} = Σ_γ (∇_δe_A)^γP_{γBC} + e_A{}^γ(g(∇_δ∇_γe_B, e_C) + g(∇_γe_B, ∇_δe_C))`. -/
theorem dGc_eq (δ : n) (A B C : ι) :
    F.dGc δ A B C = ∑ γ, F.Ne A δ γ * F.P γ B C +
      ∑ γ, F.e A γ * (ipg F.g (F.NNe B δ γ) (F.e C) + ipg F.g (F.Ne B γ) (F.Ne C δ)) := by
  unfold dGc
  simp only [F.dP_eq]
  have h : ∑ γ, F.e A γ * ∑ l, F.Γ l δ γ * F.P l B C =
      ∑ l, (∑ γ, F.Γ l δ γ * F.e A γ) * F.P l B C := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun γ _ => by ring
  have e : ∑ γ, (F.de δ A γ * F.P γ B C + F.e A γ * (ipg F.g (F.NNe B δ γ) (F.e C) +
      ∑ l, F.Γ l δ γ * F.P l B C + ipg F.g (F.Ne B γ) (F.Ne C δ))) =
      ∑ γ, F.de δ A γ * F.P γ B C + ∑ γ, F.e A γ * ∑ l, F.Γ l δ γ * F.P l B C +
        ∑ γ, F.e A γ * (ipg F.g (F.NNe B δ γ) (F.e C) + ipg F.g (F.Ne B γ) (F.Ne C δ)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun γ _ => by ring
  rw [e, h, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold Ne cv1
  ring

/-- The `∇∇` part of the frame derivative. -/
def T (D A B C : ι) : ℝ := ∑ δ, ∑ γ, F.e D δ * F.e A γ * ipg F.g (F.NNe B δ γ) (F.e C)

/-- **The frame derivatives of the connection coefficients**:
`e_D(G_{ABC}) = Σ_E ε_E G_{DAE}G_{EBC} + T_{DABC} + Σ_W ε_W G_{ABW}G_{DCW}`. -/
theorem dG_eq (D A B C : ι) :
    F.dG D A B C = ∑ E, F.ε E * F.G D A E * F.G E B C + F.T D A B C +
      ∑ W, F.ε W * F.G A B W * F.G D C W := by
  unfold dG
  simp only [F.dGc_eq, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ δ, F.e D δ * ∑ γ, F.Ne A δ γ * F.P γ B C =
      ∑ E, F.ε E * F.G D A E * F.G E B C := by
    have : ∑ δ, F.e D δ * ∑ γ, F.Ne A δ γ * F.P γ B C =
        ∑ γ, (∑ δ, F.e D δ * F.Ne A δ γ) * F.P γ B C := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => by ring
    rw [this]
    simp only [F.Ne_expand, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [show F.G E B C = ∑ γ, F.e E γ * F.P γ B C from rfl, Finset.mul_sum]
    exact Finset.sum_congr rfl fun γ _ => by ring
  have h2 : ∑ δ, F.e D δ * ∑ γ, F.e A γ * ipg F.g (F.NNe B δ γ) (F.e C) = F.T D A B C := by
    unfold T
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun γ _ => by ring
  have h3 : ∑ δ, F.e D δ * ∑ γ, F.e A γ * ipg F.g (F.Ne B γ) (F.Ne C δ) =
      ∑ W, F.ε W * F.G A B W * F.G D C W := by
    have : ∑ δ, F.e D δ * ∑ γ, F.e A γ * ipg F.g (F.Ne B γ) (F.Ne C δ) =
        ∑ γ, F.e A γ * ipg F.g (F.Ne B γ) (fun ν => ∑ δ, F.e D δ * F.Ne C δ ν) := by
      simp only [ipg_sum_right, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => by ring
    rw [this]
    have e2 : (fun ν => ∑ δ, F.e D δ * F.Ne C δ ν) =
        fun ν => ∑ W, (F.ε W * F.G D C W) * F.e W ν := by
      funext ν; rw [F.Ne_expand]
    rw [e2]
    simp only [ipg_sum_right, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun W _ => ?_
    rw [show F.G A B W = ∑ γ, F.e A γ * ipg F.g (F.Ne B γ) (F.e W) from rfl, Finset.mul_sum,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun γ _ => by ring
  rw [h1, h2, h3]
  ring

end FrameJet

/-! ### The frame Riemann tensor -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The frame Riemann tensor formula of `SpinorProlongation.LCJet.Rm`, for arbitrary
coefficients `G` and frame derivatives `dG`. -/
def rawRm (ε : ι → ℝ) (G : ι → ι → ι → ℝ) (dG : ι → ι → ι → ι → ℝ) (a b x y : ι) : ℝ :=
  dG a b x y - dG b a x y + ∑ z, ε z * (G b x z * G a z y - G a x z * G b z y) -
    ∑ e, lcΛ ε G a b e * G e x y

namespace FrameJet

variable (F : FrameJet n ι)

/-- **The frame Riemann tensor is the coordinate Riemann tensor in the frame**:
`Rm_{abxy} = Σ_{δγ} e_a{}^δe_b{}^γ g(R(∂_δ, ∂_γ)e_x, e_y)`,
`R(∂_δ, ∂_γ)e_x = R^μ{}_{σδγ}e_x{}^σ∂_μ`. -/
theorem rawRm_eq (a b x y : ι) :
    rawRm F.ε F.G F.dG a b x y = ∑ δ, ∑ γ, F.e a δ * F.e b γ *
      ipg F.g (fun μ => ∑ σ, rie F.Γ F.dΓ μ σ δ γ * F.e x σ) (F.e y) := by
  have hT : F.T a b x y - F.T b a x y = ∑ δ, ∑ γ, F.e a δ * F.e b γ *
      ipg F.g (fun μ => ∑ σ, rie F.Γ F.dΓ μ σ δ γ * F.e x σ) (F.e y) := by
    unfold T
    have hsw : ∑ δ, ∑ γ, F.e b δ * F.e a γ * ipg F.g (F.NNe x δ γ) (F.e y) =
        ∑ δ, ∑ γ, F.e a δ * F.e b γ * ipg F.g (F.NNe x γ δ) (F.e y) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun γ _ => by ring
    rw [hsw, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← mul_sub]
    congr 1
    have hc : (fun μ => ∑ σ, rie F.Γ F.dΓ μ σ δ γ * F.e x σ) =
        fun μ => F.NNe x δ γ μ + (-1) * F.NNe x γ δ μ := by
      funext μ
      rw [← cv2_comm F.dΓ (F.e x) (fun γ μ => F.de γ x μ) F.Γ_symm
        (fun δ γ μ => F.dde_symm δ γ x μ) δ γ μ]
      unfold NNe; ring
    rw [hc, ipg_add_left]
    have : ipg F.g (fun μ => (-1) * F.NNe x γ δ μ) (F.e y) =
        (-1) * ipg F.g (F.NNe x γ δ) (F.e y) := by
      have := ipg_sum_left (Finset.univ : Finset Unit) F.g (fun _ => -1)
        (fun _ => F.NNe x γ δ) (F.e y)
      simpa using this
    rw [this]; ring
  unfold rawRm lcΛ lcΓ
  rw [F.dG_eq, F.dG_eq, ← hT]
  have ha1 : ∀ W, F.G a y W = -F.G a W y := fun W => by rw [F.G_anti]
  have hb1 : ∀ W, F.G b y W = -F.G b W y := fun W => by rw [F.G_anti]
  simp only [ha1, hb1]
  have e3 : ∑ z, F.ε z * (F.G b x z * F.G a z y - F.G a x z * F.G b z y) =
      ∑ W, F.ε W * F.G b x W * F.G a W y - ∑ W, F.ε W * F.G a x W * F.G b W y := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  have e4 : ∑ E, (F.ε E * F.G a b E - F.ε E * F.G b a E) * F.G E x y =
      ∑ E, F.ε E * F.G a b E * F.G E x y - ∑ E, F.ε E * F.G b a E * F.G E x y := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun E _ => by ring
  have e5 : ∑ W, F.ε W * F.G b x W * -F.G a W y = -∑ W, F.ε W * F.G b x W * F.G a W y := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun W _ => by ring
  have e6 : ∑ W, F.ε W * F.G a x W * -F.G b W y = -∑ W, F.ε W * F.G a x W * F.G b W y := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun W _ => by ring
  rw [e3, e4, e5, e6]
  ring

end FrameJet

/-! ### Metric compatibility of the frame derivatives -/

theorem dipg_comm (g : n → n → ℝ) (hg : ∀ a b, g a b = g b a) (dg : n → n → n → ℝ)
    (δ : n) (hdg : ∀ a b, dg δ a b = dg δ b a) (X : n → ℝ) (dX : n → n → ℝ) (Y : n → ℝ)
    (dY : n → n → ℝ) : dipg g dg X dX Y dY δ = dipg g dg Y dY X dX δ := by
  rw [dipg_split, dipg_split, ipg_comm (dg δ) hdg X, ipg_comm g hg (dX δ), ipg_comm g hg X]
  ring

namespace FrameJet

variable (F : FrameJet n ι)

/-- **`e_D(G_{ABC}) = -e_D(G_{ACB})`** (the derivative of metric compatibility, from the second
derivative of orthonormality and the second-order compatibility of the Levi-Civita jets). -/
theorem dG_anti (D A B C : ι) : F.dG D A C B = -F.dG D A B C := by
  have hP : ∀ γ, F.P γ B C + F.P γ C B = 0 := fun γ => by
    rw [← F.dipg_frame γ B C]; exact F.orth1 γ B C
  have hdP : ∀ δ γ, F.dP δ γ B C + F.dP δ γ C B = 0 := by
    intro δ γ
    have h := F.orth2 δ γ B C
    rw [ddipg_eq F.g F.g_symm F.dg F.dg_symm F.ddg F.Γ F.dΓ F.compat F.compat2] at h
    rw [dipg_comm F.g F.g_symm F.dg δ (fun a b => F.dg_symm δ a b) (F.e B)] at h
    exact h
  unfold dG
  rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun δ _ => ?_
  rw [← mul_add]
  unfold dGc
  rw [← Finset.sum_add_distrib]
  have : ∑ γ, (F.de δ A γ * F.P γ C B + F.e A γ * F.dP δ γ C B +
      (F.de δ A γ * F.P γ B C + F.e A γ * F.dP δ γ B C)) = 0 := by
    refine Finset.sum_eq_zero fun γ _ => ?_
    have h1 := hP γ
    have h2 := hdP δ γ
    linear_combination F.de δ A γ * h1 + F.e A γ * h2
  rw [this, mul_zero]

end FrameJet

/-! ### The Jacobi identity of the frame -/

/-- The Jacobi expression of `SpinorProlongation.LCJet.jacobi`. -/
def jacExpr (ε : ι → ℝ) (G : ι → ι → ι → ℝ) (dG : ι → ι → ι → ι → ℝ) (a b c f : ι) : ℝ :=
  (∑ d, lcΛ ε G a b d * lcΛ ε G d c f - lcdΛ ε dG c a b f) +
    (∑ d, lcΛ ε G b c d * lcΛ ε G d a f - lcdΛ ε dG a b c f) +
      (∑ d, lcΛ ε G c a d * lcΛ ε G d b f - lcdΛ ε dG b c a f)

theorem rawRm_eq_sum (ε : ι → ℝ) (G : ι → ι → ι → ℝ) (dG : ι → ι → ι → ι → ℝ) (a b c f : ι) :
    rawRm ε G dG a b c f = dG a b c f - dG b a c f +
      ∑ z, (ε z * (G b c z * G a z f - G a c z * G b z f) - lcΛ ε G a b z * G z c f) := by
  unfold rawRm
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]

/-- **The cyclic sum of the frame Riemann tensor is the Jacobi expression**:
`Rm_{abcf} + Rm_{bcaf} + Rm_{cabf} = -ε_f · jac_{abcf}` (pure algebra, `ε_f² = 1`). -/
theorem rawRm_cyc (ε : ι → ℝ) (G : ι → ι → ι → ℝ) (dG : ι → ι → ι → ι → ℝ) (a b c f : ι)
    (hf : ε f * ε f = 1) :
    rawRm ε G dG a b c f + rawRm ε G dG b c a f + rawRm ε G dG c a b f =
      -(ε f) * jacExpr ε G dG a b c f := by
  rw [rawRm_eq_sum, rawRm_eq_sum, rawRm_eq_sum]
  have hpt : ∀ z,
      (ε z * (G b c z * G a z f - G a c z * G b z f) - lcΛ ε G a b z * G z c f) +
        (ε z * (G c a z * G b z f - G b a z * G c z f) - lcΛ ε G b c z * G z a f) +
        (ε z * (G a b z * G c z f - G c b z * G a z f) - lcΛ ε G c a z * G z b f) =
      -(ε f * (lcΛ ε G a b z * lcΛ ε G z c f + lcΛ ε G b c z * lcΛ ε G z a f +
        lcΛ ε G c a z * lcΛ ε G z b f)) := by
    intro z
    unfold lcΛ lcΓ
    linear_combination (ε z * ((G a b z - G b a z) * (G z c f - G c z f) +
      (G b c z - G c b z) * (G z a f - G a z f) +
      (G c a z - G a c z) * (G z b f - G b z f))) * hf
  have hsum : ∑ z, (ε z * (G b c z * G a z f - G a c z * G b z f) -
          lcΛ ε G a b z * G z c f) +
        ∑ z, (ε z * (G c a z * G b z f - G b a z * G c z f) - lcΛ ε G b c z * G z a f) +
        ∑ z, (ε z * (G a b z * G c z f - G c b z * G a z f) - lcΛ ε G c a z * G z b f) =
      -(ε f * (∑ d, lcΛ ε G a b d * lcΛ ε G d c f + ∑ d, lcΛ ε G b c d * lcΛ ε G d a f +
        ∑ d, lcΛ ε G c a d * lcΛ ε G d b f)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => hpt z
  unfold jacExpr lcdΛ
  linear_combination hsum - (dG a b c f - dG b a c f + dG b c a f - dG c b a f + dG c a b f -
    dG a c b f) * hf

/-- **First Bianchi identity of a symmetric connection jet**:
`R^μ{}_{σδγ} + R^μ{}_{δγσ} + R^μ{}_{γσδ} = 0`. -/
theorem rie_bianchi {Γ : n → n → n → ℝ} {dΓ : n → n → n → n → ℝ}
    (hΓ : ∀ l μ ν, Γ l μ ν = Γ l ν μ) (hdΓ : ∀ δ l μ ν, dΓ δ l μ ν = dΓ δ l ν μ)
    (μ σ δ γ : n) : rie Γ dΓ μ σ δ γ + rie Γ dΓ μ δ γ σ + rie Γ dΓ μ γ σ δ = 0 := by
  unfold rie
  have hk : ∑ κ, (Γ μ δ κ * Γ κ γ σ - Γ μ γ κ * Γ κ δ σ) +
      ∑ κ, (Γ μ γ κ * Γ κ σ δ - Γ μ σ κ * Γ κ γ δ) +
      ∑ κ, (Γ μ σ κ * Γ κ δ γ - Γ μ δ κ * Γ κ σ γ) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun κ _ => ?_
    rw [hΓ κ σ δ, hΓ κ γ δ, hΓ κ σ γ]; ring
  have h1 := hdΓ γ μ σ δ
  have h2 := hdΓ σ μ δ γ
  have h3 := hdΓ δ μ σ γ
  linarith

/-- Cyclic relabelling of a triple sum. -/
theorem sum3_cyc {M : Type*} [AddCommMonoid M] (H : n → n → n → M) :
    ∑ δ, ∑ γ, ∑ σ, H δ γ σ = ∑ δ, ∑ γ, ∑ σ, H γ σ δ := by
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [Finset.sum_comm]

namespace FrameJet

variable (F : FrameJet n ι)

/-- `rawRm` with the frame vector `e_x` pulled out of the pairing. -/
theorem rawRm_eq' (a b x y : ι) :
    rawRm F.ε F.G F.dG a b x y = ∑ δ, ∑ γ, ∑ σ, F.e a δ * F.e b γ * F.e x σ *
      ipg F.g (fun μ => rie F.Γ F.dΓ μ σ δ γ) (F.e y) := by
  rw [F.rawRm_eq]
  refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun γ _ => ?_
  have : (fun μ => ∑ σ, rie F.Γ F.dΓ μ σ δ γ * F.e x σ) =
      fun μ => ∑ σ, F.e x σ * rie F.Γ F.dΓ μ σ δ γ := by
    funext μ; exact Finset.sum_congr rfl fun σ _ => by ring
  rw [this, ipg_sum_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- The cyclic sum of the frame Riemann tensor vanishes (coordinate first Bianchi identity). -/
theorem rawRm_cyc_zero (a b c f : ι) :
    rawRm F.ε F.G F.dG a b c f + rawRm F.ε F.G F.dG b c a f + rawRm F.ε F.G F.dG c a b f = 0 := by
  set K : n → n → n → ℝ := fun δ γ σ => ipg F.g (fun μ => rie F.Γ F.dΓ μ σ δ γ) (F.e f) with hK
  have hKc : ∀ δ γ σ, K δ γ σ + K γ σ δ + K σ δ γ = 0 := by
    intro δ γ σ
    simp only [hK]
    rw [← ipg_add_left, ← ipg_add_left]
    have : (fun μ => rie F.Γ F.dΓ μ σ δ γ + rie F.Γ F.dΓ μ δ γ σ + rie F.Γ F.dΓ μ γ σ δ) =
        fun _ => 0 := by
      funext μ; exact rie_bianchi F.Γ_symm F.dΓ_symm μ σ δ γ
    rw [this]; unfold ipg; simp
  rw [F.rawRm_eq', F.rawRm_eq', F.rawRm_eq']
  have e2 : ∑ δ, ∑ γ, ∑ σ, F.e b δ * F.e c γ * F.e a σ * K δ γ σ =
      ∑ δ, ∑ γ, ∑ σ, F.e a δ * F.e b γ * F.e c σ * K γ σ δ := by
    rw [sum3_cyc]
    exact Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun γ _ =>
      Finset.sum_congr rfl fun σ _ => by ring
  have e3 : ∑ δ, ∑ γ, ∑ σ, F.e c δ * F.e a γ * F.e b σ * K δ γ σ =
      ∑ δ, ∑ γ, ∑ σ, F.e a δ * F.e b γ * F.e c σ * K σ δ γ := by
    rw [sum3_cyc, sum3_cyc]
    exact Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun γ _ =>
      Finset.sum_congr rfl fun σ _ => by ring
  change ∑ δ, ∑ γ, ∑ σ, F.e a δ * F.e b γ * F.e c σ * K δ γ σ +
    ∑ δ, ∑ γ, ∑ σ, F.e b δ * F.e c γ * F.e a σ * K δ γ σ +
    ∑ δ, ∑ γ, ∑ σ, F.e c δ * F.e a γ * F.e b σ * K δ γ σ = 0
  rw [e2, e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun δ _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun γ _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have := hKc δ γ σ
  linear_combination (F.e a δ * F.e b γ * F.e c σ) * this

/-- **The Jacobi identity of the frame** in the form of `LCJet.jacobi`. -/
theorem jacobi (a b c f : ι) : jacExpr F.ε F.G F.dG a b c f = 0 := by
  have hf : F.ε f * F.ε f = 1 := by rw [← sq]; exact F.sign_sq f
  have h := rawRm_cyc F.ε F.G F.dG a b c f hf
  rw [F.rawRm_cyc_zero] at h
  have hne : F.ε f ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hf; exact zero_ne_one hf
  have : F.ε f * jacExpr F.ε F.G F.dG a b c f = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hne
  · exact h1

/-- **The coordinate commutator of frame vectors**: `[e_a, e_b]^μ = Σ_c Λ_{ab}{}^ce_c{}^μ`
(torsion-freeness of the Levi-Civita jets). -/
theorem bracket_eq (a b : ι) (μ : n) :
    ∑ δ, (F.e a δ * F.de δ b μ - F.e b δ * F.de δ a μ) =
      ∑ c, lcΛ F.ε F.G a b c * F.e c μ := by
  have h1 := F.Ne_expand a b μ
  have h2 := F.Ne_expand b a μ
  have e : ∑ c, lcΛ F.ε F.G a b c * F.e c μ =
      ∑ c, F.ε c * F.G a b c * F.e c μ - ∑ c, F.ε c * F.G b a c * F.e c μ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold lcΛ lcΓ; ring
  rw [e, ← h1, ← h2, ← Finset.sum_sub_distrib]
  unfold Ne cv1
  have hΓ : ∑ γ, F.e a γ * ∑ σ, F.Γ μ γ σ * F.e b σ = ∑ γ, F.e b γ * ∑ σ, F.Γ μ γ σ * F.e a σ := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun σ _ => by
      rw [F.Γ_symm μ σ γ]; ring
  have : ∑ x, (F.e a x * (F.de x b μ + ∑ σ, F.Γ μ x σ * F.e b σ) -
      F.e b x * (F.de x a μ + ∑ σ, F.Γ μ x σ * F.e a σ)) =
      ∑ δ, (F.e a δ * F.de δ b μ - F.e b δ * F.de δ a μ) +
        (∑ γ, F.e a γ * ∑ σ, F.Γ μ γ σ * F.e b σ - ∑ γ, F.e b γ * ∑ σ, F.Γ μ γ σ * F.e a σ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun δ _ => by ring
  rw [this, hΓ, sub_self, add_zero]

/-- The frame Ricci contraction of `rawRm` is the coordinate Ricci tensor in the order
`Ric(e_b, e_a)`. -/
theorem ricciOf_rawRm (a b : ι) :
    ricciOf F.ε (rawRm F.ε F.G F.dG) a b =
      ∑ γ, ∑ σ, F.e a γ * F.e b σ * ricci F.gi F.dg F.ddg σ γ := by
  unfold ricciOf
  simp only [F.rawRm_eq]
  set Y : n → n → n → ℝ := fun δ γ μ => ∑ σ, rie F.Γ F.dΓ μ σ δ γ * F.e b σ with hY
  have h1 : ∑ c, F.ε c * ∑ δ, ∑ γ, F.e c δ * F.e a γ * ipg F.g (Y δ γ) (F.e c) =
      ∑ δ, ∑ γ, F.e a γ * Y δ γ δ := by
    have : ∑ c, F.ε c * ∑ δ, ∑ γ, F.e c δ * F.e a γ * ipg F.g (Y δ γ) (F.e c) =
        ∑ δ, ∑ γ, F.e a γ * ∑ c, F.ε c * ipg F.g (Y δ γ) (F.e c) * F.e c δ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun c _ => by ring
    rw [this]
    refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun γ _ => ?_
    rw [← F.expand]
  rw [h1]
  have h2 : ∀ σ γ, ∑ δ, rie F.Γ F.dΓ δ σ δ γ = ricci F.gi F.dg F.ddg σ γ := by
    intro σ γ
    unfold ricci ricciJ rie
    rw [← Finset.sum_sub_distrib]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    change ∑ x, F.dΓ x x γ σ - ∑ x, F.dΓ γ x x σ + (∑ x, ∑ κ, F.Γ x x κ * F.Γ κ γ σ -
      ∑ x, ∑ κ, F.Γ x γ κ * F.Γ κ x σ) = _
    have a1 : ∑ x, F.dΓ x x γ σ = ∑ x, F.dΓ x x σ γ :=
      Finset.sum_congr rfl fun x _ => F.dΓ_symm x x γ σ
    have a2 : ∑ x, F.dΓ γ x x σ = ∑ x, F.dΓ γ x σ x :=
      Finset.sum_congr rfl fun x _ => F.dΓ_symm γ x x σ
    have a3 : ∑ x, ∑ κ, F.Γ x x κ * F.Γ κ γ σ = ∑ x, ∑ κ, F.Γ x x κ * F.Γ κ σ γ :=
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun κ _ => by rw [F.Γ_symm κ γ σ]
    have a4 : ∑ x, ∑ κ, F.Γ x γ κ * F.Γ κ x σ = ∑ x, ∑ κ, F.Γ x γ κ * F.Γ κ σ x :=
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun κ _ => by rw [F.Γ_symm κ x σ]
    rw [a1, a2, a3, a4]
    simp only [FrameJet.dΓ, FrameJet.Γ]
    ring
  have h3 : ∑ δ, ∑ γ, F.e a γ * Y δ γ δ = ∑ γ, ∑ σ, F.e a γ * F.e b σ *
      ∑ δ, rie F.Γ F.dΓ δ σ δ γ := by
    simp only [hY, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun δ _ => by ring
  rw [h3]
  simp only [h2]

end FrameJet

/-! ### The frame jet as a Levi-Civita spin-connection jet -/

section LC

variable {A : Type*} [Ring A] [Algebra ℝ A]

namespace FrameJet

variable (F : FrameJet n ι)

/-- **The frame jet defines the jets of the twisted Levi-Civita spin connection**
(`SpinorProlongation.LCJet`) for a Clifford frame of the same signature and a gauge potential
`ρ(A_μ)` (with derivative jets `ρ(∂_δA_μ)`) commuting with Clifford multiplication:
`G = FrameJet.G`, `dG = FrameJet.dG`, `ρ_a = e_a{}^μρ(A_μ)`, `e_D(ρ_a)` by the product rule. -/
def toLCJet (Fr : CliffordFrame ι A) (hε : Fr.ε = F.ε) (ρA : n → A) (dρA : n → n → A)
    (hcomm : ∀ μ b, ρA μ * Fr.c b = Fr.c b * ρA μ) : LCJet Fr where
  G := F.G
  dG := F.dG
  ρ := fun a => ∑ μ, F.e a μ • ρA μ
  dρ := fun D a => ∑ δ, F.e D δ • ∑ μ, (F.de δ a μ • ρA μ + F.e a μ • dρA δ μ)
  G_anti := F.G_anti
  dG_anti := F.dG_anti
  ρ_comm := by
    intro a b
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [smul_mul_assoc, hcomm, mul_smul_comm]
  jacobi := by
    intro a b c f
    have := F.jacobi a b c f
    rw [hε]
    exact this

variable (Fr : CliffordFrame ι A) (hε : Fr.ε = F.ε) (ρA : n → A) (dρA : n → n → A)
  (hcomm : ∀ μ b, ρA μ * Fr.c b = Fr.c b * ρA μ)

theorem toLCJet_Rm (a b x y : ι) :
    (F.toLCJet Fr hε ρA dρA hcomm).Rm a b x y = rawRm F.ε F.G F.dG a b x y := by
  show rawRm Fr.ε F.G F.dG a b x y = _
  rw [hε]

/-- **The frame Ricci tensor of the twisted Levi-Civita connection is the coordinate Ricci tensor
of the metric 2-jet**: `Ric_{ab} = Σ_c ε_c Rm_{cabc} = e_a{}^μe_b{}^ν R_{μν}`. -/
theorem ricciOf_eq (a b : ι) :
    ricciOf Fr.ε (F.toLCJet Fr hε ρA dρA hcomm).Rm a b =
      ∑ μ, ∑ ν, F.e a μ * F.e b ν * ricci F.gi F.dg F.ddg μ ν := by
  set J := F.toLCJet Fr hε ρA dρA hcomm
  have hsym : ricciOf Fr.ε J.Rm a b = ricciOf Fr.ε J.Rm b a := by
    unfold ricciOf
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [J.Rm_pair c a b c, J.Rm_anti₂ c b c a, J.Rm_anti₁ c b a c, neg_neg]
  have hR : J.Rm = rawRm F.ε F.G F.dG := by
    funext a b x y; exact F.toLCJet_Rm Fr hε ρA dρA hcomm a b x y
  rw [hsym, hR, hε, F.ricciOf_rawRm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

/-- **`eq:trace-reversal-residual` in the moving frame**: in four dimensions, for every stress
`T` and constants `Λ, κ`, with `𝓔 = G + Λg - κT`,
`Ric_{ab} = κ T^{tr}(e_a, e_b) + Λ ε_aδ_{ab} + 𝓔^{tr}(e_a, e_b)`. -/
theorem frame_trace_reversal (hcard : Fintype.card n = 4) (T : n → n → ℝ) (Λ κ : ℝ) (a b : ι) :
    ricciOf Fr.ε (F.toLCJet Fr hε ρA dρA hcomm).Rm a b =
      κ * ∑ μ, ∑ ν, F.e a μ * F.e b ν * traceRev F.g F.gi T μ ν +
        Λ * (if a = b then F.ε a else 0) +
        ∑ μ, ∑ ν, F.e a μ * F.e b ν * traceRev F.g F.gi
          (fun x y => einstein F.g F.gi F.dg F.ddg x y + Λ * F.g x y - κ * T x y) μ ν := by
  rw [F.ricciOf_eq Fr hε ρA dρA hcomm]
  simp only [ricci_trace_reversal F.g F.gi F.dg F.ddg F.gi_symm F.hinv hcard T Λ κ]
  have ho : ∑ μ, ∑ ν, F.e a μ * F.e b ν * (Λ * F.g μ ν) = Λ * (if a = b then F.ε a else 0) := by
    rw [← F.orth a b]
    unfold ipg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  rw [← ho]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

/-- The frame derivative of a frame contraction `e_b{}^μX_μ` (product rule) splits into the
frame-derivative part and the derivative-jet part. -/
theorem frame_deriv_split {M : Type*} [AddCommGroup M] [Module ℝ M] (a b : ι) (X : n → M)
    (dX : n → n → M) :
    (∑ δ, F.e a δ • ∑ μ, (F.de δ b μ • X μ + F.e b μ • dX δ μ)) =
      ∑ μ, (∑ δ, F.e a δ * F.de δ b μ) • X μ + ∑ μ, ∑ ν, (F.e a μ * F.e b ν) • dX μ ν := by
  simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib, smul_smul, Finset.sum_smul]
  congr 1
  exact Finset.sum_comm

/-- The antisymmetrized frame derivative of a frame contraction. -/
theorem frame_deriv_anti {M : Type*} [AddCommGroup M] [Module ℝ M] (a b : ι) (X : n → M)
    (dX : n → n → M) :
    (∑ δ, F.e a δ • ∑ μ, (F.de δ b μ • X μ + F.e b μ • dX δ μ)) -
        (∑ δ, F.e b δ • ∑ μ, (F.de δ a μ • X μ + F.e a μ • dX δ μ)) =
      (∑ c, lcΛ F.ε F.G a b c • ∑ μ, F.e c μ • X μ) +
        ∑ μ, ∑ ν, (F.e a μ * F.e b ν) • (dX μ ν - dX ν μ) := by
  rw [F.frame_deriv_split a b, F.frame_deriv_split b a]
  have hbr : ∑ c, lcΛ F.ε F.G a b c • ∑ μ, F.e c μ • X μ =
      ∑ μ, (∑ δ, F.e a δ * F.de δ b μ) • X μ - ∑ μ, (∑ δ, F.e b δ * F.de δ a μ) • X μ := by
    rw [← Finset.sum_sub_distrib]
    have : ∀ μ, (∑ δ, F.e a δ * F.de δ b μ) • X μ - (∑ δ, F.e b δ * F.de δ a μ) • X μ =
        (∑ c, lcΛ F.ε F.G a b c * F.e c μ) • X μ := by
      intro μ
      rw [← F.bracket_eq, ← sub_smul, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun μ _ => this μ]
    simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  have hsw : ∑ μ, ∑ ν, (F.e b μ * F.e a ν) • dX μ ν = ∑ μ, ∑ ν, (F.e a μ * F.e b ν) • dX ν μ := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by rw [mul_comm]
  have hd : ∑ μ, ∑ ν, (F.e a μ * F.e b ν) • (dX μ ν - dX ν μ) =
      ∑ μ, ∑ ν, (F.e a μ * F.e b ν) • dX μ ν - ∑ μ, ∑ ν, (F.e a μ * F.e b ν) • dX ν μ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun μ _ => by rw [← Finset.sum_sub_distrib]; simp only [smul_sub]
  rw [hbr, hsw, hd]
  abel

/-- **The frame gauge curvature is the frame components of the coordinate curvature**:
`ρ(F)_{ab} = e_a{}^μe_b{}^ν(ρ(∂_μA_ν) - ρ(∂_νA_μ) + [ρ(A_μ), ρ(A_ν)])`. -/
theorem frameF_eq (a b : ι) :
    (F.toLCJet Fr hε ρA dρA hcomm).F a b = ∑ μ, ∑ ν, (F.e a μ * F.e b ν) •
      (dρA μ ν - dρA ν μ + (ρA μ * ρA ν - ρA ν * ρA μ)) := by
  show (∑ δ, F.e a δ • ∑ μ, (F.de δ b μ • ρA μ + F.e b μ • dρA δ μ)) -
      (∑ δ, F.e b δ • ∑ μ, (F.de δ a μ • ρA μ + F.e a μ • dρA δ μ)) +
      ((∑ μ, F.e a μ • ρA μ) * (∑ μ, F.e b μ • ρA μ) -
        (∑ μ, F.e b μ • ρA μ) * (∑ μ, F.e a μ • ρA μ)) -
      ∑ c, lcΛ Fr.ε F.G a b c • ∑ μ, F.e c μ • ρA μ = _
  rw [hε, F.frame_deriv_anti a b ρA dρA]
  have hm : ∀ x y : ι, (∑ μ, F.e x μ • ρA μ) * (∑ μ, F.e y μ • ρA μ) =
      ∑ μ, ∑ ν, (F.e x μ * F.e y ν) • (ρA μ * ρA ν) := by
    intro x y
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hm2 : ∑ μ, ∑ ν, (F.e b μ * F.e a ν) • (ρA μ * ρA ν) =
      ∑ μ, ∑ ν, (F.e a μ * F.e b ν) • (ρA ν * ρA μ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by rw [mul_comm]
  rw [hm, hm, hm2]
  simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end FrameJet

/-- **The frame commutator relation** of `prop:spinor-prolongation` for frame jets computed from
coordinate jets: with `dψ_a = e_a{}^γ∂_γΨ` and `ddψ_{ab} = e_a{}^δ∂_δ(e_b{}^γ∂_γΨ)`,
`ddψ_{ab} - ddψ_{ba} = Σ_c Λ_{ab}{}^c dψ_c`. -/
theorem FrameJet.hψ_frame {V : Type*} [AddCommGroup V] [Module ℝ V] (F : FrameJet n ι)
    (cψ : n → V) (ccψ : n → n → V) (hs : ∀ δ γ, ccψ δ γ = ccψ γ δ) (a b : ι) :
    (∑ δ, F.e a δ • ∑ γ, (F.de δ b γ • cψ γ + F.e b γ • ccψ δ γ)) -
        (∑ δ, F.e b δ • ∑ γ, (F.de δ a γ • cψ γ + F.e a γ • ccψ δ γ)) =
      ∑ c, lcΛ F.ε F.G a b c • ∑ γ, F.e c γ • cψ γ := by
  rw [F.frame_deriv_anti a b cψ ccψ]
  have : ∑ μ, ∑ ν, (F.e a μ * F.e b ν) • (ccψ μ ν - ccψ ν μ) = 0 :=
    Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => by rw [hs, sub_self, smul_zero]
  rw [this, add_zero]

end LC

end

end RenewalGeometry.FrameCurvature
