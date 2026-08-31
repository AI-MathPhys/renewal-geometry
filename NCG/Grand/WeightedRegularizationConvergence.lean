import NCG.Grand.CriticalWeightedResponseLocality

/-!
# Weighted regularization convergence

A form-compatible regularization difference is itself a weighted holomorphic
packet.  Applying the Banach-valued Cauchy estimate to that difference gives
quantitative convergence of the first and mixed responses, including every
fixed collar leakage.  A final continuity lemma transports their leakage
Grams.
-/

open Filter Set

noncomputable section

namespace NCG
namespace WeightedRegularizationConvergence

open CriticalWeightedResponseLocality

universe u v w

variable {Q : Type u} [Nonempty Q]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F]
variable {Region : Type w}

/-- The weighted supremum is nonnegative, including in the unbounded case. -/
theorem weightedNorm_nonneg (T : Q → F) : 0 ≤ weightedNorm T := by
  exact Real.sSup_nonneg (Set.forall_mem_range.mpr fun q => norm_nonneg (T q))

/-- Quantitative weighted Cauchy control of a regularization-difference packet. -/
theorem regularization_defect_bounds
    (D : ℕ → Packet Q F Region) (eps : ℕ → ℝ)
    {rhoZ rhoW : ℝ} (hrhoZ : 0 < rhoZ) (hrhoW : 0 < rhoW)
    (holo : ∀ n, HolomorphicOnClosedPolydisc (D n) rhoZ rhoW)
    (hboundary : ∀ n, HasWeightedCollar (D n) rhoZ rhoW (eps n) 0 0) :
    ∀ n,
      weightedNorm (fun q => (D n).weight q (D n).firstResponse)
          ≤ eps n / rhoZ ∧
      weightedNorm (fun q => (D n).weight q (D n).pairResponse)
          ≤ eps n / (rhoZ * rhoW) := by
  intro n
  have h := critical_weighted_bounds (D n) hrhoZ hrhoW (holo n) (hboundary n)
  simpa using h

/-- Boundary convergence on the command circles forces weighted convergence of
both critical response defects. -/
theorem regularization_first_pair_tendsto
    (D : ℕ → Packet Q F Region) (eps : ℕ → ℝ)
    {rhoZ rhoW : ℝ} (hrhoZ : 0 < rhoZ) (hrhoW : 0 < rhoW)
    (heps : ∀ n, 0 ≤ eps n)
    (hzero : Tendsto eps atTop (nhds 0))
    (holo : ∀ n, HolomorphicOnClosedPolydisc (D n) rhoZ rhoW)
    (hboundary : ∀ n, HasWeightedCollar (D n) rhoZ rhoW (eps n) 0 0) :
    Tendsto
        (fun n => weightedNorm
          (fun q => (D n).weight q (D n).firstResponse))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => weightedNorm
          (fun q => (D n).weight q (D n).pairResponse))
        atTop (nhds 0) := by
  have hb := regularization_defect_bounds D eps hrhoZ hrhoW holo hboundary
  constructor
  · refine squeeze_zero'
      (Eventually.of_forall fun n => weightedNorm_nonneg
        (fun q => (D n).weight q (D n).firstResponse))
      (Eventually.of_forall fun n => (hb n).1) ?_
    simpa [div_eq_mul_inv] using hzero.mul_const rhoZ⁻¹
  · refine squeeze_zero'
      (Eventually.of_forall fun n => weightedNorm_nonneg
        (fun q => (D n).weight q (D n).pairResponse))
      (Eventually.of_forall fun n => (hb n).2) ?_
    simpa [div_eq_mul_inv] using hzero.mul_const (rhoZ * rhoW)⁻¹

/-- The same boundary convergence controls every fixed physical collar
leakage of the first and pair response defects. -/
theorem regularization_collar_tendsto
    (D : ℕ → Packet Q F Region) (eps : ℕ → ℝ)
    {rhoZ rhoW mu : ℝ} (hrhoZ : 0 < rhoZ) (hrhoW : 0 < rhoW)
    (hmu : 0 ≤ mu) (heps : ∀ n, 0 ≤ eps n)
    (hzero : Tendsto eps atTop (nhds 0))
    (holo : ∀ n, HolomorphicOnClosedPolydisc (D n) rhoZ rhoW)
    (hboundary : ∀ n, HasWeightedCollar (D n) rhoZ rhoW (eps n) 0 0)
    (X Y : Region)
    (hdistance : ∀ n, (D n).distance X Y = (D 0).distance X Y) :
    Tendsto (fun n => ‖(D n).compress X Y (D n).firstResponse‖)
        atTop (nhds 0) ∧
      Tendsto (fun n => ‖(D n).compress X Y (D n).pairResponse‖)
        atTop (nhds 0) := by
  have hb : ∀ n,
      ‖(D n).compress X Y (D n).firstResponse‖ ≤
          (eps n / rhoZ) * Real.exp (-mu * (D n).distance X Y) ∧
      ‖(D n).compress X Y (D n).pairResponse‖ ≤
          (eps n / (rhoZ * rhoW)) *
            Real.exp (-mu * (D n).distance X Y) := by
    intro n
    have h := critical_weighted_first_pair_locality (D n)
      hrhoZ hrhoW hmu (holo n) (hboundary n) X Y
    constructor
    · convert h.2.2.1 using 1 <;> ring
    · convert h.2.2.2 using 1 <;> ring
  let C := Real.exp (-mu * (D 0).distance X Y)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have huFirst : ∀ n,
      ‖(D n).compress X Y (D n).firstResponse‖
        ≤ (eps n / rhoZ) * C := by
    intro n
    calc
      ‖(D n).compress X Y (D n).firstResponse‖
          ≤ (eps n / rhoZ) *
              Real.exp (-mu * (D n).distance X Y) := (hb n).1
      _ = (eps n / rhoZ) * C := by rw [hdistance n]
  have huPair : ∀ n,
      ‖(D n).compress X Y (D n).pairResponse‖
        ≤ (eps n / (rhoZ * rhoW)) * C := by
    intro n
    calc
      ‖(D n).compress X Y (D n).pairResponse‖
          ≤ (eps n / (rhoZ * rhoW)) *
              Real.exp (-mu * (D n).distance X Y) := (hb n).2
      _ = (eps n / (rhoZ * rhoW)) * C := by rw [hdistance n]
  constructor
  · refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.of_forall huFirst) ?_
    have hscaled := (hzero.mul_const rhoZ⁻¹).mul_const C
    simpa [div_eq_mul_inv, mul_assoc] using hscaled
  · refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.of_forall huPair) ?_
    have hscaled := (hzero.mul_const (rhoZ * rhoW)⁻¹).mul_const C
    simpa [div_eq_mul_inv, mul_assoc] using hscaled

section Gram

variable {A : Type*} [NormedRing A] [StarRing A] [ContinuousStar A]

/-- Norm convergence of collar leakages transports their quadratic Grams. -/
theorem gram_tendsto {ι : Type*} {l : Filter ι} (a : ι → A) (b : A)
    (h : Tendsto a l (nhds b)) :
    Tendsto (fun i => star (a i) * a i) l (nhds (star b * b)) :=
  h.star.mul h

end Gram

end WeightedRegularizationConvergence
end NCG
