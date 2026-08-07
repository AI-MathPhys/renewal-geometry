/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Zeno collapse and the growing protected chronology
  (`cth:renewal-Zeno` and `cth:growing-ledger-gap`,
  Gran-Tensor manuscript)

* `renewal_zeno`: a fixed per-cycle contraction `q < 1` on the
  transient sector collapses in the dense limit: along any
  cutoff sequence `τ_j ↓ 0` (with `t > 0` fixed), the cycle
  count `⌊t/τ_j⌋` diverges and `q^{⌊t/τ_j⌋} → 0` — the
  limiting family is the equilibrium projection for every
  `t > 0`, not a nontrivial strongly continuous continuum
  evolution; a finite dense rate needs an order-`τ` deficit.

* `growing_ledger_gap`: for the nilpotent history-copy shift
  on `ℝᴺ` and any physical metric `G` with
  `m‖x‖² ≤ ⟨x,Gx⟩ ≤ M‖x‖²`, a uniform `G`-contraction factor
  `q` for the shift obeys the boxed obstruction
  `m ≤ q^{2(N-1)}·M` (`q^{N-1} ≥ κ^{-1/2}` for the condition
  number `κ = M/m`, hence `liminf q_N ≥ 1` under bounded
  condition numbers): no uniformly conditioned metric gives
  the growing point-readable ledger a noncollapsing transient
  contraction gap.
-/

open Matrix

namespace NCG

/-- `cth:renewal-Zeno`. -/
theorem renewal_zeno (q t : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ht : 0 < t) (τ : ℕ → ℝ) (hpos : ∀ j, 0 < τ j)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun j => q ^ ⌊t / τ j⌋₊)
      Filter.atTop (nhds 0) := by
  have hdiv : Filter.Tendsto (fun j => t / τ j)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro C
    have hden : (0 : ℝ) < t / max C 1 := by
      have h1 : (0 : ℝ) < max C 1 :=
        lt_of_lt_of_le one_pos (le_max_right C 1)
      positivity
    have hev := hτ.eventually_lt_const hden
    filter_upwards [hev] with j hj
    have hτj := hpos j
    calc C ≤ max C 1 := le_max_left C 1
      _ = t / (t / max C 1) := by
          field_simp
      _ ≤ t / τ j := by
          gcongr
  have hfloor : Filter.Tendsto (fun x : ℝ => ⌊x⌋₊)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro C
    filter_upwards [Filter.eventually_ge_atTop (C : ℝ)]
      with x hx
    exact Nat.le_floor hx
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq0
    hq1).comp (hfloor.comp hdiv)

/-- The nilpotent history-copy shift `e_j ↦ e_{j+1}`. -/
def ledgerShift (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- `cth:growing-ledger-gap`. -/
theorem growing_ledger_gap (N : ℕ) (hN : 1 ≤ N)
    (G : Matrix (Fin N) (Fin N) ℝ) (m M q : ℝ)
    (hlow : ∀ x : Fin N → ℝ, m * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G *ᵥ x))
    (hupp : ∀ x : Fin N → ℝ, x ⬝ᵥ (G *ᵥ x) ≤ M * (x ⬝ᵥ x))
    (hcontr : ∀ x : Fin N → ℝ,
      (ledgerShift N *ᵥ x) ⬝ᵥ (G *ᵥ (ledgerShift N *ᵥ x))
        ≤ q ^ 2 * (x ⬝ᵥ (G *ᵥ x))) :
    m ≤ q ^ (2 * (N - 1)) * M := by
  have h0 : 0 < N := hN
  -- unit dot products of ledger cells
  have hdot : ∀ a : Fin N,
      (Pi.single a (1 : ℝ)) ⬝ᵥ Pi.single a 1 = 1 := by
    intro a
    simp [dotProduct, Pi.single_apply]
  -- the shift advances ledger cells
  have hstep : ∀ (k : ℕ) (hk : k + 1 < N),
      ledgerShift N *ᵥ
        Pi.single (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin N) 1
        = Pi.single (⟨k + 1, hk⟩ : Fin N) 1 := by
    intro k hk
    funext i
    simp only [ledgerShift, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Pi.single_apply]
    rw [Finset.sum_eq_single
      (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin N)]
    · simp [Fin.ext_iff]
    · intro b _ hb
      simp [hb]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  -- iterated shift on the initial cell
  have hpow : ∀ (n : ℕ) (hn : n < N),
      (ledgerShift N) ^ n *ᵥ Pi.single (⟨0, h0⟩ : Fin N) 1
        = Pi.single (⟨n, hn⟩ : Fin N) 1 := by
    intro n
    induction n with
    | zero =>
        intro hn
        rw [pow_zero, Matrix.one_mulVec]
    | succ k ih =>
        intro hn
        rw [pow_succ', ← Matrix.mulVec_mulVec,
          ih (Nat.lt_of_succ_lt hn), hstep k hn]
  -- iterated contraction
  have hiter : ∀ (n : ℕ) (x : Fin N → ℝ),
      ((ledgerShift N) ^ n *ᵥ x) ⬝ᵥ
          (G *ᵥ ((ledgerShift N) ^ n *ᵥ x))
        ≤ (q ^ 2) ^ n * (x ⬝ᵥ (G *ᵥ x)) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        have hrw : (ledgerShift N) ^ (k + 1) *ᵥ x
            = ledgerShift N *ᵥ
              ((ledgerShift N) ^ k *ᵥ x) := by
          rw [pow_succ', ← Matrix.mulVec_mulVec]
        rw [hrw]
        calc (ledgerShift N *ᵥ ((ledgerShift N) ^ k *ᵥ x))
              ⬝ᵥ (G *ᵥ (ledgerShift N *ᵥ
                ((ledgerShift N) ^ k *ᵥ x)))
            ≤ q ^ 2 * (((ledgerShift N) ^ k *ᵥ x) ⬝ᵥ
                (G *ᵥ ((ledgerShift N) ^ k *ᵥ x))) :=
              hcontr _
          _ ≤ q ^ 2 * ((q ^ 2) ^ k * (x ⬝ᵥ (G *ᵥ x))) :=
              mul_le_mul_of_nonneg_left (ih x) (sq_nonneg q)
          _ = (q ^ 2) ^ (k + 1) * (x ⬝ᵥ (G *ᵥ x)) := by
              ring
  -- assemble on the length-(N-1) ledger word
  have hNlt : N - 1 < N := Nat.sub_lt h0 one_pos
  have h1 : m ≤ (Pi.single (⟨N - 1, hNlt⟩ : Fin N) (1 : ℝ))
      ⬝ᵥ (G *ᵥ Pi.single (⟨N - 1, hNlt⟩ : Fin N) 1) := by
    have h := hlow (Pi.single (⟨N - 1, hNlt⟩ : Fin N) 1)
    rwa [hdot, mul_one] at h
  have h2 := hiter (N - 1)
    (Pi.single (⟨0, h0⟩ : Fin N) 1)
  rw [hpow (N - 1) hNlt] at h2
  have h3 : (Pi.single (⟨0, h0⟩ : Fin N) (1 : ℝ))
      ⬝ᵥ (G *ᵥ Pi.single (⟨0, h0⟩ : Fin N) 1) ≤ M := by
    have h := hupp (Pi.single (⟨0, h0⟩ : Fin N) 1)
    rwa [hdot, mul_one] at h
  calc m ≤ _ := h1
    _ ≤ (q ^ 2) ^ (N - 1)
        * ((Pi.single (⟨0, h0⟩ : Fin N) (1 : ℝ))
          ⬝ᵥ (G *ᵥ Pi.single (⟨0, h0⟩ : Fin N) 1)) := h2
    _ ≤ (q ^ 2) ^ (N - 1) * M :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = q ^ (2 * (N - 1)) * M := by
        rw [pow_mul]

end NCG
