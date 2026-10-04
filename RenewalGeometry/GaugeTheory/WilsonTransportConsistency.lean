/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.PathOrderedExponential

/-!
# Open finite links versus continuum parallel transport (`eq:Wilson-transport-consistency`)

The transport clause of `prop:Wilson-packet-transfer` (Einstein–SM action-closure manuscript,
"Finite Wilson packets and continuum covariant translations"): "For one edge, Duhamel's formula
compares the exact parallel-transport ODE with the frozen coefficient entering `U_μ(x)`; the
error is `O(h² B_h)`.  Unitary factors do not amplify operator norm, so telescoping over `|m|`
edges gives `‖ρ(𝒰_{μ,m}(x)) - ρ(P^{A_h}_{μ,mh}(x))‖ ≤ C ϱ₀ h B_h`."

Setting: a complete normed real algebra `𝔸` with `‖1‖ = 1` (the represented connection
`ρ(A)` acting on a fibre; `ρ` is absorbed into `𝔸`), a connection coefficient along a coordinate
line `ω(t) = -ρ(A_μ(x + t e_μ))` (so that the exact transport `U' = -ωU` of
`PathOrderedExp.IsTransport` has frozen link `e^{hρ(A_μ(x))}`), bounded by `K` and Lipschitz with
constant `L` (`L ≍ B_h` under the growing band `eq:eq-growing-band`, `K` bounded).

* `gronwallBound_zero_le`: `gronwallBound 0 K ε x ≤ ε x e^{Kx}`.
* `norm_edge_transport_sub_exp_le` (**one edge, Duhamel/Grönwall**):
  `‖U(a+h) - e^{-hω(a)}‖ ≤ L h² e^{2Kh}`.
* `prodUpTo`, `norm_prodUpTo_sub_le` (**telescoping**): for factors of norm `≤ M`, `M ≥ 1`,
  `‖Π a_j - Π b_j‖ ≤ m M^m max‖a_j - b_j‖`.
* `transport_eq_prodUpTo`: the exact transport over `m` edges is the ordered product of the exact
  edge transports (composition law `PathOrderedExp.transport_concat`).
* `norm_openLink_sub_transport_le` (**`eq:Wilson-transport-consistency`**): the open finite link
  `𝒰_m = Π_{j<m} e^{-hω(jh)}` and the product of exact edge transports satisfy
  `‖𝒰_m - P_m‖ ≤ (mh) L h e^{K(mh) + 2Kh}`, i.e. `≤ C ϱ₀ h L` for `|m|h ≤ ϱ₀`.
-/

open NormedSpace Set Filter

namespace RenewalGeometry.WilsonTransport

open PathOrderedExp

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

theorem gronwallBound_zero_le {K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    gronwallBound 0 K ε x ≤ ε * x * Real.exp (K * x) := by
  rcases eq_or_lt_of_le hK with h0 | hpos
  · subst h0
    rw [gronwallBound_K0]
    simp
  · rw [gronwallBound_of_K_ne_0 hpos.ne']
    simp only [zero_mul, zero_add]
    have h1 := exp_sub_one_le_mul_exp (K * x)
    calc ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hε hK)
      _ = ε * x * Real.exp (K * x) := by field_simp

/-- **One edge** (Duhamel/Grönwall comparison with the frozen coefficient): if `‖ω‖ ≤ K` and
`‖ω(t) - ω(a)‖ ≤ L(t - a)` on `[a, a+h]`, the exact transport with `U(a) = 1` satisfies
`‖U(a+h) - e^{-hω(a)}‖ ≤ L h² e^{2Kh}`. -/
theorem norm_edge_transport_sub_exp_le {ω : ℝ → 𝔸} {a h K L : ℝ} (hh : 0 ≤ h)
    (hK : ∀ t ∈ Icc a (a + h), ‖ω t‖ ≤ K) (hL0 : 0 ≤ L)
    (hL : ∀ t ∈ Icc a (a + h), ‖ω t - ω a‖ ≤ L * (t - a)) {U : ℝ → 𝔸}
    (hU : IsTransport ω a (a + h) U) (h1 : U a = 1) :
    ‖U (a + h) - exp (h • (-ω a))‖ ≤ L * h ^ 2 * Real.exp (2 * K * h) := by
  have hmem : a ∈ Icc a (a + h) := ⟨le_rfl, by linarith⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK a hmem)
  have hV := isTransport_const_exp (ω a) a (a + h)
  have hδ : ∀ t ∈ Icc a (a + h), ‖ω t - (fun _ => ω a) t‖ ≤ L * h := fun t ht =>
    (hL t ht).trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hL0)
  have hcmp := norm_transport_sub_transport_le hK (fun _ _ => hK a hmem) hδ hU hV
    (by simp [h1]) (a + h) ⟨by linarith, le_rfl⟩
  have e : exp ((a + h - a) • (-ω a)) = exp (h • (-ω a)) := by rw [add_sub_cancel_left]
  simp only [e, h1, norm_one, one_mul, add_sub_cancel_left] at hcmp
  refine hcmp.trans ((gronwallBound_zero_le hK0 (by positivity) hh).trans (le_of_eq ?_))
  rw [show 2 * K * h = K * h + K * h by ring, Real.exp_add]
  ring

/-! ### Telescoping ordered products -/

/-- The ordered product `a_{m-1} ⋯ a_1 a_0` (later edges act on the left, as in the composition law
of transports). -/
def prodUpTo (a : ℕ → 𝔸) : ℕ → 𝔸
  | 0 => 1
  | m + 1 => a m * prodUpTo a m

theorem norm_prodUpTo_le {a : ℕ → 𝔸} {M : ℝ} (hM : ∀ j, ‖a j‖ ≤ M) (hM0 : 0 ≤ M) :
    ∀ m, ‖prodUpTo a m‖ ≤ M ^ m
  | 0 => by simp [prodUpTo]
  | m + 1 => by
      rw [prodUpTo, pow_succ']
      exact (norm_mul_le _ _).trans (mul_le_mul (hM m) (norm_prodUpTo_le hM hM0 m)
        (norm_nonneg _) hM0)

/-- **Telescoping**: `‖Π a_j - Π b_j‖ ≤ m M^m δ` for factors of norm `≤ M`, `M ≥ 1`, with
`‖a_j - b_j‖ ≤ δ`. -/
theorem norm_prodUpTo_sub_le {a b : ℕ → 𝔸} {M δ : ℝ} (hMa : ∀ j, ‖a j‖ ≤ M)
    (hMb : ∀ j, ‖b j‖ ≤ M) (hM1 : 1 ≤ M) (hδ : ∀ j, ‖a j - b j‖ ≤ δ) :
    ∀ m, ‖prodUpTo a m - prodUpTo b m‖ ≤ m * M ^ m * δ
  | 0 => by simp [prodUpTo]
  | m + 1 => by
      have hM0 : 0 ≤ M := by linarith
      have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
      have ih := norm_prodUpTo_sub_le hMa hMb hM1 hδ m
      have hPa := norm_prodUpTo_le hMa hM0 m
      have e : prodUpTo a (m + 1) - prodUpTo b (m + 1) =
          (a m - b m) * prodUpTo a m + b m * (prodUpTo a m - prodUpTo b m) := by
        simp only [prodUpTo]; noncomm_ring
      rw [e]
      have hMm : M ^ m ≤ M ^ (m + 1) := pow_le_pow_right₀ hM1 (Nat.le_succ m)
      calc ‖(a m - b m) * prodUpTo a m + b m * (prodUpTo a m - prodUpTo b m)‖
          ≤ ‖a m - b m‖ * ‖prodUpTo a m‖ + ‖b m‖ * ‖prodUpTo a m - prodUpTo b m‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ δ * M ^ m + M * (m * M ^ m * δ) := by gcongr; exact hδ m; exact hMb m
        _ ≤ ((m + 1 : ℕ) : ℝ) * M ^ (m + 1) * δ := by
            push_cast
            rw [pow_succ]
            have h1 : δ * M ^ m ≤ δ * M ^ m * M :=
              le_mul_of_one_le_right (mul_nonneg hδ0 (pow_nonneg hM0 m)) hM1
            have e2 : ((m : ℝ) + 1) * (M ^ m * M) * δ = δ * M ^ m * M + M * (m * M ^ m * δ) := by
              ring
            linarith

/-! ### Exact transports over `m` edges -/

/-- The exact transport over `m` edges is the ordered product of the exact edge transports. -/
theorem transport_eq_prodUpTo {ω : ℝ → 𝔸} {h K : ℝ} (hh : 0 ≤ h) {W : ℝ → 𝔸} (m : ℕ)
    (hK : ∀ t ∈ Icc 0 (m * h), ‖ω t‖ ≤ K) (hW : IsTransport ω 0 (m * h) W) (hW0 : W 0 = 1)
    (P : ℕ → ℝ → 𝔸) (hP : ∀ j : ℕ, j < m → IsTransport ω (j * h) ((j + 1) * h) (P j))
    (hP1 : ∀ j : ℕ, j < m → P j (j * h) = 1) :
    W (m * h) = prodUpTo (fun j => P j ((j + 1) * h)) m := by
  have key : ∀ k ≤ m, W (k * h) = prodUpTo (fun j => P j ((j + 1) * h)) k := by
    intro k
    induction k with
    | zero => intro _; simp [prodUpTo, hW0]
    | succ k ih =>
      intro hk
      have hk' : k < m := hk
      have hmk : ((k + 1 : ℕ) : ℝ) * h ≤ m * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh
      have hWk : IsTransport ω 0 ((k + 1 : ℕ) * h) W := hW.mono le_rfl hmk
      have hcat := transport_concat (a := 0) (b := k * h) (c := (k + 1 : ℕ) * h) (K := K)
        (by positivity) (by push_cast; nlinarith)
        (fun t ht => hK t ⟨ht.1, ht.2.trans hmk⟩) hWk
        (by push_cast; exact hP k hk') (hP1 k hk') ((k + 1 : ℕ) * h)
        ⟨by push_cast; nlinarith, le_rfl⟩
      rw [hcat, ih hk'.le, prodUpTo]
      push_cast
      ring_nf
  exact key m le_rfl

/-- **`eq:Wilson-transport-consistency`**: for a connection coefficient bounded by `K` and
`L`-Lipschitz along the line, with exact edge transports `P_j` (`P_j(jh) = 1`), the open finite
link `𝒰_m = Π_{j<m} e^{-hω(jh)}` and the product of exact edge transports satisfy
`‖𝒰_m - Π P_j((j+1)h)‖ ≤ (mh) L h e^{K(mh) + 2Kh}`; for `mh ≤ ϱ₀` this is `C ϱ₀ h L`. -/
theorem norm_openLink_sub_transport_le {ω : ℝ → 𝔸} {h K L : ℝ} (hh : 0 ≤ h) (hL0 : 0 ≤ L)
    (hK0 : 0 ≤ K) (hK : ∀ t, ‖ω t‖ ≤ K) (hL : ∀ s t, s ≤ t → ‖ω t - ω s‖ ≤ L * (t - s))
    (P : ℕ → ℝ → 𝔸) (hP : ∀ j : ℕ, IsTransport ω (j * h) ((j + 1) * h) (P j))
    (hP1 : ∀ j : ℕ, P j (j * h) = 1) (m : ℕ) :
    ‖prodUpTo (fun j => exp (h • (-ω (j * h)))) m - prodUpTo (fun j => P j ((j + 1) * h)) m‖ ≤
      (m * h) * L * h * Real.exp (K * (m * h) + 2 * K * h) := by
  set M := Real.exp (K * h)
  have hM1 : 1 ≤ M := Real.one_le_exp (by positivity)
  have hMa : ∀ j : ℕ, ‖exp (h • (-ω (j * h)))‖ ≤ M := by
    intro j
    have hV := isTransport_const_exp (ω (j * h)) 0 h
    have := norm_transport_le (K := K) (fun _ _ => hK _) hV h ⟨hh, le_rfl⟩
    simpa [M] using this
  have hMb : ∀ j : ℕ, ‖P j ((j + 1) * h)‖ ≤ M := by
    intro j
    have := norm_transport_le (K := K) (fun _ _ => hK _) (hP j) ((j + 1) * h)
      ⟨by nlinarith, le_rfl⟩
    rw [hP1 j, norm_one, one_mul] at this
    simpa [M, show (j + 1 : ℝ) * h - j * h = h by ring] using this
  have hδ : ∀ j : ℕ, ‖exp (h • (-ω (j * h))) - P j ((j + 1) * h)‖ ≤
      L * h ^ 2 * Real.exp (2 * K * h) := by
    intro j
    have e : ((j : ℝ) + 1) * h = j * h + h := by ring
    have hPj : IsTransport ω (j * h) (j * h + h) (P j) := e ▸ hP j
    have h1 := norm_edge_transport_sub_exp_le hh (fun t _ => hK t) hL0
      (fun t ht => hL _ _ ht.1) hPj (hP1 j)
    rw [norm_sub_rev, ← e] at h1
    exact h1
  refine (norm_prodUpTo_sub_le hMa hMb hM1 hδ m).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul, Real.exp_add]
  have : (m : ℝ) * (K * h) = K * (m * h) := by ring
  rw [this]
  ring

/-- **`eq:Wilson-transport-consistency`, against the continuum transport**: if `W` is the exact
parallel transport along `[0, mh]` with `W(0) = 1`, `ω` is `K`-bounded and `L`-Lipschitz and the
mesh is short (`Kh ≤ 1/2`, needed only to produce the exact edge transports), then the open finite
link satisfies `‖𝒰_m - W(mh)‖ ≤ (mh) L h e^{K(mh) + 2Kh}`. -/
theorem norm_openLink_sub_continuumTransport_le {ω : ℝ → 𝔸} {h K L : ℝ} (hh : 0 ≤ h)
    (hL0 : 0 ≤ L) (hK0 : 0 ≤ K) (hK : ∀ t, ‖ω t‖ ≤ K)
    (hL : ∀ s t, s ≤ t → ‖ω t - ω s‖ ≤ L * (t - s)) (hshort : K * h ≤ 1 / 2) (m : ℕ)
    {W : ℝ → 𝔸} (hW : IsTransport ω 0 (m * h) W) (hW0 : W 0 = 1) :
    ‖prodUpTo (fun j => exp (h • (-ω (j * h)))) m - W (m * h)‖ ≤
      (m * h) * L * h * Real.exp (K * (m * h) + 2 * K * h) := by
  have hcont : Continuous ω := by
    refine Metric.continuous_iff.2 fun t ε hε => ⟨ε / (L + 1), by positivity, fun s hs => ?_⟩
    have hLs : ‖ω s - ω t‖ ≤ L * |s - t| := by
      rcases le_total t s with hts | hst
      · rw [abs_of_nonneg (by linarith)]; exact hL t s hts
      · rw [norm_sub_rev, abs_of_nonpos (by linarith), neg_sub]; exact hL s t hst
    rw [dist_eq_norm]
    rw [Real.dist_eq] at hs
    calc ‖ω s - ω t‖ ≤ L * |s - t| := hLs
      _ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left hs.le hL0
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have hex : ∀ j : ℕ, ∃ U : ℝ → 𝔸, U (j * h) = 1 ∧ IsTransport ω (j * h) ((j + 1) * h) U := by
    intro j
    exact exists_transport (K := K) (by nlinarith) hcont.continuousOn (fun t _ => hK t)
      (by rw [show ((j : ℝ) + 1) * h - j * h = h by ring]; exact hshort) 1
  choose P hP1 hP using hex
  rw [transport_eq_prodUpTo hh m (fun t _ => hK t) hW hW0 P (fun j _ => hP j) (fun j _ => hP1 j)]
  exact norm_openLink_sub_transport_le hh hL0 hK0 hK hL P hP hP1 m

/-- Non-vacuity: for a constant coefficient (`L = 0`) the exact edge transports are the frozen
exponentials and the bound reads `‖𝒰_m - Π P_j‖ ≤ 0`. -/
example (X : 𝔸) (h : ℝ) (hh : 0 ≤ h) (m : ℕ) :
    ‖prodUpTo (fun j => exp (h • (-(fun _ : ℝ => X) (j * h)))) m -
      prodUpTo (fun j => (fun t => exp ((t - j * h) • (-X))) ((j + 1) * h)) m‖ ≤
      (m * h) * 0 * h * Real.exp (‖X‖ * (m * h) + 2 * ‖X‖ * h) :=
  norm_openLink_sub_transport_le hh le_rfl (norm_nonneg X) (fun _ => le_rfl)
    (fun s t _ => by simp) (fun j => fun t => exp ((t - j * h) • (-X)))
    (fun j => isTransport_const_exp X _ _) (fun j => by simp) m

end

end RenewalGeometry.WilsonTransport
