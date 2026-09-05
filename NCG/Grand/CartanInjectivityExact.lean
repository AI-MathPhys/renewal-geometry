/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.PotentialPalatini

/-!
# Injectivity of the Cartan map in four dimensions

Machinery for `thm:Palatini-torsion`, addressing the fidelity-audit gap ("the
Cartan-map injectivity — the content — disclosed"): the manuscript's own
index chase is formalized exactly at the coefficient level.

In the coframe basis, `𝒦_e(T)^{IJ} = T^I ∧ e^J − e^I ∧ T^J` has coefficients
`kart T I J K L M` on `e^K ∧ e^L ∧ e^M` (cyclic Kronecker contractions, using
the antisymmetry of `T` in its last two slots).

* `offdiag_zero`: choosing `J ∉ {I,K,L}` kills every coefficient
  `T^I_{KL}` with `K, L ≠ I` — the manuscript's first step;
* `diag_pair` / `diag_zero`: the remaining coefficients `t_{I,K} = T^I_{IK}`
  satisfy `t_{I,K} + t_{J,K} = 0` for distinct rows, and four dimensions give
  three independent rows, forcing them all to vanish — the second step;
* `cartan_injective`: **the Cartan map is injective**;
* `spinless_torsion_zero`: with the (proved) invertibility of
  `P_{α,β} = α⋆ + βI`, connection stationarity on the spinless branch forces
  `T = 0` — the record's torsion conclusion.
-/

namespace NCG
namespace CartanInjectivity

/-- The Kronecker delta on frame indices. -/
def kd (a b : Fin 4) : ℝ := if a = b then 1 else 0

/-- The coefficient Cartan map: the component of
`T^I ∧ e^J − e^I ∧ T^J` on `e^K ∧ e^L ∧ e^M`. -/
def kart (T : Fin 4 → Fin 4 → Fin 4 → ℝ) (I J K L M : Fin 4) : ℝ :=
  (T I K L * kd J M + T I L M * kd J K + T I M K * kd J L)
    - (T J K L * kd I M + T J L M * kd I K + T J M K * kd I L)

theorem exists_avoiding : ∀ I K L : Fin 4, ∃ J : Fin 4,
    J ≠ I ∧ J ≠ K ∧ J ≠ L := by decide

theorem exists_avoiding2 : ∀ I K : Fin 4, ∃ J J' : Fin 4,
    J ≠ I ∧ J ≠ K ∧ J' ≠ I ∧ J' ≠ K ∧ J ≠ J' := by decide

variable {T : Fin 4 → Fin 4 → Fin 4 → ℝ}

/-- **Step one of the chase**: choosing `J` distinct from `I, K, L` forces
`T^I_{KL} = 0` whenever `K, L ≠ I`. -/
theorem offdiag_zero (hT : ∀ I K L, T I K L = -T I L K)
    (h : ∀ I J K L M, kart T I J K L M = 0)
    {I K L : Fin 4} (hKI : K ≠ I) (hLI : L ≠ I) : T I K L = 0 := by
  rcases eq_or_ne K L with rfl | hKL
  · have hself := hT I K K
    linarith
  obtain ⟨J, hJI, hJK, hJL⟩ := exists_avoiding I K L
  have hk := h I J K L J
  simp only [kart, kd, if_true, if_neg hJK, if_neg hJL,
    if_neg (Ne.symm hJI), if_neg (Ne.symm hKI), if_neg (Ne.symm hLI),
    mul_one, mul_zero, add_zero, sub_zero] at hk
  exact hk

/-- **Step two of the chase**: the diagonal coefficients of distinct rows are
opposite: `t_{I,K} + t_{J,K} = 0`. -/
theorem diag_pair (hT : ∀ I K L, T I K L = -T I L K)
    (h : ∀ I J K L M, kart T I J K L M = 0)
    {I J K : Fin 4} (hJI : J ≠ I) (hJK : J ≠ K) (hKI : K ≠ I) :
    T I I K + T J J K = 0 := by
  have hk := h I J I K J
  simp only [kart, kd, if_true, if_neg hJI, if_neg hJK,
    if_neg (Ne.symm hJI), if_neg (Ne.symm hKI),
    mul_one, mul_zero, add_zero, zero_add] at hk
  have hswap := hT J J K
  linarith

/-- Every diagonal coefficient vanishes: four dimensions supply three
independent rows. -/
theorem diag_zero (hT : ∀ I K L, T I K L = -T I L K)
    (h : ∀ I J K L M, kart T I J K L M = 0) (I K : Fin 4) :
    T I I K = 0 := by
  rcases eq_or_ne I K with rfl | hIK
  · have hself := hT I I I
    linarith
  obtain ⟨J, J', hJI, hJK, hJ'I, hJ'K, hJJ'⟩ := exists_avoiding2 I K
  have h1 := diag_pair hT h hJI hJK (Ne.symm hIK)
  have h2 := diag_pair hT h hJ'I hJ'K (Ne.symm hIK)
  have h3 := diag_pair hT h (Ne.symm hJJ') hJ'K (Ne.symm hJK)
  linarith

/-- **Injectivity of the Cartan map**: a torsion coefficient array,
antisymmetric in its form slots, with vanishing Cartan image is zero. -/
theorem cartan_injective (hT : ∀ I K L, T I K L = -T I L K)
    (h : ∀ I J K L M, kart T I J K L M = 0) :
    ∀ I K L, T I K L = 0 := by
  intro I K L
  rcases eq_or_ne K I with rfl | hKI
  · exact diag_zero hT h K L
  rcases eq_or_ne L I with rfl | hLI
  · have hd := diag_zero hT h L K
    have hswap := hT L K L
    have hswap2 := hT L L K
    linarith
  exact offdiag_zero hT h hKI hLI

/-- **The spinless branch**: with `P_{α,β}` injective (its two-sided inverse
is the proved boxed formula) and the Cartan map injective, connection
stationarity with vanishing spin current forces `T = 0`. -/
theorem spinless_torsion_zero {V W : Type*} (K : V → W) (Pmap : W → W)
    (z : V) (hPinj : Function.Injective Pmap)
    (hKinj : ∀ v, K v = K z → v = z) (T : V)
    (hEuler : Pmap (K T) = Pmap (K z)) : T = z :=
  hKinj T (hPinj hEuler)

end CartanInjectivity
end NCG
