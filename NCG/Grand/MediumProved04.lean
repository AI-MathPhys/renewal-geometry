/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EasyExact02
import NCG.Grand.MediumProved02
import NCG.Grand.MetricCongruencePseudoinverseClassificationExact
import NCG.Grand.SMSTReflectionPositivityExact

/-!
# Medium exact records, batch 04 (Gran-Tensor manuscript)

Exact formalizations of the following manuscript records:

* `thm:RPESM-four-mode-radius` — the covariance-radius/four-mode
  equivalence (CW.13), the complete two-sided kinetic window (CW.14) under
  a bounded four-mode infrared jet, the converse jet bound
  `𝔍_IR ≤ 16π²Z₊`, and the uniform three-way equivalence between a uniform
  covariance radius, a uniform all-momentum upper kinetic estimate, and a
  uniform four-character upper estimate.
* `thm:RPESM-infrared-source-compiler` — the finite source-Hessian
  compiler (CW.16) reconstructing the four-mode symbol from the root and
  eight scalar log-pressure curvatures, the derivative-oracle-free central
  difference bound (CW.17), and the domain-safe four-valued interval
  conclusion.
* `thm:SMOS-source-visible-superselection` — commuting resolvents force
  commuting charge and Hamiltonian (QSF.12), spectral sectors reduce `H`,
  the charge/flux/screening Pythagoras (QSF.13) with its screened-branch
  witness, sector Grams and the visible charge set (QSF.14), the visible
  superselection decomposition (QSF.15), block-diagonality of observables,
  and the charged-field ladder relation (QSF.16).
* `thm:SMOS-translation-target-ladder` — the Laplace-resolvent identity
  (LNS.13a), the Dirichlet-form limit (LNS.13b), the invariant-mass
  resolvent (LNS.13c) with its well-definedness, and the explicit
  forgetting counterexample (LNS.13d) plus the hyperboloid-forgetting
  witness.
* `thm:SMOS-mass-shell-separator` — Stieltjes inversion of the compressed
  invariant-mass measure (LNS.15) and the source residue (LNS.16), the
  Krylov innovation and flat atomic closure (LNS.17–LNS.18), the polar
  minimal new source, the isolated-shell criterion (LNS.19) with the shell
  isometry (LNS.19a) and its rank, and the exhaustive five-branch
  source-visible alternative.
* `cth:SMOS-atom-dissolution` — the explicit atomic measures (LNS.20a)
  with residue and gap `1/n`, and their weak convergence to the uniform
  measure on `[m², m²+1]`, which has no atom at `m²`.
* `thm:SMQG-crossing-factorization` — relation descent (HX.4), the
  minimum-norm represented extension (HX.5) with its uniqueness, the
  nearest-PSD distance identity (HX.6) as an attained minimum, the
  three-way factorization equivalence (HX.7), rank minimality, uniqueness
  of rank-minimal factors up to a unitary, and the crossing action (HX.8).
* `thm:SMST-actual-kinetic-derivative` — the conditional-score derivatives
  (HIT.3) of the deformed half-density, ground projection, conditional
  projections and kinetic Hamiltonian, the exact operator norm (HIT.4) of
  `Ṗ_j`, and the rank-two bound on every conditional block.
* `thm:SMST-centered-material-tangent` — unitarity and ground-line
  transport of the minimum connection (HIT.5), the centered material
  tangent (HIT.6), tracelessness, the conditional-locality bounds (HIT.7)
  with exact vanishing on independent coordinates, and the finite
  gauge–Higgs constants (HIT.8).
* `thm:SMST-Fisher-Green-bridge` — the exact Fisher–Green reconstruction
  (HIT.10) with `Ker 𝒥 = Ker M`, and the stationary follower (HIT.11).

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset Filter
open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank NCG.PsdBlockSchur
open scoped ComplexOrder Topology

-- decidability/fintype instances enter only through the spectral support calculus in proofs
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace NCG

/-! ### `thm:RPESM-four-mode-radius` — Covariance-radius and four-mode equivalence

Rendering: at a retuned root the mass-subtracted kinetic symbol is the
Dirichlet form of the positive covariance walk
`K̂(k) = q Σ_z p(z)(1 - cos(k·z))` (CW.6, record
`thm:RPESM-covariance-walk`), so the walk data are the interface: a finite
support `S` of integer coarse displacements with coordinates in the box
`|z_j| ≤ m` (minimum Euclidean representatives on the coarse torus of
half-period `m`), a probability weight `p` on `S` (CW.4), and the eight
nearest-atom floors `q/2·p(±2e_j) ≥ 100/6313` (CW.8, record
`thm:RPESM-all-mode-kinetic-floor`).  The radius is (CW.11), the four-mode
jet is (CW.12) with `κ_j = (π/m)e_j`, and `ω` is (CW.3).  The coarse
Brillouin bank is `|k_j| ≤ π/2` (currents live on the even sublattice).
The uniform equivalence quantifies over an arbitrary family of retuned
roots with the WB.25/WB.27a root bracket `3200/6313 ≤ q ≤ 1513/200`. -/

section FourModeRadiusSection

namespace FourModeRadius

/-- The four coordinate characters `ω_{2,L}(k) = 2 Σ_j (1 - cos 2k_j)` (CW.3). -/
noncomputable def omega2 (k : Fin 4 → ℝ) : ℝ := 2 * ∑ j, (1 - Real.cos (2 * k j))

/-- The Dirichlet kinetic symbol of the covariance walk at a retuned root
(CW.6): `K̂(k) = q Σ_z p(z)(1 - cos(k·z))`. -/
noncomputable def Khat (q : ℝ) (S : Finset (Fin 4 → ℤ)) (p : (Fin 4 → ℤ) → ℝ)
    (k : Fin 4 → ℝ) : ℝ :=
  q * ∑ z ∈ S, p z * (1 - Real.cos (∑ j, k j * (z j : ℝ)))

/-- The squared covariance radius `𝓡² = Σ_z p(z)|z|²` (CW.11). -/
noncomputable def radiusSq (S : Finset (Fin 4 → ℤ)) (p : (Fin 4 → ℤ) → ℝ) : ℝ :=
  ∑ z ∈ S, p z * ∑ j, ((z j : ℝ)) ^ 2

/-- The lowest coordinate momentum `κ_{L,j} = π m⁻¹ e_j`. -/
noncomputable def kappa (m : ℕ) (j : Fin 4) : Fin 4 → ℝ :=
  fun j' => if j' = j then Real.pi / m else 0

/-- The four-mode infrared jet `𝔍_IR = m² Σ_j K̂(κ_j)` (CW.12). -/
noncomputable def jet (m : ℕ) (q : ℝ) (S : Finset (Fin 4 → ℤ))
    (p : (Fin 4 → ℤ) → ℝ) : ℝ :=
  (m : ℝ) ^ 2 * ∑ j, Khat q S p (kappa m j)

/-- The positive nearest displacement `+2e_j`. -/
def eplus (j : Fin 4) : Fin 4 → ℤ := fun j' => if j' = j then 2 else 0

/-- The negative nearest displacement `-2e_j`. -/
def eminus (j : Fin 4) : Fin 4 → ℤ := fun j' => if j' = j then -2 else 0

/-- The diagonal value of `+2e_j`. -/
theorem eplus_same (j : Fin 4) : eplus j j = 2 := by
  unfold eplus
  rw [ite_eq_left rfl]

/-- The off-diagonal values of `+2e_j` vanish. -/
theorem eplus_other {j j' : Fin 4} (h : j' ≠ j) : eplus j j' = 0 := by
  unfold eplus
  rw [ite_eq_right h]

/-- The diagonal value of `-2e_j`. -/
theorem eminus_same (j : Fin 4) : eminus j j = -2 := by
  unfold eminus
  rw [ite_eq_left rfl]

/-- The off-diagonal values of `-2e_j` vanish. -/
theorem eminus_other {j j' : Fin 4} (h : j' ≠ j) : eminus j j' = 0 := by
  unfold eminus
  rw [ite_eq_right h]

/-- The diagonal value of `κ_j`. -/
theorem kappa_same (m : ℕ) (j : Fin 4) : kappa m j j = Real.pi / m := by
  unfold kappa
  rw [ite_eq_left rfl]

/-- The off-diagonal values of `κ_j` vanish. -/
theorem kappa_other (m : ℕ) {j j' : Fin 4} (h : j' ≠ j) : kappa m j j' = 0 := by
  unfold kappa
  rw [ite_eq_right h]

/-- Upper cosine comparison: `1 - cos t ≤ t²/2`. -/
theorem one_sub_cos_le_half_sq (t : ℝ) : 1 - Real.cos t ≤ t ^ 2 / 2 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := t)
  linarith

/-- Lower cosine comparison on `|t| ≤ π`: `2t²/π² ≤ 1 - cos t`. -/
theorem jordan_one_sub_cos {t : ℝ} (ht : |t| ≤ Real.pi) :
    2 * t ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos t := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hhalf : 1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
    have h2 : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
      rw [show t = 2 * (t / 2) by ring, Real.cos_two_mul]
      ring_nf
    have hs := Real.sin_sq_add_cos_sq (t / 2)
    nlinarith [hs]
  have habs : |t| / Real.pi ≤ |Real.sin (t / 2)| := by
    rcases le_or_gt 0 t with htpos | htneg
    · have h1 : 0 ≤ t / 2 := by linarith
      have h2 : t / 2 ≤ Real.pi / 2 := by
        rw [abs_of_nonneg htpos] at ht; linarith
      have := Real.mul_le_sin h1 h2
      have hsin : 0 ≤ Real.sin (t / 2) := le_trans (by positivity) this
      rw [abs_of_nonneg htpos, abs_of_nonneg hsin]
      calc t / Real.pi = 2 / Real.pi * (t / 2) := by ring
        _ ≤ Real.sin (t / 2) := this
    · have h1 : 0 ≤ -t / 2 := by linarith
      have h2 : -t / 2 ≤ Real.pi / 2 := by
        rw [abs_of_neg htneg] at ht; linarith
      have := Real.mul_le_sin h1 h2
      have hsin : Real.sin (-t / 2) = -Real.sin (t / 2) := by
        rw [neg_div, Real.sin_neg]
      rw [hsin] at this
      have hneg : 0 ≤ -Real.sin (t / 2) := le_trans (by positivity) this
      rw [abs_of_neg htneg, abs_of_nonpos (by linarith)]
      calc -t / Real.pi = 2 / Real.pi * (-t / 2) := by ring
        _ ≤ -Real.sin (t / 2) := this
  have hsq : t ^ 2 / Real.pi ^ 2 ≤ Real.sin (t / 2) ^ 2 := by
    have h2 := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ |t| / Real.pi) habs
    have h3 : |Real.sin (t / 2)| * |Real.sin (t / 2)| = Real.sin (t / 2) ^ 2 := by
      rw [← abs_mul, abs_mul_self, sq]
    have h4 : |t| / Real.pi * (|t| / Real.pi) = t ^ 2 / Real.pi ^ 2 := by
      rw [div_mul_div_comm, ← abs_mul, abs_mul_self, sq, sq]
    rw [h3, h4] at h2
    exact h2
  have hexp : 2 * t ^ 2 / Real.pi ^ 2 = 2 * (t ^ 2 / Real.pi ^ 2) := by ring
  rw [hhalf, hexp]
  linarith

/-- The kinetic symbol is nonnegative for nonnegative walk weights. -/
theorem Khat_nonneg {q : ℝ} (hq : 0 ≤ q) {S : Finset (Fin 4 → ℤ)}
    {p : (Fin 4 → ℤ) → ℝ} (hp0 : ∀ z ∈ S, 0 ≤ p z) (k : Fin 4 → ℝ) :
    0 ≤ Khat q S p k := by
  refine mul_nonneg hq (Finset.sum_nonneg fun z hz => mul_nonneg (hp0 z hz) ?_)
  have := Real.cos_le_one (∑ j, k j * (z j : ℝ))
  linarith

/-- Evaluation of the walk symbol at `κ_j`: only the `j`-th coordinate
contributes to the phase. -/
theorem Khat_kappa (q : ℝ) (S : Finset (Fin 4 → ℤ)) (p : (Fin 4 → ℤ) → ℝ)
    (m : ℕ) (j : Fin 4) :
    Khat q S p (kappa m j)
      = q * ∑ z ∈ S, p z * (1 - Real.cos (Real.pi / m * (z j : ℝ))) := by
  unfold Khat kappa
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 2
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ j (fun j' => Real.pi / m * (z j' : ℝ)),
    ite_eq_left (Finset.mem_univ j)]

/-- The jet as a single displacement sum:
`𝔍 = q Σ_z p(z) Σ_j m²(1 - cos(π z_j/m))`. -/
theorem jet_eq (m : ℕ) (q : ℝ) (S : Finset (Fin 4 → ℤ)) (p : (Fin 4 → ℤ) → ℝ) :
    jet m q S p
      = ∑ z ∈ S, ∑ j : Fin 4,
          q * (p z * ((m : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m * (z j : ℝ))))) := by
  unfold jet
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => Khat_kappa q S p m j]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun j _ => by ring

section MainEstimates

variable {m : ℕ} {q : ℝ} {S : Finset (Fin 4 → ℤ)} {p : (Fin 4 → ℤ) → ℝ}

/-- The squared phase identity `(π z_j/m)² m² = π² z_j²`. -/
theorem phase_sq (hm : 0 < m) (z : ℝ) :
    (Real.pi / m * z) ^ 2 * (m : ℝ) ^ 2 = Real.pi ^ 2 * z ^ 2 := by
  have hm' : ((m : ℝ)) ≠ 0 := by positivity
  field_simp

/-- **(CW.13), lower bound**: `(2/(qπ²))·𝔍_IR ≤ 𝓡²`. -/
theorem radius_lower (hm : 0 < m) (hq : 0 < q)
    (hp0 : ∀ z ∈ S, 0 ≤ p z) :
    2 / (q * Real.pi ^ 2) * jet m q S p ≤ radiusSq S p := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkey : jet m q S p ≤ q * (Real.pi ^ 2 / 2) * radiusSq S p := by
    rw [jet_eq]
    have hRHS : q * (Real.pi ^ 2 / 2) * radiusSq S p
        = ∑ z ∈ S, ∑ j : Fin 4,
            q * (p z * (Real.pi ^ 2 / 2 * ((z j : ℝ)) ^ 2)) := by
      unfold radiusSq
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hRHS]
    refine Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun j _ => ?_
    have h1 := one_sub_cos_le_half_sq (Real.pi / m * (z j : ℝ))
    have h2 := phase_sq hm ((z j : ℝ))
    have h3 : (m : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m * (z j : ℝ)))
        ≤ (m : ℝ) ^ 2 * ((Real.pi / m * (z j : ℝ)) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : (m : ℝ) ^ 2 * ((Real.pi / m * (z j : ℝ)) ^ 2 / 2)
        = Real.pi ^ 2 / 2 * ((z j : ℝ)) ^ 2 := by
      linear_combination h2 / 2
    have h5 : (m : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m * (z j : ℝ)))
        ≤ Real.pi ^ 2 / 2 * ((z j : ℝ)) ^ 2 := by
      rw [h4] at h3; exact h3
    have hpz : 0 ≤ q * p z := mul_nonneg hq.le (hp0 z hz)
    calc q * (p z * ((m : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m * (z j : ℝ)))))
        = q * p z * ((m : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m * (z j : ℝ)))) := by ring
      _ ≤ q * p z * (Real.pi ^ 2 / 2 * ((z j : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left h5 hpz
      _ = q * (p z * (Real.pi ^ 2 / 2 * ((z j : ℝ)) ^ 2)) := by ring
  have hqπ : (0 : ℝ) < q * Real.pi ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hqπ]
  calc 2 * jet m q S p ≤ 2 * (q * (Real.pi ^ 2 / 2) * radiusSq S p) := by linarith
    _ = radiusSq S p * (q * Real.pi ^ 2) := by ring

/-- **(CW.13), upper bound**: `𝓡² ≤ (1/(2q))·𝔍_IR`. -/
theorem radius_upper (hm : 0 < m) (hq : 0 < q)
    (hp0 : ∀ z ∈ S, 0 ≤ p z)
    (hbox : ∀ z ∈ S, ∀ j, |(z j : ℝ)| ≤ m) :
    radiusSq S p ≤ 1 / (2 * q) * jet m q S p := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkey : 2 * q * radiusSq S p ≤ jet m q S p := by
    rw [jet_eq]
    have hLHS : 2 * q * radiusSq S p
        = ∑ z ∈ S, ∑ j : Fin 4, q * (p z * (2 * ((z j : ℝ)) ^ 2)) := by
      unfold radiusSq
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hLHS]
    refine Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun j _ => ?_
    have habs : |Real.pi / m * (z j : ℝ)| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / m)]
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      calc Real.pi / m * |(z j : ℝ)| ≤ Real.pi / m * m :=
          mul_le_mul_of_nonneg_left (hbox z hz j) (by positivity)
        _ = Real.pi := by field_simp
    have h1 := jordan_one_sub_cos habs
    have h2 := phase_sq hm ((z j : ℝ))
    have h3 : (m : ℝ) ^ 2 * (2 * (Real.pi / m * (z j : ℝ)) ^ 2 / Real.pi ^ 2)
        ≤ (m : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m * (z j : ℝ))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : (m : ℝ) ^ 2 * (2 * (Real.pi / m * (z j : ℝ)) ^ 2 / Real.pi ^ 2)
        = 2 * ((z j : ℝ)) ^ 2 := by
      have hπ0 : Real.pi ^ 2 ≠ 0 := by positivity
      rw [show (m : ℝ) ^ 2 * (2 * (Real.pi / m * (z j : ℝ)) ^ 2 / Real.pi ^ 2)
          = 2 * ((Real.pi / m * (z j : ℝ)) ^ 2 * (m : ℝ) ^ 2) / Real.pi ^ 2 by ring, h2]
      rw [show 2 * (Real.pi ^ 2 * ((z j : ℝ)) ^ 2) / Real.pi ^ 2
          = 2 * ((z j : ℝ)) ^ 2 * (Real.pi ^ 2 / Real.pi ^ 2) by ring, div_self hπ0,
        mul_one]
    have h5 : 2 * ((z j : ℝ)) ^ 2
        ≤ (m : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m * (z j : ℝ))) := by
      rw [h4] at h3; exact h3
    have hpz : 0 ≤ q * p z := mul_nonneg hq.le (hp0 z hz)
    calc q * (p z * (2 * ((z j : ℝ)) ^ 2))
        = q * p z * (2 * ((z j : ℝ)) ^ 2) := by ring
      _ ≤ q * p z * ((m : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m * (z j : ℝ)))) :=
          mul_le_mul_of_nonneg_left h5 hpz
      _ = q * (p z * ((m : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m * (z j : ℝ))))) := by ring
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

/-- **(CW.13)**: the boxed two-sided covariance-radius/four-mode
equivalence `(2/(qπ²))𝔍_IR ≤ 𝓡²(q) ≤ (1/(2q))𝔍_IR`. -/
theorem covariance_radius_four_mode (hm : 0 < m) (hq : 0 < q)
    (hp0 : ∀ z ∈ S, 0 ≤ p z)
    (hbox : ∀ z ∈ S, ∀ j, |(z j : ℝ)| ≤ m) :
    2 / (q * Real.pi ^ 2) * jet m q S p ≤ radiusSq S p ∧
      radiusSq S p ≤ 1 / (2 * q) * jet m q S p :=
  ⟨radius_lower hm hq hp0, radius_upper hm hq hp0 hbox⟩

/-- **(CW.14), lower window**: the eight nearest-atom floors give
`(200/6313)·ω(k) ≤ K̂(k)` for every coarse momentum. -/
theorem kinetic_window_lower (hq : 0 < q)
    (hp0 : ∀ z ∈ S, 0 ≤ p z)
    (hplus : ∀ j, eplus j ∈ S ∧ (100 : ℝ) / 6313 ≤ q / 2 * p (eplus j))
    (hminus : ∀ j, eminus j ∈ S ∧ (100 : ℝ) / 6313 ≤ q / 2 * p (eminus j))
    (k : Fin 4 → ℝ) :
    (200 : ℝ) / 6313 * omega2 k ≤ Khat q S p k := by
  classical
  have hplus_inj : Function.Injective eplus := by
    intro a b hab
    by_contra hne
    have h := congrFun hab b
    rw [eplus_other (fun hh => hne hh.symm), eplus_same] at h
    exact absurd h (by norm_num)
  have hminus_inj : Function.Injective eminus := by
    intro a b hab
    by_contra hne
    have h := congrFun hab b
    rw [eminus_other (fun hh => hne hh.symm), eminus_same] at h
    exact absurd h (by norm_num)
  have hdisj : Disjoint (Finset.univ.image eplus) (Finset.univ.image eminus) := by
    rw [Finset.disjoint_left]
    rintro z hz1 hz2
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨b, -, hba⟩ := Finset.mem_image.mp hz2
    have h := congrFun hba a
    rw [eplus_same] at h
    by_cases hab : a = b
    · rw [hab, eminus_same] at h
      norm_num at h
    · rw [eminus_other hab] at h
      norm_num at h
  have hTS : Finset.univ.image eplus ∪ Finset.univ.image eminus ⊆ S := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact (hplus a).1
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact (hminus a).1
  have hsub : ∑ z ∈ Finset.univ.image eplus ∪ Finset.univ.image eminus,
        p z * (1 - Real.cos (∑ j, k j * (z j : ℝ)))
      ≤ ∑ z ∈ S, p z * (1 - Real.cos (∑ j, k j * (z j : ℝ))) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hTS fun z hz _ => ?_
    refine mul_nonneg (hp0 z hz) ?_
    have := Real.cos_le_one (∑ j, k j * (z j : ℝ))
    linarith
  -- evaluate the atom phases
  have hphase_plus : ∀ j : Fin 4, (∑ j', k j' * ((eplus j j' : ℤ) : ℝ)) = 2 * k j := by
    intro j
    rw [Finset.sum_eq_single j]
    · rw [eplus_same]
      push_cast
      ring
    · intro j' _ hj'
      rw [eplus_other hj', Int.cast_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hphase_minus : ∀ j : Fin 4,
      (∑ j', k j' * ((eminus j j' : ℤ) : ℝ)) = -(2 * k j) := by
    intro j
    rw [Finset.sum_eq_single j]
    · rw [eminus_same]
      push_cast
      ring
    · intro j' _ hj'
      rw [eminus_other hj', Int.cast_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hTsum : ∑ z ∈ Finset.univ.image eplus ∪ Finset.univ.image eminus,
        p z * (1 - Real.cos (∑ j, k j * (z j : ℝ)))
      = ∑ j : Fin 4, (p (eplus j) + p (eminus j)) * (1 - Real.cos (2 * k j)) := by
    rw [Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => hplus_inj h),
      Finset.sum_image (fun a _ b _ h => hminus_inj h), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hphase_plus j, hphase_minus j, Real.cos_neg]
    ring
  -- the atom floors
  have hfloor : ∀ j : Fin 4,
      (400 : ℝ) / 6313 * (1 - Real.cos (2 * k j))
        ≤ q * ((p (eplus j) + p (eminus j)) * (1 - Real.cos (2 * k j))) := by
    intro j
    have h1 := (hplus j).2
    have h2 := (hminus j).2
    have hcos : 0 ≤ 1 - Real.cos (2 * k j) := by
      have := Real.cos_le_one (2 * k j)
      linarith
    have hcoef : (400 : ℝ) / 6313 ≤ q * (p (eplus j) + p (eminus j)) := by
      nlinarith
    nlinarith
  calc (200 : ℝ) / 6313 * omega2 k
      = ∑ j : Fin 4, (400 : ℝ) / 6313 * (1 - Real.cos (2 * k j)) := by
        unfold omega2
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j : Fin 4, q * ((p (eplus j) + p (eminus j)) * (1 - Real.cos (2 * k j))) :=
        Finset.sum_le_sum fun j _ => hfloor j
    _ = q * ∑ z ∈ Finset.univ.image eplus ∪ Finset.univ.image eminus,
          p z * (1 - Real.cos (∑ j, k j * (z j : ℝ))) := by
        rw [hTsum, Finset.mul_sum]
    _ ≤ q * ∑ z ∈ S, p z * (1 - Real.cos (∑ j, k j * (z j : ℝ))) :=
        mul_le_mul_of_nonneg_left hsub hq.le
    _ = Khat q S p k := rfl

/-- The all-momentum quadratic upper bound
`K̂(k) ≤ (q/2)·|k|²·𝓡²` (Cauchy–Schwarz on the phase). -/
theorem Khat_le_norm_radius (hq : 0 < q) (hp0 : ∀ z ∈ S, 0 ≤ p z)
    (k : Fin 4 → ℝ) :
    Khat q S p k ≤ q / 2 * (∑ j, k j ^ 2) * radiusSq S p := by
  have hterm : ∀ z ∈ S,
      p z * (1 - Real.cos (∑ j, k j * (z j : ℝ)))
        ≤ p z * ((∑ j, k j ^ 2) / 2 * ∑ j, ((z j : ℝ)) ^ 2) := by
    intro z hz
    refine mul_le_mul_of_nonneg_left ?_ (hp0 z hz)
    have h1 := one_sub_cos_le_half_sq (∑ j, k j * (z j : ℝ))
    have h2 : (∑ j, k j * (z j : ℝ)) ^ 2 ≤ (∑ j, k j ^ 2) * ∑ j, ((z j : ℝ)) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ k (fun j => ((z j : ℝ)))
    calc 1 - Real.cos (∑ j, k j * (z j : ℝ))
        ≤ (∑ j, k j * (z j : ℝ)) ^ 2 / 2 := h1
      _ ≤ (∑ j, k j ^ 2) * (∑ j, ((z j : ℝ)) ^ 2) / 2 := by linarith
      _ = (∑ j, k j ^ 2) / 2 * ∑ j, ((z j : ℝ)) ^ 2 := by ring
  unfold Khat
  have hsum : ∑ z ∈ S, p z * (1 - Real.cos (∑ j, k j * (z j : ℝ)))
      ≤ ∑ z ∈ S, p z * ((∑ j, k j ^ 2) / 2 * ∑ j, ((z j : ℝ)) ^ 2) :=
    Finset.sum_le_sum hterm
  calc q * ∑ z ∈ S, p z * (1 - Real.cos (∑ j, k j * (z j : ℝ)))
      ≤ q * ∑ z ∈ S, p z * ((∑ j, k j ^ 2) / 2 * ∑ j, ((z j : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hq.le
    _ = q / 2 * (∑ j, k j ^ 2) * radiusSq S p := by
        unfold radiusSq
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by ring

/-- The Brillouin comparison: on `|k_j| ≤ π/2`,
`|k|² ≤ (π²/16)·ω(k)`. -/
theorem norm_le_omega {k : Fin 4 → ℝ} (hk : ∀ j, |k j| ≤ Real.pi / 2) :
    ∑ j, k j ^ 2 ≤ Real.pi ^ 2 / 16 * omega2 k := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hterm : ∀ j : Fin 4, k j ^ 2 ≤ Real.pi ^ 2 / 16 * (2 * (1 - Real.cos (2 * k j))) := by
    intro j
    have habs : |2 * k j| ≤ Real.pi := by
      rw [abs_mul, abs_two]
      have := hk j
      linarith
    have h1 := jordan_one_sub_cos habs
    have h2 : 2 * (2 * k j) ^ 2 / Real.pi ^ 2 = 8 * k j ^ 2 / Real.pi ^ 2 := by ring
    rw [h2] at h1
    have h3 : Real.pi ^ 2 / 16 * (2 * (8 * k j ^ 2 / Real.pi ^ 2)) = k j ^ 2 := by
      rw [show Real.pi ^ 2 / 16 * (2 * (8 * k j ^ 2 / Real.pi ^ 2))
          = k j ^ 2 * (Real.pi ^ 2 / Real.pi ^ 2) by ring, div_self (by positivity),
        mul_one]
    have h4 : Real.pi ^ 2 / 16 * (2 * (8 * k j ^ 2 / Real.pi ^ 2))
        ≤ Real.pi ^ 2 / 16 * (2 * (1 - Real.cos (2 * k j))) := by
      have : 0 ≤ Real.pi ^ 2 / 16 := by positivity
      nlinarith
    rw [h3] at h4
    exact h4
  calc ∑ j, k j ^ 2
      ≤ ∑ j : Fin 4, Real.pi ^ 2 / 16 * (2 * (1 - Real.cos (2 * k j))) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = Real.pi ^ 2 / 16 * omega2 k := by
        unfold omega2
        rw [Finset.mul_sum, Finset.mul_sum]

/-- **(CW.14), upper window**: if `𝔍_IR ≤ J⋆`, then
`K̂(k) ≤ (π²J⋆/64)·ω(k)` for every coarse momentum in the Brillouin bank. -/
theorem kinetic_window_upper (hm : 0 < m) (hq : 0 < q)
    (hp0 : ∀ z ∈ S, 0 ≤ p z)
    (hbox : ∀ z ∈ S, ∀ j, |(z j : ℝ)| ≤ m)
    {Jstar : ℝ} (hJ : jet m q S p ≤ Jstar)
    {k : Fin 4 → ℝ} (hk : ∀ j, |k j| ≤ Real.pi / 2) :
    Khat q S p k ≤ Real.pi ^ 2 * Jstar / 64 * omega2 k := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 := Khat_le_norm_radius hq hp0 (S := S) (p := p) k
  have h2 := radius_upper hm hq hp0 hbox
  have h3 := norm_le_omega hk
  have hnorm0 : 0 ≤ ∑ j, k j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hrad0 : 0 ≤ radiusSq S p :=
    Finset.sum_nonneg fun z hz => mul_nonneg (hp0 z hz)
      (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have homega0 : 0 ≤ omega2 k := by
    unfold omega2
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => ?_)
    have := Real.cos_le_one (2 * k j)
    linarith
  -- `K̂ ≤ (q/2)|k|²𝓡² ≤ (|k|²/4)J⋆ ≤ (π²/64)J⋆·ω`
  have h4 : Khat q S p k ≤ (∑ j, k j ^ 2) / 4 * Jstar := by
    have h5 : q / 2 * (∑ j, k j ^ 2) * radiusSq S p
        ≤ q / 2 * (∑ j, k j ^ 2) * (1 / (2 * q) * jet m q S p) := by
      refine mul_le_mul_of_nonneg_left h2 (by positivity)
    have h6 : q / 2 * (∑ j, k j ^ 2) * (1 / (2 * q) * jet m q S p)
        = (∑ j, k j ^ 2) / 4 * jet m q S p := by
      rw [show q / 2 * (∑ j, k j ^ 2) * (1 / (2 * q) * jet m q S p)
          = (∑ j, k j ^ 2) / 4 * jet m q S p * (q / q) by ring, div_self hq.ne',
        mul_one]
    have h7 : (∑ j, k j ^ 2) / 4 * jet m q S p ≤ (∑ j, k j ^ 2) / 4 * Jstar :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    linarith
  have hJ0 : 0 ≤ Jstar := by
    have hjet0 : 0 ≤ jet m q S p := by
      unfold jet
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
      exact Khat_nonneg hq.le hp0 _
    linarith
  calc Khat q S p k ≤ (∑ j, k j ^ 2) / 4 * Jstar := h4
    _ ≤ Real.pi ^ 2 / 16 * omega2 k / 4 * Jstar := by
        refine mul_le_mul_of_nonneg_right ?_ hJ0
        linarith
    _ = Real.pi ^ 2 * Jstar / 64 * omega2 k := by ring

/-- **The complete two-sided kinetic window (CW.14)** under a bounded jet:
`(200/6313)ω(k) ≤ K̂(k) ≤ (π²J⋆/64)ω(k)` for every coarse momentum. -/
theorem complete_kinetic_window (hm : 0 < m) (hq : 0 < q)
    (hp0 : ∀ z ∈ S, 0 ≤ p z)
    (hbox : ∀ z ∈ S, ∀ j, |(z j : ℝ)| ≤ m)
    (hplus : ∀ j, eplus j ∈ S ∧ (100 : ℝ) / 6313 ≤ q / 2 * p (eplus j))
    (hminus : ∀ j, eminus j ∈ S ∧ (100 : ℝ) / 6313 ≤ q / 2 * p (eminus j))
    {Jstar : ℝ} (hJ : jet m q S p ≤ Jstar)
    {k : Fin 4 → ℝ} (hk : ∀ j, |k j| ≤ Real.pi / 2) :
    (200 : ℝ) / 6313 * omega2 k ≤ Khat q S p k ∧
      Khat q S p k ≤ Real.pi ^ 2 * Jstar / 64 * omega2 k :=
  ⟨kinetic_window_lower hq hp0 hplus hminus k,
    kinetic_window_upper hm hq hp0 hbox hJ hk⟩

/-- The four-character evaluation `ω(κ_j) = 2(1 - cos(2π/m))`. -/
theorem omega_kappa (m : ℕ) (j : Fin 4) :
    omega2 (kappa m j) = 2 * (1 - Real.cos (2 * (Real.pi / m))) := by
  unfold omega2
  rw [Finset.sum_eq_single j]
  · rw [kappa_same]
  · intro j' _ hj'
    rw [kappa_other m hj', mul_zero, Real.cos_zero, sub_self]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **Converse four-character bound**: an upper coefficient `Z₊` on the four
lowest characters gives `𝔍_IR ≤ 16π²Z₊`. -/
theorem converse_jet_bound (hm : 2 ≤ m) (hq : 0 < q)
    (hp0 : ∀ z ∈ S, 0 ≤ p z)
    {Zplus : ℝ}
    (hZ : ∀ j, Khat q S p (kappa m j) ≤ Zplus * omega2 (kappa m j)) :
    jet m q S p ≤ 16 * Real.pi ^ 2 * Zplus := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hm' : (0 : ℝ) < m := by
    have : (0 : ℕ) < m := lt_of_lt_of_le (by norm_num) hm
    exact_mod_cast this
  -- `ω(κ_j) = 2(1-cos(2π/m))`, positive since `0 < 2π/m < 2π`
  have homega_pos : 0 < 2 * (1 - Real.cos (2 * (Real.pi / m))) := by
    have hval : 1 - Real.cos (2 * (Real.pi / m)) = 2 * Real.sin (Real.pi / m) ^ 2 := by
      have h2 : Real.cos (2 * (Real.pi / m)) = 2 * Real.cos (Real.pi / m) ^ 2 - 1 :=
        Real.cos_two_mul (Real.pi / m)
      have hs := Real.sin_sq_add_cos_sq (Real.pi / m)
      nlinarith
    have hsin : 0 < Real.sin (Real.pi / m) := by
      refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
      rw [div_lt_iff₀ hm']
      nlinarith
    nlinarith
  -- `Z₊ ≥ 0` from the `j = 0` bound
  have hZ0 : 0 ≤ Zplus := by
    have h1 := hZ 0
    have h2 := Khat_nonneg hq.le hp0 (kappa m 0)
    rw [omega_kappa] at h1
    nlinarith
  -- `ω(κ_j) ≤ 4π²/m²`
  have homega_le : 2 * (1 - Real.cos (2 * (Real.pi / m))) ≤ 4 * Real.pi ^ 2 / (m : ℝ) ^ 2 := by
    have h1 := one_sub_cos_le_half_sq (2 * (Real.pi / m))
    have h2 : (2 * (Real.pi / m)) ^ 2 / 2 = 2 * Real.pi ^ 2 / (m : ℝ) ^ 2 := by
      rw [mul_pow, div_pow]
      ring
    rw [h2] at h1
    have h3 : 2 * (2 * Real.pi ^ 2 / (m : ℝ) ^ 2) = 4 * Real.pi ^ 2 / (m : ℝ) ^ 2 := by
      ring
    linarith
  have hsum : ∑ j : Fin 4, Khat q S p (kappa m j)
      ≤ 4 * (Zplus * (4 * Real.pi ^ 2 / (m : ℝ) ^ 2)) := by
    have hterm : ∀ j : Fin 4,
        Khat q S p (kappa m j) ≤ Zplus * (4 * Real.pi ^ 2 / (m : ℝ) ^ 2) := by
      intro j
      calc Khat q S p (kappa m j) ≤ Zplus * omega2 (kappa m j) := hZ j
        _ = Zplus * (2 * (1 - Real.cos (2 * (Real.pi / m)))) := by rw [omega_kappa]
        _ ≤ Zplus * (4 * Real.pi ^ 2 / (m : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left homega_le hZ0
    calc ∑ j : Fin 4, Khat q S p (kappa m j)
        ≤ ∑ _j : Fin 4, Zplus * (4 * Real.pi ^ 2 / (m : ℝ) ^ 2) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = 4 * (Zplus * (4 * Real.pi ^ 2 / (m : ℝ) ^ 2)) := by
          rw [Finset.sum_const]
          simp only [Finset.card_univ, Fintype.card_fin]
          ring
  unfold jet
  have hstep : (m : ℝ) ^ 2 * ∑ j : Fin 4, Khat q S p (kappa m j)
      ≤ (m : ℝ) ^ 2 * (4 * (Zplus * (4 * Real.pi ^ 2 / (m : ℝ) ^ 2))) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hfin : (m : ℝ) ^ 2 * (4 * (Zplus * (4 * Real.pi ^ 2 / (m : ℝ) ^ 2)))
      = 16 * Real.pi ^ 2 * Zplus := by
    rw [show (m : ℝ) ^ 2 * (4 * (Zplus * (4 * Real.pi ^ 2 / (m : ℝ) ^ 2)))
        = 16 * Real.pi ^ 2 * Zplus * ((m : ℝ) ^ 2 / (m : ℝ) ^ 2) by ring,
      div_self (by positivity), mul_one]
  linarith

end MainEstimates

/-- The bundled data of one retuned root (the interface produced by
`thm:RPESM-covariance-walk` and `thm:RPESM-all-mode-kinetic-floor`). -/
structure RootData where
  /-- the coordinate half-period of the coarse torus -/
  m : ℕ
  /-- the retuned root -/
  q : ℝ
  /-- the walk support of minimum Euclidean coarse representatives -/
  S : Finset (Fin 4 → ℤ)
  /-- the covariance-walk weight -/
  p : (Fin 4 → ℤ) → ℝ
  /-- torus half-period at least two -/
  hm : 2 ≤ m
  /-- root bracket, left (WB.25/WB.27a) -/
  hql : (3200 : ℝ) / 6313 ≤ q
  /-- root bracket, right (WB.25/WB.27a) -/
  hqr : q ≤ (1513 : ℝ) / 200
  /-- walk weights are nonnegative (CW.4) -/
  hp0 : ∀ z ∈ S, 0 ≤ p z
  /-- displacements are minimum representatives: `|z_j| ≤ m` -/
  hbox : ∀ z ∈ S, ∀ j, |(z j : ℝ)| ≤ m
  /-- shared-site atom floors at `+2e_j` (CW.8) -/
  hplus : ∀ j, eplus j ∈ S ∧ (100 : ℝ) / 6313 ≤ q / 2 * p (eplus j)
  /-- shared-site atom floors at `-2e_j` (CW.8) -/
  hminus : ∀ j, eminus j ∈ S ∧ (100 : ℝ) / 6313 ≤ q / 2 * p (eminus j)

/-- The root of a data packet is positive. -/
theorem RootData.q_pos (D : RootData) : 0 < D.q :=
  lt_of_lt_of_le (by norm_num) D.hql

/-- The half-period of a data packet is positive. -/
theorem RootData.m_pos (D : RootData) : 0 < D.m :=
  lt_of_lt_of_le (by norm_num) D.hm

/-- **Uniform equivalence**: over any family of retuned roots, a uniform
covariance radius, a uniform upper kinetic estimate on every Brillouin
momentum, and a uniform upper estimate on only the four lowest coordinate
characters are equivalent. -/
theorem uniform_equivalence {ι : Type*} (D : ι → RootData) :
    ((∃ C : ℝ, ∀ i, radiusSq (D i).S (D i).p ≤ C) ↔
      ∃ Z : ℝ, ∀ i, ∀ k : Fin 4 → ℝ, (∀ j, |k j| ≤ Real.pi / 2) →
        Khat (D i).q (D i).S (D i).p k ≤ Z * omega2 k) ∧
    ((∃ Z : ℝ, ∀ i, ∀ k : Fin 4 → ℝ, (∀ j, |k j| ≤ Real.pi / 2) →
        Khat (D i).q (D i).S (D i).p k ≤ Z * omega2 k) ↔
      ∃ Z : ℝ, ∀ i, ∀ j : Fin 4,
        Khat (D i).q (D i).S (D i).p (kappa (D i).m j)
          ≤ Z * omega2 (kappa (D i).m j)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- (radius → all-momentum)
  have h12 : (∃ C : ℝ, ∀ i, radiusSq (D i).S (D i).p ≤ C) →
      ∃ Z : ℝ, ∀ i, ∀ k : Fin 4 → ℝ, (∀ j, |k j| ≤ Real.pi / 2) →
        Khat (D i).q (D i).S (D i).p k ≤ Z * omega2 k := by
    rintro ⟨C, hC⟩
    refine ⟨1513 / 400 * (Real.pi ^ 2 / 16) * max C 0, fun i k hk => ?_⟩
    have hq := (D i).q_pos
    have h1 := Khat_le_norm_radius hq (D i).hp0 (S := (D i).S) (p := (D i).p) k
    have h2 := norm_le_omega hk
    have hrad0 : 0 ≤ radiusSq (D i).S (D i).p :=
      Finset.sum_nonneg fun z hz => mul_nonneg ((D i).hp0 z hz)
        (Finset.sum_nonneg fun j _ => sq_nonneg _)
    have hnorm0 : 0 ≤ ∑ j, k j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hCmax : radiusSq (D i).S (D i).p ≤ max C 0 :=
      le_trans (hC i) (le_max_left _ _)
    have hq2 : (D i).q / 2 ≤ 1513 / 400 := by
      have := (D i).hqr
      linarith
    have homega0 : 0 ≤ omega2 k := by
      unfold omega2
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => ?_)
      have := Real.cos_le_one (2 * k j)
      linarith
    have hmax0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
    have hqq : 0 ≤ (D i).q / 2 := by positivity
    calc Khat (D i).q (D i).S (D i).p k
        ≤ (D i).q / 2 * (∑ j, k j ^ 2) * radiusSq (D i).S (D i).p := h1
      _ ≤ 1513 / 400 * (∑ j, k j ^ 2) * max C 0 := by
          have s1 : (D i).q / 2 * (∑ j, k j ^ 2) * radiusSq (D i).S (D i).p
              ≤ (D i).q / 2 * (∑ j, k j ^ 2) * max C 0 :=
            mul_le_mul_of_nonneg_left hCmax (mul_nonneg hqq hnorm0)
          have s2 : (D i).q / 2 * (∑ j, k j ^ 2) * max C 0
              ≤ 1513 / 400 * (∑ j, k j ^ 2) * max C 0 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hq2 hnorm0) hmax0
          linarith
      _ ≤ 1513 / 400 * (Real.pi ^ 2 / 16 * omega2 k) * max C 0 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2 (by norm_num)) hmax0
      _ = 1513 / 400 * (Real.pi ^ 2 / 16) * max C 0 * omega2 k := by ring
  -- (all-momentum → four characters)
  have h23 : (∃ Z : ℝ, ∀ i, ∀ k : Fin 4 → ℝ, (∀ j, |k j| ≤ Real.pi / 2) →
      Khat (D i).q (D i).S (D i).p k ≤ Z * omega2 k) →
      ∃ Z : ℝ, ∀ i, ∀ j : Fin 4,
        Khat (D i).q (D i).S (D i).p (kappa (D i).m j)
          ≤ Z * omega2 (kappa (D i).m j) := by
    rintro ⟨Z, hZ⟩
    refine ⟨Z, fun i j => hZ i (kappa (D i).m j) fun j' => ?_⟩
    have hm0 : (0 : ℝ) < (D i).m := by exact_mod_cast (D i).m_pos
    by_cases hjj : j' = j
    · rw [hjj, kappa_same, abs_of_pos (div_pos Real.pi_pos hm0)]
      have hm2 : (2 : ℝ) ≤ (D i).m := by exact_mod_cast (D i).hm
      rw [div_le_div_iff₀ hm0 (by norm_num)]
      nlinarith
    · rw [kappa_other (D i).m hjj, abs_zero]
      positivity
  -- (four characters → radius)
  have h31 : (∃ Z : ℝ, ∀ i, ∀ j : Fin 4,
      Khat (D i).q (D i).S (D i).p (kappa (D i).m j)
        ≤ Z * omega2 (kappa (D i).m j)) →
      ∃ C : ℝ, ∀ i, radiusSq (D i).S (D i).p ≤ C := by
    rintro ⟨Z, hZ⟩
    refine ⟨16 * Real.pi ^ 2 * max Z 0 * (6313 / 6400), fun i => ?_⟩
    have hq := (D i).q_pos
    have hjet := converse_jet_bound (D i).hm hq (D i).hp0 (hZ i)
    have hZmax : 16 * Real.pi ^ 2 * Z ≤ 16 * Real.pi ^ 2 * max Z 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have hrad := radius_upper (D i).m_pos hq (D i).hp0 (D i).hbox
    have hql := (D i).hql
    have hqinv : 1 / (2 * (D i).q) ≤ 6313 / 6400 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hjet0 : 0 ≤ jet (D i).m (D i).q (D i).S (D i).p := by
      unfold jet
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
      exact Khat_nonneg hq.le (D i).hp0 _
    calc radiusSq (D i).S (D i).p
        ≤ 1 / (2 * (D i).q) * jet (D i).m (D i).q (D i).S (D i).p := hrad
      _ ≤ 6313 / 6400 * (16 * Real.pi ^ 2 * max Z 0) := by
          have hb : jet (D i).m (D i).q (D i).S (D i).p
              ≤ 16 * Real.pi ^ 2 * max Z 0 := le_trans hjet hZmax
          have h1 : 1 / (2 * (D i).q) * jet (D i).m (D i).q (D i).S (D i).p
              ≤ 6313 / 6400 * jet (D i).m (D i).q (D i).S (D i).p :=
            mul_le_mul_of_nonneg_right hqinv hjet0
          have h2 : 6313 / 6400 * jet (D i).m (D i).q (D i).S (D i).p
              ≤ 6313 / 6400 * (16 * Real.pi ^ 2 * max Z 0) :=
            mul_le_mul_of_nonneg_left hb (by norm_num)
          linarith
      _ = 16 * Real.pi ^ 2 * max Z 0 * (6313 / 6400) := by ring
  exact ⟨⟨h12, fun h => h31 (h23 h)⟩, ⟨h23, fun h => h12 (h31 h)⟩⟩

end FourModeRadius

end FourModeRadiusSection

/-! ### `thm:RPESM-infrared-source-compiler` — Finite source-Hessian compiler

Rendering: the coarse cells are `(ℤ/m_Lℤ)⁴` (positions `2c`, so the lowest
coordinate momentum `κ_{L,j} = (π/m_L)e_j` has phase
`κ_j·(2c) = 2π c_j/m_L`); the current bank is a finite probability space
`(Ω, P)` with one real coarse current `b_c` per cell.  The cosine/sine
currents are (CW.15), the mode symbol `Ĉ(κ_j)` is the manuscript's
(WB.27) with `e^{-iκ_j·c}` realized by the explicit character, and
`K̂(κ_j) = q - 2Ĉ(κ_j)`.  The logarithmic source pressure is
`Ψ_X(t) = log E[e^{tX}]`; its derivative data are carried by explicit
scalar functions.  (CW.16) needs only the translation invariance of the
one-point function (the mean of `b_c` is independent of `c`), which kills
the nonzero-character mean; the curvatures are variances.  (CW.17) is
stated for an arbitrary scalar function with four derivative functions on
`[-h, h]` and a fourth-derivative bound `M₄`.  The four-valued conclusion
is a total decision on outward interval data for the nine scalar rows
(root bracket plus eight curvature intervals), sound in each branch, with
the proved branch discharging the complete kinetic window (CW.14) through
`thm:RPESM-four-mode-radius`. -/

section SourceCompilerSection

namespace SourceCompiler

/-! #### The derivative-oracle-free central difference (CW.17) -/

/-- Integral growth transfer: a function vanishing at `0` whose derivative
is bounded by `C·tⁿ` on `[0, b]` is bounded by `C·tⁿ⁺¹/(n+1)` there. -/
theorem cumulative_bound {f f' : ℝ → ℝ} {b C : ℝ} {n : ℕ}
    (hf0 : f 0 = 0)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivAt f (f' t) t)
    (hcont : ContinuousOn f' (Set.Icc 0 b))
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) b, |f' t| ≤ C * t ^ n) :
    ∀ t ∈ Set.Icc (0 : ℝ) b, |f t| ≤ C * t ^ (n + 1) / (n + 1) := by
  intro t ht
  obtain ⟨ht0, htb⟩ := ht
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.Icc 0 b := by
    rw [Set.uIcc_of_le ht0]
    exact Set.Icc_subset_Icc le_rfl htb
  have hint : IntervalIntegrable f' MeasureTheory.volume 0 t :=
    (hcont.mono hsub).intervalIntegrable
  have hFTC : ∫ u in (0 : ℝ)..t, f' u = f t - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hf u (hsub hu)) hint
  rw [hf0, sub_zero] at hFTC
  rw [← hFTC]
  have hintp : IntervalIntegrable (fun u : ℝ => C * u ^ n) MeasureTheory.volume 0 t :=
    ((continuous_const.mul (continuous_pow n)).continuousOn).intervalIntegrable
  calc |∫ u in (0 : ℝ)..t, f' u|
      ≤ ∫ u in (0 : ℝ)..t, |f' u| := intervalIntegral.abs_integral_le_integral_abs ht0
    _ ≤ ∫ u in (0 : ℝ)..t, C * u ^ n := by
        refine intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht0
          hint.abs hintp fun u hu => ?_
        exact hbound u ⟨hu.1, le_trans hu.2 htb⟩
    _ = C * ∫ u in (0 : ℝ)..t, u ^ n := by rw [intervalIntegral.integral_const_mul]
    _ = C * t ^ (n + 1) / (n + 1) := by
        rw [integral_pow, zero_pow (Nat.succ_ne_zero n)]
        ring

/-- One-sided fourth-order Taylor bound on `[0, b]` from derivative data. -/
theorem taylor_side {Ψ Ψ1 Ψ2 Ψ3 Ψ4 : ℝ → ℝ} {b M4 : ℝ} (hb : 0 ≤ b)
    (hd1 : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivAt Ψ (Ψ1 t) t)
    (hd2 : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivAt Ψ1 (Ψ2 t) t)
    (hd3 : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivAt Ψ2 (Ψ3 t) t)
    (hd4 : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivAt Ψ3 (Ψ4 t) t)
    (hM4 : ∀ t ∈ Set.Icc (0 : ℝ) b, |Ψ4 t| ≤ M4) :
    |Ψ b - Ψ 0 - Ψ1 0 * b - Ψ2 0 * b ^ 2 / 2 - Ψ3 0 * b ^ 3 / 6|
      ≤ M4 * b ^ 4 / 24 := by
  have hb_mem : b ∈ Set.Icc (0 : ℝ) b := ⟨hb, le_rfl⟩
  -- level 3: mean value inequality
  have hE3 : ∀ t ∈ Set.Icc (0 : ℝ) b, |Ψ3 t - Ψ3 0| ≤ M4 * t ^ 1 := by
    intro t ht
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := Ψ3) (f' := Ψ4) (C := M4) (s := Set.Icc (0 : ℝ) b)
      (fun u hu => (hd4 u hu).hasDerivWithinAt)
      (fun u hu => by rw [Real.norm_eq_abs]; exact hM4 u hu)
      (convex_Icc 0 b) (Set.left_mem_Icc.mpr hb) ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at h
    calc |Ψ3 t - Ψ3 0| ≤ M4 * |t| := h
      _ = M4 * t ^ 1 := by rw [abs_of_nonneg ht.1, pow_one]
  -- level 2
  have hd2' : ∀ t ∈ Set.Icc (0 : ℝ) b,
      HasDerivAt (fun u => Ψ2 u - Ψ2 0 - Ψ3 0 * u) (Ψ3 t - Ψ3 0) t := by
    intro t ht
    have h := ((hd3 t ht).sub_const (Ψ2 0)).sub ((hasDerivAt_id t).const_mul (Ψ3 0))
    have heq : Ψ3 t - Ψ3 0 * 1 = Ψ3 t - Ψ3 0 := by ring
    rwa [heq] at h
  have hcont3 : ContinuousOn (fun t => Ψ3 t - Ψ3 0) (Set.Icc (0 : ℝ) b) :=
    fun t ht => ((hd4 t ht).continuousAt.sub continuousAt_const).continuousWithinAt
  have hE2 := cumulative_bound (f := fun u => Ψ2 u - Ψ2 0 - Ψ3 0 * u)
    (f' := fun t => Ψ3 t - Ψ3 0) (C := M4) (n := 1) (by ring) hd2' hcont3 hE3
  have hE2' : ∀ t ∈ Set.Icc (0 : ℝ) b,
      |Ψ2 t - Ψ2 0 - Ψ3 0 * t| ≤ M4 / 2 * t ^ 2 := by
    intro t ht
    have h := hE2 t ht
    have heq2 : M4 * t ^ (1 + 1) / ((1 : ℕ) + 1) = M4 / 2 * t ^ 2 := by
      push_cast
      ring
    rwa [heq2] at h
  -- level 1
  have hd1' : ∀ t ∈ Set.Icc (0 : ℝ) b,
      HasDerivAt (fun u => Ψ1 u - Ψ1 0 - Ψ2 0 * u - Ψ3 0 * u ^ 2 / 2)
        (Ψ2 t - Ψ2 0 - Ψ3 0 * t) t := by
    intro t ht
    have h := (((hd2 t ht).sub_const (Ψ1 0)).sub
        ((hasDerivAt_id t).const_mul (Ψ2 0))).sub
      (((hasDerivAt_pow 2 t).const_mul (Ψ3 0)).div_const 2)
    have heq : Ψ2 t - Ψ2 0 * 1 - Ψ3 0 * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) / 2
        = Ψ2 t - Ψ2 0 - Ψ3 0 * t := by
      push_cast
      ring
    rwa [heq] at h
  have hcont2 : ContinuousOn (fun t => Ψ2 t - Ψ2 0 - Ψ3 0 * t) (Set.Icc (0 : ℝ) b) := by
    intro t ht
    exact (((hd3 t ht).continuousAt.sub continuousAt_const).sub
      (continuousAt_const.mul continuousAt_id)).continuousWithinAt
  have hE1 := cumulative_bound (f := fun u => Ψ1 u - Ψ1 0 - Ψ2 0 * u - Ψ3 0 * u ^ 2 / 2)
    (f' := fun t => Ψ2 t - Ψ2 0 - Ψ3 0 * t) (C := M4 / 2) (n := 2) (by ring) hd1' hcont2 hE2'
  have hE1' : ∀ t ∈ Set.Icc (0 : ℝ) b,
      |Ψ1 t - Ψ1 0 - Ψ2 0 * t - Ψ3 0 * t ^ 2 / 2| ≤ M4 / 6 * t ^ 3 := by
    intro t ht
    have h := hE1 t ht
    have heq1 : M4 / 2 * t ^ (2 + 1) / ((2 : ℕ) + 1) = M4 / 6 * t ^ 3 := by
      push_cast
      ring
    rwa [heq1] at h
  -- level 0
  have hd0' : ∀ t ∈ Set.Icc (0 : ℝ) b,
      HasDerivAt (fun u => Ψ u - Ψ 0 - Ψ1 0 * u - Ψ2 0 * u ^ 2 / 2 - Ψ3 0 * u ^ 3 / 6)
        (Ψ1 t - Ψ1 0 - Ψ2 0 * t - Ψ3 0 * t ^ 2 / 2) t := by
    intro t ht
    have h := ((((hd1 t ht).sub_const (Ψ 0)).sub
        ((hasDerivAt_id t).const_mul (Ψ1 0))).sub
      (((hasDerivAt_pow 2 t).const_mul (Ψ2 0)).div_const 2)).sub
      (((hasDerivAt_pow 3 t).const_mul (Ψ3 0)).div_const 6)
    have heq : Ψ1 t - Ψ1 0 * 1 - Ψ2 0 * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) / 2
        - Ψ3 0 * (((3 : ℕ) : ℝ) * t ^ (3 - 1)) / 6
        = Ψ1 t - Ψ1 0 - Ψ2 0 * t - Ψ3 0 * t ^ 2 / 2 := by
      push_cast
      ring
    rwa [heq] at h
  have hcont1 : ContinuousOn (fun t => Ψ1 t - Ψ1 0 - Ψ2 0 * t - Ψ3 0 * t ^ 2 / 2)
      (Set.Icc (0 : ℝ) b) := by
    intro t ht
    refine ContinuousWithinAt.sub (ContinuousWithinAt.sub (ContinuousWithinAt.sub ?_ ?_) ?_) ?_
    · exact (hd2 t ht).continuousAt.continuousWithinAt
    · exact continuousWithinAt_const
    · exact (continuousAt_const.mul continuousAt_id).continuousWithinAt
    · exact ((continuousAt_const.mul (continuousAt_pow t 2)).div_const 2).continuousWithinAt
  have hE0 := cumulative_bound
    (f := fun u => Ψ u - Ψ 0 - Ψ1 0 * u - Ψ2 0 * u ^ 2 / 2 - Ψ3 0 * u ^ 3 / 6)
    (f' := fun t => Ψ1 t - Ψ1 0 - Ψ2 0 * t - Ψ3 0 * t ^ 2 / 2) (C := M4 / 6) (n := 3)
    (by ring) hd0' hcont1 hE1'
  have h := hE0 b hb_mem
  have heq : M4 / 6 * b ^ (3 + 1) / ((3 : ℕ) + 1) = M4 * b ^ 4 / 24 := by
    push_cast
    ring
  rwa [heq] at h

/-- **(CW.17)**: the derivative-oracle-free central second difference:
if `Ψ` has four derivative functions on `[-h, h]` with `|Ψ⁗| ≤ M₄` there,
then `|(Ψ(h) - 2Ψ(0) + Ψ(-h))/h² - Ψ''(0)| ≤ h²M₄/12`. -/
theorem central_difference_curvature {Ψ Ψ1 Ψ2 Ψ3 Ψ4 : ℝ → ℝ} {h M4 : ℝ} (hh : 0 < h)
    (hd1 : ∀ t ∈ Set.Icc (-h) h, HasDerivAt Ψ (Ψ1 t) t)
    (hd2 : ∀ t ∈ Set.Icc (-h) h, HasDerivAt Ψ1 (Ψ2 t) t)
    (hd3 : ∀ t ∈ Set.Icc (-h) h, HasDerivAt Ψ2 (Ψ3 t) t)
    (hd4 : ∀ t ∈ Set.Icc (-h) h, HasDerivAt Ψ3 (Ψ4 t) t)
    (hM4 : ∀ t ∈ Set.Icc (-h) h, |Ψ4 t| ≤ M4) :
    |(Ψ h - 2 * Ψ 0 + Ψ (-h)) / h ^ 2 - Ψ2 0| ≤ h ^ 2 * M4 / 12 := by
  have hIcc : Set.Icc (0 : ℝ) h ⊆ Set.Icc (-h) h :=
    Set.Icc_subset_Icc (by linarith) le_rfl
  have hmem : ∀ u ∈ Set.Icc (0 : ℝ) h, -u ∈ Set.Icc (-h) h := by
    intro u hu
    exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  -- forward side
  have hA := taylor_side hh.le
    (fun t ht => hd1 t (hIcc ht)) (fun t ht => hd2 t (hIcc ht))
    (fun t ht => hd3 t (hIcc ht)) (fun t ht => hd4 t (hIcc ht))
    (fun t ht => hM4 t (hIcc ht))
  -- reflected side
  have hneg : ∀ u : ℝ, HasDerivAt (fun x : ℝ => -x) (-1) u := fun u => hasDerivAt_neg u
  have hr1 : ∀ u ∈ Set.Icc (0 : ℝ) h,
      HasDerivAt (fun x => Ψ (-x)) (-Ψ1 (-u)) u := by
    intro u hu
    have hc : HasDerivAt (fun x : ℝ => Ψ (-x)) (Ψ1 (-u) * (-1)) u :=
      (hd1 (-u) (hmem u hu)).comp u (hneg u)
    have heq : Ψ1 (-u) * (-1) = -Ψ1 (-u) := by ring
    rwa [heq] at hc
  have hr2 : ∀ u ∈ Set.Icc (0 : ℝ) h,
      HasDerivAt (fun x => -Ψ1 (-x)) (Ψ2 (-u)) u := by
    intro u hu
    have hc : HasDerivAt (fun x : ℝ => Ψ1 (-x)) (Ψ2 (-u) * (-1)) u :=
      (hd2 (-u) (hmem u hu)).comp u (hneg u)
    have hc2 := hc.neg
    have heq : -(Ψ2 (-u) * (-1)) = Ψ2 (-u) := by ring
    rwa [heq] at hc2
  have hr3 : ∀ u ∈ Set.Icc (0 : ℝ) h,
      HasDerivAt (fun x => Ψ2 (-x)) (-Ψ3 (-u)) u := by
    intro u hu
    have hc : HasDerivAt (fun x : ℝ => Ψ2 (-x)) (Ψ3 (-u) * (-1)) u :=
      (hd3 (-u) (hmem u hu)).comp u (hneg u)
    have heq : Ψ3 (-u) * (-1) = -Ψ3 (-u) := by ring
    rwa [heq] at hc
  have hr4 : ∀ u ∈ Set.Icc (0 : ℝ) h,
      HasDerivAt (fun x => -Ψ3 (-x)) (Ψ4 (-u)) u := by
    intro u hu
    have hc : HasDerivAt (fun x : ℝ => Ψ3 (-x)) (Ψ4 (-u) * (-1)) u :=
      (hd4 (-u) (hmem u hu)).comp u (hneg u)
    have hc2 := hc.neg
    have heq : -(Ψ4 (-u) * (-1)) = Ψ4 (-u) := by ring
    rwa [heq] at hc2
  have hB := taylor_side (Ψ := fun x => Ψ (-x)) (Ψ1 := fun x => -Ψ1 (-x))
    (Ψ2 := fun x => Ψ2 (-x)) (Ψ3 := fun x => -Ψ3 (-x)) (Ψ4 := fun x => Ψ4 (-x))
    hh.le hr1 hr2 hr3 hr4 (fun u hu => hM4 (-u) (hmem u hu))
  simp only [neg_zero] at hB
  -- combine
  have hsum : |Ψ h + Ψ (-h) - 2 * Ψ 0 - Ψ2 0 * h ^ 2| ≤ M4 * h ^ 4 / 12 := by
    have habs := abs_add_le (Ψ h - Ψ 0 - Ψ1 0 * h - Ψ2 0 * h ^ 2 / 2 - Ψ3 0 * h ^ 3 / 6)
      (Ψ (-h) - Ψ 0 - -Ψ1 0 * h - Ψ2 0 * h ^ 2 / 2 - -Ψ3 0 * h ^ 3 / 6)
    have hcomb : Ψ h - Ψ 0 - Ψ1 0 * h - Ψ2 0 * h ^ 2 / 2 - Ψ3 0 * h ^ 3 / 6
        + (Ψ (-h) - Ψ 0 - -Ψ1 0 * h - Ψ2 0 * h ^ 2 / 2 - -Ψ3 0 * h ^ 3 / 6)
        = Ψ h + Ψ (-h) - 2 * Ψ 0 - Ψ2 0 * h ^ 2 := by ring
    rw [hcomb] at habs
    calc |Ψ h + Ψ (-h) - 2 * Ψ 0 - Ψ2 0 * h ^ 2|
        ≤ |Ψ h - Ψ 0 - Ψ1 0 * h - Ψ2 0 * h ^ 2 / 2 - Ψ3 0 * h ^ 3 / 6|
          + |Ψ (-h) - Ψ 0 - -Ψ1 0 * h - Ψ2 0 * h ^ 2 / 2 - -Ψ3 0 * h ^ 3 / 6| := habs
      _ ≤ M4 * h ^ 4 / 24 + M4 * h ^ 4 / 24 := add_le_add hA hB
      _ = M4 * h ^ 4 / 12 := by ring
  have hh2 : (0 : ℝ) < h ^ 2 := by positivity
  have hquot : (Ψ h - 2 * Ψ 0 + Ψ (-h)) / h ^ 2 - Ψ2 0
      = (Ψ h + Ψ (-h) - 2 * Ψ 0 - Ψ2 0 * h ^ 2) / h ^ 2 := by
    field_simp
    ring
  rw [hquot, abs_div, abs_of_pos hh2, div_le_iff₀ hh2]
  calc |Ψ h + Ψ (-h) - 2 * Ψ 0 - Ψ2 0 * h ^ 2| ≤ M4 * h ^ 4 / 12 := hsum
    _ = h ^ 2 * M4 / 12 * h ^ 2 := by ring

/-! #### Logarithmic source pressures and their curvatures -/

section Pressure

variable {Ω : Type*} [Fintype Ω]

/-- The moment generating sum `Z_X(t) = Σ_ω P(ω) e^{tX(ω)}`. -/
noncomputable def mgf (P X : Ω → ℝ) (t : ℝ) : ℝ := ∑ ω, P ω * Real.exp (t * X ω)

/-- The first derivative sum of the moment generating sum. -/
noncomputable def mgf1 (P X : Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ ω, P ω * (X ω * Real.exp (t * X ω))

/-- The second derivative sum of the moment generating sum. -/
noncomputable def mgf2 (P X : Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ ω, P ω * (X ω ^ 2 * Real.exp (t * X ω))

/-- The logarithmic source pressure `Ψ_X(t) = log E[e^{tX}]`. -/
noncomputable def pressure (P X : Ω → ℝ) (t : ℝ) : ℝ := Real.log (mgf P X t)

/-- The moment generating sum of a probability weight is positive. -/
theorem mgf_pos {P : Ω → ℝ} (hP0 : ∀ ω, 0 ≤ P ω) (hP1 : ∑ ω, P ω = 1) (X : Ω → ℝ)
    (t : ℝ) : 0 < mgf P X t := by
  obtain ⟨ω₀, hω₀⟩ : ∃ ω, 0 < P ω := by
    by_contra hc
    push Not at hc
    have hz : ∑ ω, P ω = 0 :=
      Finset.sum_eq_zero fun ω _ => le_antisymm (hc ω) (hP0 ω)
    rw [hz] at hP1
    exact absurd hP1 (by norm_num)
  refine Finset.sum_pos' (fun ω _ => mul_nonneg (hP0 ω) (Real.exp_pos _).le)
    ⟨ω₀, Finset.mem_univ ω₀, mul_pos hω₀ (Real.exp_pos _)⟩

/-- Termwise derivative of the moment generating sum. -/
theorem hasDerivAt_mgf (P X : Ω → ℝ) (t : ℝ) :
    HasDerivAt (mgf P X) (mgf1 P X t) t := by
  unfold mgf mgf1
  refine HasDerivAt.fun_sum fun ω _ => ?_
  have h1 : HasDerivAt (fun u : ℝ => u * X ω) (X ω) t := hasDerivAt_mul_const _
  have h2 : HasDerivAt (fun u : ℝ => Real.exp (u * X ω))
      (Real.exp (t * X ω) * X ω) t := h1.exp
  have h3 := h2.const_mul (P ω)
  have heq : P ω * (Real.exp (t * X ω) * X ω) = P ω * (X ω * Real.exp (t * X ω)) := by
    ring
  rwa [heq] at h3

/-- Termwise derivative of the first moment sum. -/
theorem hasDerivAt_mgf1 (P X : Ω → ℝ) (t : ℝ) :
    HasDerivAt (mgf1 P X) (mgf2 P X t) t := by
  unfold mgf1 mgf2
  refine HasDerivAt.fun_sum fun ω _ => ?_
  have h1 : HasDerivAt (fun u : ℝ => u * X ω) (X ω) t := hasDerivAt_mul_const _
  have h2 : HasDerivAt (fun u : ℝ => Real.exp (u * X ω))
      (Real.exp (t * X ω) * X ω) t := h1.exp
  have h3 := (h2.const_mul (X ω)).const_mul (P ω)
  have heq : P ω * (X ω * (Real.exp (t * X ω) * X ω))
      = P ω * (X ω ^ 2 * Real.exp (t * X ω)) := by ring
  rwa [heq] at h3

/-- The pressure has derivative `Z'/Z`. -/
theorem hasDerivAt_pressure {P : Ω → ℝ} (hP0 : ∀ ω, 0 ≤ P ω) (hP1 : ∑ ω, P ω = 1)
    (X : Ω → ℝ) (t : ℝ) :
    HasDerivAt (pressure P X) (mgf1 P X t / mgf P X t) t := by
  unfold pressure
  exact (hasDerivAt_mgf P X t).log (mgf_pos hP0 hP1 X t).ne'

/-- **The source curvature is the variance**: `Ψ_X''(0) = E X² - (E X)²`. -/
theorem pressure_curvature {P : Ω → ℝ} (hP0 : ∀ ω, 0 ≤ P ω) (hP1 : ∑ ω, P ω = 1)
    (X : Ω → ℝ) :
    deriv (deriv (pressure P X)) 0
      = (∑ ω, P ω * X ω ^ 2) - (∑ ω, P ω * X ω) ^ 2 := by
  have hd : deriv (pressure P X) = fun t => mgf1 P X t / mgf P X t :=
    funext fun t => (hasDerivAt_pressure hP0 hP1 X t).deriv
  rw [hd]
  have h2 : HasDerivAt (fun t => mgf1 P X t / mgf P X t)
      ((mgf2 P X 0 * mgf P X 0 - mgf1 P X 0 * mgf1 P X 0) / mgf P X 0 ^ 2) 0 :=
    (hasDerivAt_mgf1 P X 0).div (hasDerivAt_mgf P X 0) (mgf_pos hP0 hP1 X 0).ne'
  rw [h2.deriv]
  have hZ0 : mgf P X 0 = 1 := by
    unfold mgf
    rw [Finset.sum_congr rfl fun ω _ => by rw [zero_mul, Real.exp_zero, mul_one]]
    exact hP1
  have hZ1 : mgf1 P X 0 = ∑ ω, P ω * X ω := by
    unfold mgf1
    refine Finset.sum_congr rfl fun ω _ => by rw [zero_mul, Real.exp_zero, mul_one]
  have hZ2 : mgf2 P X 0 = ∑ ω, P ω * X ω ^ 2 := by
    unfold mgf2
    refine Finset.sum_congr rfl fun ω _ => by rw [zero_mul, Real.exp_zero, mul_one]
  rw [hZ0, hZ1, hZ2]
  ring

end Pressure

/-! #### The coarse-cell characters and the four lowest currents -/

section Cells

/-- The complex character power identity for the coarse torus. -/
theorem char_pow (mL : ℕ) (k : ℕ) :
    Complex.exp (((2 * Real.pi / mL : ℝ) : ℂ) * Complex.I) ^ k
      = Complex.exp (((2 * Real.pi * k / mL : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The geometric character sum over one coordinate period vanishes. -/
theorem char_geom_zero {mL : ℕ} (hm : 2 ≤ mL) :
    ∑ k ∈ Finset.range mL,
        Complex.exp (((2 * Real.pi * k / mL : ℝ) : ℂ) * Complex.I) = 0 := by
  have hmR : (2 : ℝ) ≤ mL := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < mL := by linarith
  rw [Finset.sum_congr rfl fun k _ => (char_pow mL k).symm]
  have hz1 : Complex.exp (((2 * Real.pi / mL : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    rw [Complex.exp_eq_one_iff] at hcon
    obtain ⟨n, hn⟩ := hcon
    have him := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_im,
      Complex.ofReal_re, mul_zero, mul_one, zero_mul, add_zero,
      Complex.intCast_re, Complex.intCast_im, Complex.mul_re, sub_zero,
      Complex.re_ofNat, Complex.im_ofNat] at him
    -- him : 2π/mL = n * (2π)
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    have hprod : (n : ℝ) * mL = 1 := by
      have hthis : 2 * Real.pi = (n : ℝ) * (2 * Real.pi) * mL := by
        rw [div_eq_iff hmpos.ne'] at him
        linarith [him]
      have hc : (2 * Real.pi) * ((n : ℝ) * mL) = (2 * Real.pi) * 1 := by
        rw [mul_one]
        linear_combination -hthis
      exact mul_left_cancel₀ h2π.ne' hc
    rcases le_or_gt (n : ℝ) 0 with hn0 | hn0
    · nlinarith
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        have : (0 : ℤ) < n := by exact_mod_cast hn0
        exact_mod_cast this
      nlinarith
  have hzm : Complex.exp (((2 * Real.pi / mL : ℝ) : ℂ) * Complex.I) ^ mL = 1 := by
    rw [char_pow]
    have harg : ((2 * Real.pi * mL / mL : ℝ) : ℂ) * Complex.I
        = 2 * Real.pi * Complex.I := by
      have : (2 * Real.pi * mL / mL : ℝ) = 2 * Real.pi := by
        field_simp
      rw [this]
      push_cast
      ring
    rw [harg]
    exact Complex.exp_eq_one_iff.mpr ⟨1, by push_cast; ring⟩
  rw [geom_sum_eq hz1, hzm, sub_self, zero_div]

/-- The real cosine character sum over one coordinate period vanishes. -/
theorem cos_char_sum {mL : ℕ} (hm : 2 ≤ mL) :
    ∑ k ∈ Finset.range mL, Real.cos (2 * Real.pi * k / mL) = 0 := by
  have h := congrArg Complex.re (char_geom_zero hm)
  rw [Complex.re_sum] at h
  simp only [Complex.exp_ofReal_mul_I_re, Complex.zero_re] at h
  exact h

/-- The real sine character sum over one coordinate period vanishes. -/
theorem sin_char_sum {mL : ℕ} (hm : 2 ≤ mL) :
    ∑ k ∈ Finset.range mL, Real.sin (2 * Real.pi * k / mL) = 0 := by
  have h := congrArg Complex.im (char_geom_zero hm)
  rw [Complex.im_sum] at h
  simp only [Complex.exp_ofReal_mul_I_im, Complex.zero_im] at h
  exact h

/-- Sums over `ℤ/m_Lℤ` through the value map are range sums. -/
theorem sum_zmod_eq_sum_range {mL : ℕ} [NeZero mL] (f : ℕ → ℝ) :
    ∑ u : ZMod mL, f (ZMod.val u) = ∑ k ∈ Finset.range mL, f k := by
  have himg : Finset.range mL = Finset.univ.image (ZMod.val (n := mL)) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hk
      exact ⟨(k : ZMod mL), ZMod.val_cast_of_lt hk⟩
    · rintro ⟨u, rfl⟩
      exact ZMod.val_lt u
  rw [himg, Finset.sum_image fun a _ b _ h => ZMod.val_injective mL h]

/-- A coordinate observable with vanishing one-period sum has vanishing
cell sum. -/
theorem cell_sum_factor {mL : ℕ} [NeZero mL] (j : Fin 4) (g : ZMod mL → ℝ)
    (hg : ∑ u : ZMod mL, g u = 0) :
    ∑ c : Fin 4 → ZMod mL, g (c j) = 0 := by
  classical
  have hsplit : ∑ c : Fin 4 → ZMod mL, g (c j)
      = ∑ p : ZMod mL × ({ j' // j' ≠ j } → ZMod mL),
          g (((Equiv.funSplitAt j (ZMod mL)).symm p) j) :=
    (Equiv.sum_comp (Equiv.funSplitAt j (ZMod mL)).symm
      (fun c => g (c j))).symm
  have hval : ∀ p : ZMod mL × ({ j' // j' ≠ j } → ZMod mL),
      ((Equiv.funSplitAt j (ZMod mL)).symm p) j = p.1 := fun p => by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  calc ∑ c : Fin 4 → ZMod mL, g (c j)
      = ∑ p : ZMod mL × ({ j' // j' ≠ j } → ZMod mL), g p.1 := by
        rw [hsplit]
        exact Finset.sum_congr rfl fun p _ => by rw [hval p]
    _ = ∑ u : ZMod mL, ∑ _r : { j' // j' ≠ j } → ZMod mL, g u := by
        rw [Fintype.sum_prod_type]
    _ = ∑ u : ZMod mL, (Fintype.card ({ j' // j' ≠ j } → ZMod mL)) • g u := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_const, Finset.card_univ]
    _ = (Fintype.card ({ j' // j' ≠ j } → ZMod mL)) • ∑ u : ZMod mL, g u := by
        rw [Finset.smul_sum]
    _ = 0 := by rw [hg, smul_zero]

variable {Ω : Type*} [Fintype Ω] {mL : ℕ} [NeZero mL]

/-- The coarse phase `κ_j·(2c) = 2π c_j/m_L` of cell `c` at the lowest
coordinate momentum `κ_j`. -/
noncomputable def phase (j : Fin 4) (c : Fin 4 → ZMod mL) : ℝ :=
  2 * Real.pi * ((c j).val : ℝ) / mL

/-- The normalized cosine current `C_{L,j}` (CW.15). -/
noncomputable def cosCurrent (b : (Fin 4 → ZMod mL) → Ω → ℝ) (j : Fin 4) (ω : Ω) : ℝ :=
  (Real.sqrt (Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹
    * ∑ c, Real.cos (phase j c) * b c ω

/-- The normalized sine current `S_{L,j}` (CW.15). -/
noncomputable def sinCurrent (b : (Fin 4 → ZMod mL) → Ω → ℝ) (j : Fin 4) (ω : Ω) : ℝ :=
  (Real.sqrt (Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹
    * ∑ c, Real.sin (phase j c) * b c ω

/-- The four-mode current symbol `Ĉ(κ_j) = N⁻¹ E|Σ_c e^{-iκ_j·c} b_c|²`
(WB.27). -/
noncomputable def modeSymbol (P : Ω → ℝ) (b : (Fin 4 → ZMod mL) → Ω → ℝ)
    (j : Fin 4) : ℝ :=
  ((Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹
    * ∑ ω, P ω * Complex.normSq
        (∑ c, Complex.exp (((-phase j c : ℝ) : ℂ) * Complex.I) * (b c ω : ℂ))

/-- The kinetic symbol `K̂(κ_j) = q - 2Ĉ(κ_j)` (WB.27). -/
noncomputable def kinSymbol (q : ℝ) (P : Ω → ℝ) (b : (Fin 4 → ZMod mL) → Ω → ℝ)
    (j : Fin 4) : ℝ :=
  q - 2 * modeSymbol P b j

omit [Fintype Ω] in
/-- The squared modulus of the complex mode splits into the cosine and
sine currents. -/
theorem mode_normSq (b : (Fin 4 → ZMod mL) → Ω → ℝ) (j : Fin 4) (ω : Ω) :
    Complex.normSq
        (∑ c, Complex.exp (((-phase j c : ℝ) : ℂ) * Complex.I) * (b c ω : ℂ))
      = (∑ c, Real.cos (phase j c) * b c ω) ^ 2
        + (∑ c, Real.sin (phase j c) * b c ω) ^ 2 := by
  have hre : (∑ c, Complex.exp (((-phase j c : ℝ) : ℂ) * Complex.I) * (b c ω : ℂ)).re
      = ∑ c, Real.cos (phase j c) * b c ω := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.cos_neg]
  have him : (∑ c, Complex.exp (((-phase j c : ℝ) : ℂ) * Complex.I) * (b c ω : ℂ)).im
      = -∑ c, Real.sin (phase j c) * b c ω := by
    rw [Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, Real.sin_neg]
    ring
  rw [Complex.normSq_apply, hre, him]
  ring

/-- The mode symbol is the sum of the second moments of the cosine and
sine currents. -/
theorem modeSymbol_eq_moments (P : Ω → ℝ) (b : (Fin 4 → ZMod mL) → Ω → ℝ)
    (j : Fin 4) :
    modeSymbol P b j
      = (∑ ω, P ω * cosCurrent b j ω ^ 2) + ∑ ω, P ω * sinCurrent b j ω ^ 2 := by
  unfold modeSymbol
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [mode_normSq b j ω]
  unfold cosCurrent sinCurrent
  have hN0 : (0 : ℝ) ≤ (Fintype.card (Fin 4 → ZMod mL) : ℝ) := by positivity
  have hinv : ((Real.sqrt (Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹) ^ 2
      = ((Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹ := by
    rw [sq, ← mul_inv, Real.mul_self_sqrt hN0]
  rw [mul_pow, mul_pow, hinv]
  ring

/-- Translation-invariant one-point functions kill the cosine mean. -/
theorem cos_mean_zero (hm : 2 ≤ mL) (P : Ω → ℝ)
    (b : (Fin 4 → ZMod mL) → Ω → ℝ)
    (hmean : ∀ c : Fin 4 → ZMod mL,
      ∑ ω, P ω * b c ω = ∑ ω, P ω * b (fun _ => 0) ω)
    (j : Fin 4) :
    ∑ ω, P ω * cosCurrent b j ω = 0 := by
  unfold cosCurrent
  have hswap : ∑ ω, P ω * ((Real.sqrt (Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹
        * ∑ c, Real.cos (phase j c) * b c ω)
      = ∑ c, (Real.sqrt (Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹
          * (Real.cos (phase j c) * ∑ ω, P ω * b c ω) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun ω _ => by ring
  rw [hswap, Finset.sum_congr rfl fun c _ => by rw [hmean c]]
  have hchar : ∑ c : Fin 4 → ZMod mL, Real.cos (phase j c) = 0 := by
    have hg : ∑ u : ZMod mL, Real.cos (2 * Real.pi * ((ZMod.val u : ℕ) : ℝ) / mL) = 0 := by
      rw [sum_zmod_eq_sum_range fun k => Real.cos (2 * Real.pi * (k : ℝ) / mL)]
      exact cos_char_sum hm
    exact cell_sum_factor j (fun u => Real.cos (2 * Real.pi * ((ZMod.val u : ℕ) : ℝ) / mL)) hg
  calc ∑ c, (Real.sqrt (Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹
        * (Real.cos (phase j c) * ∑ ω, P ω * b (fun _ => 0) ω)
      = ((Real.sqrt (Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹
          * ∑ ω, P ω * b (fun _ => 0) ω) * ∑ c, Real.cos (phase j c) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = 0 := by rw [hchar, mul_zero]

/-- Translation-invariant one-point functions kill the sine mean. -/
theorem sin_mean_zero (hm : 2 ≤ mL) (P : Ω → ℝ)
    (b : (Fin 4 → ZMod mL) → Ω → ℝ)
    (hmean : ∀ c : Fin 4 → ZMod mL,
      ∑ ω, P ω * b c ω = ∑ ω, P ω * b (fun _ => 0) ω)
    (j : Fin 4) :
    ∑ ω, P ω * sinCurrent b j ω = 0 := by
  unfold sinCurrent
  have hswap : ∑ ω, P ω * ((Real.sqrt (Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹
        * ∑ c, Real.sin (phase j c) * b c ω)
      = ∑ c, (Real.sqrt (Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹
          * (Real.sin (phase j c) * ∑ ω, P ω * b c ω) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun ω _ => by ring
  rw [hswap, Finset.sum_congr rfl fun c _ => by rw [hmean c]]
  have hchar : ∑ c : Fin 4 → ZMod mL, Real.sin (phase j c) = 0 := by
    have hg : ∑ u : ZMod mL, Real.sin (2 * Real.pi * ((ZMod.val u : ℕ) : ℝ) / mL) = 0 := by
      rw [sum_zmod_eq_sum_range fun k => Real.sin (2 * Real.pi * (k : ℝ) / mL)]
      exact sin_char_sum hm
    exact cell_sum_factor j (fun u => Real.sin (2 * Real.pi * ((ZMod.val u : ℕ) : ℝ) / mL)) hg
  calc ∑ c, (Real.sqrt (Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹
        * (Real.sin (phase j c) * ∑ ω, P ω * b (fun _ => 0) ω)
      = ((Real.sqrt (Fintype.card (Fin 4 → ZMod mL) : ℝ))⁻¹
          * ∑ ω, P ω * b (fun _ => 0) ω) * ∑ c, Real.sin (phase j c) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = 0 := by rw [hchar, mul_zero]

/-- **(CW.16)**: at a retuned root, one root calibration and the two scalar
source curvatures reconstruct the four-mode kinetic symbol:
`K̂(κ_j) = q - 2Ψ''_{c,j}(0) - 2Ψ''_{s,j}(0)`. -/
theorem source_hessian_compiler (hm : 2 ≤ mL)
    {P : Ω → ℝ} (hP0 : ∀ ω, 0 ≤ P ω) (hP1 : ∑ ω, P ω = 1)
    (q : ℝ) (b : (Fin 4 → ZMod mL) → Ω → ℝ)
    (hmean : ∀ c : Fin 4 → ZMod mL,
      ∑ ω, P ω * b c ω = ∑ ω, P ω * b (fun _ => 0) ω)
    (j : Fin 4) :
    kinSymbol q P b j
      = q - 2 * deriv (deriv (pressure P (cosCurrent b j))) 0
          - 2 * deriv (deriv (pressure P (sinCurrent b j))) 0 := by
  rw [pressure_curvature hP0 hP1 (cosCurrent b j),
    pressure_curvature hP0 hP1 (sinCurrent b j),
    cos_mean_zero hm P b hmean j, sin_mean_zero hm P b hmean j]
  unfold kinSymbol
  rw [modeSymbol_eq_moments]
  ring

end Cells

/-! #### The domain-safe four-valued interval conclusion -/

section Decision

/-- The four-valued executable status of the nine-row infrared jet audit. -/
inductive JetStatus : Type
  /-- a uniform bounded jet: the complete kinetic window (CW.14) is proved -/
  | proved : JetStatus
  /-- a certified divergent lower jet: an explicit long-range obstruction -/
  | obstructed : JetStatus
  /-- a failed strict margin without either certificate -/
  | unresolved : JetStatus
  /-- violation of the root, variance, or lower-floor domains -/
  | inputError : JetStatus

/-- Outward interval data for the nine scalar rows: the root bracket and
the eight curvature intervals. -/
structure JetRows where
  /-- the coarse torus half-period -/
  mrow : ℕ
  /-- root interval, lower end -/
  qlo : ℝ
  /-- root interval, upper end -/
  qhi : ℝ
  /-- cosine curvature intervals, lower ends -/
  clo : Fin 4 → ℝ
  /-- cosine curvature intervals, upper ends -/
  chi : Fin 4 → ℝ
  /-- sine curvature intervals, lower ends -/
  slo : Fin 4 → ℝ
  /-- sine curvature intervals, upper ends -/
  shi : Fin 4 → ℝ

/-- The domain gate: the half-period is at least two, the root interval
lands in the WB.25/WB.27a root bracket, and the curvature intervals are
ordered with nonnegative upper ends (curvatures are variances). -/
def JetRows.domainOK (R : JetRows) : Prop :=
  2 ≤ R.mrow ∧ (3200 : ℝ) / 6313 ≤ R.qlo ∧ R.qhi ≤ 1513 / 200 ∧ R.qlo ≤ R.qhi ∧
    ∀ j, R.clo j ≤ R.chi j ∧ R.slo j ≤ R.shi j ∧ 0 ≤ R.chi j ∧ 0 ≤ R.shi j

/-- The certified upper end of the reconstructed jet interval (CW.16). -/
noncomputable def JetRows.jetHi (R : JetRows) : ℝ :=
  (R.mrow : ℝ) ^ 2 * ∑ j, (R.qhi - 2 * R.clo j - 2 * R.slo j)

/-- The certified lower end of the reconstructed jet interval (CW.16). -/
noncomputable def JetRows.jetLo (R : JetRows) : ℝ :=
  (R.mrow : ℝ) ^ 2 * ∑ j, (R.qlo - 2 * R.chi j - 2 * R.shi j)

/-- Outwardness: the true root and the eight true curvatures lie inside
the declared intervals. -/
def JetRows.captures (R : JetRows) (q : ℝ) (c2 s2 : Fin 4 → ℝ) : Prop :=
  R.qlo ≤ q ∧ q ≤ R.qhi ∧
    ∀ j, R.clo j ≤ c2 j ∧ c2 j ≤ R.chi j ∧ R.slo j ≤ s2 j ∧ s2 j ≤ R.shi j

open Classical in
/-- The four-valued decision on outward interval data, with a declared
bounded-jet threshold `J⋆` and a declared divergence floor `J_div`. -/
noncomputable def jetStatus (R : JetRows) (Jstar Jdiv : ℝ) : JetStatus :=
  if ¬ R.domainOK then .inputError
  else if R.jetHi ≤ Jstar then .proved
  else if Jdiv ≤ R.jetLo then .obstructed
  else .unresolved

/-- Outward rows bracket the reconstructed jet. -/
theorem JetRows.jet_between (R : JetRows) {q : ℝ} {c2 s2 : Fin 4 → ℝ}
    (hcap : R.captures q c2 s2) :
    R.jetLo ≤ (R.mrow : ℝ) ^ 2 * ∑ j, (q - 2 * c2 j - 2 * s2 j) ∧
      (R.mrow : ℝ) ^ 2 * ∑ j, (q - 2 * c2 j - 2 * s2 j) ≤ R.jetHi := by
  obtain ⟨hq1, hq2, hrows⟩ := hcap
  have hm2 : (0 : ℝ) ≤ (R.mrow : ℝ) ^ 2 := by positivity
  constructor
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hm2
    obtain ⟨h1, h2, h3, h4⟩ := hrows j
    linarith
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hm2
    obtain ⟨h1, h2, h3, h4⟩ := hrows j
    linarith

/-- **The domain-safe four-valued conclusion**: the decision is total; the
input-error branch is exactly domain violation; on the proved branch the
true jet is certified below `J⋆`; on the obstructed branch the true jet is
certified above the divergence floor (the explicit long-range
obstruction); and the unresolved branch carries no certificate. -/
theorem four_valued_conclusion (R : JetRows) (Jstar Jdiv : ℝ) {q : ℝ}
    {c2 s2 : Fin 4 → ℝ} (hcap : R.captures q c2 s2) :
    (jetStatus R Jstar Jdiv = .proved ∨ jetStatus R Jstar Jdiv = .obstructed ∨
      jetStatus R Jstar Jdiv = .unresolved ∨ jetStatus R Jstar Jdiv = .inputError) ∧
    (jetStatus R Jstar Jdiv = .inputError ↔ ¬ R.domainOK) ∧
    (jetStatus R Jstar Jdiv = .proved →
      R.domainOK ∧ (R.mrow : ℝ) ^ 2 * ∑ j, (q - 2 * c2 j - 2 * s2 j) ≤ Jstar) ∧
    (jetStatus R Jstar Jdiv = .obstructed →
      R.domainOK ∧ Jdiv ≤ (R.mrow : ℝ) ^ 2 * ∑ j, (q - 2 * c2 j - 2 * s2 j)) ∧
    (jetStatus R Jstar Jdiv = .unresolved →
      ¬ R.jetHi ≤ Jstar ∧ ¬ Jdiv ≤ R.jetLo) := by
  classical
  have hj := R.jet_between hcap
  unfold jetStatus
  by_cases hdom : R.domainOK
  · rw [ite_eq_right (fun hc => hc hdom)]
    by_cases hup : R.jetHi ≤ Jstar
    · rw [ite_eq_left hup]
      refine ⟨Or.inl rfl, ⟨fun h => absurd h (by simp), fun h => absurd hdom h⟩,
        fun _ => ⟨hdom, le_trans hj.2 hup⟩, fun h => absurd h (by simp), fun h =>
          absurd h (by simp)⟩
    · rw [ite_eq_right hup]
      by_cases hlo : Jdiv ≤ R.jetLo
      · rw [ite_eq_left hlo]
        refine ⟨Or.inr (Or.inl rfl), ⟨fun h => absurd h (by simp),
          fun h => absurd hdom h⟩, fun h => absurd h (by simp),
          fun _ => ⟨hdom, le_trans hlo hj.1⟩, fun h => absurd h (by simp)⟩
      · rw [ite_eq_right hlo]
        refine ⟨Or.inr (Or.inr (Or.inl rfl)), ⟨fun h => absurd h (by simp),
          fun h => absurd hdom h⟩, fun h => absurd h (by simp),
          fun h => absurd h (by simp), fun _ => ⟨hup, hlo⟩⟩
  · rw [ite_eq_left hdom]
    refine ⟨Or.inr (Or.inr (Or.inr rfl)), ⟨fun _ => hdom, fun _ => rfl⟩,
      fun h => absurd h (by simp), fun h => absurd h (by simp),
      fun h => absurd h (by simp)⟩

/-- **The proved branch discharges the complete kinetic window (CW.14)**:
for walk data at a retuned root whose Dirichlet jet is reconstructed by
the nine rows (the compiler identity CW.16 with the root calibration
CW.12), a proved decision certifies the two-sided window at every coarse
momentum of the Brillouin bank. -/
theorem proved_branch_window (R : JetRows) (Jstar Jdiv : ℝ)
    (D : FourModeRadius.RootData) {c2 s2 : Fin 4 → ℝ}
    (hcap : R.captures D.q c2 s2) (hm : R.mrow = D.m)
    (hlink : FourModeRadius.jet D.m D.q D.S D.p
      = (D.m : ℝ) ^ 2 * ∑ j, (D.q - 2 * c2 j - 2 * s2 j))
    (hdec : jetStatus R Jstar Jdiv = .proved)
    {k : Fin 4 → ℝ} (hk : ∀ j, |k j| ≤ Real.pi / 2) :
    (200 : ℝ) / 6313 * FourModeRadius.omega2 k
        ≤ FourModeRadius.Khat D.q D.S D.p k ∧
      FourModeRadius.Khat D.q D.S D.p k
        ≤ Real.pi ^ 2 * Jstar / 64 * FourModeRadius.omega2 k := by
  have h4 := four_valued_conclusion R Jstar Jdiv hcap
  have hbound := (h4.2.2.1 hdec).2
  rw [hm] at hbound
  rw [← hlink] at hbound
  exact FourModeRadius.complete_kinetic_window D.m_pos D.q_pos D.hp0 D.hbox
    D.hplus D.hminus hbound hk

end Decision

end SourceCompiler

end SourceCompilerSection

/-! ### Shared complex spectral calculus

`cSpec hA f = U · diag(f ∘ λ) · Uᴴ` for a Hermitian `A`, with complex
values: the resolvent and Laplace/Stieltjes symbols of the SMOS records
live here.  The real calculus `spectralFunction` embeds via `ofReal`. -/

section ComplexSpectralSection

namespace CSpec

open NCG.TraceExp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complex spectral calculus on a Hermitian matrix. -/
noncomputable def cSpec {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ)
    * diagonal (fun i => f (hA.eigenvalues i))
    * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ

/-- The eigenvector unitary is a left inverse (any index universe). -/
theorem unitary_ct_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix n n ℂ)
      = 1 :=
  UnitaryGroup.star_mul_self hA.eigenvectorUnitary

/-- The eigenvector unitary is a right inverse (any index universe). -/
theorem unitary_mul_ct {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ
      = 1 :=
  mul_eq_one_comm.mp (unitary_ct_mul hA)

/-- Spectral decomposition in explicit sandwich form (any index universe). -/
theorem hermitian_spectral' {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (fun i => (hA.eigenvalues i : ℂ))
        * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

/-- Equal spectral values give equal spectral functions. -/
theorem cSpec_congr {A : Matrix n n ℂ} (hA : A.IsHermitian) {f g : ℝ → ℂ}
    (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    cSpec hA f = cSpec hA g := by
  unfold cSpec
  have hfg : (fun i => f (hA.eigenvalues i)) = fun i => g (hA.eigenvalues i) :=
    funext fun i => h i
  rw [hfg]

/-- The identity function recovers the matrix. -/
theorem cSpec_id {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cSpec hA (fun l => (l : ℂ)) = A :=
  (hermitian_spectral' hA).symm

/-- Spectral products multiply pointwise. -/
theorem cSpec_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    cSpec hA f * cSpec hA g = cSpec hA (fun l => f l * g l) := by
  unfold cSpec
  have h1 : (hA.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (fun i => f (hA.eigenvalues i))
        * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ
        * ((hA.eigenvectorUnitary : Matrix n n ℂ)
          * diagonal (fun i => g (hA.eigenvalues i))
          * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
      = (hA.eigenvectorUnitary : Matrix n n ℂ)
        * (diagonal (fun i => f (hA.eigenvalues i))
          * diagonal (fun i => g (hA.eigenvalues i)))
        * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    have hUU := unitary_ct_mul hA
    calc (hA.eigenvectorUnitary : Matrix n n ℂ)
          * diagonal (fun i => f (hA.eigenvalues i))
          * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ
          * ((hA.eigenvectorUnitary : Matrix n n ℂ)
            * diagonal (fun i => g (hA.eigenvalues i))
            * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
        = (hA.eigenvectorUnitary : Matrix n n ℂ)
          * diagonal (fun i => f (hA.eigenvalues i))
          * ((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ
            * (hA.eigenvectorUnitary : Matrix n n ℂ))
          * (diagonal (fun i => g (hA.eigenvalues i))
            * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = (hA.eigenvectorUnitary : Matrix n n ℂ)
          * (diagonal (fun i => f (hA.eigenvalues i))
            * diagonal (fun i => g (hA.eigenvalues i)))
          * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
          rw [hUU, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [h1, diagonal_mul_diagonal]

/-- Spectral sums add pointwise. -/
theorem cSpec_add {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    cSpec hA f + cSpec hA g = cSpec hA (fun l => f l + g l) := by
  unfold cSpec
  rw [← diagonal_add, Matrix.mul_add, Matrix.add_mul]

/-- Spectral differences subtract pointwise. -/
theorem cSpec_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    cSpec hA f - cSpec hA g = cSpec hA (fun l => f l - g l) := by
  unfold cSpec
  rw [← diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]

/-- Constants map to scalar matrices. -/
theorem cSpec_const {A : Matrix n n ℂ} (hA : A.IsHermitian) (c : ℂ) :
    cSpec hA (fun _ => c) = c • (1 : Matrix n n ℂ) := by
  unfold cSpec
  have hd : diagonal (fun _ : n => c) = c • (1 : Matrix n n ℂ) := by
    rw [← diagonal_one, ← diagonal_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, smul_eq_mul, mul_one]
  rw [hd, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, unitary_mul_ct hA]

/-- Scalars pull out of the spectral calculus. -/
theorem cSpec_smul {A : Matrix n n ℂ} (hA : A.IsHermitian) (c : ℂ) (f : ℝ → ℂ) :
    cSpec hA (fun l => c * f l) = c • cSpec hA f := by
  unfold cSpec
  have hd : diagonal (fun i => c * f (hA.eigenvalues i))
      = c • diagonal (fun i => f (hA.eigenvalues i)) := by
    rw [← diagonal_smul]
    congr 1
  rw [hd, Matrix.mul_smul, Matrix.smul_mul]


/-- The shifted matrix as a spectral function. -/
theorem cSpec_shift {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) :
    A - z • (1 : Matrix n n ℂ) = cSpec hA (fun l => (l : ℂ) - z) := by
  rw [← cSpec_sub hA (fun l => (l : ℂ)) (fun _ => z), cSpec_id, cSpec_const]

/-- The resolvent as a spectral function: on the complement of the
spectrum, `A - z` has explicit inverse `cSpec ((λ - z)⁻¹)`. -/
theorem cSpec_resolvent {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : ∀ i, ((hA.eigenvalues i : ℂ)) ≠ z) :
    (A - z • (1 : Matrix n n ℂ)) * cSpec hA (fun l => ((l : ℂ) - z)⁻¹) = 1 ∧
      cSpec hA (fun l => ((l : ℂ) - z)⁻¹) * (A - z • (1 : Matrix n n ℂ)) = 1 := by
  constructor
  · rw [cSpec_shift hA z, cSpec_mul]
    have h1 : cSpec hA (fun l => ((l : ℂ) - z) * ((l : ℂ) - z)⁻¹)
        = cSpec hA (fun _ => (1 : ℂ)) := by
      refine cSpec_congr hA fun i => ?_
      rw [mul_inv_cancel₀ (sub_ne_zero.mpr (hz i))]
    rw [h1, cSpec_const, one_smul]
  · rw [cSpec_shift hA z, cSpec_mul]
    have h1 : cSpec hA (fun l => ((l : ℂ) - z)⁻¹ * ((l : ℂ) - z))
        = cSpec hA (fun _ => (1 : ℂ)) := by
      refine cSpec_congr hA fun i => ?_
      rw [inv_mul_cancel₀ (sub_ne_zero.mpr (hz i))]
    rw [h1, cSpec_const, one_smul]

/-- Off the spectrum the shift is a unit and the inverse is the spectral
resolvent. -/
theorem shift_inv_eq_cSpec {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : ∀ i, ((hA.eigenvalues i : ℂ)) ≠ z) :
    IsUnit (A - z • (1 : Matrix n n ℂ)) ∧
      (A - z • (1 : Matrix n n ℂ))⁻¹ = cSpec hA (fun l => ((l : ℂ) - z)⁻¹) := by
  obtain ⟨h1, h2⟩ := cSpec_resolvent hA hz
  constructor
  · exact ⟨⟨A - z • (1 : Matrix n n ℂ), cSpec hA (fun l => ((l : ℂ) - z)⁻¹), h1,
      mul_eq_one_comm.mp h1⟩, rfl⟩
  · exact Matrix.inv_eq_right_inv h1

/-- The entrywise expansion of the spectral calculus. -/
theorem cSpec_apply {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) (x y : n) :
    cSpec hA f x y
      = ∑ i, f (hA.eigenvalues i)
          * ((hA.eigenvectorUnitary : Matrix n n ℂ) x i
            * (starRingEnd ℂ) ((hA.eigenvectorUnitary : Matrix n n ℂ) y i)) := by
  unfold cSpec
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, RCLike.star_def]
  ring

/-- The compressed weight vector `w_i = Bᴴ u_i` of one eigencolumn. -/
noncomputable def wcol {A : Matrix n n ℂ} (hA : A.IsHermitian) {e : Type*}
    (B : Matrix n e ℂ) (i : n) : e → ℂ :=
  Bᴴ *ᵥ fun x => (hA.eigenvectorUnitary : Matrix n n ℂ) x i

/-- The compressed rank-one spectral weight `W_i = w_i w_i^*`. -/
noncomputable def wMat {A : Matrix n n ℂ} (hA : A.IsHermitian) {e : Type*}
    (B : Matrix n e ℂ) (i : n) : Matrix e e ℂ :=
  vecMulVec (wcol hA B i) (star (wcol hA B i))

/-- The compressed spectral calculus expands into the rank-one weights:
`Bᴴ f(A) B = Σ_i f(λ_i) • W_i`. -/
theorem compress_cSpec {A : Matrix n n ℂ} (hA : A.IsHermitian) {e : Type*}
    [Fintype e] (B : Matrix n e ℂ) (f : ℝ → ℂ) :
    Bᴴ * cSpec hA f * B = ∑ i, f (hA.eigenvalues i) • wMat hA B i := by
  ext c d
  rw [Matrix.mul_apply, Matrix.sum_apply]
  have hleft : ∀ x, (Bᴴ * cSpec hA f) c x
      = ∑ i, f (hA.eigenvalues i)
          * ((Bᴴ *ᵥ fun y => (hA.eigenvectorUnitary : Matrix n n ℂ) y i) c
            * (starRingEnd ℂ) ((hA.eigenvectorUnitary : Matrix n n ℂ) x i)) := by
    intro x
    rw [Matrix.mul_apply]
    have hswap : ∀ y, Bᴴ c y * cSpec hA f y x
        = ∑ i, f (hA.eigenvalues i)
            * (Bᴴ c y * (hA.eigenvectorUnitary : Matrix n n ℂ) y i
              * (starRingEnd ℂ) ((hA.eigenvectorUnitary : Matrix n n ℂ) x i)) := by
      intro y
      rw [cSpec_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl fun y _ => hswap y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => congrArg (· * B x d) (hleft x)]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_apply, wMat, vecMulVec_apply, wcol, smul_eq_mul]
  rw [Matrix.mulVec, dotProduct, Pi.star_apply, Matrix.mulVec, dotProduct, star_sum]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [star_mul', Matrix.conjTranspose_apply, star_star, RCLike.star_def]
  ring

/-- Each compressed spectral weight is PSD. -/
theorem wMat_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) {e : Type*}
    [Fintype e] [DecidableEq e] (B : Matrix n e ℂ) (i : n) :
    (wMat hA B i).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (wcol hA B i)

end CSpec

end ComplexSpectralSection

/-! ### `thm:SMOS-source-visible-superselection` — Conservation and superselection

Rendering: the landed charge `Q` and the OS Hamiltonian `H` are Hermitian
matrices on the finite OS carrier.  (QSF.12) is commutation of the literal
resolvents at `i` (well defined: `Q - i·1` is invertible for Hermitian
`Q`), and strong commutation is finite-dimensional matrix commutation,
under which every spectral sector `P_μ = 1_{{μ}}(Q)` reduces `H`.  The
Pythagoras (QSF.13) is the orthogonal three-way defect decomposition of
the charge synthesis against the flux range and the flux-orthogonalized
screening range (`NCG.ChargeFlux`), with the zero-residual classification
trichotomy and the explicit completely screened witness carrying zero
asymptotic flux and nonzero matter charge.  (QSF.14) defines the sector
Grams and the visible charge set over the finite spectrum.  The observable
algebra is a subalgebra `𝒜` of matrices commuting with `Q` that contains
the charge (the superselection reading: the charge is a central
observable), and the visible carrier is the `𝒜`-orbit span of the source
columns; sector projections lie in `𝒜` by Lagrange interpolation on the
finite spectrum, giving the visible decomposition (QSF.15): invisible
sectors annihilate the carrier, sector components stay in the carrier, and
the visible sectors reconstruct every visible vector.  Observables have no
off-diagonal blocks between distinct charges, and the held-out charged
field obeys the ladder relation (QSF.16). -/

section SuperselectionSection

namespace Superselection

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral charge sector `P_μ = 1_{{μ}}(Q)`. -/
noncomputable def sectorProj {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (μ : ℝ) :
    Matrix n n ℂ :=
  spectralFunction hQ (fun l => if l = μ then 1 else 0)

/-- Sector projections are Hermitian. -/
theorem sectorProj_isHermitian {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (μ : ℝ) :
    (sectorProj hQ μ).IsHermitian :=
  (spectralFunction_posSemidef hQ _ fun i => by split_ifs <;> norm_num).1

/-- Sector projections are idempotent. -/
theorem sectorProj_idem {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (μ : ℝ) :
    sectorProj hQ μ * sectorProj hQ μ = sectorProj hQ μ := by
  unfold sectorProj
  rw [spectralFunction_mul]
  refine spectralFunction_congr hQ fun i => ?_
  split_ifs <;> norm_num

/-- The charge acts on its sector by the sector value. -/
theorem charge_mul_sectorProj {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (μ : ℝ) :
    Q * sectorProj hQ μ = (μ : ℂ) • sectorProj hQ μ := by
  have hmul := spectralFunction_mul hQ id fun l => if l = μ then 1 else 0
  rw [spectralFunction_id] at hmul
  unfold sectorProj
  rw [hmul]
  have h1 : spectralFunction hQ (fun l => id l * if l = μ then 1 else 0)
      = spectralFunction hQ (fun l => μ * if l = μ then 1 else 0) := by
    refine spectralFunction_congr hQ fun i => ?_
    by_cases h : hQ.eigenvalues i = μ
    · rw [ite_eq_left h]
      simp only [id_eq, h]
    · rw [ite_eq_right h, mul_zero, mul_zero]
  rw [h1, spectralFunction_smul]

/-- The kill lemma: a sector annihilates any `Q`-eigencolumn family at a
different sector value. -/
theorem sectorProj_mul_eq_zero {Q M : Matrix n n ℂ} (hQ : Q.IsHermitian) {μ ν : ℝ}
    (hM : Q * M = (ν : ℂ) • M) (hμν : μ ≠ ν) : sectorProj hQ μ * M = 0 := by
  have hshift : spectralFunction hQ (fun l => l - ν) * M = 0 := by
    rw [← sub_smul_one_eq_spectral hQ ν, Matrix.sub_mul, hM, Matrix.smul_mul,
      Matrix.one_mul, sub_self]
  have hfac : sectorProj hQ μ
      = spectralFunction hQ (fun l => (if l = μ then 1 else 0) * (l - ν)⁻¹)
        * spectralFunction hQ (fun l => l - ν) := by
    rw [spectralFunction_mul]
    unfold sectorProj
    refine spectralFunction_congr hQ fun i => ?_
    by_cases h : hQ.eigenvalues i = μ
    · have hne : hQ.eigenvalues i - ν ≠ 0 := sub_ne_zero.mpr (by rw [h]; exact hμν)
      rw [ite_eq_left h, one_mul, inv_mul_cancel₀ hne]
    · rw [ite_eq_right h, zero_mul, zero_mul]
  rw [hfac, Matrix.mul_assoc, hshift, Matrix.mul_zero]

/-- The fix lemma: a sector fixes every `Q`-eigencolumn family at its own
sector value. -/
theorem sectorProj_mul_eq_self {Q M : Matrix n n ℂ} (hQ : Q.IsHermitian) {ν : ℝ}
    (hM : Q * M = (ν : ℂ) • M) : sectorProj hQ ν * M = M := by
  have hshift : spectralFunction hQ (fun l => l - ν) * M = 0 := by
    rw [← sub_smul_one_eq_spectral hQ ν, Matrix.sub_mul, hM, Matrix.smul_mul,
      Matrix.one_mul, sub_self]
  have hfac : (1 : Matrix n n ℂ) - sectorProj hQ ν
      = spectralFunction hQ (fun l => (if l = ν then 0 else (l - ν)⁻¹))
        * spectralFunction hQ (fun l => l - ν) := by
    rw [spectralFunction_mul]
    unfold sectorProj
    have hone : (1 : Matrix n n ℂ) = spectralFunction hQ (fun _ => 1) := by
      rw [spectralFunction_const, Complex.ofReal_one, one_smul]
    rw [hone, ← spectralFunction_sub hQ]
    refine spectralFunction_congr hQ fun i => ?_
    by_cases h : hQ.eigenvalues i = ν
    · rw [ite_eq_left h, ite_eq_left h, zero_mul, sub_self]
    · rw [ite_eq_right h, ite_eq_right h, sub_zero,
        inv_mul_cancel₀ (sub_ne_zero.mpr h)]
  have hres : ((1 : Matrix n n ℂ) - sectorProj hQ ν) * M = 0 := by
    rw [hfac, Matrix.mul_assoc, hshift, Matrix.mul_zero]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hres
  exact hres.symm

/-- The sectors over the finite spectrum resolve the identity. -/
theorem sectorProj_sum {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) :
    ∑ μ ∈ Finset.univ.image hQ.eigenvalues, sectorProj hQ μ = 1 := by
  classical
  unfold sectorProj
  rw [← spectralFunction_sum hQ (Finset.univ.image hQ.eigenvalues)
    (fun μ l => if l = μ then 1 else 0)]
  have h1 : spectralFunction hQ
      (fun l => ∑ μ ∈ Finset.univ.image hQ.eigenvalues, if l = μ then 1 else 0)
      = spectralFunction hQ (fun _ => 1) := by
    refine spectralFunction_congr hQ fun i => ?_
    rw [Finset.sum_ite_eq (Finset.univ.image hQ.eigenvalues) (hQ.eigenvalues i)
      (fun _ => (1 : ℝ)), ite_eq_left
      (Finset.mem_image_of_mem hQ.eigenvalues (Finset.mem_univ i))]
  rw [h1, spectralFunction_const, Complex.ofReal_one, one_smul]

/-- Anything commuting with the charge commutes with every sector. -/
theorem sectorProj_commute {Q M : Matrix n n ℂ} (hQ : Q.IsHermitian)
    (hcomm : Q * M = M * Q) (μ : ℝ) :
    sectorProj hQ μ * M = M * sectorProj hQ μ := by
  classical
  have hright : ∀ ν : ℝ, Q * (M * sectorProj hQ ν)
      = (ν : ℂ) • (M * sectorProj hQ ν) := by
    intro ν
    rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, charge_mul_sectorProj hQ ν,
      Matrix.mul_smul]
  have hexp : sectorProj hQ μ * M
      = ∑ ν ∈ Finset.univ.image hQ.eigenvalues,
          sectorProj hQ μ * (M * sectorProj hQ ν) := by
    calc sectorProj hQ μ * M
        = sectorProj hQ μ * M * ∑ ν ∈ Finset.univ.image hQ.eigenvalues,
            sectorProj hQ ν := by rw [sectorProj_sum hQ, Matrix.mul_one]
      _ = ∑ ν ∈ Finset.univ.image hQ.eigenvalues,
            sectorProj hQ μ * (M * sectorProj hQ ν) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ν _ => by rw [Matrix.mul_assoc]
  have hexp2 : M * sectorProj hQ μ
      = ∑ ν ∈ Finset.univ.image hQ.eigenvalues,
          sectorProj hQ ν * (M * sectorProj hQ μ) := by
    calc M * sectorProj hQ μ
        = (∑ ν ∈ Finset.univ.image hQ.eigenvalues, sectorProj hQ ν)
            * (M * sectorProj hQ μ) := by rw [sectorProj_sum hQ, Matrix.one_mul]
      _ = ∑ ν ∈ Finset.univ.image hQ.eigenvalues,
            sectorProj hQ ν * (M * sectorProj hQ μ) := Finset.sum_mul _ _ _
  rw [hexp, hexp2]
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases hν : ν = μ
  · rw [hν]
  · rw [sectorProj_mul_eq_zero hQ (hright ν) (fun h => hν h.symm),
      sectorProj_mul_eq_zero hQ (hright μ) hν]

/-- **(QSF.12)**: commuting resolvents at `i` force strong commutation of
the charge and the OS Hamiltonian, and every spectral sector of the charge
reduces `H`. -/
theorem strong_commutation {Q H : Matrix n n ℂ} (hQ : Q.IsHermitian)
    (hH : H.IsHermitian)
    (hres : (Q - Complex.I • 1)⁻¹ * (H - Complex.I • 1)⁻¹
      = (H - Complex.I • 1)⁻¹ * (Q - Complex.I • 1)⁻¹) :
    Q * H = H * Q ∧
      ∀ μ : ℝ, sectorProj hQ μ * H = H * sectorProj hQ μ := by
  have hzQ : ∀ i, ((hQ.eigenvalues i : ℂ)) ≠ Complex.I := by
    intro i hcon
    have him := congrArg Complex.im hcon
    rw [Complex.ofReal_im, Complex.I_im] at him
    norm_num at him
  have hzH : ∀ i, ((hH.eigenvalues i : ℂ)) ≠ Complex.I := by
    intro i hcon
    have him := congrArg Complex.im hcon
    rw [Complex.ofReal_im, Complex.I_im] at him
    norm_num at him
  obtain ⟨huQ, -⟩ := CSpec.shift_inv_eq_cSpec hQ hzQ
  obtain ⟨huH, -⟩ := CSpec.shift_inv_eq_cSpec hH hzH
  have hQdet := (Matrix.isUnit_iff_isUnit_det _).mp huQ
  have hHdet := (Matrix.isUnit_iff_isUnit_det _).mp huH
  have h2 : (H - Complex.I • 1) * (Q - Complex.I • 1)
      = (Q - Complex.I • 1) * (H - Complex.I • 1) := by
    have h1 := congrArg Inv.inv hres
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ hQdet, Matrix.nonsing_inv_nonsing_inv _ hHdet]
      at h1
    exact h1
  have hexpand : ∀ X Y : Matrix n n ℂ,
      (X - Complex.I • 1) * (Y - Complex.I • 1)
        = X * Y - Complex.I • Y - Complex.I • X + (Complex.I * Complex.I) • 1 := by
    intro X Y
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  rw [hexpand, hexpand] at h2
  have hQH : Q * H = H * Q := by
    linear_combination (norm := module) -h2
  exact ⟨hQH, fun μ => sectorProj_commute hQ hQH μ⟩

/-- **(QSF.13)**: the exact charge Pythagoras
`Y_Q^*Y_Q = 𝔾_Q^Φ + 𝔾_Q^{S|Φ} + ℂ_Q^unbal` through the flux range and the
flux-orthogonalized screening range, all three pieces PSD. -/
theorem charge_pythagoras {k eQ eΦ eS : Type*} [Fintype k] [DecidableEq k]
    [Fintype eQ] [Fintype eΦ] [DecidableEq eΦ] [Fintype eS] [DecidableEq eS]
    (YQ : Matrix k eQ ℂ) (YΦ : Matrix k eΦ ℂ) (YS : Matrix k eS ℂ) :
    YQᴴ * YQ
        = YQᴴ * colProj YΦ * YQ
          + YQᴴ * colProj (ChargeFlux.screenRes YΦ YS) * YQ
          + YQᴴ * ((1 : Matrix k k ℂ) - colProj YΦ
              - colProj (ChargeFlux.screenRes YΦ YS)) * YQ ∧
      (YQᴴ * colProj YΦ * YQ).PosSemidef ∧
      (YQᴴ * colProj (ChargeFlux.screenRes YΦ YS) * YQ).PosSemidef ∧
      (YQᴴ * ((1 : Matrix k k ℂ) - colProj YΦ
          - colProj (ChargeFlux.screenRes YΦ YS)) * YQ).PosSemidef :=
  ChargeFlux.defect_decomposition YQ YΦ YS

/-- **Zero-residual classification**: on the zero-residual branch the
charge Gram splits into flux and screening, and a nonzero charge is
unscreened, completely screened, or partially screened. -/
theorem screened_classification {k eQ eΦ eS : Type*} [Fintype k] [DecidableEq k]
    [Fintype eQ] [Fintype eΦ] [DecidableEq eΦ] [Fintype eS] [DecidableEq eS]
    (YQ : Matrix k eQ ℂ) (YΦ : Matrix k eΦ ℂ) (YS : Matrix k eS ℂ)
    (hres : YQᴴ * ((1 : Matrix k k ℂ) - colProj YΦ
        - colProj (ChargeFlux.screenRes YΦ YS)) * YQ = 0) :
    YQᴴ * YQ = YQᴴ * colProj YΦ * YQ
        + YQᴴ * colProj (ChargeFlux.screenRes YΦ YS) * YQ ∧
      (YQ ≠ 0 →
        (YQᴴ * colProj YΦ * YQ = 0
            ∧ YQᴴ * colProj (ChargeFlux.screenRes YΦ YS) * YQ ≠ 0) ∨
          (YQᴴ * colProj YΦ * YQ ≠ 0
            ∧ YQᴴ * colProj (ChargeFlux.screenRes YΦ YS) * YQ = 0) ∨
          (YQᴴ * colProj YΦ * YQ ≠ 0
            ∧ YQᴴ * colProj (ChargeFlux.screenRes YΦ YS) * YQ ≠ 0)) := by
  obtain ⟨hsum, -, -, -⟩ := charge_pythagoras YQ YΦ YS
  rw [hres, add_zero] at hsum
  refine ⟨hsum, fun hYQ => ?_⟩
  by_cases h1 : YQᴴ * colProj YΦ * YQ = 0
  · by_cases h2 : YQᴴ * colProj (ChargeFlux.screenRes YΦ YS) * YQ = 0
    · exfalso
      rw [h1, h2, add_zero] at hsum
      exact hYQ (Matrix.conjTranspose_mul_self_eq_zero.mp hsum)
    · exact Or.inl ⟨h1, h2⟩
  · by_cases h2 : YQᴴ * colProj (ChargeFlux.screenRes YΦ YS) * YQ = 0
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- The column projection of the zero synthesis vanishes. -/
theorem colProj_zero {k e : Type*} [Fintype k] [Fintype e] [DecidableEq e] :
    colProj (0 : Matrix k e ℂ) = 0 := by
  unfold colProj
  rw [Matrix.zero_mul, Matrix.zero_mul]

/-- **Screened-branch witness**: zero asymptotic flux does not imply zero
matter charge — an explicit completely screened charge with zero flux Gram
and nonzero charge synthesis. -/
theorem screened_charge_witness :
    ∃ (YQ YΦ YS : Matrix (Fin 1) (Fin 1) ℂ),
      YQᴴ * colProj YΦ * YQ = 0 ∧ YQ ≠ 0 ∧
        YQᴴ * ((1 : Matrix (Fin 1) (Fin 1) ℂ) - colProj YΦ
            - colProj (ChargeFlux.screenRes YΦ YS)) * YQ = 0 := by
  refine ⟨1, 0, 1, ?_, ?_, ?_⟩
  · rw [colProj_zero, Matrix.mul_zero, Matrix.zero_mul]
  · exact one_ne_zero
  · have hscreen : ChargeFlux.screenRes (0 : Matrix (Fin 1) (Fin 1) ℂ)
        (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
      unfold ChargeFlux.screenRes
      rw [colProj_zero, sub_zero, Matrix.one_mul]
    rw [hscreen, colProj_zero, sub_zero]
    have hone : colProj (1 : Matrix (Fin 1) (Fin 1) ℂ) * 1 = 1 :=
      colProj_mul_self (1 : Matrix (Fin 1) (Fin 1) ℂ)
    rw [Matrix.mul_one] at hone
    rw [hone, sub_self, Matrix.mul_zero, Matrix.zero_mul]

/-- **(QSF.14)**: the sector Gram `𝔾_λ^sec = B^*P_λB`. -/
noncomputable def sectorGram {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {e : Type*}
    (B : Matrix n e ℂ) (μ : ℝ) : Matrix e e ℂ :=
  Bᴴ * sectorProj hQ μ * B

open Classical in
/-- **(QSF.14)**: the visible charge set `Λ_Q^vis = {λ : 𝔾_λ^sec ≠ 0}`. -/
noncomputable def visibleSet {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {e : Type*}
    [Fintype e] (B : Matrix n e ℂ) : Finset ℝ :=
  (Finset.univ.image hQ.eigenvalues).filter fun μ => sectorGram hQ B μ ≠ 0

/-- An invisible sector annihilates the source atlas. -/
theorem sectorProj_mul_source_eq_zero {Q : Matrix n n ℂ} (hQ : Q.IsHermitian)
    {e : Type*} [Fintype e] {B : Matrix n e ℂ} {μ : ℝ}
    (h : sectorGram hQ B μ = 0) : sectorProj hQ μ * B = 0 := by
  have hgram : (sectorProj hQ μ * B)ᴴ * (sectorProj hQ μ * B) = 0 := by
    rw [conjTranspose_mul, (sectorProj_isHermitian hQ μ).eq]
    calc Bᴴ * sectorProj hQ μ * (sectorProj hQ μ * B)
        = Bᴴ * (sectorProj hQ μ * sectorProj hQ μ) * B := by
          simp only [Matrix.mul_assoc]
      _ = Bᴴ * sectorProj hQ μ * B := by rw [sectorProj_idem hQ μ]
      _ = 0 := h
  exact Matrix.conjTranspose_mul_self_eq_zero.mp hgram

/-- The visible carrier: the observable-algebra orbit of the source
columns. -/
def visSpace (A : Subalgebra ℂ (Matrix n n ℂ)) {e : Type*} [Fintype e]
    (B : Matrix n e ℂ) : Submodule ℂ (n → ℂ) :=
  Submodule.span ℂ {y | ∃ M ∈ A, ∃ v, y = M *ᵥ (B *ᵥ v)}

/-- The list product of spectral shifts is a spectral function. -/
theorem list_shift_prod {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (L : List ℝ) :
    (L.map fun ν : ℝ => Q - (ν : ℂ) • (1 : Matrix n n ℂ)).prod
      = spectralFunction hQ fun l => (L.map fun ν => l - ν).prod := by
  induction L with
  | nil =>
    rw [List.map_nil, List.prod_nil]
    have h1 : (fun l : ℝ => (List.map (fun ν => l - ν) []).prod)
        = fun _ : ℝ => (1 : ℝ) := by
      funext l
      rw [List.map_nil, List.prod_nil]
    rw [h1, spectralFunction_const, Complex.ofReal_one, one_smul]
  | cons ν L ih =>
    rw [List.map_cons, List.prod_cons, ih, sub_smul_one_eq_spectral hQ ν,
      spectralFunction_mul]
    refine spectralFunction_congr hQ fun i => ?_
    rw [List.map_cons, List.prod_cons]

/-- Sector projections lie in every subalgebra containing the charge
(Lagrange interpolation on the finite spectrum). -/
theorem sectorProj_mem (A : Subalgebra ℂ (Matrix n n ℂ)) {Q : Matrix n n ℂ}
    (hQ : Q.IsHermitian) (hQmem : Q ∈ A) (μ : ℝ) : sectorProj hQ μ ∈ A := by
  classical
  by_cases hμ : μ ∈ Finset.univ.image hQ.eigenvalues
  · set L : List ℝ := ((Finset.univ.image hQ.eigenvalues).erase μ).toList with hL
    have hne : (L.map fun ν => μ - ν).prod ≠ 0 := by
      refine List.prod_ne_zero fun hcon => ?_
      obtain ⟨ν, hν, hν0⟩ := List.mem_map.mp hcon
      have hνμ : ν ≠ μ :=
        (Finset.mem_erase.mp ((Finset.mem_toList).mp hν)).1
      exact hνμ (sub_eq_zero.mp hν0).symm
    set c : ℝ := ((L.map fun ν => μ - ν).prod)⁻¹ with hc
    have hrepr : sectorProj hQ μ
        = (c : ℂ) • (L.map fun ν : ℝ => Q - (ν : ℂ) • (1 : Matrix n n ℂ)).prod := by
      rw [list_shift_prod hQ L, ← spectralFunction_smul]
      unfold sectorProj
      refine spectralFunction_congr hQ fun i => ?_
      by_cases h : hQ.eigenvalues i = μ
      · rw [ite_eq_left h, h]
        rw [hc, inv_mul_cancel₀ hne]
      · rw [ite_eq_right h]
        have hmem : hQ.eigenvalues i ∈ L := by
          rw [hL, Finset.mem_toList, Finset.mem_erase]
          exact ⟨h, Finset.mem_image_of_mem hQ.eigenvalues (Finset.mem_univ i)⟩
        have hzero : (L.map fun ν => hQ.eigenvalues i - ν).prod = 0 := by
          refine List.prod_eq_zero ?_
          exact List.mem_map.mpr ⟨hQ.eigenvalues i, hmem, sub_self _⟩
        rw [hzero, mul_zero]
    rw [hrepr]
    refine Subalgebra.smul_mem A ?_ _
    refine Subalgebra.list_prod_mem A fun X hX => ?_
    obtain ⟨ν, -, rfl⟩ := List.mem_map.mp hX
    exact Subalgebra.sub_mem A hQmem (Subalgebra.smul_mem A (Subalgebra.one_mem A) _)
  · have h0 : sectorProj hQ μ = 0 := by
      unfold sectorProj
      have hz : spectralFunction hQ (fun l => if l = μ then 1 else 0)
          = spectralFunction hQ fun _ => 0 := by
        refine spectralFunction_congr hQ fun i => ?_
        rw [ite_eq_right]
        intro hcon
        exact absurd (hcon ▸ Finset.mem_image_of_mem hQ.eigenvalues
          (Finset.mem_univ i)) hμ
      rw [hz, spectralFunction_const, Complex.ofReal_zero, zero_smul]
    rw [h0]
    exact Subalgebra.zero_mem A

/-- **(QSF.15)**: the visible superselection decomposition — invisible
sectors annihilate the visible carrier, sector components stay in the
carrier, and the visible sectors reconstruct every visible vector. -/
theorem visible_superselection (A : Subalgebra ℂ (Matrix n n ℂ))
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (hQmem : Q ∈ A)
    (hcomm : ∀ M ∈ A, Q * M = M * Q)
    {e : Type*} [Fintype e] (B : Matrix n e ℂ) :
    (∀ μ : ℝ, sectorGram hQ B μ = 0 →
      ∀ y ∈ visSpace A B, sectorProj hQ μ *ᵥ y = 0) ∧
    (∀ μ : ℝ, ∀ y ∈ visSpace A B, sectorProj hQ μ *ᵥ y ∈ visSpace A B) ∧
    (∀ y ∈ visSpace A B, ∑ μ ∈ visibleSet hQ B, sectorProj hQ μ *ᵥ y = y) := by
  classical
  have hkill : ∀ μ : ℝ, sectorGram hQ B μ = 0 →
      ∀ y ∈ visSpace A B, sectorProj hQ μ *ᵥ y = 0 := by
    intro μ hμ y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨M, hM, v, rfl⟩ := hy
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        sectorProj_commute hQ (hcomm M hM) μ, Matrix.mul_assoc,
        sectorProj_mul_source_eq_zero hQ hμ, Matrix.mul_zero, Matrix.zero_mulVec]
    | zero => rw [Matrix.mulVec_zero]
    | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz, add_zero]
    | smul a y _ hy => rw [Matrix.mulVec_smul, hy, smul_zero]
  refine ⟨hkill, ?_, ?_⟩
  · intro μ y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨M, hM, v, rfl⟩ := hy
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      exact Submodule.subset_span
        ⟨sectorProj hQ μ * M, A.mul_mem (sectorProj_mem A hQ hQmem μ) hM, v,
          (Matrix.mulVec_mulVec _ _ _).symm⟩
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [Matrix.mulVec_add]
      exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ a hy
  · intro y hy
    have hall : ∑ μ ∈ Finset.univ.image hQ.eigenvalues, sectorProj hQ μ *ᵥ y = y := by
      rw [← Matrix.sum_mulVec, sectorProj_sum hQ, Matrix.one_mulVec]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ.image hQ.eigenvalues) (fun μ => sectorGram hQ B μ ≠ 0)
      (fun μ => sectorProj hQ μ *ᵥ y)
    have hinvis : ∑ μ ∈ (Finset.univ.image hQ.eigenvalues).filter
        (fun μ => ¬ sectorGram hQ B μ ≠ 0), sectorProj hQ μ *ᵥ y = 0 := by
      refine Finset.sum_eq_zero fun μ hμ => ?_
      have h0 : sectorGram hQ B μ = 0 :=
        not_not.mp (Finset.mem_filter.mp hμ).2
      exact hkill μ h0 y hy
    unfold visibleSet
    rw [← hsplit] at hall
    rw [hinvis, add_zero] at hall
    exact hall

/-- **Observables have no off-diagonal blocks between distinct charges.** -/
theorem observable_no_offdiagonal {Q M : Matrix n n ℂ} (hQ : Q.IsHermitian)
    (hcommM : Q * M = M * Q) {μ ν : ℝ} (hμν : μ ≠ ν) :
    sectorProj hQ μ * M * sectorProj hQ ν = 0 := by
  have h1 : Q * (M * sectorProj hQ ν) = (ν : ℂ) • (M * sectorProj hQ ν) := by
    rw [← Matrix.mul_assoc, hcommM, Matrix.mul_assoc, charge_mul_sectorProj hQ ν,
      Matrix.mul_smul]
  rw [Matrix.mul_assoc]
  exact sectorProj_mul_eq_zero hQ h1 hμν

/-- **(QSF.16)**: the charged-field ladder relation
`P_{λ+q} Ψ_q P_λ = Ψ_q P_λ` for a held-out field with `[Q,Ψ_q] = qΨ_q`. -/
theorem charged_field_ladder {Q Psi : Matrix n n ℂ} (hQ : Q.IsHermitian) (q : ℝ)
    (hlad : Q * Psi - Psi * Q = (q : ℂ) • Psi) (lam : ℝ) :
    sectorProj hQ (lam + q) * (Psi * sectorProj hQ lam)
      = Psi * sectorProj hQ lam := by
  have h2 : Q * Psi = Psi * Q + (q : ℂ) • Psi := by
    rw [← hlad]
    abel
  have h1 : Q * (Psi * sectorProj hQ lam)
      = ((lam + q : ℝ) : ℂ) • (Psi * sectorProj hQ lam) := by
    rw [← Matrix.mul_assoc, h2, Matrix.add_mul, Matrix.mul_assoc,
      charge_mul_sectorProj hQ lam, Matrix.mul_smul, Matrix.smul_mul,
      Complex.ofReal_add, add_smul]
  exact sectorProj_mul_eq_self hQ h1

end Superselection

end SuperselectionSection

/-! ### `thm:SMOS-translation-target-ladder` — The two resolvent variables

Rendering: the source-cyclic realization of `thm:SMOS-translation-GNS` on
the finite carrier is a PSD Hamiltonian `H`, a commuting Hermitian
momentum `P` (whose Stone generator gives the spatial translation
unitaries `U(x) = e^{ixP}` for one spatial dimension), and a source
synthesis `B`; the translated kernel is
`F(t,x) = B^*e^{-tH}U(x)B` with semigroup and unitaries realized by the
complex spectral calculus.  (LNS.13a) is the entrywise Laplace identity on
`(0,∞)`; (LNS.13b) is the one-sided Dirichlet limit (the finite carrier
makes the form domain automatic and the squared norm is the canonical
sesquilinear square); (LNS.13c) is the invariant-mass resolvent of
`A = H² - P²`, well defined off `[0,∞)`.  The forgetting counterexample
(LNS.13d) is realized by the explicit models `H₀ = 2, P₀ = 0, B₀ = 1` and
`H₁ = 2·1₂, P₁ = diag(1,-1), B₁ = 2^{-1/2}(1,1)ᵀ` of the scalar kernels
`e^{-2t}` and `e^{-2t}cos x₁`: identical time-only kernels (hence
identical Laplace panels and Dirichlet forms), invariant-mass supports
`{4}` and `{3}` through the sector Grams of `A`.  The converse
hyperboloid-forgetting witness has equal mass operators and sector Grams
but different compressed momenta. -/

section TranslationLadderSection

namespace TranslationLadder

open CSpec MeasureTheory

variable {n e : Type*} [Fintype n] [DecidableEq n] [Fintype e]

/-- The Euclidean clock `e^{-tH}` by spectral calculus. -/
noncomputable def clock {H : Matrix n n ℂ} (hH : H.IsHermitian) (t : ℝ) :
    Matrix n n ℂ :=
  cSpec hH fun l => ((Real.exp (-(t * l)) : ℝ) : ℂ)

/-- The spatial translation unitary `U(x) = e^{ixP}` by spectral
calculus. -/
noncomputable def spaceU {P : Matrix n n ℂ} (hP : P.IsHermitian) (x : ℝ) :
    Matrix n n ℂ :=
  cSpec hP fun p => Complex.exp (((p * x : ℝ) : ℂ) * Complex.I)

/-- The complete translated source kernel `F(t,x) = B^*e^{-tH}U(x)B`
(LNS.9/LNS.11). -/
noncomputable def transKernel {H P : Matrix n n ℂ} (hH : H.IsHermitian)
    (hP : P.IsHermitian) (B : Matrix n e ℂ) (t x : ℝ) : Matrix e e ℂ :=
  Bᴴ * (clock hH t * spaceU hP x) * B

/-- The spatial unitary at the origin is the identity. -/
theorem spaceU_zero {P : Matrix n n ℂ} (hP : P.IsHermitian) : spaceU hP 0 = 1 := by
  unfold spaceU
  have h1 : cSpec hP (fun p => Complex.exp (((p * 0 : ℝ) : ℂ) * Complex.I))
      = cSpec hP fun _ => (1 : ℂ) := by
    refine cSpec_congr hP fun i => ?_
    rw [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [h1, cSpec_const, one_smul]

omit [Fintype e] in
/-- The time-only restriction of the kernel. -/
theorem transKernel_time {H P : Matrix n n ℂ} (hH : H.IsHermitian)
    (hP : P.IsHermitian) (B : Matrix n e ℂ) (t : ℝ) :
    transKernel hH hP B t 0 = Bᴴ * clock hH t * B := by
  unfold transKernel
  rw [spaceU_zero, Matrix.mul_one]

/-- The entrywise expansion of the time-only kernel. -/
theorem transKernel_entry {H P : Matrix n n ℂ} (hH : H.IsHermitian)
    (hP : P.IsHermitian) (B : Matrix n e ℂ) (t : ℝ) (c d : e) :
    transKernel hH hP B t 0 c d
      = ∑ i, ((Real.exp (-(t * hH.eigenvalues i)) : ℝ) : ℂ) * wMat hH B i c d := by
  rw [transKernel_time, clock, compress_cSpec, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]

/-- **(LNS.13a)**: the fixed-Laplace Green identity
`Q_λ = ∫₀^∞ e^{-λt}F(t,0) dt = B^*(H+λ)⁻¹B`, entrywise on the finite
carrier. -/
theorem laplace_resolvent_identity {H P : Matrix n n ℂ} (hH : H.IsHermitian)
    (hP : P.IsHermitian) (hpos : H.PosSemidef) (B : Matrix n e ℂ)
    {lam : ℝ} (hlam : 0 < lam) (c d : e) :
    ∫ t in Set.Ioi (0 : ℝ),
        ((Real.exp (-(lam * t)) : ℝ) : ℂ) * transKernel hH hP B t 0 c d
      = (Bᴴ * (H + (lam : ℂ) • 1)⁻¹ * B) c d := by
  classical
  -- the resolvent side
  have hz : ∀ i, ((hH.eigenvalues i : ℂ)) ≠ -((lam : ℝ) : ℂ) := by
    intro i hcon
    have hre := congrArg Complex.re hcon
    rw [Complex.ofReal_re, Complex.neg_re, Complex.ofReal_re] at hre
    have h0 : 0 ≤ hH.eigenvalues i := hpos.eigenvalues_nonneg i
    linarith
  obtain ⟨-, hinv⟩ := shift_inv_eq_cSpec hH hz
  have hplus : H + (lam : ℂ) • (1 : Matrix n n ℂ)
      = H - (-((lam : ℝ) : ℂ)) • (1 : Matrix n n ℂ) := by
    rw [neg_smul, sub_neg_eq_add]
  rw [hplus, hinv, compress_cSpec, Matrix.sum_apply]
  -- the integrand as a finite exponential sum
  have hnegre : ∀ i : n, ((-(lam + hH.eigenvalues i) : ℝ) : ℂ).re < 0 := by
    intro i
    rw [Complex.ofReal_re]
    have h0 : 0 ≤ hH.eigenvalues i := hpos.eigenvalues_nonneg i
    linarith
  have hint : ∀ i : n, IntegrableOn
      (fun t : ℝ => Complex.exp (((-(lam + hH.eigenvalues i) : ℝ) : ℂ) * t))
      (Set.Ioi (0 : ℝ)) MeasureTheory.volume :=
    fun i => integrableOn_exp_mul_complex_Ioi (hnegre i) 0
  have hfun : Set.EqOn
      (fun t : ℝ => ((Real.exp (-(lam * t)) : ℝ) : ℂ) * transKernel hH hP B t 0 c d)
      (fun t : ℝ => ∑ i, Complex.exp (((-(lam + hH.eigenvalues i) : ℝ) : ℂ) * t)
        * wMat hH B i c d)
      (Set.Ioi (0 : ℝ)) := by
    intro t _
    simp only
    rw [transKernel_entry hH hP B t c d, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    congr 1
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have harg : Complex.exp (((-(lam + hH.eigenvalues i) : ℝ) : ℂ) * t)
        = ((Real.exp (-(lam + hH.eigenvalues i) * t) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp, Complex.ofReal_mul]
    rw [harg]
    congr 2
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hfun,
    MeasureTheory.integral_finsetSum _ fun i _ => (hint i).mul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_mul_const, integral_exp_mul_complex_Ioi (hnegre i) 0,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, Matrix.smul_apply, smul_eq_mul]
  congr 1
  rw [Complex.ofReal_neg, neg_div_neg_eq, one_div]
  congr 1
  push_cast
  ring

omit [DecidableEq n] in
/-- The sesquilinear Gram square `‖Mv‖² = ⟨v, M^*Mv⟩`. -/
theorem gram_quadform (M : Matrix n e ℂ) (v : e → ℂ) :
    star (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = star v ⬝ᵥ ((Mᴴ * M) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

/-- **(LNS.13b)**: the one-sided Dirichlet limit of the time-only kernel
recovers the kinetic form `‖H^{1/2}B c‖²`. -/
theorem dirichlet_limit {H P : Matrix n n ℂ} (hH : H.IsHermitian)
    (hP : P.IsHermitian) (hpos : H.PosSemidef) (B : Matrix n e ℂ) (c : e → ℂ) :
    Filter.Tendsto (fun t : ℝ =>
        (star c ⬝ᵥ ((transKernel hH hP B 0 0 - transKernel hH hP B t 0) *ᵥ c)) / (t : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (star ((psdSqrt hH * B) *ᵥ c) ⬝ᵥ ((psdSqrt hH * B) *ᵥ c))) := by
  classical
  -- the difference kernel is the compressed spectral function `1 - e^{-tλ}`
  have hdiff : ∀ t : ℝ, transKernel hH hP B 0 0 - transKernel hH hP B t 0
      = ∑ i, ((1 - Real.exp (-(t * hH.eigenvalues i)) : ℝ) : ℂ) • wMat hH B i := by
    intro t
    rw [transKernel_time, transKernel_time]
    unfold clock
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, cSpec_sub hH]
    have hzero : cSpec hH (fun l => (((Real.exp (-(0 * l)) : ℝ) : ℂ))
          - ((Real.exp (-(t * l)) : ℝ) : ℂ))
        = cSpec hH fun l => (((1 - Real.exp (-(t * l)) : ℝ) : ℂ)) := by
      refine cSpec_congr hH fun i => ?_
      rw [zero_mul, neg_zero, Real.exp_zero, Complex.ofReal_sub, Complex.ofReal_one]
    rw [hzero, compress_cSpec]
  -- the quadratic form as a finite sum
  have hquad : ∀ t : ℝ,
      star c ⬝ᵥ ((transKernel hH hP B 0 0 - transKernel hH hP B t 0) *ᵥ c)
        = ∑ i, ((1 - Real.exp (-(t * hH.eigenvalues i)) : ℝ) : ℂ)
            * (star c ⬝ᵥ (wMat hH B i *ᵥ c)) := by
    intro t
    rw [hdiff t, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  -- the limit form as the same weights against the eigenvalues
  have hlimit : star ((psdSqrt hH * B) *ᵥ c) ⬝ᵥ ((psdSqrt hH * B) *ᵥ c)
      = ∑ i, ((hH.eigenvalues i : ℝ) : ℂ) * (star c ⬝ᵥ (wMat hH B i *ᵥ c)) := by
    rw [gram_quadform]
    have hgram : (psdSqrt hH * B)ᴴ * (psdSqrt hH * B) = Bᴴ * H * B := by
      rw [conjTranspose_mul, (psdSqrt_posSemidef hH).1.eq]
      calc Bᴴ * psdSqrt hH * (psdSqrt hH * B)
          = Bᴴ * (psdSqrt hH * psdSqrt hH) * B := by simp only [Matrix.mul_assoc]
        _ = Bᴴ * H * B := by rw [psdSqrt_mul_self hpos]
    have hHspec : Bᴴ * H * B = ∑ i, ((hH.eigenvalues i : ℝ) : ℂ) • wMat hH B i := by
      conv_lhs => rw [← cSpec_id hH]
      exact compress_cSpec hH B _
    rw [hgram, hHspec, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  -- pointwise identification on the right half line, then termwise limits
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      (star c ⬝ᵥ ((transKernel hH hP B 0 0 - transKernel hH hP B t 0) *ᵥ c)) / (t : ℂ)
        = ∑ i, (((1 - Real.exp (-(t * hH.eigenvalues i))) / t : ℝ) : ℂ)
            * (star c ⬝ᵥ (wMat hH B i *ᵥ c)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Set.mem_Ioi.mp ht)
    rw [hquad t, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_div]
    ring
  rw [hlimit]
  have hterm : ∀ i : n, Filter.Tendsto
      (fun t : ℝ => (((1 - Real.exp (-(t * hH.eigenvalues i))) / t : ℝ) : ℂ)
        * (star c ⬝ᵥ (wMat hH B i *ᵥ c)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((hH.eigenvalues i : ℝ) : ℂ) * (star c ⬝ᵥ (wMat hH B i *ᵥ c)))) := by
    intro i
    refine Filter.Tendsto.mul_const _ ?_
    -- scalar limit `(1 - e^{-tλ})/t → λ` as `t ↓ 0`
    have hderiv : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(t * hH.eigenvalues i)))
        (hH.eigenvalues i) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => -(t * hH.eigenvalues i))
          (-hH.eigenvalues i) 0 := (hasDerivAt_mul_const (hH.eigenvalues i)).neg
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(t * hH.eigenvalues i)))
          (Real.exp (-(0 * hH.eigenvalues i)) * -hH.eigenvalues i) 0 := h1.exp
      have h3 := h2.const_sub 1
      have heq : -(Real.exp (-(0 * hH.eigenvalues i)) * -hH.eigenvalues i)
          = hH.eigenvalues i := by
        rw [zero_mul, neg_zero, Real.exp_zero]
        ring
      rw [heq] at h3
      exact h3
    have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
    have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_mono 0 fun t ht => ne_of_gt ht
    have hslope' := hslope.mono_left hsub
    refine Filter.Tendsto.comp (Complex.continuous_ofReal.tendsto _) ?_
    refine hslope'.congr fun t => ?_
    rw [slope_def_field, zero_mul, neg_zero, Real.exp_zero, sub_self, sub_zero,
      sub_zero]
  have hsum : Filter.Tendsto
      (fun t : ℝ => ∑ i, (((1 - Real.exp (-(t * hH.eigenvalues i))) / t : ℝ) : ℂ)
        * (star c ⬝ᵥ (wMat hH B i *ᵥ c)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ i, ((hH.eigenvalues i : ℝ) : ℂ) * (star c ⬝ᵥ (wMat hH B i *ᵥ c)))) :=
    tendsto_finsetSum _ fun i _ => hterm i
  have heqf : (fun t : ℝ => ∑ i, (((1 - Real.exp (-(t * hH.eigenvalues i))) / t : ℝ) : ℂ)
        * (star c ⬝ᵥ (wMat hH B i *ᵥ c)))
      =ᶠ[𝓝[>] (0 : ℝ)]
      fun t : ℝ =>
        (star c ⬝ᵥ ((transKernel hH hP B 0 0 - transKernel hH hP B t 0) *ᵥ c))
          / (t : ℂ) :=
    eventuallyEq_nhdsWithin_of_eqOn fun t ht => (hcongr t ht).symm
  exact Filter.Tendsto.congr' heqf hsum

omit [DecidableEq n] in
/-- The invariant-mass operator `A = H² - P²` is Hermitian. -/
theorem invariantMass_isHermitian {H P : Matrix n n ℂ} (hH : H.IsHermitian)
    (hP : P.IsHermitian) : (H * H - P * P).IsHermitian := by
  change (H * H - P * P)ᴴ = _
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hH.eq, hP.eq]

/-- **(LNS.13c)**: the invariant-mass resolvent
`G^M(z) = B^*(A - z)⁻¹B` on `ℂ \ [0,∞)`. -/
noncomputable def massResolvent (H P : Matrix n n ℂ) {e : Type*}
    (B : Matrix n e ℂ) (z : ℂ) : Matrix e e ℂ :=
  Bᴴ * (H * H - P * P - z • 1)⁻¹ * B

/-- The invariant-mass resolvent is well defined off `[0,∞)`: under the
forward-cone gate `A ⪰ 0`, the shift is a unit with spectral inverse. -/
theorem massResolvent_wellDefined {H P : Matrix n n ℂ} (hH : H.IsHermitian)
    (hP : P.IsHermitian) (hA : (H * H - P * P).PosSemidef) {z : ℂ}
    (hz : ∀ r : ℝ, 0 ≤ r → (r : ℂ) ≠ z) :
    IsUnit (H * H - P * P - z • (1 : Matrix n n ℂ)) ∧
      (H * H - P * P - z • (1 : Matrix n n ℂ))
          * (H * H - P * P - z • (1 : Matrix n n ℂ))⁻¹ = 1 := by
  have hz' : ∀ i, (((invariantMass_isHermitian hH hP).eigenvalues i : ℂ)) ≠ z :=
    fun i => hz _ (hA.eigenvalues_nonneg i)
  obtain ⟨hu, hinv⟩ := shift_inv_eq_cSpec (invariantMass_isHermitian hH hP) hz'
  refine ⟨hu, ?_⟩
  rw [hinv]
  exact (cSpec_resolvent (invariantMass_isHermitian hH hP) hz').1

/-! #### The forgetting counterexample (LNS.13d) -/

/-- A scalar Hermitian matrix has constant spectral calculus. -/
theorem cSpec_smul_one {c : ℝ} {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hAc : A = (c : ℂ) • 1) (f : ℝ → ℂ) : cSpec hA f = f c • 1 := by
  have hUD : (hA.eigenvectorUnitary : Matrix n n ℂ)
      * diagonal (fun i => (hA.eigenvalues i : ℂ))
      * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = (c : ℂ) • 1 :=
    (hermitian_spectral' hA).symm.trans hAc
  have hdiag : diagonal (fun i => (hA.eigenvalues i : ℂ))
      = (c : ℂ) • (1 : Matrix n n ℂ) := by
    calc diagonal (fun i => (hA.eigenvalues i : ℂ))
        = (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ
          * ((hA.eigenvectorUnitary : Matrix n n ℂ)
            * diagonal (fun i => (hA.eigenvalues i : ℂ))
            * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
          * (hA.eigenvectorUnitary : Matrix n n ℂ) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, unitary_ct_mul hA, Matrix.mul_one,
            ← Matrix.mul_assoc, unitary_ct_mul hA, Matrix.one_mul]
      _ = (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * ((c : ℂ) • 1)
          * (hA.eigenvectorUnitary : Matrix n n ℂ) := by rw [hUD]
      _ = (c : ℂ) • (1 : Matrix n n ℂ) := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, unitary_ct_mul hA]
  have heig : ∀ i, hA.eigenvalues i = c := by
    intro i
    have hii := congrFun (congrFun hdiag i) i
    rw [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at hii
    exact_mod_cast hii
  have hcongr : cSpec hA f = cSpec hA fun _ => f c :=
    cSpec_congr hA fun i => by rw [heig i]
  rw [hcongr, cSpec_const]

/-- Sector projection of a scalar operator at its own value is `1`. -/
theorem sectorProj_smul_one_self {c : ℝ} {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hAc : A = ((c : ℝ) : ℂ) • 1) : Superselection.sectorProj hA c = 1 := by
  have hM : A * (1 : Matrix n n ℂ) = ((c : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
    rw [Matrix.mul_one, hAc]
  have h := Superselection.sectorProj_mul_eq_self hA hM
  rwa [Matrix.mul_one] at h

/-- Sector projection of a scalar operator away from its value is `0`. -/
theorem sectorProj_smul_one_ne {c μ : ℝ} {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hAc : A = ((c : ℝ) : ℂ) • 1) (hμ : μ ≠ c) :
    Superselection.sectorProj hA μ = 0 := by
  have hM : A * (1 : Matrix n n ℂ) = ((c : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
    rw [Matrix.mul_one, hAc]
  have h := Superselection.sectorProj_mul_eq_zero hA hM hμ
  rwa [Matrix.mul_one] at h

/-- Model 0: the one-dimensional carrier of `F₀(t,x) = e^{-2t}`. -/
noncomputable def H0 : Matrix (Fin 1) (Fin 1) ℂ := ((2 : ℝ) : ℂ) • 1

/-- Model 0 momentum. -/
def P0 : Matrix (Fin 1) (Fin 1) ℂ := 0

/-- Model 0 source. -/
def B0 : Matrix (Fin 1) (Fin 1) ℂ := 1

/-- Model 1: the two-dimensional carrier of `F₁(t,x) = e^{-2t}cos x₁`. -/
noncomputable def H1 : Matrix (Fin 2) (Fin 2) ℂ := ((2 : ℝ) : ℂ) • 1

/-- Model 1 momentum `P₁ = diag(1,-1)`. -/
def P1 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Model 1 source `B₁ = 2^{-1/2}(1,1)ᵀ`. -/
noncomputable def B1 : Matrix (Fin 2) (Fin 1) ℂ :=
  !![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ); (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)]

/-- `H₀` is Hermitian. -/
theorem H0_isHermitian : H0.IsHermitian := by
  change H0ᴴ = H0
  unfold H0
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
    Complex.conj_ofReal]

/-- `P₀` is Hermitian. -/
theorem P0_isHermitian : P0.IsHermitian := by
  change P0ᴴ = P0
  unfold P0
  rw [Matrix.conjTranspose_zero]

/-- `H₁` is Hermitian. -/
theorem H1_isHermitian : H1.IsHermitian := by
  change H1ᴴ = H1
  unfold H1
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
    Complex.conj_ofReal]

/-- `P₁` is Hermitian. -/
theorem P1_isHermitian : P1.IsHermitian := by
  change P1ᴴ = P1
  unfold P1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply]

/-- The model-1 source has unit Gram: `B₁ᴴB₁ = 1`. -/
theorem B1_gram : B1ᴴ * B1 = 1 := by
  have hs : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
      = ((2 : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num),
      Complex.ofReal_inv]
  ext i j
  have hi : i = 0 := Subsingleton.elim i 0
  have hj : j = 0 := Subsingleton.elim j 0
  subst hi
  subst hj
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply_eq]
  have h0 : B1 0 0 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := rfl
  have h1 : B1 1 0 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := rfl
  rw [h0, h1, Complex.star_def, Complex.conj_ofReal, hs]
  norm_num

/-- **(LNS.13d), kernel identity**: the two models have identical
time-only translated kernels. -/
theorem forgetting_time_kernels (t : ℝ) :
    transKernel H0_isHermitian P0_isHermitian B0 t 0
      = transKernel H1_isHermitian P1_isHermitian B1 t 0 := by
  rw [transKernel_time, transKernel_time]
  unfold clock
  rw [cSpec_smul_one H0_isHermitian rfl, cSpec_smul_one H1_isHermitian rfl]
  unfold B0
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, B1_gram]

/-- **(LNS.13d), Laplace panels**: every fixed-Laplace Green matrix of the
two models agrees. -/
theorem forgetting_laplace (lam : ℝ) (c d : Fin 1) :
    ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-(lam * t)) : ℝ) : ℂ)
        * transKernel H0_isHermitian P0_isHermitian B0 t 0 c d
      = ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-(lam * t)) : ℝ) : ℂ)
        * transKernel H1_isHermitian P1_isHermitian B1 t 0 c d := by
  have hfun : (fun t : ℝ => ((Real.exp (-(lam * t)) : ℝ) : ℂ)
        * transKernel H0_isHermitian P0_isHermitian B0 t 0 c d)
      = fun t : ℝ => ((Real.exp (-(lam * t)) : ℝ) : ℂ)
        * transKernel H1_isHermitian P1_isHermitian B1 t 0 c d := by
    funext t
    rw [forgetting_time_kernels t]
  rw [hfun]

/-- **(LNS.13d), Dirichlet forms**: the compressed kinetic forms agree. -/
theorem forgetting_dirichlet :
    B0ᴴ * H0 * B0 = B1ᴴ * H1 * B1 := by
  unfold B0 H0 H1
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, B1_gram]

/-- The model-0 invariant mass is the scalar `4`. -/
theorem A0_eq : H0 * H0 - P0 * P0 = ((4 : ℝ) : ℂ) • 1 := by
  unfold H0 P0
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    Matrix.zero_mul, sub_zero, ← Complex.ofReal_mul]
  norm_num

/-- The model-1 invariant mass is the scalar `3`. -/
theorem A1_eq : H1 * H1 - P1 * P1 = ((3 : ℝ) : ℂ) • 1 := by
  have hP1 : P1 * P1 = 1 := by
    unfold P1
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp
  unfold H1
  rw [hP1, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    ← Complex.ofReal_mul]
  have h43 : ((4 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - 1
      = ((3 : ℝ) : ℂ) • 1 := by
    rw [show ((4 : ℝ) : ℂ) = ((3 : ℝ) : ℂ) + 1 by norm_num, add_smul, one_smul,
      add_sub_cancel_right]
  rw [show ((2 : ℝ) * 2 : ℝ) = (4 : ℝ) by norm_num]
  exact h43

/-- **(LNS.13d), mass separation**: the source-visible invariant-mass
supports of the two models are `{4}` and `{3}`. -/
theorem forgetting_mass_supports :
    (Superselection.sectorGram
        (invariantMass_isHermitian H0_isHermitian P0_isHermitian) B0 4 ≠ 0 ∧
      ∀ μ : ℝ, μ ≠ 4 → Superselection.sectorGram
        (invariantMass_isHermitian H0_isHermitian P0_isHermitian) B0 μ = 0) ∧
    (Superselection.sectorGram
        (invariantMass_isHermitian H1_isHermitian P1_isHermitian) B1 3 ≠ 0 ∧
      ∀ μ : ℝ, μ ≠ 3 → Superselection.sectorGram
        (invariantMass_isHermitian H1_isHermitian P1_isHermitian) B1 μ = 0) := by
  constructor
  · constructor
    · unfold Superselection.sectorGram
      rw [sectorProj_smul_one_self _ A0_eq]
      unfold B0
      rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      exact one_ne_zero
    · intro μ hμ
      unfold Superselection.sectorGram
      rw [sectorProj_smul_one_ne _ A0_eq hμ, Matrix.mul_zero, Matrix.zero_mul]
  · constructor
    · unfold Superselection.sectorGram
      rw [sectorProj_smul_one_self _ A1_eq, Matrix.mul_one, B1_gram]
      exact one_ne_zero
    · intro μ hμ
      unfold Superselection.sectorGram
      rw [sectorProj_smul_one_ne _ A1_eq hμ, Matrix.mul_zero, Matrix.zero_mul]

/-- **Hyperboloid forgetting**: two realizations with identical
invariant-mass operators and sector Grams but different compressed
momenta — the invariant-mass measure forgets the distribution along the
mass hyperboloid. -/
theorem hyperboloid_forgetting :
    ∃ (Pp Pm : Matrix (Fin 1) (Fin 1) ℂ),
      Pp.IsHermitian ∧ Pm.IsHermitian ∧
        H0 * H0 - Pp * Pp = H0 * H0 - Pm * Pm ∧
        B0ᴴ * Pp * B0 ≠ B0ᴴ * Pm * B0 := by
  refine ⟨1, -1, ?_, ?_, ?_, ?_⟩
  · change (1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ = 1
    rw [Matrix.conjTranspose_one]
  · change (-1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ = -1
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one]
  · rw [Matrix.one_mul, neg_mul_neg, Matrix.one_mul]
  · unfold B0
    rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one]
    intro hcon
    have h := congrFun (congrFun hcon 0) 0
    rw [Matrix.one_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq] at h
    norm_num at h

end TranslationLadder

end TranslationLadderSection

/-! ### `thm:SMOS-mass-shell-separator` — Mass measure, flat closure, shell alternative

Rendering: the invariant-mass operator is a PSD Hermitian `A` on the
finite carrier with source synthesis `B`; the compressed invariant-mass
measure is the window Gram `Σ_B^M(S) = B^*1_S(A)B` and the matrix
Stieltjes transform is `G_B(z) = B^*(A-z)⁻¹B`.  (LNS.15) and (LNS.16) are
the entrywise Poisson-inversion and residue limits along `η ↓ 0`, with
`Im G = (G - G^*)/2i`; continuity endpoints are the vanishing of the
endpoint atoms.  The Krylov innovation (LNS.17) is the Gram of the
orthogonal residual `(I-P_{r-1})A^rB` against the Krylov range projection
`colProj (B,AB,…,A^{r-1}B)`; its zero is equivalent to stabilization and
implies that the Krylov range reduces `A`.  (LNS.18) is the whitened
compressed operator `Â_r = ℍ^{†/2}(M_{i+j+1})ℍ^{†/2}` with the exact
moment reconstruction `M_k = V^*Â_r^kV`, `V = ℍ^{†/2}(M_i)_{i<r}`; the
block Hankel entries are identified with the moments.  The positive
innovation has the canonical polar synthesis with its uniqueness clause.
(LNS.19/19a) render the isolated-shell criterion (on a finite carrier the
punctured-window clause holds with any `δ` below the least spectral gap,
so the criterion is the nonvanishing of the residue Gram), the shell
isometry with `J^*J` the support of `Z` and `rank J = rank Z`, and the
exhaustive five-branch source-visible alternative (the embedded-atom and
threshold-continuum branches are stated literally; on a finite carrier
they are never taken). -/

section MassShellSection

namespace MassShell

open CSpec

variable {n e : Type*} [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e]

open Classical in
/-- The compressed invariant-mass window Gram `Σ_B^M(S) = B^*1_S(A)B`. -/
noncomputable def windowGram {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (B : Matrix n e ℂ) (S : Set ℝ) : Matrix e e ℂ :=
  Bᴴ * cSpec hA (fun l => if l ∈ S then 1 else 0) * B

/-- The matrix Stieltjes transform `G_B(z) = B^*(A-z)⁻¹B` (LNS.14). -/
noncomputable def stieltjes (A : Matrix n n ℂ) (B : Matrix n e ℂ) (z : ℂ) :
    Matrix e e ℂ :=
  Bᴴ * (A - z • 1)⁻¹ * B

/-- The matrix imaginary part `Im M = (M - M^*)/(2i)`. -/
noncomputable def imPart (M : Matrix e e ℂ) : Matrix e e ℂ :=
  (2 * Complex.I)⁻¹ • (M - Mᴴ)

omit [DecidableEq e] in
open Classical in
/-- The window Gram in rank-one spectral weights. -/
theorem windowGram_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (B : Matrix n e ℂ)
    (S : Set ℝ) :
    windowGram hA B S
      = ∑ i, (if hA.eigenvalues i ∈ S then (1 : ℂ) else 0) • wMat hA B i := by
  unfold windowGram
  rw [compress_cSpec]

/-- The scalar Poisson kernel identity for the imaginary part of the
resolvent. -/
theorem inv_im_scalar (μ lam η : ℝ) (hη : η ≠ 0) :
    (2 * Complex.I)⁻¹ * (((μ : ℂ) - ((lam : ℂ) + (η : ℂ) * Complex.I))⁻¹
        - (starRingEnd ℂ) (((μ : ℂ) - ((lam : ℂ) + (η : ℂ) * Complex.I))⁻¹))
      = ((η / ((μ - lam) ^ 2 + η ^ 2) : ℝ) : ℂ) := by
  set w : ℂ := (μ : ℂ) - ((lam : ℂ) + (η : ℂ) * Complex.I) with hw
  have hwre : w.re = μ - lam := by
    rw [hw]
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
  have hwim : w.im = -η := by
    rw [hw]
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
  have hns : Complex.normSq w = (μ - lam) ^ 2 + η ^ 2 := by
    rw [Complex.normSq_apply, hwre, hwim]
    ring
  have hinv : w⁻¹ = (starRingEnd ℂ) w * (((Complex.normSq w)⁻¹ : ℝ) : ℂ) :=
    Complex.inv_def w
  have hconjinv : (starRingEnd ℂ) (w⁻¹)
      = w * (((Complex.normSq w)⁻¹ : ℝ) : ℂ) := by
    rw [hinv, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  have hsub : w⁻¹ - (starRingEnd ℂ) (w⁻¹)
      = ((starRingEnd ℂ) w - w) * (((Complex.normSq w)⁻¹ : ℝ) : ℂ) := by
    rw [hconjinv, hinv, ← sub_mul]
  have hdiffc : (starRingEnd ℂ) w - w = 2 * (η : ℂ) * Complex.I := by
    have hcs := Complex.sub_conj w
    have hneg : (starRingEnd ℂ) w - w = -(w - (starRingEnd ℂ) w) := by ring
    rw [hneg, hcs, hwim]
    push_cast
    ring
  rw [hsub, hdiffc]
  have hI : (2 * Complex.I)⁻¹ * (2 * (η : ℂ) * Complex.I) = (η : ℂ) := by
    have h2I : (2 : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by norm_num) Complex.I_ne_zero
    field_simp
  calc (2 * Complex.I)⁻¹
        * (2 * (η : ℂ) * Complex.I * (((Complex.normSq w)⁻¹ : ℝ) : ℂ))
      = (2 * Complex.I)⁻¹ * (2 * (η : ℂ) * Complex.I)
        * (((Complex.normSq w)⁻¹ : ℝ) : ℂ) := by ring
    _ = (η : ℂ) * (((Complex.normSq w)⁻¹ : ℝ) : ℂ) := by rw [hI]
    _ = ((η / ((μ - lam) ^ 2 + η ^ 2) : ℝ) : ℂ) := by
        rw [hns]
        push_cast
        ring

/-- Nonreal points are off the spectrum of a Hermitian matrix. -/
theorem offSpectrum_of_im_ne {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : ∀ i, ((hA.eigenvalues i : ℂ)) ≠ z := by
  intro i hcon
  have him := congrArg Complex.im hcon
  rw [Complex.ofReal_im] at him
  exact hz him.symm

/-- The imaginary part of the Stieltjes transform is the Poisson-kernel
average of the spectral weights. -/
theorem imPart_stieltjes {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (B : Matrix n e ℂ) (lam : ℝ) {η : ℝ} (hη : η ≠ 0) :
    imPart (stieltjes A B ((lam : ℂ) + (η : ℂ) * Complex.I))
      = ∑ i, ((η / ((hA.eigenvalues i - lam) ^ 2 + η ^ 2) : ℝ) : ℂ)
          • wMat hA B i := by
  have hzim : ((lam : ℂ) + (η : ℂ) * Complex.I).im ≠ 0 := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add]
    exact hη
  obtain ⟨-, hinv⟩ := shift_inv_eq_cSpec hA (offSpectrum_of_im_ne hA hzim)
  have hG : stieltjes A B ((lam : ℂ) + (η : ℂ) * Complex.I)
      = ∑ i, (((hA.eigenvalues i : ℂ))
          - ((lam : ℂ) + (η : ℂ) * Complex.I))⁻¹ • wMat hA B i := by
    unfold stieltjes
    rw [hinv, compress_cSpec]
  have hGH : (stieltjes A B ((lam : ℂ) + (η : ℂ) * Complex.I))ᴴ
      = ∑ i, (starRingEnd ℂ) ((((hA.eigenvalues i : ℂ))
          - ((lam : ℂ) + (η : ℂ) * Complex.I))⁻¹) • wMat hA B i := by
    rw [hG, conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_smul, (wMat_posSemidef hA B i).1.eq]
    rfl
  unfold imPart
  rw [hGH, hG, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_smul, smul_smul, inv_im_scalar _ _ _ hη]

/-- The Poisson kernel integrates to an arctangent difference. -/
theorem poisson_integral (μ a b : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ lam in a..b, η / ((μ - lam) ^ 2 + η ^ 2)
      = Real.arctan ((b - μ) / η) - Real.arctan ((a - μ) / η) := by
  have hderiv : ∀ lam : ℝ, HasDerivAt (fun l => Real.arctan ((l - μ) / η))
      (η / ((μ - lam) ^ 2 + η ^ 2)) lam := by
    intro lam
    have h1 : HasDerivAt (fun l : ℝ => (l - μ) / η) (1 / η) lam := by
      have h0 : HasDerivAt (fun l : ℝ => l - μ) 1 lam := (hasDerivAt_id lam).sub_const μ
      have h2 := h0.div_const η
      rwa [show (1 : ℝ) / η = 1 / η by ring] at h2
    have h3 := (Real.hasDerivAt_arctan ((lam - μ) / η)).comp lam h1
    have hη' : η ≠ 0 := ne_of_gt hη
    have heq : 1 / (1 + ((lam - μ) / η) ^ 2) * (1 / η)
        = η / ((μ - lam) ^ 2 + η ^ 2) := by
      rw [div_mul_div_comm, one_mul,
        div_eq_div_iff (by positivity) (by positivity)]
      field_simp
      ring
    rwa [heq] at h3
  have hcont : Continuous fun lam : ℝ => η / ((μ - lam) ^ 2 + η ^ 2) := by
    refine Continuous.div continuous_const (by fun_prop) fun lam => ?_
    positivity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun l => Real.arctan ((l - μ) / η))
    (f' := fun lam => η / ((μ - lam) ^ 2 + η ^ 2))
    (fun lam _ => hderiv lam) (hcont.intervalIntegrable a b)
  rw [hFTC]

/-- One-sided arctangent limit at a positive argument. -/
theorem arctan_limit_pos {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (fun η : ℝ => Real.arctan (x / η)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi / 2)) := by
  have h1 : Filter.Tendsto (fun η : ℝ => x / η) (𝓝[>] (0 : ℝ)) atTop := by
    have h2 : Filter.Tendsto (fun η : ℝ => η⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero
    have h3 := h2.const_mul_atTop hx
    refine h3.congr fun η => ?_
    rw [div_eq_mul_inv]
  exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1

/-- One-sided arctangent limit at a negative argument. -/
theorem arctan_limit_neg {x : ℝ} (hx : x < 0) :
    Filter.Tendsto (fun η : ℝ => Real.arctan (x / η)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.pi / 2))) := by
  have h := (arctan_limit_pos (x := -x) (by linarith)).neg
  refine h.congr fun η => ?_
  rw [neg_div, Real.arctan_neg, neg_neg]

open Classical in
/-- The endpoint-aware pointwise arctangent limit. -/
theorem arctan_diff_limit {a b : ℝ} (hab : a < b) (μ : ℝ) :
    Filter.Tendsto
      (fun η : ℝ => Real.arctan ((b - μ) / η) - Real.arctan ((a - μ) / η))
      (𝓝[>] (0 : ℝ))
      (𝓝 (if μ ∈ Set.Ioo a b then Real.pi
        else if μ = a ∨ μ = b then Real.pi / 2 else 0)) := by
  rcases lt_trichotomy μ a with hμa | hμa | hμa
  · -- `μ < a`: both arctans tend to `π/2`
    have h1 := arctan_limit_pos (x := b - μ) (by linarith)
    have h2 := arctan_limit_pos (x := a - μ) (by linarith)
    have h3 := h1.sub h2
    rw [sub_self] at h3
    have hif : (if μ ∈ Set.Ioo a b then Real.pi
        else if μ = a ∨ μ = b then Real.pi / 2 else 0) = 0 := by
      rw [ite_eq_right (by rintro ⟨h4, -⟩; linarith),
        ite_eq_right (by rintro (rfl | rfl) <;> linarith)]
    rw [hif]
    exact h3
  · -- `μ = a`: the left endpoint contributes `π/2`
    subst hμa
    have h1 := arctan_limit_pos (x := b - μ) (by linarith)
    have h2 : Filter.Tendsto (fun η : ℝ => Real.arctan ((μ - μ) / η))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hz : (fun η : ℝ => Real.arctan ((μ - μ) / η)) = fun _ : ℝ => 0 := by
        funext η
        rw [sub_self, zero_div, Real.arctan_zero]
      rw [hz]
      exact tendsto_const_nhds
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    have hif : (if μ ∈ Set.Ioo μ b then Real.pi
        else if μ = μ ∨ μ = b then Real.pi / 2 else 0) = Real.pi / 2 := by
      rw [ite_eq_right (by rintro ⟨h4, -⟩; exact lt_irrefl μ h4),
        ite_eq_left (Or.inl rfl)]
    rw [hif]
    exact h3
  rcases lt_trichotomy μ b with hμb | hμb | hμb
  · -- `a < μ < b`: the bulk value `π`
    have h1 := arctan_limit_pos (x := b - μ) (by linarith)
    have h2 := arctan_limit_neg (x := a - μ) (by linarith)
    have h3 := h1.sub h2
    have hval : Real.pi / 2 - -(Real.pi / 2) = Real.pi := by ring
    rw [hval] at h3
    have hif : (if μ ∈ Set.Ioo a b then Real.pi
        else if μ = a ∨ μ = b then Real.pi / 2 else 0) = Real.pi :=
      ite_eq_left ⟨hμa, hμb⟩
    rw [hif]
    exact h3
  · -- `μ = b`: the right endpoint contributes `π/2`
    subst hμb
    have h2 := arctan_limit_neg (x := a - μ) (by linarith)
    have h1 : Filter.Tendsto (fun η : ℝ => Real.arctan ((μ - μ) / η))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hz : (fun η : ℝ => Real.arctan ((μ - μ) / η)) = fun _ : ℝ => 0 := by
        funext η
        rw [sub_self, zero_div, Real.arctan_zero]
      rw [hz]
      exact tendsto_const_nhds
    have h3 := h1.sub h2
    have hval : (0 : ℝ) - -(Real.pi / 2) = Real.pi / 2 := by ring
    rw [hval] at h3
    have hif : (if μ ∈ Set.Ioo a μ then Real.pi
        else if μ = a ∨ μ = μ then Real.pi / 2 else 0) = Real.pi / 2 := by
      rw [ite_eq_right (by rintro ⟨-, h4⟩; exact lt_irrefl μ h4),
        ite_eq_left (Or.inr rfl)]
    rw [hif]
    exact h3
  · -- `b < μ`: both arctans tend to `-π/2`
    have h1 := arctan_limit_neg (x := b - μ) (by linarith)
    have h2 := arctan_limit_neg (x := a - μ) (by linarith)
    have h3 := h1.sub h2
    rw [sub_self] at h3
    have hif : (if μ ∈ Set.Ioo a b then Real.pi
        else if μ = a ∨ μ = b then Real.pi / 2 else 0) = 0 := by
      rw [ite_eq_right (by rintro ⟨-, h4⟩; linarith),
        ite_eq_right (by rintro (rfl | rfl) <;> linarith)]
    rw [hif]
    exact h3

open Classical in
/-- **(LNS.15)**: the Poisson inversion of the compressed invariant-mass
measure at continuity endpoints, entrywise:
`Σ_B^M((a,b)) = lim_{η↓0} π⁻¹∫_a^b Im G_B(λ+iη) dλ`. -/
theorem stieltjes_inversion {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (B : Matrix n e ℂ) {a b : ℝ} (hab : a < b)
    (ha : windowGram hA B {a} = 0) (hb : windowGram hA B {b} = 0) (c d : e) :
    Filter.Tendsto (fun η : ℝ =>
        (Real.pi : ℂ)⁻¹ * ∫ lam in a..b,
          imPart (stieltjes A B ((lam : ℂ) + (η : ℂ) * Complex.I)) c d)
      (𝓝[>] (0 : ℝ)) (𝓝 (windowGram hA B (Set.Ioo a b) c d)) := by
  classical
  -- the integral as an arctangent sum
  have hval : ∀ η : ℝ, 0 < η →
      ∫ lam in a..b, imPart (stieltjes A B ((lam : ℂ) + (η : ℂ) * Complex.I)) c d
        = ∑ i, ((Real.arctan ((b - hA.eigenvalues i) / η)
            - Real.arctan ((a - hA.eigenvalues i) / η) : ℝ) : ℂ)
            * wMat hA B i c d := by
    intro η hη
    have hfun : ∀ lam : ℝ,
        imPart (stieltjes A B ((lam : ℂ) + (η : ℂ) * Complex.I)) c d
          = ∑ i, ((η / ((hA.eigenvalues i - lam) ^ 2 + η ^ 2) : ℝ) : ℂ)
              * wMat hA B i c d := by
      intro lam
      rw [imPart_stieltjes hA B lam hη.ne', Matrix.sum_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [Matrix.smul_apply, smul_eq_mul]
    have hcont : ∀ i : n, Continuous fun lam : ℝ =>
        ((η / ((hA.eigenvalues i - lam) ^ 2 + η ^ 2) : ℝ) : ℂ) * wMat hA B i c d := by
      intro i
      refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const
      refine Continuous.div continuous_const (by fun_prop) fun lam => ?_
      positivity
    calc ∫ lam in a..b, imPart (stieltjes A B ((lam : ℂ) + (η : ℂ) * Complex.I)) c d
        = ∫ lam in a..b, ∑ i, ((η / ((hA.eigenvalues i - lam) ^ 2 + η ^ 2) : ℝ) : ℂ)
            * wMat hA B i c d :=
          intervalIntegral.integral_congr fun lam _ => hfun lam
      _ = ∑ i, ∫ lam in a..b, ((η / ((hA.eigenvalues i - lam) ^ 2 + η ^ 2) : ℝ) : ℂ)
            * wMat hA B i c d :=
          intervalIntegral.integral_finsetSum fun i _ =>
            ((hcont i).intervalIntegrable a b)
      _ = ∑ i, ((Real.arctan ((b - hA.eigenvalues i) / η)
            - Real.arctan ((a - hA.eigenvalues i) / η) : ℝ) : ℂ)
            * wMat hA B i c d := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
            poisson_integral _ _ _ hη]
  -- endpoint sums vanish and the interior sum is the window Gram
  have hIoo : windowGram hA B (Set.Ioo a b) c d
      = ∑ i, (if hA.eigenvalues i ∈ Set.Ioo a b then (1 : ℂ) else 0)
          * wMat hA B i c d := by
    rw [windowGram_eq, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, Set.mem_Ioo]
  have hsingle : ∀ x : ℝ, windowGram hA B {x} c d
      = ∑ i, (if hA.eigenvalues i = x then (1 : ℂ) else 0) * wMat hA B i c d := by
    intro x
    rw [windowGram_eq, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, Set.mem_singleton_iff]
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hLval : (Real.pi : ℂ)⁻¹
      * (∑ i, (((if hA.eigenvalues i ∈ Set.Ioo a b then Real.pi
          else if hA.eigenvalues i = a ∨ hA.eigenvalues i = b then Real.pi / 2
          else 0) : ℝ) : ℂ) * wMat hA B i c d)
      = windowGram hA B (Set.Ioo a b) c d := by
    have hsplit : ∀ i : n,
        (((if hA.eigenvalues i ∈ Set.Ioo a b then Real.pi
          else if hA.eigenvalues i = a ∨ hA.eigenvalues i = b then Real.pi / 2
          else 0) : ℝ) : ℂ)
        = (Real.pi : ℂ) * (if hA.eigenvalues i ∈ Set.Ioo a b then 1 else 0)
          + ((Real.pi : ℂ) / 2) * (if hA.eigenvalues i = a then 1 else 0)
          + ((Real.pi : ℂ) / 2) * (if hA.eigenvalues i = b then 1 else 0) := by
      intro i
      by_cases h1 : hA.eigenvalues i ∈ Set.Ioo a b
      · have hna : hA.eigenvalues i ≠ a := by
          obtain ⟨hx, -⟩ := h1
          exact fun hc => absurd (hc ▸ hx) (lt_irrefl a)
        have hnb : hA.eigenvalues i ≠ b := by
          obtain ⟨-, hx⟩ := h1
          exact fun hc => absurd (hc ▸ hx) (lt_irrefl b)
        rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right hna, ite_eq_right hnb]
        ring
      · rw [ite_eq_right h1, ite_eq_right h1, mul_zero, zero_add]
        by_cases h2 : hA.eigenvalues i = a
        · have hnb : hA.eigenvalues i ≠ b := by
            rw [h2]
            exact ne_of_lt hab
          rw [ite_eq_left (Or.inl h2), ite_eq_left h2, ite_eq_right hnb]
          push_cast
          ring
        · by_cases h3 : hA.eigenvalues i = b
          · rw [ite_eq_left (Or.inr h3), ite_eq_right h2, ite_eq_left h3]
            push_cast
            ring
          · rw [ite_eq_right (by rintro (hc | hc); exacts [h2 hc, h3 hc]),
              ite_eq_right h2, ite_eq_right h3]
            push_cast
            ring
    rw [Finset.sum_congr rfl fun i _ => by rw [hsplit i, add_mul, add_mul]]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hzeroa : ∑ i, (Real.pi : ℂ) / 2 * (if hA.eigenvalues i = a then 1 else 0)
        * wMat hA B i c d = 0 := by
      have h := hsingle a
      rw [ha] at h
      have h0 : ∑ i, (if hA.eigenvalues i = a then (1 : ℂ) else 0)
          * wMat hA B i c d = 0 := by
        rw [← h]
        rw [Matrix.zero_apply]
      calc ∑ i, (Real.pi : ℂ) / 2 * (if hA.eigenvalues i = a then 1 else 0)
            * wMat hA B i c d
          = (Real.pi : ℂ) / 2 * ∑ i, (if hA.eigenvalues i = a then (1 : ℂ) else 0)
            * wMat hA B i c d := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [h0, mul_zero]
    have hzerob : ∑ i, (Real.pi : ℂ) / 2 * (if hA.eigenvalues i = b then 1 else 0)
        * wMat hA B i c d = 0 := by
      have h := hsingle b
      rw [hb] at h
      have h0 : ∑ i, (if hA.eigenvalues i = b then (1 : ℂ) else 0)
          * wMat hA B i c d = 0 := by
        rw [← h]
        rw [Matrix.zero_apply]
      calc ∑ i, (Real.pi : ℂ) / 2 * (if hA.eigenvalues i = b then 1 else 0)
            * wMat hA B i c d
          = (Real.pi : ℂ) / 2 * ∑ i, (if hA.eigenvalues i = b then (1 : ℂ) else 0)
            * wMat hA B i c d := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [h0, mul_zero]
    rw [hzeroa, hzerob, add_zero, add_zero, hIoo, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
  -- assemble the limit
  have hterm : ∀ i : n, Filter.Tendsto
      (fun η : ℝ => ((Real.arctan ((b - hA.eigenvalues i) / η)
          - Real.arctan ((a - hA.eigenvalues i) / η) : ℝ) : ℂ) * wMat hA B i c d)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((if hA.eigenvalues i ∈ Set.Ioo a b then Real.pi
          else if hA.eigenvalues i = a ∨ hA.eigenvalues i = b then Real.pi / 2
          else 0) : ℝ) : ℂ) * wMat hA B i c d)) := by
    intro i
    refine Filter.Tendsto.mul_const _ ?_
    exact (Complex.continuous_ofReal.tendsto _).comp (arctan_diff_limit hab _)
  have hsum := tendsto_finsetSum (Finset.univ : Finset n) fun i _ => hterm i
  have hmul := hsum.const_mul ((Real.pi : ℂ)⁻¹)
  rw [hLval] at hmul
  refine hmul.congr' ?_
  refine eventuallyEq_nhdsWithin_of_eqOn fun η hη => ?_
  rw [hval η hη]

open Classical in
/-- **(LNS.16)**: the source residue at `m²` is the endpoint atom:
`Z_m(B) = lim_{η↓0} η·Im G_B(m²+iη)`, entrywise. -/
theorem residue_limit {A : Matrix n n ℂ} (hA : A.IsHermitian) (B : Matrix n e ℂ)
    (m : ℝ) (c d : e) :
    Filter.Tendsto (fun η : ℝ =>
        (η : ℂ) * imPart (stieltjes A B (((m ^ 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I)) c d)
      (𝓝[>] (0 : ℝ)) (𝓝 (windowGram hA B {m ^ 2} c d)) := by
  classical
  have hval : ∀ η : ℝ, 0 < η →
      (η : ℂ) * imPart (stieltjes A B (((m ^ 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I)) c d
        = ∑ i, ((η * (η / ((hA.eigenvalues i - m ^ 2) ^ 2 + η ^ 2)) : ℝ) : ℂ)
            * wMat hA B i c d := by
    intro η hη
    rw [imPart_stieltjes hA B (m ^ 2) hη.ne', Matrix.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  have hsingle : windowGram hA B {m ^ 2} c d
      = ∑ i, (if hA.eigenvalues i = m ^ 2 then (1 : ℂ) else 0)
          * wMat hA B i c d := by
    rw [windowGram_eq, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, Set.mem_singleton_iff]
  have hterm : ∀ i : n, Filter.Tendsto
      (fun η : ℝ => ((η * (η / ((hA.eigenvalues i - m ^ 2) ^ 2 + η ^ 2)) : ℝ) : ℂ)
        * wMat hA B i c d)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((if hA.eigenvalues i = m ^ 2 then (1 : ℂ) else 0) * wMat hA B i c d)) := by
    intro i
    refine Filter.Tendsto.mul_const _ ?_
    have hreal : Filter.Tendsto
        (fun η : ℝ => η * (η / ((hA.eigenvalues i - m ^ 2) ^ 2 + η ^ 2)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (if hA.eigenvalues i = m ^ 2 then (1 : ℝ) else 0)) := by
      by_cases hi : hA.eigenvalues i = m ^ 2
      · rw [ite_eq_left hi]
        have hfun : Set.EqOn
            (fun η : ℝ => η * (η / ((hA.eigenvalues i - m ^ 2) ^ 2 + η ^ 2)))
            (fun _ : ℝ => (1 : ℝ)) (Set.Ioi 0) := by
          intro η hη
          have hη0 : η ≠ 0 := ne_of_gt hη
          simp only
          rw [hi, sub_self]
          field_simp
          ring
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        exact eventuallyEq_nhdsWithin_of_eqOn fun η hη => (hfun hη).symm
      · rw [ite_eq_right hi]
        have hpos : 0 < (hA.eigenvalues i - m ^ 2) ^ 2 := by
          have hne : hA.eigenvalues i - m ^ 2 ≠ 0 := sub_ne_zero.mpr hi
          positivity
        have hnum : Filter.Tendsto (fun η : ℝ => η * η) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have h0 : Filter.Tendsto (fun η : ℝ => η * η) (𝓝 (0 : ℝ)) (𝓝 (0 * 0)) :=
            tendsto_id.mul tendsto_id
          rw [mul_zero] at h0
          exact h0.mono_left nhdsWithin_le_nhds
        have hden : Filter.Tendsto
            (fun η : ℝ => (hA.eigenvalues i - m ^ 2) ^ 2 + η ^ 2) (𝓝[>] (0 : ℝ))
            (𝓝 ((hA.eigenvalues i - m ^ 2) ^ 2)) := by
          have h0 : Filter.Tendsto
              (fun η : ℝ => (hA.eigenvalues i - m ^ 2) ^ 2 + η ^ 2) (𝓝 (0 : ℝ))
              (𝓝 ((hA.eigenvalues i - m ^ 2) ^ 2 + (0 : ℝ) ^ 2)) :=
            tendsto_const_nhds.add ((continuous_pow 2).tendsto (0 : ℝ))
          rw [show ((0 : ℝ) ^ 2) = 0 by ring, add_zero] at h0
          exact h0.mono_left nhdsWithin_le_nhds
        have hquot := hnum.div hden (ne_of_gt hpos)
        rw [zero_div] at hquot
        refine hquot.congr fun η => ?_
        rw [Pi.div_apply, mul_div_assoc']
    have hcast := (Complex.continuous_ofReal.tendsto _).comp hreal
    have hite : (((if hA.eigenvalues i = m ^ 2 then (1 : ℝ) else 0) : ℝ) : ℂ)
        = (if hA.eigenvalues i = m ^ 2 then (1 : ℂ) else 0) := by
      rw [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero]
    rw [hite] at hcast
    exact hcast
  have hsum := tendsto_finsetSum (Finset.univ : Finset n) fun i _ => hterm i
  rw [← hsingle] at hsum
  refine hsum.congr' ?_
  refine eventuallyEq_nhdsWithin_of_eqOn fun η hη => ?_
  rw [hval η hη]

/-! #### The Krylov innovation (LNS.17) and the flat atomic closure (LNS.18) -/

section Krylov

open NCG.RenormCongruence

variable {A : Matrix n n ℂ} {B : Matrix n e ℂ}

/-- The source moments `M_k = B^*A^kB`. -/
noncomputable def moment (A : Matrix n n ℂ) (B : Matrix n e ℂ) (k : ℕ) :
    Matrix e e ℂ :=
  Bᴴ * A ^ k * B

/-- The Krylov synthesis `(B, AB, …, A^{r-1}B)` as one block matrix. -/
noncomputable def krylovMat (A : Matrix n n ℂ) (B : Matrix n e ℂ) (r : ℕ) :
    Matrix n (Fin r × e) ℂ :=
  Matrix.of fun x p => (A ^ (p.1 : ℕ) * B) x p.2

/-- The Krylov projection fixes each stored power block. -/
theorem colProj_krylov_fix (A : Matrix n n ℂ) (B : Matrix n e ℂ) {r i : ℕ}
    (hi : i < r) :
    colProj (krylovMat A B r) * (A ^ i * B) = A ^ i * B := by
  ext x c
  have h := congrFun (congrFun (colProj_mul_self (krylovMat A B r)) x) (⟨i, hi⟩, c)
  simp only [Matrix.mul_apply, krylovMat, Matrix.of_apply] at h ⊢
  exact h

omit [Fintype e] [DecidableEq e] in
/-- The block shift: `A` advances every stored Krylov power. -/
theorem mul_krylovMat_apply (A : Matrix n n ℂ) (B : Matrix n e ℂ) (r : ℕ)
    (x : n) (p : Fin r × e) :
    (A * krylovMat A B r) x p = (A ^ ((p.1 : ℕ) + 1) * B) x p.2 := by
  rw [Matrix.mul_apply, pow_succ', Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [krylovMat, Matrix.of_apply]

/-- **(LNS.17)**: the Krylov innovation `𝕀_r^M = B^*A^r(I - P_{r-1})A^rB`. -/
noncomputable def innovation (A : Matrix n n ℂ) (B : Matrix n e ℂ) (r : ℕ) :
    Matrix e e ℂ :=
  Bᴴ * A ^ r * ((1 : Matrix n n ℂ) - colProj (krylovMat A B r)) * (A ^ r * B)

/-- The innovation is the Gram of the orthogonal residual
`(I - P_{r-1})A^rB`. -/
theorem innovation_eq_gram (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    innovation A B r
      = (((1 : Matrix n n ℂ) - colProj (krylovMat A B r)) * (A ^ r * B))ᴴ
        * (((1 : Matrix n n ℂ) - colProj (krylovMat A B r)) * (A ^ r * B)) := by
  have hidem := one_sub_colProj_idem (krylovMat A B r)
  have hherm := one_sub_colProj_isHermitian (krylovMat A B r)
  have hrhs : (((1 : Matrix n n ℂ) - colProj (krylovMat A B r)) * (A ^ r * B))ᴴ
        * (((1 : Matrix n n ℂ) - colProj (krylovMat A B r)) * (A ^ r * B))
      = Bᴴ * A ^ r * (((1 : Matrix n n ℂ) - colProj (krylovMat A B r))
          * ((1 : Matrix n n ℂ) - colProj (krylovMat A B r))) * (A ^ r * B) := by
    rw [conjTranspose_mul, hherm.eq, conjTranspose_mul, (hA.pow r).eq]
    simp only [Matrix.mul_assoc]
  rw [hrhs, hidem]
  rfl

/-- The innovation is PSD. -/
theorem innovation_posSemidef (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    (innovation A B r).PosSemidef := by
  rw [innovation_eq_gram hA]
  exact posSemidef_conjTranspose_mul_self _

/-- Zero innovation is exactly vanishing of the orthogonal residual. -/
theorem innovation_eq_zero_iff (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    innovation A B r = 0
      ↔ ((1 : Matrix n n ℂ) - colProj (krylovMat A B r)) * (A ^ r * B) = 0 := by
  rw [innovation_eq_gram hA]
  exact ⟨fun h => Matrix.conjTranspose_mul_self_eq_zero.mp h,
    fun h => by rw [h, Matrix.mul_zero]⟩

/-- Zero innovation makes the projection fix every power up to `r`. -/
theorem proj_fixes_le (hA : A.IsHermitian) {r : ℕ}
    (h : innovation A B r = 0) {m : ℕ} (hm : m ≤ r) :
    colProj (krylovMat A B r) * (A ^ m * B) = A ^ m * B := by
  rcases lt_or_eq_of_le hm with hlt | rfl
  · exact colProj_krylov_fix A B hlt
  · have h0 := (innovation_eq_zero_iff hA B m).mp h
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h0
    exact h0.symm

/-- Zero innovation makes the stabilized Krylov range reduce `A`. -/
theorem innovation_zero_reduces (hA : A.IsHermitian) {r : ℕ}
    (h : innovation A B r = 0) :
    A * colProj (krylovMat A B r) = colProj (krylovMat A B r) * A := by
  set P := colProj (krylovMat A B r) with hPdef
  have hPH : P.IsHermitian := colProj_isHermitian _
  -- the projection fixes the shifted block matrix
  have hfix : P * (A * krylovMat A B r) = A * krylovMat A B r := by
    ext x p
    have hcol := proj_fixes_le hA (B := B) h (Nat.succ_le_of_lt p.1.isLt)
    have h1 := congrFun (congrFun hcol x) p.2
    calc (P * (A * krylovMat A B r)) x p
        = ∑ y, P x y * (A * krylovMat A B r) y p := Matrix.mul_apply
      _ = ∑ y, P x y * (A ^ ((p.1 : ℕ) + 1) * B) y p.2 :=
          Finset.sum_congr rfl fun y _ => by rw [mul_krylovMat_apply]
      _ = (P * (A ^ ((p.1 : ℕ) + 1) * B)) x p.2 := (Matrix.mul_apply).symm
      _ = (A ^ ((p.1 : ℕ) + 1) * B) x p.2 := h1
      _ = (A * krylovMat A B r) x p := (mul_krylovMat_apply A B r x p).symm
  -- invariance of the range
  have hinv : ((1 : Matrix n n ℂ) - P) * A * P = 0 := by
    have hPrep : P = krylovMat A B r
        * pinv (posSemidef_conjTranspose_mul_self (krylovMat A B r)).1
        * (krylovMat A B r)ᴴ := rfl
    have hzero : ((1 : Matrix n n ℂ) - P) * (A * krylovMat A B r) = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hfix, sub_self]
    calc ((1 : Matrix n n ℂ) - P) * A * P
        = ((1 : Matrix n n ℂ) - P) * (A * krylovMat A B r)
          * (pinv (posSemidef_conjTranspose_mul_self (krylovMat A B r)).1
            * (krylovMat A B r)ᴴ) := by
          rw [hPrep]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hzero, Matrix.zero_mul]
  have h1 : A * P = P * A * P := by
    have h0 := hinv
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h0
    exact h0
  have h2 : P * A = P * (A * P) := by
    have hct := congrArg conjTranspose h1
    simp only [conjTranspose_mul, hPH.eq, hA.eq, Matrix.mul_assoc] at hct
    exact hct
  calc A * P = P * A * P := h1
    _ = P * (A * P) := by rw [Matrix.mul_assoc]
    _ = P * A := h2.symm

/-- Zero innovation fixes every source power (cofinal stabilization). -/
theorem innovation_zero_fixes_pow (hA : A.IsHermitian) {r : ℕ}
    (h : innovation A B r = 0) (m : ℕ) :
    colProj (krylovMat A B r) * (A ^ m * B) = A ^ m * B := by
  induction m with
  | zero => exact proj_fixes_le hA h (Nat.zero_le r)
  | succ m ih =>
    have hcomm := innovation_zero_reduces hA h
    calc colProj (krylovMat A B r) * (A ^ (m + 1) * B)
        = colProj (krylovMat A B r) * A * (A ^ m * B) := by
          rw [pow_succ', Matrix.mul_assoc, Matrix.mul_assoc]
      _ = A * (colProj (krylovMat A B r) * (A ^ m * B)) := by
          rw [← hcomm, Matrix.mul_assoc]
      _ = A * (A ^ m * B) := by rw [ih]
      _ = A ^ (m + 1) * B := by rw [pow_succ', Matrix.mul_assoc]

/-- **(LNS.17), stabilization iff**: the innovation vanishes exactly when
the source-Krylov space has stabilized at the next step. -/
theorem innovation_zero_iff_stabilized (hA : A.IsHermitian) (B : Matrix n e ℂ)
    (r : ℕ) :
    innovation A B r = 0
      ↔ colProj (krylovMat A B (r + 1)) = colProj (krylovMat A B r) := by
  set P := colProj (krylovMat A B r) with hPdef
  set P' := colProj (krylovMat A B (r + 1)) with hP'def
  have hPH : P.IsHermitian := colProj_isHermitian _
  have hP'H : P'.IsHermitian := colProj_isHermitian _
  constructor
  · intro h
    -- `P` fixes the extended Krylov block matrix
    have hfix : P * krylovMat A B (r + 1) = krylovMat A B (r + 1) := by
      ext x p
      have hcol := proj_fixes_le hA (B := B) h (Nat.lt_succ_iff.mp p.1.isLt)
      have h1 := congrFun (congrFun hcol x) p.2
      calc (P * krylovMat A B (r + 1)) x p
          = ∑ y, P x y * (A ^ (p.1 : ℕ) * B) y p.2 := by
            rw [Matrix.mul_apply]
            exact Finset.sum_congr rfl fun y _ => by rw [krylovMat, Matrix.of_apply]
        _ = (P * (A ^ (p.1 : ℕ) * B)) x p.2 := (Matrix.mul_apply).symm
        _ = (A ^ (p.1 : ℕ) * B) x p.2 := h1
        _ = krylovMat A B (r + 1) x p := by rw [krylovMat, Matrix.of_apply]
    -- `P'` fixes the restricted Krylov block matrix
    have hfix' : P' * krylovMat A B r = krylovMat A B r := by
      ext x p
      have hcol := colProj_krylov_fix A B (r := r + 1)
        (Nat.lt_succ_of_lt p.1.isLt)
      have h1 := congrFun (congrFun hcol x) p.2
      calc (P' * krylovMat A B r) x p
          = ∑ y, P' x y * (A ^ (p.1 : ℕ) * B) y p.2 := by
            rw [Matrix.mul_apply]
            exact Finset.sum_congr rfl fun y _ => by rw [krylovMat, Matrix.of_apply]
        _ = (P' * (A ^ (p.1 : ℕ) * B)) x p.2 := (Matrix.mul_apply).symm
        _ = (A ^ (p.1 : ℕ) * B) x p.2 := h1
        _ = krylovMat A B r x p := by rw [krylovMat, Matrix.of_apply]
    -- the two absorptions
    have habs1 : P * P' = P' := by
      have hrep : P' = krylovMat A B (r + 1)
          * pinv (posSemidef_conjTranspose_mul_self (krylovMat A B (r + 1))).1
          * (krylovMat A B (r + 1))ᴴ := rfl
      calc P * P'
          = P * krylovMat A B (r + 1)
            * (pinv (posSemidef_conjTranspose_mul_self (krylovMat A B (r + 1))).1
              * (krylovMat A B (r + 1))ᴴ) := by
            rw [hrep]
            simp only [Matrix.mul_assoc]
        _ = P' := by
            rw [hfix, hrep]
            simp only [Matrix.mul_assoc]
    have habs2 : P' * P = P := by
      have hrep : P = krylovMat A B r
          * pinv (posSemidef_conjTranspose_mul_self (krylovMat A B r)).1
          * (krylovMat A B r)ᴴ := rfl
      calc P' * P
          = P' * krylovMat A B r
            * (pinv (posSemidef_conjTranspose_mul_self (krylovMat A B r)).1
              * (krylovMat A B r)ᴴ) := by
            rw [hrep]
            simp only [Matrix.mul_assoc]
        _ = P := by
            rw [hfix', hrep]
            simp only [Matrix.mul_assoc]
    have hct : P * P' = P := by
      have h2 := congrArg conjTranspose habs2
      simp only [conjTranspose_mul, hPH.eq, hP'H.eq] at h2
      exact h2
    exact habs1.symm.trans hct
  · intro h
    rw [innovation_eq_zero_iff hA, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]
    have hfix := colProj_krylov_fix A B (i := r) (Nat.lt_succ_self r)
    rw [show colProj (krylovMat A B (r + 1)) = colProj (krylovMat A B r) from h]
      at hfix
    exact hfix.symm

/-- **(LNS.17), bundled**: zero innovation ↔ Krylov stabilization, and on
that branch the stabilized range reduces `A` and absorbs every power. -/
theorem krylov_innovation (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    (innovation A B r = 0
        ↔ colProj (krylovMat A B (r + 1)) = colProj (krylovMat A B r)) ∧
      (innovation A B r = 0 →
        A * colProj (krylovMat A B r) = colProj (krylovMat A B r) * A ∧
          ∀ m : ℕ, colProj (krylovMat A B r) * (A ^ m * B) = A ^ m * B) :=
  ⟨innovation_zero_iff_stabilized hA B r, fun h =>
    ⟨innovation_zero_reduces hA h, innovation_zero_fixes_pow hA h⟩⟩

omit [Fintype e] [DecidableEq e] in
/-- The Gram of two stored powers is the corresponding moment. -/
theorem pow_block_gram (hA : A.IsHermitian) (B : Matrix n e ℂ) (i j : ℕ) :
    (A ^ i * B)ᴴ * (A ^ j * B) = moment A B (i + j) := by
  unfold moment
  rw [conjTranspose_mul, (hA.pow i).eq, pow_add]
  simp only [Matrix.mul_assoc]

/-- The block Hankel matrix `ℍ_{r-1} = (M_{i+j})` of the first moments. -/
noncomputable def hankelLow (A : Matrix n n ℂ) (B : Matrix n e ℂ) (r : ℕ) :
    Matrix (Fin r × e) (Fin r × e) ℂ :=
  Matrix.of fun p q => moment A B ((p.1 : ℕ) + (q.1 : ℕ)) p.2 q.2

/-- The shifted block Hankel matrix `(M_{i+j+1})`. -/
noncomputable def hankelShift (A : Matrix n n ℂ) (B : Matrix n e ℂ) (r : ℕ) :
    Matrix (Fin r × e) (Fin r × e) ℂ :=
  Matrix.of fun p q => moment A B ((p.1 : ℕ) + (q.1 : ℕ) + 1) p.2 q.2

omit [Fintype e] [DecidableEq e] in
/-- The Hankel matrix is the Krylov Gram. -/
theorem hankelLow_eq (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    hankelLow A B r = (krylovMat A B r)ᴴ * krylovMat A B r := by
  ext p q
  have hblock := congrFun (congrFun (pow_block_gram hA B (p.1 : ℕ) (q.1 : ℕ)) p.2) q.2
  calc hankelLow A B r p q
      = moment A B ((p.1 : ℕ) + (q.1 : ℕ)) p.2 q.2 := by
        rw [hankelLow, Matrix.of_apply]
    _ = ((A ^ (p.1 : ℕ) * B)ᴴ * (A ^ (q.1 : ℕ) * B)) p.2 q.2 := hblock.symm
    _ = ((krylovMat A B r)ᴴ * krylovMat A B r) p q := by
        rw [Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, krylovMat,
          Matrix.of_apply, Matrix.of_apply]

omit [DecidableEq e] in
/-- The Hankel matrix is PSD. -/
theorem hankelLow_posSemidef (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    (hankelLow A B r).PosSemidef := by
  rw [hankelLow_eq hA]
  exact posSemidef_conjTranspose_mul_self _

omit [Fintype e] [DecidableEq e] in
/-- The block shift in matrix form. -/
theorem mul_krylovMat (A : Matrix n n ℂ) (B : Matrix n e ℂ) (r : ℕ) :
    A * krylovMat A B r
      = Matrix.of fun x (p : Fin r × e) => (A ^ ((p.1 : ℕ) + 1) * B) x p.2 := by
  ext x p
  exact mul_krylovMat_apply A B r x p

omit [Fintype e] [DecidableEq e] in
/-- The shifted Hankel matrix is the compressed operator on the Krylov
synthesis. -/
theorem hankelShift_eq (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    hankelShift A B r = (krylovMat A B r)ᴴ * A * krylovMat A B r := by
  rw [Matrix.mul_assoc, mul_krylovMat]
  ext p q
  have hblock := congrFun (congrFun
    (pow_block_gram hA B (p.1 : ℕ) ((q.1 : ℕ) + 1)) p.2) q.2
  calc hankelShift A B r p q
      = moment A B ((p.1 : ℕ) + ((q.1 : ℕ) + 1)) p.2 q.2 := by
        rw [hankelShift, Matrix.of_apply, Nat.add_assoc]
    _ = ((A ^ (p.1 : ℕ) * B)ᴴ * (A ^ ((q.1 : ℕ) + 1) * B)) p.2 q.2 := hblock.symm
    _ = ((krylovMat A B r)ᴴ
          * Matrix.of (fun x (p' : Fin r × e) => (A ^ ((p'.1 : ℕ) + 1) * B) x p'.2))
          p q := by
        rw [Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          krylovMat, Matrix.of_apply]

/-- **(LNS.18)**: the whitened compressed operator
`Â_r = ℍ_{r-1}^{†/2}(M_{i+j+1})ℍ_{r-1}^{†/2}`. -/
noncomputable def whitenedOp (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    Matrix (Fin r × e) (Fin r × e) ℂ :=
  pinvSqrt (hankelLow_posSemidef hA B r).1 * hankelShift A B r
    * pinvSqrt (hankelLow_posSemidef hA B r).1

/-- The stacked moment column `(M_i)_{i<r}`. -/
noncomputable def momentCol (A : Matrix n n ℂ) (B : Matrix n e ℂ) (r : ℕ) :
    Matrix (Fin r × e) e ℂ :=
  Matrix.of fun p c => moment A B (p.1 : ℕ) p.2 c

/-- The whitened moment column `V = ℍ^{†/2}(M_i)_{i<r}`. -/
noncomputable def whitenedV (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    Matrix (Fin r × e) e ℂ :=
  pinvSqrt (hankelLow_posSemidef hA B r).1 * momentCol A B r

omit [Fintype e] [DecidableEq e] in
/-- The moment column is the Krylov compression of the source. -/
theorem momentCol_eq (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    momentCol A B r = (krylovMat A B r)ᴴ * B := by
  ext p c
  have hblock := congrFun (congrFun (pow_block_gram hA B (p.1 : ℕ) 0) p.2) c
  rw [pow_zero, Matrix.one_mul, Nat.add_zero] at hblock
  calc momentCol A B r p c
      = moment A B (p.1 : ℕ) p.2 c := by rw [momentCol, Matrix.of_apply]
    _ = ((A ^ (p.1 : ℕ) * B)ᴴ * B) p.2 c := hblock.symm
    _ = ((krylovMat A B r)ᴴ * B) p c := by
        rw [Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, krylovMat,
          Matrix.of_apply]

/-- The squared pseudoinverse square root is the pseudoinverse. -/
theorem pinvSqrt_mul_pinvSqrt {M : Matrix e e ℂ} (hM : M.IsHermitian) :
    pinvSqrt hM * pinvSqrt hM = pinv hM := by
  unfold pinvSqrt pinv
  rw [spectralFunction_mul]
  refine spectralFunction_congr hM fun i => ?_
  by_cases h : 0 < hM.eigenvalues i
  · rw [ite_eq_left h, ite_eq_left h, ← mul_inv, Real.mul_self_sqrt h.le]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-- The whitened Krylov synthesis `W = K ℍ^{†/2}`. -/
noncomputable def krylovWhite (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    Matrix n (Fin r × e) ℂ :=
  krylovMat A B r * pinvSqrt (hankelLow_posSemidef hA B r).1

/-- The adjoint of the whitened synthesis. -/
theorem krylovWhite_conjTranspose (hA : A.IsHermitian) (B : Matrix n e ℂ)
    (r : ℕ) :
    (krylovWhite hA B r)ᴴ
      = pinvSqrt (hankelLow_posSemidef hA B r).1 * (krylovMat A B r)ᴴ := by
  rw [krylovWhite, conjTranspose_mul, (pinvSqrt_isHermitian _).eq]

/-- The whitened synthesis realizes the Krylov range projection. -/
theorem krylovWhite_mul_conjTranspose (hA : A.IsHermitian) (B : Matrix n e ℂ)
    (r : ℕ) :
    krylovWhite hA B r * (krylovWhite hA B r)ᴴ = colProj (krylovMat A B r) := by
  rw [krylovWhite_conjTranspose hA, krylovWhite]
  have hpinv_eq : pinv (hankelLow_posSemidef hA B r).1
      = pinv (posSemidef_conjTranspose_mul_self (krylovMat A B r)).1 :=
    pinv_congr (hankelLow_eq hA B r) _ _
  calc krylovMat A B r * pinvSqrt (hankelLow_posSemidef hA B r).1
        * (pinvSqrt (hankelLow_posSemidef hA B r).1 * (krylovMat A B r)ᴴ)
      = krylovMat A B r * (pinvSqrt (hankelLow_posSemidef hA B r).1
          * pinvSqrt (hankelLow_posSemidef hA B r).1) * (krylovMat A B r)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = krylovMat A B r
        * pinv (posSemidef_conjTranspose_mul_self (krylovMat A B r)).1
        * (krylovMat A B r)ᴴ := by
        rw [pinvSqrt_mul_pinvSqrt, hpinv_eq]
    _ = colProj (krylovMat A B r) := rfl

/-- The whitened operator through the whitened synthesis. -/
theorem whitenedOp_eq (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    whitenedOp hA B r = (krylovWhite hA B r)ᴴ * A * krylovWhite hA B r := by
  rw [whitenedOp, hankelShift_eq hA, krylovWhite_conjTranspose hA, krylovWhite]
  simp only [Matrix.mul_assoc]

/-- The whitened column through the whitened synthesis. -/
theorem whitenedV_eq (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    whitenedV hA B r = (krylovWhite hA B r)ᴴ * B := by
  rw [whitenedV, momentCol_eq hA, krylovWhite_conjTranspose hA, Matrix.mul_assoc]

/-- **(LNS.18)**: on the flat branch the whitened compressed operator and
column reconstruct every source moment: `M_k = V^*Â_r^kV`.  In particular
the complete source-visible mass measure is determined by the finitely
many Hankel data entering `Â_r` and `V`. -/
theorem flat_moment_reconstruction (hA : A.IsHermitian) {B : Matrix n e ℂ}
    {r : ℕ} (hflat : innovation A B r = 0) (k : ℕ) :
    moment A B k
      = (whitenedV hA B r)ᴴ * (whitenedOp hA B r) ^ k * whitenedV hA B r := by
  have hfix : ∀ m : ℕ,
      colProj (krylovMat A B r) * (A ^ m * B) = A ^ m * B := fun m =>
    innovation_zero_fixes_pow hA hflat m
  have hWWc := krylovWhite_mul_conjTranspose hA B r
  -- the reconstruction induction
  have hind : ∀ k : ℕ, (whitenedOp hA B r) ^ k * whitenedV hA B r
      = (krylovWhite hA B r)ᴴ * (A ^ k * B) := by
    intro k
    induction k with
    | zero => rw [pow_zero, Matrix.one_mul, whitenedV_eq hA, pow_zero, Matrix.one_mul]
    | succ k ih =>
      calc (whitenedOp hA B r) ^ (k + 1) * whitenedV hA B r
          = whitenedOp hA B r * ((whitenedOp hA B r) ^ k * whitenedV hA B r) := by
            rw [pow_succ', Matrix.mul_assoc]
        _ = (krylovWhite hA B r)ᴴ * A * (krylovWhite hA B r
            * ((krylovWhite hA B r)ᴴ * (A ^ k * B))) := by
            rw [ih, whitenedOp_eq hA, Matrix.mul_assoc]
        _ = (krylovWhite hA B r)ᴴ * A
            * (colProj (krylovMat A B r) * (A ^ k * B)) := by
            rw [← Matrix.mul_assoc (krylovWhite hA B r) _ _, hWWc]
        _ = (krylovWhite hA B r)ᴴ * (A ^ (k + 1) * B) := by
            rw [hfix, pow_succ']
            simp only [Matrix.mul_assoc]
  -- conclude
  calc moment A B k
      = Bᴴ * (A ^ k * B) := by rw [moment, Matrix.mul_assoc]
    _ = Bᴴ * (colProj (krylovMat A B r) * (A ^ k * B)) := by rw [hfix]
    _ = ((krylovWhite hA B r)ᴴ * B)ᴴ * ((krylovWhite hA B r)ᴴ * (A ^ k * B)) := by
        rw [conjTranspose_mul, conjTranspose_conjTranspose, ← hWWc]
        simp only [Matrix.mul_assoc]
    _ = (whitenedV hA B r)ᴴ * ((whitenedOp hA B r) ^ k * whitenedV hA B r) := by
        rw [hind k, whitenedV_eq hA]
    _ = _ := by rw [Matrix.mul_assoc]

open scoped MatrixOrder in
/-- **The polar synthesis of the innovation**: the innovation has a unique
positive-semidefinite square root — the canonical minimum new mass
source of the flat-closure branch. -/
theorem innovation_polar (hA : A.IsHermitian) (B : Matrix n e ℂ) (r : ℕ) :
    ∃! R : Matrix e e ℂ, R.PosSemidef ∧ R * R = innovation A B r := by
  have hpsd : (innovation A B r).PosSemidef := innovation_posSemidef hA B r
  have h0 : (0 : Matrix e e ℂ) ≤ innovation A B r := hpsd.nonneg
  refine ⟨CFC.sqrt (innovation A B r),
    ⟨(CFC.sqrt_nonneg (innovation A B r)).posSemidef,
      CFC.sqrt_mul_sqrt_self _ h0⟩, fun R hR => ?_⟩
  exact ((CFC.sqrt_eq_iff _ _ h0 hR.1.nonneg).mpr hR.2).symm

end Krylov

/-! #### The isolated-shell criterion (LNS.19/19a) and the five-branch
source-visible alternative -/

section Shell

open NCG.RenormCongruence

variable {A : Matrix n n ℂ} {B : Matrix n e ℂ}

open Classical in
/-- The complex spectral calculus of a real symbol is the real spectral
calculus. -/
theorem cSpec_eq_spectralFunction (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cSpec hA (fun l => ((f l : ℝ) : ℂ)) = spectralFunction hA f := by
  unfold cSpec spectralFunction
  rw [Unitary.conjStarAlgAut_apply]
  rfl

open Classical in
omit [Fintype e] [DecidableEq e] in
/-- The window Gram of a singleton is the sector Gram of the sector
projection. -/
theorem windowGram_singleton_eq (hA : A.IsHermitian) (B : Matrix n e ℂ) (μ : ℝ) :
    windowGram hA B {μ} = Bᴴ * Superselection.sectorProj hA μ * B := by
  unfold windowGram Superselection.sectorProj
  rw [← cSpec_eq_spectralFunction hA (fun l => if l = μ then 1 else 0)]
  congr 2
  refine cSpec_congr hA fun i => ?_
  rw [Set.mem_singleton_iff, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one,
    Complex.ofReal_zero]

omit [DecidableEq e] in
/-- Singleton window Grams are PSD. -/
theorem windowGram_singleton_posSemidef (hA : A.IsHermitian) (B : Matrix n e ℂ)
    (μ : ℝ) : (windowGram hA B {μ}).PosSemidef := by
  rw [windowGram_singleton_eq hA B μ]
  have hidem := Superselection.sectorProj_idem hA μ
  have hherm := Superselection.sectorProj_isHermitian hA μ
  have hgram : Bᴴ * Superselection.sectorProj hA μ * B
      = (Superselection.sectorProj hA μ * B)ᴴ
        * (Superselection.sectorProj hA μ * B) := by
    rw [conjTranspose_mul, hherm.eq]
    calc Bᴴ * Superselection.sectorProj hA μ * B
        = Bᴴ * (Superselection.sectorProj hA μ
            * Superselection.sectorProj hA μ) * B := by rw [hidem]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hgram]
  exact posSemidef_conjTranspose_mul_self _

open Classical in
omit [DecidableEq e] in
/-- Windows missing every eigenvalue carry zero compressed mass: the
compressed invariant-mass measure is finite atomic on the spectrum. -/
theorem windowGram_eq_zero_of_disjoint (hA : A.IsHermitian) (B : Matrix n e ℂ)
    {S : Set ℝ} (h : ∀ i, hA.eigenvalues i ∉ S) : windowGram hA B S = 0 := by
  rw [windowGram_eq]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ite_eq_right (h i), zero_smul]

/-- An isolating margin below the least spectral gap at `t`. -/
theorem exists_isolating_delta (hA : A.IsHermitian) (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, hA.eigenvalues i ≠ t →
      hA.eigenvalues i ∉ Set.Ioo (t - δ) (t + δ) := by
  classical
  set T := Finset.univ.filter fun i : n => hA.eigenvalues i ≠ t with hT
  rcases T.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun i hi => ?_⟩
    exfalso
    have : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    rw [hemp] at this
    exact absurd this (Finset.notMem_empty i)
  · set img := T.image fun i => |hA.eigenvalues i - t| with himg
    have himgne : img.Nonempty := hne.image _
    refine ⟨img.min' himgne, ?_, ?_⟩
    · have hmem := img.min'_mem himgne
      obtain ⟨i, hi, hval⟩ := Finset.mem_image.mp hmem
      rw [← hval]
      have hne0 : hA.eigenvalues i - t ≠ 0 :=
        sub_ne_zero.mpr (Finset.mem_filter.mp hi).2
      exact abs_pos.mpr hne0
    · intro i hi hcon
      obtain ⟨h1, h2⟩ := hcon
      have himem : |hA.eigenvalues i - t| ∈ img :=
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      have hmin := img.min'_le _ himem
      have habs : |hA.eigenvalues i - t| < img.min' himgne := by
        rw [abs_lt]
        constructor <;> linarith
      linarith

/-- **(LNS.19)**: the manuscript's isolated source-visible shell criterion:
a nonzero source residue and a punctured spectral window of zero
compressed mass. -/
def IsIsolatedShell (hA : A.IsHermitian) (B : Matrix n e ℂ) (m : ℝ) : Prop :=
  windowGram hA B {m ^ 2} ≠ 0 ∧ ∃ δ : ℝ, 0 < δ ∧
    windowGram hA B
      ((Set.Ioo (m ^ 2 - δ) (m ^ 2 + δ) ∩ Set.Ici 0) \ {m ^ 2}) = 0

omit [DecidableEq e] in
/-- **(LNS.19), finite form**: on the finite carrier the punctured-window
clause holds automatically below the least spectral gap, so the criterion
is the nonvanishing of the source residue. -/
theorem isolated_shell_iff (hA : A.IsHermitian) (B : Matrix n e ℂ) (m : ℝ) :
    IsIsolatedShell hA B m ↔ windowGram hA B {m ^ 2} ≠ 0 := by
  constructor
  · exact fun h => h.1
  · intro h
    obtain ⟨δ, hδ, hiso⟩ := exists_isolating_delta hA (m ^ 2)
    refine ⟨h, δ, hδ, windowGram_eq_zero_of_disjoint hA B fun i => ?_⟩
    intro hcon
    obtain ⟨⟨hIoo, -⟩, hne⟩ := hcon
    rw [Set.mem_singleton_iff] at hne
    exact hiso i hne hIoo

/-- **(LNS.19a)**: the canonical source-minimal shell isometry
`J = P_{m²} B Z^{†/2}`. -/
noncomputable def shellIsometry (hA : A.IsHermitian) (B : Matrix n e ℂ) (m : ℝ) :
    Matrix n e ℂ :=
  Superselection.sectorProj hA (m ^ 2) * B
    * pinvSqrt (windowGram_singleton_posSemidef hA B (m ^ 2)).1

/-- **(LNS.19a)**: the shell synthesis is a partial isometry from the
support of the residue Gram into the shell sector, of particle-source rank
`rank Z_m(B)`. -/
theorem shell_isometry_properties (hA : A.IsHermitian) (B : Matrix n e ℂ)
    (m : ℝ) :
    (shellIsometry hA B m)ᴴ * shellIsometry hA B m
        = supportProj (windowGram_singleton_posSemidef hA B (m ^ 2)).1 ∧
      Superselection.sectorProj hA (m ^ 2) * shellIsometry hA B m
        = shellIsometry hA B m ∧
      (shellIsometry hA B m).rank = (windowGram hA B {m ^ 2}).rank := by
  have hEH := Superselection.sectorProj_isHermitian hA (m ^ 2)
  have hEE := Superselection.sectorProj_idem hA (m ^ 2)
  have hGH : (pinvSqrt (windowGram_singleton_posSemidef hA B (m ^ 2)).1).IsHermitian :=
    pinvSqrt_isHermitian _
  have hJH : (shellIsometry hA B m)ᴴ
      = pinvSqrt (windowGram_singleton_posSemidef hA B (m ^ 2)).1
        * (Bᴴ * Superselection.sectorProj hA (m ^ 2)) := by
    rw [shellIsometry, conjTranspose_mul, conjTranspose_mul, hGH.eq, hEH.eq]
  have hgram : (shellIsometry hA B m)ᴴ * shellIsometry hA B m
      = supportProj (windowGram_singleton_posSemidef hA B (m ^ 2)).1 := by
    rw [hJH, shellIsometry]
    calc pinvSqrt (windowGram_singleton_posSemidef hA B (m ^ 2)).1
          * (Bᴴ * Superselection.sectorProj hA (m ^ 2))
          * (Superselection.sectorProj hA (m ^ 2) * B
            * pinvSqrt (windowGram_singleton_posSemidef hA B (m ^ 2)).1)
        = pinvSqrt (windowGram_singleton_posSemidef hA B (m ^ 2)).1
          * (Bᴴ * ((Superselection.sectorProj hA (m ^ 2)
              * Superselection.sectorProj hA (m ^ 2))
            * (B * pinvSqrt (windowGram_singleton_posSemidef hA B (m ^ 2)).1))) := by
          simp only [Matrix.mul_assoc]
      _ = pinvSqrt (windowGram_singleton_posSemidef hA B (m ^ 2)).1
          * (Bᴴ * Superselection.sectorProj hA (m ^ 2) * B)
          * pinvSqrt (windowGram_singleton_posSemidef hA B (m ^ 2)).1 := by
          rw [hEE]
          simp only [Matrix.mul_assoc]
      _ = pinvSqrt (windowGram_singleton_posSemidef hA B (m ^ 2)).1
          * windowGram hA B {m ^ 2}
          * pinvSqrt (windowGram_singleton_posSemidef hA B (m ^ 2)).1 := by
          rw [← windowGram_singleton_eq hA B (m ^ 2)]
      _ = supportProj (windowGram_singleton_posSemidef hA B (m ^ 2)).1 :=
          pinvSqrt_mul_mul (windowGram_singleton_posSemidef hA B (m ^ 2))
  refine ⟨hgram, ?_, ?_⟩
  · rw [shellIsometry, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE]
  · -- rank of the partial isometry is the residue rank
    have h1 : (shellIsometry hA B m).rank
        = (supportProj (windowGram_singleton_posSemidef hA B (m ^ 2)).1).rank := by
      rw [← hgram, Matrix.rank_conjTranspose_mul_self]
    have hZpsd := windowGram_singleton_posSemidef hA B (m ^ 2)
    have h2 : (supportProj hZpsd.1).rank = (windowGram hA B ({m ^ 2} : Set ℝ)).rank := by
      refine le_antisymm ?_ ?_
      · rw [supportProj_eq_pinv_mul hZpsd.1]
        exact Matrix.rank_mul_le_right _ _
      · conv_lhs => rw [← supportProj_mul_self hZpsd]
        exact Matrix.rank_mul_le_left _ _
    rw [h1, h2]

open Classical in
/-- The set of visible spectral masses: eigenvalues with nonzero sector
Gram. -/
noncomputable def visibleMassSet (hA : A.IsHermitian) (B : Matrix n e ℂ) :
    Finset ℝ :=
  (Finset.univ.image hA.eigenvalues).filter fun μ => windowGram hA B {μ} ≠ 0

omit [DecidableEq e] in
/-- The total compressed mass is the source Gram. -/
theorem windowGram_univ (hA : A.IsHermitian) (B : Matrix n e ℂ) :
    windowGram hA B Set.univ = Bᴴ * B := by
  have h2 := compress_cSpec hA B (fun _ => (1 : ℂ))
  rw [cSpec_const, one_smul, Matrix.mul_one] at h2
  simp only [one_smul] at h2
  rw [windowGram_eq]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2.symm
  rw [ite_eq_left (Set.mem_univ (hA.eigenvalues i)), one_smul]

omit [DecidableEq e] in
/-- Zero total compressed mass is exactly vanishing of the source
synthesis: invisibility is a property of the source atlas. -/
theorem windowGram_univ_eq_zero_iff (hA : A.IsHermitian) (B : Matrix n e ℂ) :
    windowGram hA B Set.univ = 0 ↔ B = 0 := by
  rw [windowGram_univ]
  exact ⟨fun h => Matrix.conjTranspose_mul_self_eq_zero.mp h,
    fun h => by rw [h, Matrix.mul_zero]⟩

omit [DecidableEq e] in
/-- The total compressed mass is the sum of the spectral atoms. -/
theorem windowGram_univ_partition (hA : A.IsHermitian) (B : Matrix n e ℂ) :
    windowGram hA B Set.univ
      = ∑ μ ∈ Finset.univ.image hA.eigenvalues, windowGram hA B {μ} := by
  classical
  have hR : ∀ μ : ℝ, windowGram hA B {μ}
      = ∑ i, (if hA.eigenvalues i = μ then (1 : ℂ) else 0) • wMat hA B i := by
    intro μ
    rw [windowGram_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Set.mem_singleton_iff]
  have hcollapse : ∀ i : n, ∑ μ ∈ Finset.univ.image hA.eigenvalues,
      (if hA.eigenvalues i = μ then (1 : ℂ) else 0) • wMat hA B i
        = wMat hA B i := by
    intro i
    have hstep : ∀ μ : ℝ,
        (if hA.eigenvalues i = μ then (1 : ℂ) else 0) • wMat hA B i
          = if hA.eigenvalues i = μ then wMat hA B i else 0 := by
      intro μ
      split_ifs
      · rw [one_smul]
      · rw [zero_smul]
    rw [Finset.sum_congr rfl fun μ _ => hstep μ,
      Finset.sum_ite_eq (Finset.univ.image hA.eigenvalues) (hA.eigenvalues i)
        (fun _ => wMat hA B i),
      ite_eq_left (Finset.mem_image_of_mem hA.eigenvalues (Finset.mem_univ i))]
  rw [windowGram_eq]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_comm.trans
      (Finset.sum_congr rfl fun μ _ => (hR μ).symm))
  rw [ite_eq_left (Set.mem_univ (hA.eigenvalues i)), one_smul,
    hcollapse i]

omit [DecidableEq e] in
/-- An empty visible set forces zero total compressed mass. -/
theorem total_eq_zero_of_visible_empty (hA : A.IsHermitian) (B : Matrix n e ℂ)
    (h : visibleMassSet hA B = ∅) : windowGram hA B Set.univ = 0 := by
  classical
  rw [windowGram_univ_partition hA B]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  by_contra hne
  have hmem : μ ∈ visibleMassSet hA B := Finset.mem_filter.mpr ⟨hμ, hne⟩
  rw [h] at hmem
  exact absurd hmem (Finset.notMem_empty μ)

/-- Branch 1: source invisibility. -/
def SourceInvisible (hA : A.IsHermitian) (B : Matrix n e ℂ) : Prop :=
  windowGram hA B Set.univ = 0

/-- Branch 2: nonzero mass with a different lower support edge. -/
def SupportMismatch (hA : A.IsHermitian) (B : Matrix n e ℂ) (m : ℝ) : Prop :=
  ∃ h : (visibleMassSet hA B).Nonempty, (visibleMassSet hA B).min' h ≠ m ^ 2

/-- Branch 4: an embedded atom with nonzero punctured-neighbourhood
leakage. -/
def EmbeddedAtom (hA : A.IsHermitian) (B : Matrix n e ℂ) (m : ℝ) : Prop :=
  windowGram hA B {m ^ 2} ≠ 0 ∧ ∀ δ : ℝ, 0 < δ →
    windowGram hA B
      ((Set.Ioo (m ^ 2 - δ) (m ^ 2 + δ) ∩ Set.Ici 0) \ {m ^ 2}) ≠ 0

/-- Branch 5: a threshold continuum with zero atom and positive mass in
every right neighbourhood. -/
def ThresholdContinuum (hA : A.IsHermitian) (B : Matrix n e ℂ) (m : ℝ) : Prop :=
  windowGram hA B {m ^ 2} = 0 ∧ ∀ δ : ℝ, 0 < δ →
    windowGram hA B (Set.Ioo (m ^ 2) (m ^ 2 + δ)) ≠ 0

omit [DecidableEq e] in
/-- **The exhaustive five-branch source-visible alternative** for a
declared candidate lower edge `m²`: source invisibility, support mismatch,
an isolated shell, an embedded atom, or a threshold continuum. -/
theorem shell_alternative (hA : A.IsHermitian) (B : Matrix n e ℂ) (m : ℝ) :
    SourceInvisible hA B ∨ SupportMismatch hA B m ∨ IsIsolatedShell hA B m
      ∨ EmbeddedAtom hA B m ∨ ThresholdContinuum hA B m := by
  classical
  by_cases hvis : (visibleMassSet hA B).Nonempty
  · by_cases hedge : (visibleMassSet hA B).min' hvis = m ^ 2
    · -- the declared edge is the least visible mass: an isolated shell
      refine Or.inr (Or.inr (Or.inl ?_))
      rw [isolated_shell_iff]
      have hmem := (visibleMassSet hA B).min'_mem hvis
      rw [hedge] at hmem
      exact (Finset.mem_filter.mp hmem).2
    · exact Or.inr (Or.inl ⟨hvis, hedge⟩)
  · refine Or.inl (total_eq_zero_of_visible_empty hA B ?_)
    exact Finset.not_nonempty_iff_eq_empty.mp hvis

omit [DecidableEq e] in
/-- On the finite carrier the embedded-atom and threshold-continuum
branches are never taken: below the least spectral gap the punctured
window and the right window are empty of spectrum. -/
theorem embedded_threshold_never (hA : A.IsHermitian) (B : Matrix n e ℂ)
    (m : ℝ) :
    ¬ EmbeddedAtom hA B m ∧ ¬ ThresholdContinuum hA B m := by
  obtain ⟨δ, hδ, hiso⟩ := exists_isolating_delta hA (m ^ 2)
  constructor
  · rintro ⟨-, hleak⟩
    refine hleak δ hδ (windowGram_eq_zero_of_disjoint hA B fun i => ?_)
    rintro ⟨⟨hIoo, -⟩, hne⟩
    rw [Set.mem_singleton_iff] at hne
    exact hiso i hne hIoo
  · rintro ⟨-, hcont⟩
    refine hcont δ hδ (windowGram_eq_zero_of_disjoint hA B fun i => ?_)
    rintro ⟨h1, h2⟩
    by_cases hne : hA.eigenvalues i = m ^ 2
    · rw [hne] at h1
      exact absurd h1 (lt_irrefl _)
    · exact hiso i hne ⟨by linarith, h2⟩

/-- Zero total source mass is absence only after the atlas is complete: an
incomplete (zero) atlas hides a nonzero mass operator. -/
theorem invisibility_needs_complete_atlas :
    ∃ (A' : Matrix (Fin 1) (Fin 1) ℂ) (hA' : A'.IsHermitian),
      A' ≠ 0 ∧ windowGram hA' (0 : Matrix (Fin 1) (Fin 1) ℂ) Set.univ = 0 := by
  refine ⟨1, ?_, one_ne_zero, ?_⟩
  · change (1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ = 1
    rw [Matrix.conjTranspose_one]
  · rw [windowGram_univ, Matrix.mul_zero]

end Shell

end MassShell

end MassShellSection

/-! ### `cth:SMOS-atom-dissolution` — Cutoffwise atoms can dissolve

Rendering: the measures (LNS.20a) are constructed literally as weighted
sums of Dirac measures on `ℝ`,
`μ_n = (1/n)δ_{m²} + (1-1/n)(1/n)Σ_{k=1}^n δ_{m²+k/n}`.  At every finite
cutoff `μ_n` is a probability measure whose atom at `m²` has residue
`1/n`, whose punctured window of radius `1/n` is empty (and the mass at
`m²+1/n` is nonzero for `n ≥ 2`, so `1/n` is exactly the isolation gap),
and `∫f dμ_n → ∫_{m²}^{m²+1} f` for every continuous test function — the
uniform (Lebesgue) measure on `[m², m²+1]`, which has no atom at `m²`. -/

section AtomDissolutionSection

namespace AtomDissolution

open MeasureTheory
open scoped ENNReal

/-- **(LNS.20a)**: the dissolving cutoff measures
`μ_n = (1/n)δ_{m²} + (1-1/n)(1/n)Σ_{k=1}^n δ_{m²+k/n}`. -/
noncomputable def dissolve (m : ℝ) (n : ℕ) : Measure ℝ :=
  ((n : ℝ≥0∞))⁻¹ • Measure.dirac (m ^ 2)
    + ((1 - ((n : ℝ≥0∞))⁻¹) * ((n : ℝ≥0∞))⁻¹)
      • ∑ k ∈ Finset.Icc 1 n, Measure.dirac (m ^ 2 + (k : ℝ) / n)

/-- The window value of the dissolving measure on any set. -/
theorem dissolve_apply (m : ℝ) (n : ℕ) (S : Set ℝ) :
    dissolve m n S
      = ((n : ℝ≥0∞))⁻¹ * S.indicator 1 (m ^ 2)
        + (1 - ((n : ℝ≥0∞))⁻¹) * ((n : ℝ≥0∞))⁻¹
          * ∑ k ∈ Finset.Icc 1 n, S.indicator 1 (m ^ 2 + (k : ℝ) / n) := by
  rw [dissolve, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.finsetSum_apply, Measure.dirac_apply, smul_eq_mul, smul_eq_mul]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [Measure.dirac_apply]

/-- The dissolving measures are probability measures. -/
theorem dissolve_univ (m : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    dissolve m n Set.univ = 1 := by
  have hn0 : ((n : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hntop : ((n : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hone : ∀ x : ℝ, (Set.univ : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) x = 1 := fun x => by
    rw [Set.indicator_of_mem (Set.mem_univ x), Pi.one_apply]
  rw [dissolve_apply, hone, Finset.sum_congr rfl fun k _ => hone _, Finset.sum_const,
    Nat.card_Icc]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rw [mul_assoc, ENNReal.inv_mul_cancel hn0 hntop, mul_one,
    add_tsub_cancel_of_le (ENNReal.inv_le_one.mpr (by exact_mod_cast hn))]

/-- The shifted spectral train never hits the atom. -/
theorem shift_ne_atom (m : ℝ) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    m ^ 2 + (k : ℝ) / n ≠ m ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (k : ℝ) / n := div_pos hk' hn'
  intro hcon
  linarith

/-- **The residue at the atom is `1/n`**. -/
theorem dissolve_atom (m : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    dissolve m n {m ^ 2} = ((n : ℝ≥0∞))⁻¹ := by
  have h1 : ({m ^ 2} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) (m ^ 2) = 1 := by
    rw [Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply]
  have h0 : ∀ k ∈ Finset.Icc 1 n,
      ({m ^ 2} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) (m ^ 2 + (k : ℝ) / n) = 0 := by
    intro k hk
    refine Set.indicator_of_notMem ?_ _
    rw [Set.mem_singleton_iff]
    exact shift_ne_atom m hn (Finset.mem_Icc.mp hk).1
  rw [dissolve_apply, h1, mul_one, Finset.sum_congr rfl h0, Finset.sum_const,
    smul_zero, mul_zero, add_zero]

/-- **The isolation gap is at least `1/n`**: the punctured window of
radius `1/n` around the atom carries zero mass. -/
theorem dissolve_gap (m : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    dissolve m n (Set.Ioo (m ^ 2 - 1 / n) (m ^ 2 + 1 / n) \ {m ^ 2}) = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (Set.Ioo (m ^ 2 - 1 / n) (m ^ 2 + 1 / n) \ {m ^ 2}).indicator
      (1 : ℝ → ℝ≥0∞) (m ^ 2) = 0 := by
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨-, hne⟩
    exact hne (Set.mem_singleton _)
  have h0 : ∀ k ∈ Finset.Icc 1 n,
      (Set.Ioo (m ^ 2 - 1 / n) (m ^ 2 + 1 / n) \ {m ^ 2}).indicator
        (1 : ℝ → ℝ≥0∞) (m ^ 2 + (k : ℝ) / n) = 0 := by
    intro k hk
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨⟨-, hlt⟩, -⟩
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hge : (1 : ℝ) / n ≤ (k : ℝ) / n := by gcongr
    linarith
  rw [dissolve_apply, h1, mul_zero, Finset.sum_congr rfl h0, Finset.sum_const,
    smul_zero, mul_zero, add_zero]

/-- **The isolation gap is exactly `1/n`**: the next support point
`m² + 1/n` carries the mass `(1 - 1/n)/n`. -/
theorem dissolve_next (m : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    dissolve m n {m ^ 2 + 1 / n}
      = (1 - ((n : ℝ≥0∞))⁻¹) * ((n : ℝ≥0∞))⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ({m ^ 2 + 1 / n} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) (m ^ 2) = 0 := by
    refine Set.indicator_of_notMem ?_ _
    rw [Set.mem_singleton_iff]
    intro hcon
    have hpos : (0 : ℝ) < 1 / n := div_pos one_pos hn'
    linarith
  have h0 : ∀ k ∈ Finset.Icc 1 n,
      ({m ^ 2 + 1 / n} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) (m ^ 2 + (k : ℝ) / n)
        = if k = 1 then 1 else 0 := by
    intro k hk
    by_cases hk1 : k = 1
    · subst hk1
      rw [ite_eq_left rfl, Set.indicator_of_mem, Pi.one_apply]
      rw [Set.mem_singleton_iff, Nat.cast_one]
    · rw [ite_eq_right hk1]
      refine Set.indicator_of_notMem ?_ _
      rw [Set.mem_singleton_iff]
      intro hcon
      have hkn : (k : ℝ) / n = 1 / n := by linarith
      have hkR : (k : ℝ) = 1 := by
        field_simp at hkn
        exact_mod_cast hkn
      exact hk1 (by exact_mod_cast hkR)
  rw [dissolve_apply, h1, mul_zero, zero_add, Finset.sum_congr rfl h0,
    Finset.sum_ite_eq' (Finset.Icc 1 n) 1 (fun _ => (1 : ℝ≥0∞)),
    ite_eq_left (Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩), mul_one]

/-- The next-atom mass does not vanish beyond the first cutoff. -/
theorem dissolve_next_ne_zero (m : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    dissolve m n {m ^ 2 + 1 / n} ≠ 0 := by
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  rw [dissolve_next m hn1]
  have hn0 : ((n : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hn1
  refine mul_ne_zero (fun hc => ?_) (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n))
  have hle : (1 : ℝ≥0∞) ≤ ((n : ℝ≥0∞))⁻¹ := tsub_eq_zero_iff_le.mp hc
  have hlt : ((n : ℝ≥0∞))⁻¹ < 1 := ENNReal.inv_lt_one.mpr (by exact_mod_cast hn)
  exact absurd hle (not_le.mpr hlt)

/-- Left Riemann-type sums of a continuous function on `[a, a+1]`
converge to its integral. -/
theorem riemann_sum_tendsto {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, f (a + (k : ℝ) / n)) atTop
      (𝓝 (∫ x in a..(a + 1), f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Set.Icc a (a + 1)) hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδ, hδf⟩ := hUC (ε / 2) (by linarith)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / δ)
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hstep : (1 : ℝ) / n < δ := by
    rw [div_lt_iff₀ hnpos]
    have hδn : 1 / δ < (n : ℝ) := lt_of_lt_of_le hN₀ hnN
    calc (1 : ℝ) = δ * (1 / δ) := by field_simp
      _ < δ * n := by
          exact mul_lt_mul_of_pos_left hδn hδ
  -- the split of the integral over the grid
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (μ := MeasureTheory.volume) (a := fun k : ℕ => a + (k : ℝ) / n)
    (n := n) (fun k _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_div, add_zero, div_self (ne_of_gt hnpos)]
    at hsplit
  -- the Riemann sum over `range n`
  have hsum : (n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, f (a + (k : ℝ) / n)
      = ∑ k ∈ Finset.range n, (n : ℝ)⁻¹ * f (a + ((k + 1 : ℕ) : ℝ) / n) := by
    rw [Finset.mul_sum, ← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      Order.succ_eq_add_one, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.add_comm 1 k]
  -- the per-piece estimate
  have hpiece : ∀ k ∈ Finset.range n,
      |(n : ℝ)⁻¹ * f (a + ((k + 1 : ℕ) : ℝ) / n)
        - ∫ x in (a + (k : ℝ) / n)..(a + ((k + 1 : ℕ) : ℝ) / n), f x|
      ≤ ε / 2 * (n : ℝ)⁻¹ := by
    intro k hk
    have hkn : (k : ℝ) + 1 ≤ n := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hlen : (a + ((k + 1 : ℕ) : ℝ) / n) - (a + (k : ℝ) / n) = (n : ℝ)⁻¹ := by
      push_cast
      field_simp
      ring
    have hle : a + (k : ℝ) / n ≤ a + ((k + 1 : ℕ) : ℝ) / n := by
      push_cast
      have : (k : ℝ) / n ≤ ((k : ℝ) + 1) / n := by
        gcongr
        linarith
      linarith
    have hconst : ∫ _x in (a + (k : ℝ) / n)..(a + ((k + 1 : ℕ) : ℝ) / n),
        f (a + ((k + 1 : ℕ) : ℝ) / n)
        = (n : ℝ)⁻¹ * f (a + ((k + 1 : ℕ) : ℝ) / n) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, hlen]
    have hdiff : (n : ℝ)⁻¹ * f (a + ((k + 1 : ℕ) : ℝ) / n)
        - ∫ x in (a + (k : ℝ) / n)..(a + ((k + 1 : ℕ) : ℝ) / n), f x
        = ∫ x in (a + (k : ℝ) / n)..(a + ((k + 1 : ℕ) : ℝ) / n),
            (f (a + ((k + 1 : ℕ) : ℝ) / n) - f x) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        (hf.intervalIntegrable _ _), hconst]
    rw [hdiff]
    -- both membership windows
    have hmemR : a + ((k + 1 : ℕ) : ℝ) / n ∈ Set.Icc a (a + 1) := by
      constructor
      · push_cast
        have : (0 : ℝ) ≤ ((k : ℝ) + 1) / n := by positivity
        linarith
      · push_cast
        have : ((k : ℝ) + 1) / n ≤ 1 := by
          rw [div_le_one hnpos]
          exact hkn
        linarith
    have hbound : ∀ x ∈ Set.uIoc (a + (k : ℝ) / n) (a + ((k + 1 : ℕ) : ℝ) / n),
        ‖f (a + ((k + 1 : ℕ) : ℝ) / n) - f x‖ ≤ ε / 2 := by
      intro x hx
      rw [Set.uIoc_of_le hle] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hxmem : x ∈ Set.Icc a (a + 1) := by
        constructor
        · have : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
          linarith
        · linarith [hmemR.2]
      have hdist : dist (a + ((k + 1 : ℕ) : ℝ) / n) x < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        have hxgap : a + ((k + 1 : ℕ) : ℝ) / n - x
            < (a + ((k + 1 : ℕ) : ℝ) / n) - (a + (k : ℝ) / n) := by linarith
        rw [hlen] at hxgap
        calc a + ((k + 1 : ℕ) : ℝ) / n - x < (n : ℝ)⁻¹ := hxgap
          _ = 1 / n := (one_div _).symm
          _ < δ := hstep
      have := hδf _ hmemR _ hxmem hdist
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      exact le_of_lt this
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs] at hnorm
    calc |∫ x in (a + (k : ℝ) / n)..(a + ((k + 1 : ℕ) : ℝ) / n),
          (f (a + ((k + 1 : ℕ) : ℝ) / n) - f x)|
        ≤ ε / 2 * |(a + ((k + 1 : ℕ) : ℝ) / n) - (a + (k : ℝ) / n)| := hnorm
      _ = ε / 2 * (n : ℝ)⁻¹ := by
          rw [hlen, abs_of_nonneg (by positivity)]
  -- assemble
  rw [Real.dist_eq, hsum, ← hsplit, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range n, ((n : ℝ)⁻¹ * f (a + ((k + 1 : ℕ) : ℝ) / n)
        - ∫ x in (a + (k : ℝ) / n)..(a + ((k + 1 : ℕ) : ℝ) / n), f x)|
      ≤ ∑ k ∈ Finset.range n, |(n : ℝ)⁻¹ * f (a + ((k + 1 : ℕ) : ℝ) / n)
        - ∫ x in (a + (k : ℝ) / n)..(a + ((k + 1 : ℕ) : ℝ) / n), f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, ε / 2 * (n : ℝ)⁻¹ := Finset.sum_le_sum hpiece
    _ = (n : ℝ) * (ε / 2 * (n : ℝ)⁻¹) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- The integral of a continuous test against the dissolving measure. -/
theorem dissolve_integral (f : ℝ → ℝ) (m : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, f x ∂dissolve m n
      = (n : ℝ)⁻¹ * f (m ^ 2)
        + (1 - (n : ℝ)⁻¹)
          * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, f (m ^ 2 + (k : ℝ) / n)) := by
  have hn0 : ((n : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hinv_ne_top : ((n : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hn0
  have hc2_ne_top : (1 - ((n : ℝ≥0∞))⁻¹) * ((n : ℝ≥0∞))⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
      hinv_ne_top
  have hdint : ∀ b : ℝ, MeasureTheory.Integrable f (Measure.dirac b) := fun b =>
    integrable_dirac enorm_lt_top
  have hsum_int : MeasureTheory.Integrable f
      (∑ k ∈ Finset.Icc 1 n, Measure.dirac (m ^ 2 + (k : ℝ) / n)) :=
    integrable_finsetSum_measure.mpr fun k _ => hdint _
  rw [dissolve, integral_add_measure ((hdint _).smul_measure hinv_ne_top)
    (hsum_int.smul_measure hc2_ne_top), integral_smul_measure,
    integral_smul_measure, integral_dirac,
    integral_finsetSum_measure fun k _ => hdint _]
  have htoReal : ((n : ℝ≥0∞))⁻¹.toReal = (n : ℝ)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hc2 : ((1 - ((n : ℝ≥0∞))⁻¹) * ((n : ℝ≥0∞))⁻¹).toReal
      = (1 - (n : ℝ)⁻¹) * (n : ℝ)⁻¹ := by
    rw [ENNReal.toReal_mul, htoReal,
      ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr (by exact_mod_cast hn))
        ENNReal.one_ne_top, ENNReal.toReal_one, htoReal]
  have hsum_dirac : ∑ k ∈ Finset.Icc 1 n,
      ∫ x, f x ∂Measure.dirac (m ^ 2 + (k : ℝ) / n)
      = ∑ k ∈ Finset.Icc 1 n, f (m ^ 2 + (k : ℝ) / n) :=
    Finset.sum_congr rfl fun k _ => integral_dirac f _
  rw [htoReal, hc2, smul_eq_mul, smul_eq_mul, hsum_dirac]
  ring

/-- **Weak convergence to the uniform measure**: for every continuous
test function the dissolving integrals converge to the Lebesgue integral
on `[m², m²+1]`. -/
theorem dissolve_weak (m : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Filter.Tendsto (fun n : ℕ => ∫ x, f x ∂dissolve m n) atTop
      (𝓝 (∫ x in (m ^ 2)..(m ^ 2 + 1), f x)) := by
  have hinv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hS := riemann_sum_tendsto hf (m ^ 2)
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * f (m ^ 2)) atTop
      (𝓝 (0 * f (m ^ 2))) := hinv.mul_const _
  have h2 : Filter.Tendsto (fun n : ℕ => 1 - (n : ℝ)⁻¹) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hinv
  have h3 := h1.add (h2.mul hS)
  rw [zero_mul, sub_zero, one_mul, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (dissolve_integral f m hn).symm

/-- The uniform measure on `[m², m²+1]` has no atom at `m²`. -/
theorem uniform_no_atom (m : ℝ) :
    MeasureTheory.volume.restrict (Set.Icc (m ^ 2) (m ^ 2 + 1)) {m ^ 2} = 0 := by
  rw [Measure.restrict_apply (measurableSet_singleton _)]
  exact measure_mono_null Set.inter_subset_left Real.volume_singleton

/-- The uniform measure on `[m², m²+1]` is a probability measure. -/
theorem uniform_prob (m : ℝ) :
    MeasureTheory.volume.restrict (Set.Icc (m ^ 2) (m ^ 2 + 1)) Set.univ = 1 := by
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  norm_num

/-- The Lebesgue integral on `[m², m²+1]` is the interval integral. -/
theorem uniform_integral (m : ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(MeasureTheory.volume.restrict (Set.Icc (m ^ 2) (m ^ 2 + 1)))
      = ∫ x in (m ^ 2)..(m ^ 2 + 1), f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith : m ^ 2 ≤ m ^ 2 + 1)]

/-- **`cth:SMOS-atom-dissolution`**, bundled: at every finite cutoff the
measure (LNS.20a) is a probability measure with an atom of residue `1/n`
at `m²`, empty punctured window of radius `1/n`, and (for `n ≥ 2`) a
nonzero next atom at distance exactly `1/n`; the measures converge weakly
to the uniform measure on `[m², m²+1]`, which is a probability measure
with no atom at `m²`. -/
theorem atom_dissolution (m : ℝ) :
    (∀ n : ℕ, 1 ≤ n → dissolve m n Set.univ = 1) ∧
    (∀ n : ℕ, 1 ≤ n → dissolve m n {m ^ 2} = ((n : ℝ≥0∞))⁻¹) ∧
    (∀ n : ℕ, 1 ≤ n →
      dissolve m n (Set.Ioo (m ^ 2 - 1 / n) (m ^ 2 + 1 / n) \ {m ^ 2}) = 0) ∧
    (∀ n : ℕ, 2 ≤ n → dissolve m n {m ^ 2 + 1 / n} ≠ 0) ∧
    (∀ f : ℝ → ℝ, Continuous f →
      Filter.Tendsto (fun n : ℕ => ∫ x, f x ∂dissolve m n) atTop
        (𝓝 (∫ x, f x
          ∂(MeasureTheory.volume.restrict (Set.Icc (m ^ 2) (m ^ 2 + 1)))))) ∧
    MeasureTheory.volume.restrict (Set.Icc (m ^ 2) (m ^ 2 + 1)) {m ^ 2} = 0 ∧
    MeasureTheory.volume.restrict (Set.Icc (m ^ 2) (m ^ 2 + 1)) Set.univ = 1 := by
  refine ⟨fun n hn => dissolve_univ m hn, fun n hn => dissolve_atom m hn,
    fun n hn => dissolve_gap m hn, fun n hn => dissolve_next_ne_zero m hn,
    fun f hf => ?_, uniform_no_atom m, uniform_prob m⟩
  rw [uniform_integral m f]
  exact dissolve_weak m hf

end AtomDissolution

end AtomDissolutionSection

/-! ### `thm:SMQG-crossing-factorization` — Relation descent and reflected hopping

Rendering: the one-letter space `𝓕₁` and the represented positive-time
carrier `𝓗₊` are finite; the occurring one-letter synthesis is
`W₁ : Matrix h f ℂ` (mapping `𝓕₁`-coefficients into `𝓗₊`), and
`P_W = W₁^†W₁` is realized as the orthogonal projection
`colProj W₁ᴴ` onto `(Ker W₁)^⊥ = Ran W₁ᴴ` (proved equal to the spectral
support projection of the Gram `W₁ᴴW₁`).  `‖·‖_HS²` is `hsNormSq`; the
relation residual (HX.2) and hopping residual (HX.3) are the manuscript
formulas; (HX.4) and (HX.5) use the Moore–Penrose data
`W₁^† = (W₁ᴴW₁)^†W₁ᴴ`, with minimality and uniqueness of the extension in
Hilbert–Schmidt norm over all represented matrices with the same
compression.  (HX.6) is the attained nearest-PSD distance through the
spectral Jordan split of the Hermitian part; (HX.7) is the three-way
equivalence; the rank clause produces an explicit rank-minimal factor and
proves all rank-minimal factors unitarily related; (HX.8) is the
substitution identity for the crossing action in an arbitrary
`ℂ`-algebra of represented sources. -/

section CrossingSection

namespace Crossing

open NCG.SMSTReflectionPositivity

variable {q : Type*} [Fintype q] [DecidableEq q]

/-- The Hermitian part `K_h = (K + K^*)/2`. -/
noncomputable def hermPart (K : Matrix q q ℂ) : Matrix q q ℂ :=
  ((2 : ℂ))⁻¹ • (K + Kᴴ)

/-- The anti-Hermitian part `K_a = (K - K^*)/2`. -/
noncomputable def antiPart (K : Matrix q q ℂ) : Matrix q q ℂ :=
  ((2 : ℂ))⁻¹ • (K - Kᴴ)

omit [Fintype q] [DecidableEq q] in
/-- The Hermitian part is Hermitian. -/
theorem hermPart_isHermitian (K : Matrix q q ℂ) : (hermPart K).IsHermitian := by
  change (hermPart K)ᴴ = hermPart K
  unfold hermPart
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  · rw [show ((2 : ℂ))⁻¹ = (((2 : ℝ))⁻¹ : ℝ) by norm_num, Complex.star_def,
      Complex.conj_ofReal]
  · rw [add_comm]

omit [Fintype q] [DecidableEq q] in
/-- The anti-Hermitian part is anti-Hermitian. -/
theorem antiPart_anti (K : Matrix q q ℂ) : (antiPart K)ᴴ = -antiPart K := by
  unfold antiPart
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose,
    show ((2 : ℂ))⁻¹ = (((2 : ℝ))⁻¹ : ℝ) by norm_num, Complex.star_def,
    Complex.conj_ofReal, ← smul_neg]
  congr 1
  rw [neg_sub]

omit [Fintype q] [DecidableEq q] in
/-- The Hermitian/anti-Hermitian decomposition. -/
theorem hermPart_add_antiPart (K : Matrix q q ℂ) :
    hermPart K + antiPart K = K := by
  unfold hermPart antiPart
  rw [← smul_add]
  have h : K + Kᴴ + (K - Kᴴ) = (2 : ℂ) • K := by
    rw [two_smul]
    abel
  rw [h, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

omit [DecidableEq q] in
/-- Vanishing Hilbert–Schmidt norm characterizes the zero matrix. -/
theorem hsNormSq_eq_zero_iff (X : Matrix q q ℂ) : hsNormSq X = 0 ↔ X = 0 := by
  rw [hsNormSq_eq_sum]
  constructor
  · intro h
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _).mp h i (Finset.mem_univ i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      sq_nonneg _).mp h1 j (Finset.mem_univ j)
    rw [Matrix.zero_apply]
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  · intro h
    rw [h]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.zero_apply, norm_zero]
    norm_num

omit [DecidableEq q] in
/-- Hilbert–Schmidt norms are invariant under negation. -/
theorem hsNormSq_neg (X : Matrix q q ℂ) : hsNormSq (-X) = hsNormSq X := by
  unfold hsNormSq
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

omit [DecidableEq q] in
/-- The Hilbert–Schmidt parallelogram expansion of a sum. -/
theorem hsNormSq_add (X Y : Matrix q q ℂ) :
    hsNormSq (X + Y)
      = hsNormSq X + hsNormSq Y + 2 * (Matrix.trace (Xᴴ * Y)).re := by
  have h := hsNormSq_sub X (-Y)
  rw [sub_neg_eq_add, hsNormSq_neg, Matrix.mul_neg, Matrix.trace_neg,
    Complex.neg_re] at h
  linarith

omit [DecidableEq q] in
/-- Anti-Hermitian and Hermitian matrices are Hilbert–Schmidt
orthogonal. -/
theorem re_trace_anti_herm (X Y : Matrix q q ℂ) (hX : Xᴴ = -X) (hY : Yᴴ = Y) :
    (Matrix.trace (Xᴴ * Y)).re = 0 := by
  have h1 : star (Matrix.trace (Xᴴ * Y)) = Matrix.trace (Yᴴ * X) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hX' : X = -Xᴴ := by rw [hX, neg_neg]
  have h2 : Matrix.trace (Yᴴ * X) = -Matrix.trace (Xᴴ * Y) := by
    rw [hY, Matrix.trace_mul_comm]
    conv_lhs => rw [hX']
    rw [Matrix.neg_mul, Matrix.trace_neg]
  have h3 := h1.trans h2
  have h4 := congrArg Complex.re h3
  rw [Complex.star_def, Complex.conj_re, Complex.neg_re] at h4
  linarith

/-- The Hilbert–Schmidt row split against an orthogonal projection. -/
theorem hsNormSq_left_split {Q : Matrix q q ℂ} (hQH : Q.IsHermitian)
    (hQ2 : Q * Q = Q) (Y : Matrix q q ℂ) :
    hsNormSq Y
      = hsNormSq (Q * Y) + hsNormSq (((1 : Matrix q q ℂ) - Q) * Y) := by
  unfold hsNormSq
  have h1 : (Q * Y)ᴴ * (Q * Y) = Yᴴ * (Q * Y) := by
    rw [Matrix.conjTranspose_mul]
    calc Yᴴ * Qᴴ * (Q * Y) = Yᴴ * ((Q * Q) * Y) := by
          rw [hQH.eq]
          simp only [Matrix.mul_assoc]
      _ = Yᴴ * (Q * Y) := by rw [hQ2]
  have hQ'H : ((1 : Matrix q q ℂ) - Q)ᴴ = (1 : Matrix q q ℂ) - Q := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQH.eq]
  have hQ'2 : ((1 : Matrix q q ℂ) - Q) * ((1 : Matrix q q ℂ) - Q)
      = (1 : Matrix q q ℂ) - Q := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hQ2]
    abel
  have h2 : (((1 : Matrix q q ℂ) - Q) * Y)ᴴ * (((1 : Matrix q q ℂ) - Q) * Y)
      = Yᴴ * (((1 : Matrix q q ℂ) - Q) * Y) := by
    rw [Matrix.conjTranspose_mul]
    calc Yᴴ * ((1 : Matrix q q ℂ) - Q)ᴴ * (((1 : Matrix q q ℂ) - Q) * Y)
        = Yᴴ * ((((1 : Matrix q q ℂ) - Q) * ((1 : Matrix q q ℂ) - Q)) * Y) := by
          rw [hQ'H]
          simp only [Matrix.mul_assoc]
      _ = Yᴴ * (((1 : Matrix q q ℂ) - Q) * Y) := by rw [hQ'2]
  rw [h1, h2, ← Complex.add_re, ← Matrix.trace_add, ← Matrix.mul_add,
    ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]

/-- The Hilbert–Schmidt column split against an orthogonal projection. -/
theorem hsNormSq_right_split {Q : Matrix q q ℂ} (hQH : Q.IsHermitian)
    (hQ2 : Q * Q = Q) (Y : Matrix q q ℂ) :
    hsNormSq Y
      = hsNormSq (Y * Q) + hsNormSq (Y * ((1 : Matrix q q ℂ) - Q)) := by
  unfold hsNormSq
  have h1 : Matrix.trace ((Y * Q)ᴴ * (Y * Q)) = Matrix.trace (Yᴴ * Y * Q) := by
    rw [Matrix.conjTranspose_mul]
    calc Matrix.trace (Qᴴ * Yᴴ * (Y * Q))
        = Matrix.trace (Qᴴ * (Yᴴ * Y * Q)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Yᴴ * Y * Q * Qᴴ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Yᴴ * Y * (Q * Q)) := by
          rw [hQH.eq]
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Yᴴ * Y * Q) := by rw [hQ2]
  have hQ'H : ((1 : Matrix q q ℂ) - Q)ᴴ = (1 : Matrix q q ℂ) - Q := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQH.eq]
  have hQ'2 : ((1 : Matrix q q ℂ) - Q) * ((1 : Matrix q q ℂ) - Q)
      = (1 : Matrix q q ℂ) - Q := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hQ2]
    abel
  have h2 : Matrix.trace ((Y * ((1 : Matrix q q ℂ) - Q))ᴴ
        * (Y * ((1 : Matrix q q ℂ) - Q)))
      = Matrix.trace (Yᴴ * Y * ((1 : Matrix q q ℂ) - Q)) := by
    rw [Matrix.conjTranspose_mul]
    calc Matrix.trace (((1 : Matrix q q ℂ) - Q)ᴴ * Yᴴ
          * (Y * ((1 : Matrix q q ℂ) - Q)))
        = Matrix.trace (((1 : Matrix q q ℂ) - Q)ᴴ
            * (Yᴴ * Y * ((1 : Matrix q q ℂ) - Q))) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Yᴴ * Y * ((1 : Matrix q q ℂ) - Q)
            * ((1 : Matrix q q ℂ) - Q)ᴴ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Yᴴ * Y * (((1 : Matrix q q ℂ) - Q)
            * ((1 : Matrix q q ℂ) - Q))) := by
          rw [hQ'H]
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Yᴴ * Y * ((1 : Matrix q q ℂ) - Q)) := by rw [hQ'2]
  rw [h1, h2, ← Complex.add_re, ← Matrix.trace_add, ← Matrix.mul_add,
    add_sub_cancel, Matrix.mul_one]

/-! #### The nearest-PSD alternative (HX.3, HX.6, HX.7) -/

/-- The spectral positive part of the Hermitian part. -/
noncomputable def hermPos (K : Matrix q q ℂ) : Matrix q q ℂ :=
  spectralFunction (hermPart_isHermitian K) fun x => max x 0

/-- The spectral negative part of the Hermitian part. -/
noncomputable def hermNeg (K : Matrix q q ℂ) : Matrix q q ℂ :=
  spectralFunction (hermPart_isHermitian K) fun x => max (-x) 0

/-- **(HX.3)**: the reflected hopping residual `Δ_hop^×`. -/
noncomputable def hopResidual (K : Matrix q q ℂ) : ℝ :=
  hsNormSq (antiPart K) + hsNormSq (hermNeg K)

/-- The spectral Jordan split of the Hermitian part. -/
theorem hermPos_sub_hermNeg (K : Matrix q q ℂ) :
    hermPos K - hermNeg K = hermPart K := by
  unfold hermPos hermNeg
  rw [← spectralFunction_sub]
  calc spectralFunction (hermPart_isHermitian K) (fun x => max x 0 - max (-x) 0)
      = spectralFunction (hermPart_isHermitian K) id :=
        spectralFunction_congr _ fun i => max_zero_sub_max_neg_zero_eq_self _
    _ = hermPart K := spectralFunction_id _

/-- The positive part is PSD. -/
theorem hermPos_posSemidef (K : Matrix q q ℂ) : (hermPos K).PosSemidef :=
  spectralFunction_posSemidef _ _ fun _ => le_max_right _ _

/-- The negative part is PSD. -/
theorem hermNeg_posSemidef (K : Matrix q q ℂ) : (hermNeg K).PosSemidef :=
  spectralFunction_posSemidef _ _ fun _ => le_max_right _ _

/-- The Jordan parts are orthogonal. -/
theorem hermPos_mul_hermNeg (K : Matrix q q ℂ) : hermPos K * hermNeg K = 0 := by
  unfold hermPos hermNeg
  rw [spectralFunction_mul]
  have h : spectralFunction (hermPart_isHermitian K)
        (fun x => max x 0 * max (-x) 0)
      = spectralFunction (hermPart_isHermitian K) fun _ => 0 := by
    refine spectralFunction_congr _ fun i => ?_
    rcases le_or_gt 0 ((hermPart_isHermitian K).eigenvalues i) with h | h
    · rw [max_eq_right (by linarith : -(hermPart_isHermitian K).eigenvalues i ≤ 0),
        mul_zero]
    · rw [max_eq_right h.le, zero_mul]
  rw [h, spectralFunction_const, Complex.ofReal_zero, zero_smul]

omit [DecidableEq q] in
/-- The Hermitian defect against a Hermitian competitor. -/
theorem hs_split_herm_defect (K : Matrix q q ℂ) {H : Matrix q q ℂ}
    (hH : H.IsHermitian) :
    hsNormSq (K - H) = hsNormSq (antiPart K) + hsNormSq (hermPart K - H) := by
  have hdec : K - H = antiPart K + (hermPart K - H) := by
    calc K - H = hermPart K + antiPart K - H := by rw [hermPart_add_antiPart]
      _ = antiPart K + (hermPart K - H) := by abel
  have hY : (hermPart K - H)ᴴ = hermPart K - H := by
    rw [Matrix.conjTranspose_sub, (hermPart_isHermitian K).eq, hH.eq]
  rw [hdec, hsNormSq_add,
    re_trace_anti_herm _ _ (antiPart_anti K) hY, mul_zero, add_zero]

/-- **(HX.6)**: the nearest Hermitian-PSD matrix in Hilbert–Schmidt norm
is `(K_h)₊`, and the attained squared distance is `Δ_hop^×(K)`. -/
theorem nearest_hopping (K : Matrix q q ℂ) :
    (∀ H : Matrix q q ℂ, H.PosSemidef → hopResidual K ≤ hsNormSq (K - H)) ∧
      (hermPos K).PosSemidef ∧ hsNormSq (K - hermPos K) = hopResidual K := by
  obtain ⟨hlow, hattain⟩ := nearest_posSemidef (hermPart K) (hermPos K)
    (hermNeg K) (hermPos_sub_hermNeg K).symm (hermPos_posSemidef K)
    (hermNeg_posSemidef K) (hermPos_mul_hermNeg K)
  refine ⟨fun H hH => ?_, hermPos_posSemidef K, ?_⟩
  · rw [hs_split_herm_defect K hH.1]
    have := hlow H hH
    unfold hopResidual
    linarith
  · rw [hs_split_herm_defect K (hermPos_posSemidef K).1, hattain]
    rfl

/-- **(HX.7)**: vanishing hopping residual, Hermitian positivity, and
one-sided factorization are equivalent. -/
theorem hopping_alternative (K : Matrix q q ℂ) :
    (hopResidual K = 0 ↔ K.PosSemidef)
      ∧ (K.PosSemidef ↔ ∃ R : Matrix q q ℂ, K = Rᴴ * R) := by
  constructor
  · constructor
    · intro h
      have hnn1 := hsNormSq_nonneg (antiPart K)
      have hnn2 := hsNormSq_nonneg (hermNeg K)
      have ha : antiPart K = 0 := (hsNormSq_eq_zero_iff _).mp (by
        unfold hopResidual at h
        linarith)
      have hng : hermNeg K = 0 := (hsNormSq_eq_zero_iff _).mp (by
        unfold hopResidual at h
        linarith)
      have hKh : K = hermPos K := by
        conv_lhs => rw [← hermPart_add_antiPart K]
        rw [ha, add_zero, ← hermPos_sub_hermNeg K, hng, sub_zero]
      rw [hKh]
      exact hermPos_posSemidef K
    · intro hK
      have hherm : hermPart K = K := by
        unfold hermPart
        rw [hK.1.eq, ← two_smul ℂ K, smul_smul,
          inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
      have ha : antiPart K = 0 := by
        unfold antiPart
        rw [hK.1.eq, sub_self, smul_zero]
      have heig : ∀ i, 0 ≤ (hermPart_isHermitian K).eigenvalues i := by
        intro i
        have hpsd : (hermPart K).PosSemidef := by rw [hherm]; exact hK
        exact hpsd.eigenvalues_nonneg i
      have hng : hermNeg K = 0 := by
        unfold hermNeg
        have h0 : spectralFunction (hermPart_isHermitian K) (fun x => max (-x) 0)
            = spectralFunction (hermPart_isHermitian K) fun _ => 0 :=
          spectralFunction_congr _ fun i =>
            max_eq_right (by linarith [heig i])
        rw [h0, spectralFunction_const, Complex.ofReal_zero, zero_smul]
      unfold hopResidual
      rw [ha, hng, (hsNormSq_eq_zero_iff _).mpr rfl, add_zero]
  · constructor
    · intro hK
      refine ⟨psdSqrt hK.1, ?_⟩
      rw [(psdSqrt_posSemidef hK.1).1.eq, psdSqrt_mul_self hK]
    · rintro ⟨R, rfl⟩
      exact posSemidef_conjTranspose_mul_self R

/-! #### Rank-minimal one-sided factorization -/

/-- **Rank minimality**: `K` has a one-sided factorization with exactly
`rank K` sources, and none with fewer. -/
theorem rank_minimal_factorization {K : Matrix q q ℂ} (hK : K.PosSemidef) :
    (∃ R : Matrix (Fin K.rank) q ℂ, K = Rᴴ * R) ∧
      ∀ (r : ℕ) (R : Matrix (Fin r) q ℂ), K = Rᴴ * R → K.rank ≤ r := by
  constructor
  · classical
    have hcard : Fintype.card {i // hK.1.eigenvalues i ≠ 0} = K.rank :=
      hK.1.rank_eq_card_non_zero_eigs.symm
    let eqv : {i // hK.1.eigenvalues i ≠ 0} ≃ Fin K.rank :=
      Fintype.equivFinOfCardEq hcard
    refine ⟨Matrix.of fun a x =>
      ((Real.sqrt (hK.1.eigenvalues (eqv.symm a).1) : ℝ) : ℂ)
        * (starRingEnd ℂ)
            ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x (eqv.symm a).1), ?_⟩
    ext x y
    have hKxy := CSpec.cSpec_apply hK.1 (fun l => (l : ℂ)) x y
    rw [CSpec.cSpec_id] at hKxy
    have hterm : ∀ i : q,
        ((hK.1.eigenvalues i : ℝ) : ℂ)
            * ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x i
              * (starRingEnd ℂ) ((hK.1.eigenvectorUnitary : Matrix q q ℂ) y i))
          = (starRingEnd ℂ)
              (((Real.sqrt (hK.1.eigenvalues i) : ℝ) : ℂ)
                * (starRingEnd ℂ) ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x i))
            * (((Real.sqrt (hK.1.eigenvalues i) : ℝ) : ℂ)
                * (starRingEnd ℂ)
                    ((hK.1.eigenvectorUnitary : Matrix q q ℂ) y i)) := by
      intro i
      rw [map_mul, Complex.conj_conj, Complex.conj_ofReal]
      have hsq : ((Real.sqrt (hK.1.eigenvalues i) : ℝ) : ℂ)
          * ((Real.sqrt (hK.1.eigenvalues i) : ℝ) : ℂ)
          = ((hK.1.eigenvalues i : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hK.eigenvalues_nonneg i)]
      calc ((hK.1.eigenvalues i : ℝ) : ℂ)
            * ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x i
              * (starRingEnd ℂ) ((hK.1.eigenvectorUnitary : Matrix q q ℂ) y i))
          = (((Real.sqrt (hK.1.eigenvalues i) : ℝ) : ℂ)
              * ((Real.sqrt (hK.1.eigenvalues i) : ℝ) : ℂ))
            * ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x i
              * (starRingEnd ℂ) ((hK.1.eigenvectorUnitary : Matrix q q ℂ) y i)) := by
            rw [hsq]
        _ = _ := by ring
    rw [hKxy, Matrix.mul_apply]
    have hcomp : ∀ a : Fin K.rank,
        (Matrix.of fun a x =>
            ((Real.sqrt (hK.1.eigenvalues (eqv.symm a).1) : ℝ) : ℂ)
              * (starRingEnd ℂ)
                  ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x (eqv.symm a).1))ᴴ
            x a
          * (Matrix.of fun a x =>
              ((Real.sqrt (hK.1.eigenvalues (eqv.symm a).1) : ℝ) : ℂ)
                * (starRingEnd ℂ)
                    ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x (eqv.symm a).1))
              a y
          = ((hK.1.eigenvalues (eqv.symm a).1 : ℝ) : ℂ)
            * ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x (eqv.symm a).1
              * (starRingEnd ℂ)
                  ((hK.1.eigenvectorUnitary : Matrix q q ℂ) y (eqv.symm a).1)) := by
      intro a
      rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply]
      exact (hterm _).symm
    rw [Finset.sum_congr rfl fun a _ => hcomp a]
    rw [Equiv.sum_comp eqv.symm fun i : {i // hK.1.eigenvalues i ≠ 0} =>
      ((hK.1.eigenvalues i.1 : ℝ) : ℂ)
        * ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x i.1
          * (starRingEnd ℂ) ((hK.1.eigenvectorUnitary : Matrix q q ℂ) y i.1))]
    rw [← Finset.sum_subtype
      (Finset.univ.filter fun i : q => hK.1.eigenvalues i ≠ 0)
      (fun i => ⟨fun hi => (Finset.mem_filter.mp hi).2,
        fun hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)
      (fun i => ((hK.1.eigenvalues i : ℝ) : ℂ)
        * ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x i
          * (starRingEnd ℂ) ((hK.1.eigenvectorUnitary : Matrix q q ℂ) y i)))]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : q => hK.1.eigenvalues i ≠ 0)
      (fun i => ((hK.1.eigenvalues i : ℝ) : ℂ)
        * ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x i
          * (starRingEnd ℂ) ((hK.1.eigenvectorUnitary : Matrix q q ℂ) y i)))]
    have hzero : ∑ i ∈ Finset.univ.filter fun i : q => ¬ hK.1.eigenvalues i ≠ 0,
        ((hK.1.eigenvalues i : ℝ) : ℂ)
          * ((hK.1.eigenvectorUnitary : Matrix q q ℂ) x i
            * (starRingEnd ℂ) ((hK.1.eigenvectorUnitary : Matrix q q ℂ) y i))
        = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have h0 : hK.1.eigenvalues i = 0 := not_not.mp (Finset.mem_filter.mp hi).2
      rw [h0, Complex.ofReal_zero, zero_mul]
    rw [hzero, add_zero]
  · intro r R hR
    have h1 : K.rank = R.rank := by
      rw [hR, Matrix.rank_conjTranspose_mul_self]
    calc K.rank = R.rank := h1
      _ ≤ Fintype.card (Fin r) := R.rank_le_card_height
      _ = r := Fintype.card_fin r

/-- A full-rank PSD matrix has full support projection. -/
theorem supportProj_eq_one_of_rank {p : Type*} [Fintype p] [DecidableEq p]
    {G : Matrix p p ℂ} (hG : G.PosSemidef) (hr : G.rank = Fintype.card p) :
    supportProj hG.1 = 1 := by
  classical
  have hcard : Fintype.card {i // hG.1.eigenvalues i ≠ 0} = Fintype.card p := by
    rw [← hG.1.rank_eq_card_non_zero_eigs, hr]
  have hall : ∀ i, hG.1.eigenvalues i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ := hcon
    have := Fintype.card_subtype_lt (p := fun i => hG.1.eigenvalues i ≠ 0)
      (x := i) (by rw [not_not]; exact hi)
    rw [hcard] at this
    exact absurd this (lt_irrefl _)
  have hpos : ∀ i, 0 < hG.1.eigenvalues i := fun i =>
    lt_of_le_of_ne (hG.eigenvalues_nonneg i) (Ne.symm (hall i))
  unfold supportProj
  have h1 : spectralFunction hG.1 (fun l => if 0 < l then 1 else 0)
      = spectralFunction hG.1 fun _ => 1 :=
    spectralFunction_congr hG.1 fun i => by rw [ite_eq_left (hpos i)]
  rw [h1, spectralFunction_const, Complex.ofReal_one, one_smul]

/-- **All rank-minimal factors differ by a unitary on the source range**:
two factorizations with exactly `rank K` sources are related by a unitary
change of source frame. -/
theorem rank_minimal_factor_unitary {K : Matrix q q ℂ} {r : ℕ}
    (R₁ R₂ : Matrix (Fin r) q ℂ) (hr : K.rank = r)
    (h1 : K = R₁ᴴ * R₁) (h2 : K = R₂ᴴ * R₂) :
    ∃ V : Matrix (Fin r) (Fin r) ℂ,
      Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧ R₂ = V * R₁ := by
  classical
  have hG : (R₁ * R₁ᴴ).PosSemidef := by
    have h := posSemidef_conjTranspose_mul_self R₁ᴴ
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hR1K : K.rank = R₁.rank :=
    (congrArg (fun M : Matrix q q ℂ => M.rank) h1).trans
      (Matrix.rank_conjTranspose_mul_self R₁)
  have hrank : (R₁ * R₁ᴴ).rank = Fintype.card (Fin r) := by
    rw [Matrix.rank_self_mul_conjTranspose, Fintype.card_fin, ← hR1K, hr]
  have hS1 : supportProj hG.1 = 1 := supportProj_eq_one_of_rank hG hrank
  have hGp : R₁ * R₁ᴴ * pinv hG.1 = 1 := by
    rw [mul_pinv_eq_supportProj, hS1]
  have hpG : pinv hG.1 * (R₁ * R₁ᴴ) = 1 := by
    rw [← supportProj_eq_pinv_mul, hS1]
  have hPH : (R₁ᴴ * pinv hG.1 * R₁)ᴴ = R₁ᴴ * pinv hG.1 * R₁ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, (pinv_isHermitian hG.1).eq,
      Matrix.mul_assoc]
  have hPK : R₁ᴴ * pinv hG.1 * R₁ * (R₁ᴴ * R₁) = R₁ᴴ * R₁ := by
    calc R₁ᴴ * pinv hG.1 * R₁ * (R₁ᴴ * R₁)
        = R₁ᴴ * (pinv hG.1 * (R₁ * R₁ᴴ)) * R₁ := by simp only [Matrix.mul_assoc]
      _ = R₁ᴴ * R₁ := by rw [hpG, Matrix.mul_one]
  have hR2P : R₂ * (R₁ᴴ * pinv hG.1 * R₁) = R₂ := by
    have hzero : ((1 : Matrix q q ℂ) - R₁ᴴ * pinv hG.1 * R₁) * R₂ᴴ
        * (((1 : Matrix q q ℂ) - R₁ᴴ * pinv hG.1 * R₁) * R₂ᴴ)ᴴ = 0 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, hPH, Matrix.conjTranspose_conjTranspose]
      calc ((1 : Matrix q q ℂ) - R₁ᴴ * pinv hG.1 * R₁) * R₂ᴴ
            * (R₂ * ((1 : Matrix q q ℂ) - R₁ᴴ * pinv hG.1 * R₁))
          = ((1 : Matrix q q ℂ) - R₁ᴴ * pinv hG.1 * R₁) * (R₂ᴴ * R₂)
            * ((1 : Matrix q q ℂ) - R₁ᴴ * pinv hG.1 * R₁) := by
            simp only [Matrix.mul_assoc]
        _ = 0 := by
            rw [← h2, h1, Matrix.sub_mul, Matrix.one_mul, hPK, sub_self,
              Matrix.zero_mul]
    have hY := Matrix.self_mul_conjTranspose_eq_zero.mp hzero
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hY
    have hYc := congrArg Matrix.conjTranspose hY
    rw [Matrix.conjTranspose_mul, hPH, Matrix.conjTranspose_conjTranspose] at hYc
    exact hYc.symm
  refine ⟨R₂ * R₁ᴴ * pinv hG.1, ?_, ?_, ?_⟩
  · -- V^*V = 1
    have hVH : (R₂ * R₁ᴴ * pinv hG.1)ᴴ = pinv hG.1 * (R₁ * R₂ᴴ) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, (pinv_isHermitian hG.1).eq]
    rw [hVH]
    calc pinv hG.1 * (R₁ * R₂ᴴ) * (R₂ * R₁ᴴ * pinv hG.1)
        = pinv hG.1 * (R₁ * (R₂ᴴ * R₂) * R₁ᴴ) * pinv hG.1 := by
          simp only [Matrix.mul_assoc]
      _ = pinv hG.1 * (R₁ * (R₁ᴴ * R₁) * R₁ᴴ) * pinv hG.1 := by rw [← h2, ← h1]
      _ = (pinv hG.1 * (R₁ * R₁ᴴ)) * ((R₁ * R₁ᴴ) * pinv hG.1) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hpG, hGp, Matrix.one_mul]
  · -- VV^* = 1 from V^*V = 1 for a square matrix
    have hVH : (R₂ * R₁ᴴ * pinv hG.1)ᴴ = pinv hG.1 * (R₁ * R₂ᴴ) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, (pinv_isHermitian hG.1).eq]
    have hVV : (R₂ * R₁ᴴ * pinv hG.1)ᴴ * (R₂ * R₁ᴴ * pinv hG.1) = 1 := by
      rw [hVH]
      calc pinv hG.1 * (R₁ * R₂ᴴ) * (R₂ * R₁ᴴ * pinv hG.1)
          = pinv hG.1 * (R₁ * (R₂ᴴ * R₂) * R₁ᴴ) * pinv hG.1 := by
            simp only [Matrix.mul_assoc]
        _ = pinv hG.1 * (R₁ * (R₁ᴴ * R₁) * R₁ᴴ) * pinv hG.1 := by rw [← h2, ← h1]
        _ = (pinv hG.1 * (R₁ * R₁ᴴ)) * ((R₁ * R₁ᴴ) * pinv hG.1) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hpG, hGp, Matrix.one_mul]
    exact mul_eq_one_comm.mp hVV
  · refine Eq.symm ?_
    calc R₂ * R₁ᴴ * pinv hG.1 * R₁
        = R₂ * (R₁ᴴ * pinv hG.1 * R₁) := by simp only [Matrix.mul_assoc]
      _ = R₂ := hR2P

/-! #### Relation descent (HX.4) and the minimum-norm extension (HX.5) -/

section Descent

variable {hp fl : Type*} [Fintype hp] [Fintype fl] [DecidableEq hp] [DecidableEq fl]

/-- **(HX.2)**: the reflected relation residual
`Δ_rel^×(K_F, W₁) = ‖(I-P_W)K_F‖²_HS + ‖K_F(I-P_W)‖²_HS`, with
`P_W = colProj W₁ᴴ` the orthogonal projection onto `(Ker W₁)^⊥`. -/
noncomputable def relResidual (W1 : Matrix hp fl ℂ) (KF : Matrix fl fl ℂ) : ℝ :=
  hsNormSq (((1 : Matrix fl fl ℂ) - colProj W1ᴴ) * KF)
    + hsNormSq (KF * ((1 : Matrix fl fl ℂ) - colProj W1ᴴ))

/-- **(HX.4)**: the raw crossing form descends to the represented
one-particle carrier iff `Δ_rel^× = 0` iff `K_F = P_W K_F P_W`. -/
theorem relation_descent (W1 : Matrix hp fl ℂ) (KF : Matrix fl fl ℂ) :
    relResidual W1 KF = 0 ↔ KF = colProj W1ᴴ * KF * colProj W1ᴴ := by
  have hnn1 := hsNormSq_nonneg (((1 : Matrix fl fl ℂ) - colProj W1ᴴ) * KF)
  have hnn2 := hsNormSq_nonneg (KF * ((1 : Matrix fl fl ℂ) - colProj W1ᴴ))
  constructor
  · intro h
    have h1 : ((1 : Matrix fl fl ℂ) - colProj W1ᴴ) * KF = 0 :=
      (hsNormSq_eq_zero_iff _).mp (by unfold relResidual at h; linarith)
    have h2 : KF * ((1 : Matrix fl fl ℂ) - colProj W1ᴴ) = 0 :=
      (hsNormSq_eq_zero_iff _).mp (by unfold relResidual at h; linarith)
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
    calc KF = KF * colProj W1ᴴ := h2
      _ = colProj W1ᴴ * KF * colProj W1ᴴ := by
          conv_lhs => rw [h1]
  · intro h
    have h1 : ((1 : Matrix fl fl ℂ) - colProj W1ᴴ) * KF = 0 := by
      rw [h, Matrix.sub_mul, Matrix.one_mul]
      have hcollapse : colProj W1ᴴ * (colProj W1ᴴ * KF * colProj W1ᴴ)
          = colProj W1ᴴ * KF * colProj W1ᴴ := by
        calc colProj W1ᴴ * (colProj W1ᴴ * KF * colProj W1ᴴ)
            = colProj W1ᴴ * colProj W1ᴴ * KF * colProj W1ᴴ := by
              simp only [Matrix.mul_assoc]
          _ = colProj W1ᴴ * KF * colProj W1ᴴ := by rw [colProj_idem]
      rw [hcollapse, sub_self]
    have h2 : KF * ((1 : Matrix fl fl ℂ) - colProj W1ᴴ) = 0 := by
      rw [h, Matrix.mul_sub, Matrix.mul_one]
      have hcollapse : colProj W1ᴴ * KF * colProj W1ᴴ * colProj W1ᴴ
          = colProj W1ᴴ * KF * colProj W1ᴴ := by
        rw [Matrix.mul_assoc, colProj_idem]
      rw [hcollapse, sub_self]
    unfold relResidual
    rw [h1, h2, (hsNormSq_eq_zero_iff (0 : Matrix fl fl ℂ)).mpr rfl, add_zero]

/-- The kernel-orthogonal projection is the support projection of the
one-letter Gram. -/
theorem colProj_conjTranspose_eq_supportProj (W1 : Matrix hp fl ℂ) :
    colProj W1ᴴ = supportProj (posSemidef_conjTranspose_mul_self W1).1 := by
  have hSW : supportProj (posSemidef_conjTranspose_mul_self W1).1 * W1ᴴ = W1ᴴ :=
    supportProj_gram_mul W1
  have hPW : colProj W1ᴴ * W1ᴴ = W1ᴴ := colProj_mul_self W1ᴴ
  have hSrep : supportProj (posSemidef_conjTranspose_mul_self W1).1
      = W1ᴴ * (W1 * pinv (posSemidef_conjTranspose_mul_self W1).1) := by
    rw [← Matrix.mul_assoc, mul_pinv_eq_supportProj]
  have hPrep : colProj W1ᴴ
      = W1ᴴ * (pinv (posSemidef_conjTranspose_mul_self W1ᴴ).1 * W1ᴴᴴ) := by
    unfold colProj
    rw [Matrix.mul_assoc]
  have hPS : colProj W1ᴴ * supportProj (posSemidef_conjTranspose_mul_self W1).1
      = supportProj (posSemidef_conjTranspose_mul_self W1).1 := by
    rw [hSrep, ← Matrix.mul_assoc, hPW]
  have hSP : supportProj (posSemidef_conjTranspose_mul_self W1).1 * colProj W1ᴴ
      = colProj W1ᴴ := by
    rw [hPrep, ← Matrix.mul_assoc, hSW]
  have hct := congrArg Matrix.conjTranspose hSP
  rw [Matrix.conjTranspose_mul, (colProj_isHermitian W1ᴴ).eq,
    (supportProj_posSemidef (posSemidef_conjTranspose_mul_self W1).1).1.eq] at hct
  rw [← hPS, hct]

/-- **(HX.5)**: the Moore–Penrose represented extension
`K× = (W₁^†)^*K_F W₁^†` with `W₁^† = (W₁ᴴW₁)^†W₁ᴴ`. -/
noncomputable def crossExt (W1 : Matrix hp fl ℂ) (KF : Matrix fl fl ℂ) :
    Matrix hp hp ℂ :=
  W1 * pinv (posSemidef_conjTranspose_mul_self W1).1 * KF
    * pinv (posSemidef_conjTranspose_mul_self W1).1 * W1ᴴ

/-- **(HX.5)**: on the descent branch, the Moore–Penrose extension
compresses back to `K_F`, and it is the unique represented extension of
minimum Hilbert–Schmidt source norm. -/
theorem minimum_norm_extension (W1 : Matrix hp fl ℂ) (KF : Matrix fl fl ℂ)
    (hdesc : KF = colProj W1ᴴ * KF * colProj W1ᴴ) :
    W1ᴴ * crossExt W1 KF * W1 = KF ∧
      ∀ K' : Matrix hp hp ℂ, W1ᴴ * K' * W1 = KF →
        hsNormSq (crossExt W1 KF) ≤ hsNormSq K'
          ∧ (hsNormSq K' = hsNormSq (crossExt W1 KF) → K' = crossExt W1 KF) := by
  have hGP : W1ᴴ * W1 * pinv (posSemidef_conjTranspose_mul_self W1).1
      = colProj W1ᴴ := by
    rw [mul_pinv_eq_supportProj, colProj_conjTranspose_eq_supportProj]
  have hPG : pinv (posSemidef_conjTranspose_mul_self W1).1 * (W1ᴴ * W1)
      = colProj W1ᴴ := by
    rw [← supportProj_eq_pinv_mul, colProj_conjTranspose_eq_supportProj]
  have hcomp : W1ᴴ * crossExt W1 KF * W1 = KF := by
    unfold crossExt
    calc W1ᴴ * (W1 * pinv (posSemidef_conjTranspose_mul_self W1).1 * KF
          * pinv (posSemidef_conjTranspose_mul_self W1).1 * W1ᴴ) * W1
        = (W1ᴴ * W1 * pinv (posSemidef_conjTranspose_mul_self W1).1) * KF
          * (pinv (posSemidef_conjTranspose_mul_self W1).1 * (W1ᴴ * W1)) := by
          simp only [Matrix.mul_assoc]
      _ = colProj W1ᴴ * KF * colProj W1ᴴ := by rw [hGP, hPG]
      _ = KF := hdesc.symm
  refine ⟨hcomp, fun K' hK' => ?_⟩
  have hQH := colProj_isHermitian W1
  have hQ2 := colProj_idem W1
  -- every represented extension has the same range compression
  have hcompress : colProj W1 * K' * colProj W1 = crossExt W1 KF := by
    unfold colProj crossExt
    calc W1 * pinv (posSemidef_conjTranspose_mul_self W1).1 * W1ᴴ * K'
          * (W1 * pinv (posSemidef_conjTranspose_mul_self W1).1 * W1ᴴ)
        = W1 * pinv (posSemidef_conjTranspose_mul_self W1).1 * (W1ᴴ * K' * W1)
          * pinv (posSemidef_conjTranspose_mul_self W1).1 * W1ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK']
  -- the corner Pythagoras against the represented range
  have hsplit1 := hsNormSq_right_split hQH hQ2 K'
  have hsplit2 := hsNormSq_left_split hQH hQ2 (K' * colProj W1)
  rw [← Matrix.mul_assoc, hcompress] at hsplit2
  have hnn1 := hsNormSq_nonneg (((1 : Matrix hp hp ℂ) - colProj W1)
    * (K' * colProj W1))
  have hnn2 := hsNormSq_nonneg (K' * ((1 : Matrix hp hp ℂ) - colProj W1))
  constructor
  · linarith
  · intro heq
    have hz2 : hsNormSq (K' * ((1 : Matrix hp hp ℂ) - colProj W1)) = 0 := by
      linarith
    have hz1 : hsNormSq (((1 : Matrix hp hp ℂ) - colProj W1)
        * (K' * colProj W1)) = 0 := by
      linarith
    have he2 : K' * ((1 : Matrix hp hp ℂ) - colProj W1) = 0 :=
      (hsNormSq_eq_zero_iff _).mp hz2
    have he1 : ((1 : Matrix hp hp ℂ) - colProj W1) * (K' * colProj W1) = 0 :=
      (hsNormSq_eq_zero_iff _).mp hz1
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at he2
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at he1
    calc K' = K' * colProj W1 := he2
      _ = colProj W1 * (K' * colProj W1) := he1
      _ = colProj W1 * K' * colProj W1 := by rw [Matrix.mul_assoc]
      _ = crossExt W1 KF := hcompress

end Descent

/-! #### The crossing action (HX.8) -/

section CrossingAction

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **(HX.8)**: substituting a one-sided factorization `K = R^*R` into the
crossing form: with the synthesized sources `F_a = Σ_j R_{aj}ξ_j` and their
conjugate-linear reflections `Θ_F(F_a) = Σ_j conj(R_{aj})Θξ_j`, the
crossing action is `ε Σ_a Θ_F(F_a)F_a = ε Σ_{jk}(R^*R)_{jk}Θξ_j ξ_k`.
Instantiated with the rank-minimal factor of `K_×`, the sum has exactly
`rank K_×` reflected one-sided squares. -/
theorem crossing_action {p f : Type*} [Fintype p] [Fintype f] (ε : ℂ)
    (R : Matrix p f ℂ) (ξ Θξ : f → A) :
    ε • ∑ a : p, (∑ j, (starRingEnd ℂ) (R a j) • Θξ j) * (∑ k, R a k • ξ k)
      = ε • ∑ j, ∑ k, (Rᴴ * R) j k • (Θξ j * ξ k) := by
  congr 1
  have hprod : ∀ a : p,
      (∑ j, (starRingEnd ℂ) (R a j) • Θξ j) * (∑ k, R a k • ξ k)
        = ∑ j, ∑ k, ((starRingEnd ℂ) (R a j) * R a k) • (Θξ j * ξ k) := by
    intro a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hprod a,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def]

end CrossingAction

end Crossing

end CrossingSection

end NCG
