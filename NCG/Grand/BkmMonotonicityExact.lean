/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.WeylTwirlExact
import NCG.Grand.TQuadConvexPsdExact

/-!
# The BKM contraction (QS.5)

The capstone of the BKM programme for `cor:accepted-BKM-loss`: the
twirl members are the isometry conjugates `W_p σ W_p^*` with
`W_p = (weyl ⊗ 1)·V`, so the intertwining supplies their support
conditions, `tQuad_convex_psd` averages them, and the Weyl twirl
collapses the mixture to `(1/d)·(1 ⊗ Φσ)`; the scaling and ancilla laws
then give the **BKM monotonicity**

`g_{Φσ}(Φv, Φv) ≤ g_σ(v, v)`

for every Kraus-presented CPTP map with faithful `σ` and `Φσ`.

* `twirlIso`: the twirl isometries;
* `tQuad_kraus_le`: the per-`t` contraction;
* `bkmForm_kraus_le`: **the BKM contraction** (cyclic environment and
  arbitrary nonempty finite Kraus index);
* `bkmLoss_nonneg`: **QS.5**, nonnegativity of the BKM loss.
-/

open Matrix Unitary Finset Kronecker
open scoped ComplexOrder

namespace NCG
namespace Petz

open NCG.QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {d : ℕ} [NeZero d]
variable {σ v : Matrix n n ℂ}

/-! ### The twirl isometries -/

/-- The twirl isometry `W_p = (weyl_p ⊗ 1) · V`. -/
noncomputable def twirlIso (K : ZMod d → Matrix m n ℂ)
    (p : ZMod d × ZMod d) : Matrix (ZMod d × m) n ℂ :=
  (weyl d p.1 p.2 ⊗ₖ (1 : Matrix m m ℂ)) * stineCol K

omit [Fintype n] in
theorem twirlIso_isometry (K : ZMod d → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (p : ZMod d × ZMod d) :
    (twirlIso K p)ᴴ * twirlIso K p = 1 := by
  unfold twirlIso
  rw [Matrix.conjTranspose_mul]
  have hU : (weyl d p.1 p.2 ⊗ₖ (1 : Matrix m m ℂ))ᴴ *
      (weyl d p.1 p.2 ⊗ₖ (1 : Matrix m m ℂ)) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact weylKron_star_mul_self p.1 p.2
  calc (stineCol K)ᴴ * (weyl d p.1 p.2 ⊗ₖ (1 : Matrix m m ℂ))ᴴ *
        ((weyl d p.1 p.2 ⊗ₖ (1 : Matrix m m ℂ)) * stineCol K)
      = (stineCol K)ᴴ *
          ((weyl d p.1 p.2 ⊗ₖ (1 : Matrix m m ℂ))ᴴ *
            (weyl d p.1 p.2 ⊗ₖ (1 : Matrix m m ℂ))) * stineCol K := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hU, Matrix.mul_one, stineCol_isometry K hK]

omit [DecidableEq n] in
theorem twirlIso_conj (K : ZMod d → Matrix m n ℂ)
    (p : ZMod d × ZMod d) (X : Matrix n n ℂ) :
    twirlIso K p * X * (twirlIso K p)ᴴ =
      weylConj p.1 p.2 (stineConj K X) := by
  unfold twirlIso weylConj stineConj
  rw [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
  simp only [Matrix.mul_assoc]

set_option maxHeartbeats 1600000 in -- twirl mixture collapse
set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The twirl mixture collapses to the scaled ancilla output, for every
input matrix. -/
theorem twirl_mixture (K : ZMod d → Matrix m n ℂ) (X : Matrix n n ℂ) :
    ∑ p : ZMod d × ZMod d, ((d : ℝ) ^ 2)⁻¹ •
      (twirlIso K p * X * (twirlIso K p)ᴴ) =
      ((d : ℝ))⁻¹ •
        ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ kraus K X) := by
  have h1 : ∑ p : ZMod d × ZMod d, ((d : ℝ) ^ 2)⁻¹ •
      (twirlIso K p * X * (twirlIso K p)ᴴ) =
      ((d : ℝ) ^ 2)⁻¹ • ∑ s : ZMod d, ∑ t : ZMod d,
        weylConj s t (stineConj K X) := by
    rw [← Finset.smul_sum]
    congr 1
    rw [← Fintype.sum_prod_type
      (f := fun p : ZMod d × ZMod d =>
        weylConj p.1 p.2 (stineConj K X))]
    exact Finset.sum_congr rfl fun p _ => twirlIso_conj K p X
  rw [h1, weyl_twirl, envTrace_stineConj]

/-! ### Two-typed ancilla positivity -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
theorem one_kron_posDef' {p : Type*} [Fintype p] [DecidableEq p]
    {C : Matrix p p ℂ} (hC : C.PosDef) {L : Type*} [Fintype L]
    [DecidableEq L] : ((1 : Matrix L L ℂ) ⊗ₖ C).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨kron_one_isHermitian hC.1, fun x hx => ?_⟩
  have hslice : star x ⬝ᵥ (((1 : Matrix L L ℂ) ⊗ₖ C) *ᵥ x) =
      ∑ i : L, star (fun b => x (i, b)) ⬝ᵥ
        (C *ᵥ fun b => x (i, b)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [if_pos rfl, one_mul]
    · intro k _ hk
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg (fun h => hk h.symm), zero_mul, zero_mul]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  rw [hslice]
  obtain ⟨i0, hi0⟩ : ∃ i0 : L, (fun b => x (i0, b)) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx
    funext q
    have := congrFun (hall q.1) q.2
    simpa using this
  have hpos : (0 : ℂ) < star (fun b => x (i0, b)) ⬝ᵥ
      (C *ᵥ fun b => x (i0, b)) :=
    (Matrix.posDef_iff_dotProduct_mulVec.mp hC).2 hi0
  have hnn : ∀ i ∈ Finset.univ, (0 : ℂ) ≤ star (fun b => x (i, b)) ⬝ᵥ
      (C *ᵥ fun b => x (i, b)) := fun i _ =>
    hC.posSemidef.dotProduct_mulVec_nonneg _
  exact Finset.sum_pos' hnn ⟨i0, Finset.mem_univ i0, hpos⟩

/-! ### Transport helpers -/

omit [Fintype n] [DecidableEq n] in
theorem tQuad_congr {σ₁ σ₂ v₁ v₂ : Matrix n n ℂ} [Fintype n]
    [DecidableEq n] (hσe : σ₁ = σ₂) (hve : v₁ = v₂)
    (h₁ : σ₁.IsHermitian) (h₂ : σ₂.IsHermitian) (t : ℝ) :
    tQuad h₁ v₁ t = tQuad h₂ v₂ t := by
  subst hσe
  subst hve
  rfl

/-! ### The per-t contraction -/

set_option maxHeartbeats 3200000 in -- metric twirl assembly
/-- **The per-t BKM contraction**:
`tQuad(Φσ, Φv, t) ≤ tQuad(σ, v, t)`. -/
theorem tQuad_kraus_le (K : ZMod d → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (hσ : σ.PosDef)
    (hbσ : (kraus K σ).PosDef) (v : Matrix n n ℂ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    tQuad hbσ.1 (kraus K v) t ≤ tQuad hσ.1 v t := by
  have hd0 : ((d : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hdpos : (0 : ℝ) < (d : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  set lam : ZMod d × ZMod d → ℝ := fun _ => ((d : ℝ) ^ 2)⁻¹ with hlam
  have hlam0 : ∀ p, 0 ≤ lam p := fun p => by positivity
  set σs : ZMod d × ZMod d → Matrix (ZMod d × m) (ZMod d × m) ℂ :=
    fun p => twirlIso K p * σ * (twirlIso K p)ᴴ with hσs
  set vs : ZMod d × ZMod d → Matrix (ZMod d × m) (ZMod d × m) ℂ :=
    fun p => twirlIso K p * v * (twirlIso K p)ᴴ with hvs
  have hσj : ∀ p, (σs p).PosSemidef := fun p => by
    simp only [hσs]
    exact hσ.posSemidef.mul_mul_conjTranspose_same _
  -- support conditions from the intertwining
  have hsupp : ∀ p, (affineOp (σs p) t *
      invMat (affineOp_isHermitian (hσj p).1 t)) *ᵥ vecM (vs p) =
      vecM (vs p) := by
    intro p
    have hiso := twirlIso_isometry K hK p
    have hint := affineOp_intertwine hiso hσ.1 t
    have hvec : vecM (vs p) = doubledIso (twirlIso K p) *ᵥ vecM v := by
      simp only [hvs]
      unfold doubledIso
      rw [vecM_kron_mulVec', Matrix.transpose_transpose]
    rw [hvec]
    have hM'h : (affineOp (σs p) t).IsHermitian :=
      affineOp_isHermitian (hσj p).1 t
    have hint' : affineOp (σs p) t * doubledIso (twirlIso K p) =
        doubledIso (twirlIso K p) * affineOp σ t := by
      simp only [hσs]
      exact hint
    exact supp_of_intertwine hM'h (affineOp_posDef hσ ht0 ht1)
      hint' (vecM v)
  -- the faithful mixture
  have hbase : ∑ p, lam p • σs p = ((d : ℝ))⁻¹ •
      ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ kraus K σ) := by
    simp only [hlam, hσs]
    exact twirl_mixture K σ
  have htang : ∑ p, lam p • vs p = ((d : ℝ))⁻¹ •
      ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ kraus K v) := by
    simp only [hlam, hvs]
    exact twirl_mixture K v
  have hσbar : (∑ p, lam p • σs p).PosDef := by
    rw [hbase]
    exact posDef_smul_real_pos (inv_pos.mpr hdpos)
      (one_kron_posDef' hbσ)
  -- the convexity at the twirl family
  have hconv := tQuad_convex_psd hlam0 hσj ht0 ht1 hsupp hσbar
  -- identify the left side
  have hLmix : tQuad hσbar.1 (∑ p, lam p • vs p) t =
      tQuad (real_smul_isHermitian' ((d : ℝ))⁻¹
          (kron_one_isHermitian hbσ.1))
        (((d : ℝ))⁻¹ • ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ
          kraus K v)) t :=
    tQuad_congr hbase htang hσbar.1 _ t
  have hLscale : tQuad (real_smul_isHermitian' ((d : ℝ))⁻¹
        (kron_one_isHermitian hbσ.1))
      (((d : ℝ))⁻¹ • ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ
        kraus K v)) t =
      ((d : ℝ))⁻¹ * tQuad (kron_one_isHermitian hbσ.1)
        ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ kraus K v) t :=
    tQuad_smul (kron_one_isHermitian hbσ.1) (inv_pos.mpr hdpos) _ _ t
  have hLkron : tQuad (kron_one_isHermitian hbσ.1)
      ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ kraus K v) t =
      (Fintype.card (ZMod d) : ℝ) * tQuad hbσ.1 (kraus K v) t :=
    tQuad_kron_one hbσ.1 (kron_one_isHermitian hbσ.1) (kraus K v) t
  -- identify the right side
  have hR : ∀ p, tQuad (hσj p).1 (vs p) t = tQuad hσ.1 v t := by
    intro p
    have hiso := twirlIso_isometry K hK p
    have h := tQuad_isometry hiso hσ.1 v t
      (conj_isHermitian' (V := twirlIso K p) hσ.1)
    calc tQuad (hσj p).1 (vs p) t
        = tQuad (conj_isHermitian' (V := twirlIso K p) hσ.1)
            (twirlIso K p * v * (twirlIso K p)ᴴ) t :=
          tQuad_congr rfl rfl _ _ t
      _ = tQuad hσ.1 v t := h
  -- assemble
  rw [hLmix, hLscale, hLkron] at hconv
  have hRsum : ∑ p : ZMod d × ZMod d, lam p * tQuad (hσj p).1 (vs p) t =
      tQuad hσ.1 v t := by
    rw [Finset.sum_congr rfl fun p _ => by rw [hR p]]
    simp only [hlam]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
      nsmul_eq_mul]
    field_simp
    push_cast
    ring
  rw [hRsum] at hconv
  have hcollapse : ((d : ℝ))⁻¹ * ((Fintype.card (ZMod d) : ℝ) *
      tQuad hbσ.1 (kraus K v) t) = tQuad hbσ.1 (kraus K v) t := by
    rw [ZMod.card]
    field_simp
  rw [hcollapse] at hconv
  exact hconv

/-! ### The BKM contraction -/

set_option maxHeartbeats 1600000 in -- integral comparison
/-- **The BKM contraction, cyclic environment**:
`g_{Φσ}(Φv, Φv) ≤ g_σ(v, v)`. -/
theorem bkmForm_kraus_le_zmod (K : ZMod d → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (hσ : σ.PosDef)
    (hbσ : (kraus K σ).PosDef) (v : Matrix n n ℂ) :
    bkmForm hbσ.1 (kraus K v) ≤ bkmForm hσ.1 v := by
  rw [bkmForm_eq_integral hbσ, bkmForm_eq_integral hσ]
  refine intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (sum_integrand_integrable hbσ _) (sum_integrand_integrable hσ _) ?_
  intro t ht
  rw [← tQuad_eq_sum hbσ (kraus K v) ht.1 ht.2,
    ← tQuad_eq_sum hσ v ht.1 ht.2]
  exact tQuad_kraus_le K hK hσ hbσ v ht.1 ht.2

omit [Fintype n] [DecidableEq n] in
theorem bkmForm_congr {σ₁ σ₂ v₁ v₂ : Matrix n n ℂ} [Fintype n]
    [DecidableEq n] (hσe : σ₁ = σ₂) (hve : v₁ = v₂)
    (h₁ : σ₁.IsHermitian) (h₂ : σ₂.IsHermitian) :
    bkmForm h₁ v₁ = bkmForm h₂ v₂ := by
  subst hσe
  subst hve
  rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The BKM contraction** for an arbitrary nonempty finite Kraus
index: `g_{Φσ}(Φv, Φv) ≤ g_σ(v, v)`. -/
theorem bkmForm_kraus_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    [Nonempty κ] (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (hσ : σ.PosDef)
    (hbσ : (kraus K σ).PosDef) (v : Matrix n n ℂ) :
    bkmForm hbσ.1 (kraus K v) ≤ bkmForm hσ.1 v := by
  haveI : NeZero (Fintype.card κ) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨e⟩ : Nonempty (ZMod (Fintype.card κ) ≃ κ) :=
    ⟨Fintype.equivOfCardEq (by rw [ZMod.card])⟩
  set K' : ZMod (Fintype.card κ) → Matrix m n ℂ := fun i => K (e i)
    with hK'def
  have hK' : ∑ i, (K' i)ᴴ * K' i = 1 := by
    rw [← hK]
    exact Fintype.sum_equiv e _ _ fun i => rfl
  have hkraus : ∀ τ : Matrix n n ℂ, kraus K' τ = kraus K τ := by
    intro τ
    unfold kraus
    exact Fintype.sum_equiv e _ _ fun i => rfl
  have hbσ' : (kraus K' σ).PosDef := by
    rw [hkraus]
    exact hbσ
  have h := bkmForm_kraus_le_zmod K' hK' hσ hbσ' v
  have hcongr : bkmForm hbσ'.1 (kraus K' v) =
      bkmForm hbσ.1 (kraus K v) :=
    bkmForm_congr (hkraus σ) (hkraus v) hbσ'.1 hbσ.1
  rw [hcongr] at h
  exact h

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **QS.5, the BKM loss is nonnegative**:
`g_σ(v,v) − g_{Φσ}(Φv,Φv) ≥ 0`. -/
theorem bkmLoss_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ]
    [Nonempty κ] (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (hσ : σ.PosDef)
    (hbσ : (kraus K σ).PosDef) (v : Matrix n n ℂ) :
    0 ≤ bkmForm hσ.1 v - bkmForm hbσ.1 (kraus K v) := by
  have h := bkmForm_kraus_le K hK hσ hbσ v
  linarith

end Petz
end NCG
