/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.WeylTwirlExact
import NCG.Grand.RelEntropyPerturbExact

/-!
# The finite data-processing inequality

The capstone of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: the joint-convexity interface of the
Weyl twirl chain is **discharged** by the proved singular joint convexity
`relEntropy_convex_psd`, closing the chain

isometry invariance (D1) → ancilla transport (D2) → Weyl twirl (D3) →
Lieb/regularised joint convexity (D4) → Stinespring reduction (D5),

so that the data-processing inequality `D(Φρ‖Φσ) ≤ D(ρ‖σ)` holds
unconditionally for finite Kraus-presented CPTP maps with `σ` and `Φσ`
faithful.

* `relEntropy_weyl_avg_le`: joint convexity at the Weyl family — the
  discharge of the `hjc` interface;
* `relEntropy_envTrace_le`: unconditional monotonicity under the
  environment partial trace;
* `relEntropy_kraus_le`: **the data-processing inequality** (QS.2's
  premise), for an arbitrary nonempty finite Kraus index.
-/

open Matrix Unitary Finset Kronecker
open scoped ComplexOrder

namespace NCG
namespace Petz

open NCG.QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {d : ℕ} [NeZero d]

/-! ### Hermitian and positivity bookkeeping -/

omit [Fintype m] [DecidableEq m] in
theorem real_smul_isHermitian {A : Matrix m m ℂ} (c : ℝ)
    (hA : A.IsHermitian) : (c • A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, star_trivial, hA.eq]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem posDef_mulVec_eq_zero {σ : Matrix n n ℂ} (hσ : σ.PosDef)
    {w : n → ℂ} (hw : σ *ᵥ w = 0) : w = 0 := by
  by_contra hne
  have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hσ).2 hne
  rw [hw, dotProduct_zero] at h
  exact lt_irrefl _ h

/-! ### The Weyl conjugates as a convexity family -/

theorem weylConj_posSemidef (s t : ZMod d)
    {X : Matrix (ZMod d × m) (ZMod d × m) ℂ} (hX : X.PosSemidef) :
    (weylConj s t X).PosSemidef := by
  unfold weylConj
  rw [Matrix.star_eq_conjTranspose]
  exact hX.mul_mul_conjTranspose_same _

theorem weylConj_ker (s t : ZMod d)
    {X Y : Matrix (ZMod d × m) (ZMod d × m) ℂ}
    (hker : ∀ v, Y *ᵥ v = 0 → X *ᵥ v = 0) :
    ∀ v, weylConj s t Y *ᵥ v = 0 → weylConj s t X *ᵥ v = 0 := by
  intro v hv
  set W : Matrix (ZMod d × m) (ZMod d × m) ℂ :=
    weyl d s t ⊗ₖ (1 : Matrix m m ℂ) with hW
  have hWW : star W * W = 1 := weylKron_star_mul_self s t
  have hYv : Y *ᵥ (star W *ᵥ v) = 0 := by
    have h1 : star W *ᵥ (weylConj s t Y *ᵥ v) =
        (Y * star W) *ᵥ v := by
      unfold weylConj
      rw [Matrix.mulVec_mulVec, ← hW]
      have hcollapse : star W * (W * Y * star W) = Y * star W := by
        calc star W * (W * Y * star W) =
            (star W * W) * (Y * star W) := by
              simp only [Matrix.mul_assoc]
          _ = Y * star W := by rw [hWW, Matrix.one_mul]
      rw [hcollapse]
    rw [hv, Matrix.mulVec_zero] at h1
    rw [Matrix.mulVec_mulVec]
    exact h1.symm
  have hXv := hker _ hYv
  unfold weylConj
  rw [← hW]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hXv,
    Matrix.mulVec_zero]

omit [Fintype m] [DecidableEq m] [NeZero d] in
set_option linter.unusedFintypeInType false in
theorem sum_posSemidef {N : Type*} [Fintype N] {ι : Type*} [Fintype ι]
    {A : ι → Matrix N N ℂ}
    (hA : ∀ p, (A p).PosSemidef) : (∑ p, A p).PosSemidef :=
  Finset.sum_induction _ _ (fun _ _ ha hb => ha.add hb)
    Matrix.PosSemidef.zero fun p _ => hA p

/-! ### The discharge of the joint-convexity interface -/

set_option maxHeartbeats 1600000 in -- convexity family bookkeeping
/-- **Joint convexity at the Weyl family** — the discharge of the `hjc`
interface of `relEntropy_envTrace_le_of_jointConvexity`, from the proved
singular joint convexity. -/
theorem relEntropy_weyl_avg_le
    {X Y : Matrix (ZMod d × m) (ZMod d × m) ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hker : ∀ v, Y *ᵥ v = 0 → X *ᵥ v = 0)
    (havgX : (((d : ℝ) ^ 2)⁻¹ •
      ∑ s : ZMod d, ∑ t : ZMod d, weylConj s t X).IsHermitian)
    (havgY : (((d : ℝ) ^ 2)⁻¹ •
      ∑ s : ZMod d, ∑ t : ZMod d, weylConj s t Y).IsHermitian) :
    relEntropy havgX havgY ≤ ((d : ℝ) ^ 2)⁻¹ *
      ∑ s : ZMod d, ∑ t : ZMod d,
        relEntropy (weylConj_isHermitian s t hX.1)
          (weylConj_isHermitian s t hY.1) := by
  have hd0 : ((d : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  set lam : ZMod d × ZMod d → ℝ := fun _ => ((d : ℝ) ^ 2)⁻¹ with hlamdef
  have hlam : ∀ p, 0 ≤ lam p := fun p => by positivity
  have hsum : ∑ p : ZMod d × ZMod d, lam p = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
      nsmul_eq_mul]
    push_cast
    field_simp
  have hmix : ∀ Z : Matrix (ZMod d × m) (ZMod d × m) ℂ,
      ∑ p : ZMod d × ZMod d, lam p • weylConj p.1 p.2 Z =
        ((d : ℝ) ^ 2)⁻¹ • ∑ s : ZMod d, ∑ t : ZMod d, weylConj s t Z := by
    intro Z
    rw [← Finset.smul_sum]
    congr 1
    exact Fintype.sum_prod_type
      (f := fun p : ZMod d × ZMod d => weylConj p.1 p.2 Z)
  have hρj : ∀ p : ZMod d × ZMod d, (weylConj p.1 p.2 X).PosSemidef :=
    fun p => weylConj_posSemidef p.1 p.2 hX
  have hσj : ∀ p : ZMod d × ZMod d, (weylConj p.1 p.2 Y).PosSemidef :=
    fun p => weylConj_posSemidef p.1 p.2 hY
  have hker' : ∀ p : ZMod d × ZMod d, ∀ v,
      weylConj p.1 p.2 Y *ᵥ v = 0 → weylConj p.1 p.2 X *ᵥ v = 0 :=
    fun p => weylConj_ker p.1 p.2 hker
  have hmixρ : (∑ p : ZMod d × ZMod d,
      lam p • weylConj p.1 p.2 X).PosSemidef :=
    sum_posSemidef fun p => posSemidef_smul_real (hlam p) (hρj p)
  have hmixσ : (∑ p : ZMod d × ZMod d,
      lam p • weylConj p.1 p.2 Y).PosSemidef :=
    sum_posSemidef fun p => posSemidef_smul_real (hlam p) (hσj p)
  have hconv := relEntropy_convex_psd hlam hsum hρj hσj hker' hmixρ hmixσ
  have hLcongr : relEntropy hmixρ.1 hmixσ.1 = relEntropy havgX havgY :=
    relEntropy_congr (hmix X) (hmix Y) hmixρ.1 hmixσ.1 havgX havgY
  rw [hLcongr] at hconv
  refine hconv.trans (le_of_eq ?_)
  simp only [hlamdef]
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_prod_type
    (f := fun p : ZMod d × ZMod d =>
      relEntropy (weylConj_isHermitian p.1 p.2 hX.1)
        (weylConj_isHermitian p.1 p.2 hY.1))

/-! ### Unconditional partial-trace monotonicity -/

set_option maxHeartbeats 1600000 in -- twirl assembly
/-- **Unconditional monotonicity under the environment partial trace**:
for PSD `X`, `Y` with `ker Y ⊆ ker X` and faithful `Tr_env Y`,
`D(Tr_env X‖Tr_env Y) ≤ D(X‖Y)`. -/
theorem relEntropy_envTrace_le
    {X Y : Matrix (ZMod d × m) (ZMod d × m) ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hker : ∀ v, Y *ᵥ v = 0 → X *ᵥ v = 0)
    (hEX : (envTrace X).PosSemidef) (hEY : (envTrace Y).PosDef) :
    relEntropy hEX.1 hEY.1 ≤ relEntropy hX.1 hY.1 := by
  have havgX : (((d : ℝ) ^ 2)⁻¹ •
      ∑ s : ZMod d, ∑ t : ZMod d, weylConj s t X).IsHermitian := by
    rw [weyl_twirl X]
    exact real_smul_isHermitian _ (kron_one_isHermitian hEX.1)
  have havgY : (((d : ℝ) ^ 2)⁻¹ •
      ∑ s : ZMod d, ∑ t : ZMod d, weylConj s t Y).IsHermitian := by
    rw [weyl_twirl Y]
    exact real_smul_isHermitian _ (kron_one_isHermitian hEY.1)
  have h1X : (((d : ℝ))⁻¹ •
      ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ envTrace X)).IsHermitian :=
    real_smul_isHermitian _ (kron_one_isHermitian hEX.1)
  have h1Y : (((d : ℝ))⁻¹ •
      ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ envTrace Y)).IsHermitian :=
    real_smul_isHermitian _ (kron_one_isHermitian hEY.1)
  exact relEntropy_envTrace_le_of_jointConvexity hX.1 hY.1 hEX hEY
    havgX havgY h1X h1Y
    (relEntropy_weyl_avg_le hX hY hker havgX havgY)

/-! ### The data-processing inequality -/

omit [DecidableEq m] in
/-- Kernel inclusion at the Stinespring dilation of a faithful reference. -/
theorem stineConj_ker {κ : Type*} [Fintype κ]
    (K : κ → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    {ρ σ : Matrix n n ℂ} (_hρ : ρ.PosSemidef) (hσ : σ.PosDef) :
    ∀ v, stineConj K σ *ᵥ v = 0 → stineConj K ρ *ᵥ v = 0 := by
  intro v hv
  set V : Matrix (κ × m) n ℂ := stineCol K with hV
  have hVV : Vᴴ * V = 1 := stineCol_isometry K hK
  have hσv : σ *ᵥ (Vᴴ *ᵥ v) = 0 := by
    have h1 : Vᴴ *ᵥ (stineConj K σ *ᵥ v) = (σ * Vᴴ) *ᵥ v := by
      unfold stineConj
      rw [Matrix.mulVec_mulVec, ← hV]
      have hcollapse : Vᴴ * (V * σ * Vᴴ) = σ * Vᴴ := by
        calc Vᴴ * (V * σ * Vᴴ) = (Vᴴ * V) * (σ * Vᴴ) := by
              simp only [Matrix.mul_assoc]
          _ = σ * Vᴴ := by rw [hVV, Matrix.one_mul]
      rw [hcollapse]
    rw [hv, Matrix.mulVec_zero] at h1
    rw [Matrix.mulVec_mulVec]
    exact h1.symm
  have hVv : Vᴴ *ᵥ v = 0 := posDef_mulVec_eq_zero hσ hσv
  unfold stineConj
  rw [← hV, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hVv,
    Matrix.mulVec_zero, Matrix.mulVec_zero]

omit [DecidableEq n] [DecidableEq m] in
set_option linter.unusedFintypeInType false in
theorem stineConj_posSemidef {κ : Type*} [Fintype κ]
    (K : κ → Matrix m n ℂ) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (stineConj K ρ).PosSemidef := by
  unfold stineConj
  exact hρ.mul_mul_conjTranspose_same _

set_option maxHeartbeats 1600000 in -- Stinespring assembly
/-- **The data-processing inequality**, cyclic environment:
`D(Φρ‖Φσ) ≤ D(ρ‖σ)` for a Kraus-presented CPTP map with faithful `σ`
and faithful `Φσ`. -/
theorem relEntropy_kraus_le_zmod (K : ZMod d → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (hbρ : (kraus K ρ).IsHermitian) (hbσ : (kraus K σ).PosDef) :
    relEntropy hbρ hbσ.1 ≤ relEntropy hρ.1 hσ.1 := by
  refine relEntropy_kraus_le_of_envTrace_le K hK hρ.1 hσ.1 hbρ hbσ.1 ?_
  intro hXh hYh
  have hXp : (stineConj K ρ).PosSemidef := stineConj_posSemidef K hρ
  have hYp : (stineConj K σ).PosSemidef :=
    stineConj_posSemidef K hσ.posSemidef
  have hEX : (envTrace (stineConj K ρ)).PosSemidef := by
    rw [envTrace_stineConj]
    exact kraus_posSemidef K hρ
  have hEY : (envTrace (stineConj K σ)).PosDef := by
    rw [envTrace_stineConj]
    exact hbσ
  exact relEntropy_envTrace_le hXp hYp
    (stineConj_ker K hK hρ hσ) hEX hEY

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The data-processing inequality** (Uhlmann monotonicity):
`D(Φρ‖Φσ) ≤ D(ρ‖σ)` for a CPTP map presented by any nonempty finite
Kraus family, with faithful `σ` and faithful `Φσ`. -/
theorem relEntropy_kraus_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    [Nonempty κ] (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (hbρ : (kraus K ρ).IsHermitian) (hbσ : (kraus K σ).PosDef) :
    relEntropy hbρ hbσ.1 ≤ relEntropy hρ.1 hσ.1 := by
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
  have hbρ' : (kraus K' ρ).IsHermitian := by
    rw [hkraus]
    exact hbρ
  have hbσ' : (kraus K' σ).PosDef := by
    rw [hkraus]
    exact hbσ
  have h := relEntropy_kraus_le_zmod K' hK' hρ hσ hbρ' hbσ'
  have hcongr : relEntropy hbρ' hbσ'.1 = relEntropy hbρ hbσ.1 :=
    relEntropy_congr (hkraus ρ) (hkraus σ) hbρ' hbσ'.1 hbρ hbσ.1
  rw [hcongr] at h
  exact h

end Petz
end NCG
