/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDiracStress

/-!
# Frame-variation algebra of the Dirac density (Hilbert stress and local Lorentz identity)

Einstein–Standard-Model action-closure manuscript, `eq:dirac-density`, `eq:stress-definition`
("the Dirac–Yukawa contribution is always taken from the complete metric variation of
`eq:dirac-density`; the spin-connection variation is not dropped"), `app:generated-dynamics`
(stationarity of the composite action with the Dirac term).

Exact algebra at one point, in an orthonormal moving frame.  The data are the lowered
connection coefficients `G_{BAC} = ⟨∇_{e_B}e_A, e_C⟩` (antisymmetric in `A, C`), the structure
coefficients `Ω_{BAC} = G_{BAC} - G_{ABC} = ⟨[e_B, e_A], e_C⟩`, and a first-order variation of the
frame `δe_A = Σ_D ε_D Λ_{AD} e_D` together with the frame derivatives `dΛ_{B;AC} = e_B(Λ_{AC})`
(the metric moves by `δg(e_A, e_B) = k_{AB} = -(Λ_{AB} + Λ_{BA})`).

* `koszul`, **`koszul_unique`** — an array antisymmetric in its last two slots is determined by
  its antisymmetrisation in the first two (`G = koszul Ω`);
* `dOm` — the variation `δΩ` of the structure coefficients; **`koszul_dOm_lorentz`** — for a
  local Lorentz rotation (`Λ = M` antisymmetric) the connection varies by
  `δG_{BAC} = Σ_D ε_D(M_{BD}G_{DAC} + M_{AD}G_{BDC} + M_{CD}G_{BAD}) + e_B(M_{AC})`;
* **`cyc_koszul_sym`** — for a symmetric variation (`Λ = -½k`) the corrected variation
  `δG_{BAC} + ½Σ_D ε_D k_{BD}G_{DAC}` has vanishing cyclic sum;
* Clifford algebra: **`anticomm_spin_cyc`** — `Σ_C ε_C{c_C, X_{W_C}} = ⅙Σ ε_Cε_aε_b
  (W_{Cab} + W_{abC} + W_{bCa}) c_Cc_ac_b` (the spin connection enters the symmetrised Dirac
  density through the totally antisymmetric part only); **`spin_comm`** — the spin lift is a Lie
  algebra homomorphism, `[X_W, X_Y] = -X_{[W,Y]}`.
-/

open Finset

noncomputable section

namespace RenewalGeometry.GenDAlg

open SpinorProlongation TwistedHalfRicci

set_option linter.unusedSectionVars false

/-! ### Real identities -/

section Real

/-- **Koszul inversion** `G_{BAC} = ½(Ω_{BAC} - Ω_{ACB} + Ω_{CBA})`. -/
def koszul (Ω : Fin 4 → Fin 4 → Fin 4 → ℝ) (B A C : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (Ω B A C - Ω A C B + Ω C B A)

/-- **Koszul uniqueness**: an array antisymmetric in its last two slots whose antisymmetrisation
in the first two slots is `Ω` is `koszul Ω`. -/
theorem koszul_unique {W Ω : Fin 4 → Fin 4 → Fin 4 → ℝ} (hW : ∀ B A C, W B C A = -W B A C)
    (hΩ : ∀ B A C, W B A C - W A B C = Ω B A C) (B A C : Fin 4) :
    W B A C = koszul Ω B A C := by
  unfold koszul
  rw [← hΩ B A C, ← hΩ A C B, ← hΩ C B A]
  have h1 := hW A B C
  have h2 := hW C A B
  have h3 := hW B A C
  linear_combination (1 / 2 : ℝ) * h1 - (1 / 2 : ℝ) * h2 + (1 / 2 : ℝ) * h3

/-- The structure coefficients `Ω_{BAC} = G_{BAC} - G_{ABC}` of a torsion-free connection. -/
def omG (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (B A C : Fin 4) : ℝ := G B A C - G A B C

variable (ε : Fin 4 → ℝ)

/-- **The variation of the structure coefficients** under `δe_A = Σ_D ε_D Λ_{AD}e_D`,
`δg(e_D, e_C) = k_{DC}`, with frame derivatives `dΛ_{B;AC} = e_B(Λ_{AC})`. -/
def dOm (Ω : Fin 4 → Fin 4 → Fin 4 → ℝ) (Λ k : Fin 4 → Fin 4 → ℝ)
    (dΛ : Fin 4 → Fin 4 → Fin 4 → ℝ) (B A C : Fin 4) : ℝ :=
  ∑ D, ε D * (Ω B A D * k D C + Λ B D * Ω D A C + Λ A D * Ω B D C + Ω B A D * Λ C D) +
    dΛ B A C - dΛ A B C

theorem dOm_add (Ω : Fin 4 → Fin 4 → Fin 4 → ℝ) (Λ Λ' k k' : Fin 4 → Fin 4 → ℝ)
    (dΛ dΛ' : Fin 4 → Fin 4 → Fin 4 → ℝ) (B A C : Fin 4) :
    dOm ε Ω (Λ + Λ') (k + k') (dΛ + dΛ') B A C = dOm ε Ω Λ k dΛ B A C + dOm ε Ω Λ' k' dΛ' B A C := by
  unfold dOm
  simp only [Pi.add_apply]
  rw [show ∀ x y z w : ℝ, x + y - z + (w) = x + y - z + w from fun _ _ _ _ => rfl]
  have : ∑ D, ε D * (Ω B A D * (k D C + k' D C) + (Λ B D + Λ' B D) * Ω D A C +
      (Λ A D + Λ' A D) * Ω B D C + Ω B A D * (Λ C D + Λ' C D)) =
      ∑ D, ε D * (Ω B A D * k D C + Λ B D * Ω D A C + Λ A D * Ω B D C + Ω B A D * Λ C D) +
      ∑ D, ε D * (Ω B A D * k' D C + Λ' B D * Ω D A C + Λ' A D * Ω B D C + Ω B A D * Λ' C D) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun D _ => by ring
  rw [this]
  ring

theorem koszul_add (Ω Ω' : Fin 4 → Fin 4 → Fin 4 → ℝ) (B A C : Fin 4) :
    koszul (fun x y z => Ω x y z + Ω' x y z) B A C = koszul Ω B A C + koszul Ω' B A C := by
  unfold koszul; ring

/-- The connection variation of a local Lorentz rotation. -/
def gM (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (M : Fin 4 → Fin 4 → ℝ)
    (dM : Fin 4 → Fin 4 → Fin 4 → ℝ) (B A C : Fin 4) : ℝ :=
  ∑ D, ε D * (M B D * G D A C + M A D * G B D C + M C D * G B A D) + dM B A C

/-- **The connection variation of a local Lorentz rotation** `δe_A = Σ_D ε_D M_{AD}e_D`
(`M` antisymmetric, the metric fixed): `δG = koszul(δΩ)` is `gM`. -/
theorem koszul_dOm_lorentz {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C)
    {M : Fin 4 → Fin 4 → ℝ} (hM : ∀ A B, M B A = -M A B) {dM : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hdM : ∀ B A C, dM B C A = -dM B A C) (B A C : Fin 4) :
    koszul (dOm ε (omG G) M 0 dM) B A C = gM ε G M dM B A C := by
  refine (koszul_unique (W := gM ε G M dM) (fun B A C => ?_) (fun B A C => ?_) B A C).symm
  · unfold gM
    rw [hdM, neg_add, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [hG D C A, hG B D A, hG B C D]
    ring
  · unfold gM dOm omG
    simp only [Pi.zero_apply, mul_zero, zero_add]
    have : ∑ D, ε D * (M B D * G D A C + M A D * G B D C + M C D * G B A D) -
        ∑ D, ε D * (M A D * G D B C + M B D * G A D C + M C D * G A B D) =
        ∑ D, ε D * (M B D * (G D A C - G A D C) + M A D * (G B D C - G D B C) +
          (G B A D - G A B D) * M C D) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun D _ => by ring
    linear_combination this

/-- **The cyclic sum of the corrected symmetric connection variation vanishes**: for
`δe_A = -½Σ_D ε_D k_{AD}e_D`, `δg = k` (`k` symmetric, `dk` symmetric in its last two slots),
`W_{BAC} = koszul(δΩ)_{BAC} + ½Σ_D ε_D k_{BD}G_{DAC}` has `W_{BAC} + W_{ACB} + W_{CBA} = 0`. -/
theorem cyc_koszul_sym {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C)
    {k : Fin 4 → Fin 4 → ℝ} (hk : ∀ A B, k B A = k A B) {dk : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hdk : ∀ B A C, dk B C A = dk B A C) (B A C : Fin 4) :
    let W : Fin 4 → Fin 4 → Fin 4 → ℝ := fun x y z =>
      koszul (dOm ε (omG G) (fun a b => -(1 / 2 : ℝ) * k a b) k
        (fun a b c => -(1 / 2 : ℝ) * dk a b c)) x y z + (1 / 2 : ℝ) * ∑ D, ε D * k x D * G D y z
    W B A C + W A C B + W C B A = 0 := by
  intro W
  obtain ⟨G', rfl⟩ : ∃ G' : Fin 4 → Fin 4 → Fin 4 → ℝ, G = fun x y z => G' x y z - G' x z y :=
    ⟨fun x y z => G x y z / 2, by
      funext x y z; show G x y z = G x y z / 2 - G x z y / 2; rw [hG x y z]; ring⟩
  obtain ⟨k', rfl⟩ : ∃ k' : Fin 4 → Fin 4 → ℝ, k = fun x y => k' x y + k' y x :=
    ⟨fun x y => k x y / 2, by
      funext x y; show k x y = k x y / 2 + k y x / 2; rw [hk x y]; ring⟩
  have hd1 : dk A C B = dk A B C := hdk A B C
  have hd2 : dk C B A = dk C A B := hdk C A B
  have hd3 : dk B A C = dk B C A := (hdk B A C).symm
  simp only [W, koszul, dOm, omG, Fin.sum_univ_four]
  rw [hd1, hd2, hd3]
  ring

end Real

/-! ### Clifford identities -/

section Cliff

variable {A : Type*} [Ring A] [Algebra ℝ A] (Fr : CliffordFrame (Fin 4) A)

/-- Relabelling of a triple sum by a cyclic rotation of the summation variables. -/
theorem sum3_rot' {M : Type*} [AddCommMonoid M] (f : Fin 4 → Fin 4 → Fin 4 → M) :
    ∑ x, ∑ y, ∑ z, f y z x = ∑ x, ∑ y, ∑ z, f x y z := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Finset.sum_comm

theorem anti_c (a b : Fin 4) :
    Fr.c a * Fr.c b = ((-2 : ℝ) * (if a = b then Fr.ε a else 0)) • (1 : A) - Fr.c b * Fr.c a := by
  rw [← Fr.anticomm a b]; abel

/-- **A three-generator identity**: `O(C,a,b) = O(C,b,a)` for
`O(C,a,b) = c_Cc_ac_b + c_ac_bc_C - 2c_bc_Cc_a`. -/
theorem triple_aux (a b C : Fin 4) :
    Fr.c C * Fr.c a * Fr.c b + Fr.c a * Fr.c b * Fr.c C - (2 : ℝ) • (Fr.c b * Fr.c C * Fr.c a) =
      Fr.c C * Fr.c b * Fr.c a + Fr.c b * Fr.c a * Fr.c C -
        (2 : ℝ) • (Fr.c a * Fr.c C * Fr.c b) := by
  set x := Fr.c a
  set y := Fr.c b
  set z := Fr.c C
  set sxz : ℝ := (-2 : ℝ) * (if a = C then Fr.ε a else 0)
  set syz : ℝ := (-2 : ℝ) * (if b = C then Fr.ε b else 0)
  have hxz : x * z = sxz • (1 : A) - z * x := anti_c Fr a C
  have hyz : y * z = syz • (1 : A) - z * y := anti_c Fr b C
  have e1 : x * y * z = syz • x - sxz • y + z * x * y := by
    rw [mul_assoc, hyz, mul_sub, mul_smul_comm, mul_one, ← mul_assoc, hxz, sub_mul,
      smul_mul_assoc, one_mul]
    abel
  have e2 : y * x * z = sxz • y - syz • x + z * y * x := by
    rw [mul_assoc, hxz, mul_sub, mul_smul_comm, mul_one, ← mul_assoc, hyz, sub_mul,
      smul_mul_assoc, one_mul]
    abel
  have e3 : y * z * x = syz • x - z * y * x := by
    rw [hyz, sub_mul, smul_mul_assoc, one_mul]
  have e4 : x * z * y = sxz • y - z * x * y := by
    rw [hxz, sub_mul, smul_mul_assoc, one_mul]
  rw [e1, e2, e3, e4]
  module

/-- **The spin connection enters the symmetrised Dirac density through its cyclic part**:
for `W` antisymmetric in its last two slots,
`Σ_C ε_C(c_C X_{W_C} + X_{W_C} c_C) = ⅙ Σ_{C,a,b} ε_Cε_aε_b (W_{Cab} + W_{abC} + W_{bCa}) c_Cc_ac_b`. -/
theorem anticomm_spin_cyc (W : Fin 4 → Fin 4 → Fin 4 → ℝ) (hW : ∀ C a b, W C b a = -W C a b) :
    ∑ C, Fr.ε C • (Fr.c C * spinPart Fr (W C) + spinPart Fr (W C) * Fr.c C) =
      (1 / 6 : ℝ) • ∑ C, ∑ a, ∑ b, (Fr.ε C * Fr.ε a * Fr.ε b *
        (W C a b + W a b C + W b C a)) • (Fr.c C * Fr.c a * Fr.c b) := by
  set e := Fr.ε
  set c := Fr.c
  -- the left side as a triple sum
  have hL : ∑ C, e C • (c C * spinPart Fr (W C) + spinPart Fr (W C) * c C) =
      (1 / 4 : ℝ) • ∑ C, ∑ a, ∑ b, (e C * e a * e b * W C a b) •
        (c C * c a * c b + c a * c b * c C) := by
    unfold spinPart
    simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
      smul_add, Finset.sum_add_distrib, smul_smul]
    congr 1
    · refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => ?_
      simp only [mul_assoc]; congr 1; ring
    · refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => ?_
      congr 1; ring
  -- the right side relabelled
  have hR : ∑ C, ∑ a, ∑ b, (e C * e a * e b * (W C a b + W a b C + W b C a)) • (c C * c a * c b) =
      ∑ C, ∑ a, ∑ b, (e C * e a * e b * W C a b) •
        (c C * c a * c b + c b * c C * c a + c a * c b * c C) := by
    have h2 : ∑ C, ∑ a, ∑ b, (e C * e a * e b * W a b C) • (c C * c a * c b) =
        ∑ C, ∑ a, ∑ b, (e C * e a * e b * W C a b) • (c b * c C * c a) := by
      have := sum3_rot' (fun x y z => (e x * e y * e z * W x y z) • (c z * c x * c y))
      rw [← this]
      refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => ?_
      congr 1; ring
    have h3 : ∑ C, ∑ a, ∑ b, (e C * e a * e b * W b C a) • (c C * c a * c b) =
        ∑ C, ∑ a, ∑ b, (e C * e a * e b * W C a b) • (c a * c b * c C) := by
      have := sum3_rot' (fun x y z => (e z * e x * e y * W z x y) • (c x * c y * c z))
      rw [this]
      refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => ?_
      congr 1; ring
    simp only [mul_add, add_smul, Finset.sum_add_distrib, smul_add]
    rw [h2, h3]
  -- the difference is a multiple of an antisymmetric pairing of `W` with a symmetric operator
  set O : Fin 4 → Fin 4 → Fin 4 → A := fun C a b =>
    c C * c a * c b + c a * c b * c C - (2 : ℝ) • (c b * c C * c a) with hO
  have hOsym : ∀ C a b, O C a b = O C b a := fun C a b => triple_aux Fr a b C
  have hzero : ∑ C, ∑ a, ∑ b, (e C * e a * e b * W C a b) • O C a b = 0 := by
    have hswap : ∑ C, ∑ a, ∑ b, (e C * e a * e b * W C a b) • O C a b =
        -∑ C, ∑ a, ∑ b, (e C * e a * e b * W C a b) • O C a b := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun C _ => ?_
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hOsym C b a, hW C a b, ← neg_smul]
      congr 1; ring
    have h2 : (2 : ℝ) • ∑ C, ∑ a, ∑ b, (e C * e a * e b * W C a b) • O C a b = 0 := by
      rw [two_smul]; nth_rewrite 2 [hswap]; rw [add_neg_cancel]
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [hL, hR]
  have hdiff : (1 / 4 : ℝ) • ∑ C, ∑ a, ∑ b, (e C * e a * e b * W C a b) •
        (c C * c a * c b + c a * c b * c C) -
      (1 / 6 : ℝ) • ∑ C, ∑ a, ∑ b, (e C * e a * e b * W C a b) •
        (c C * c a * c b + c b * c C * c a + c a * c b * c C) =
      (1 / 12 : ℝ) • ∑ C, ∑ a, ∑ b, (e C * e a * e b * W C a b) • O C a b := by
    simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, hO]
    refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    module
  rw [hzero, smul_zero] at hdiff
  exact sub_eq_zero.mp hdiff

/-- The commutator array `[X, Y]_{ab} = Σ_D ε_D(X_{aD}Y_{Db} - Y_{aD}X_{Db})`. -/
def brk (ε : Fin 4 → ℝ) (X Y : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) : ℝ :=
  ∑ D, ε D * (X a D * Y D b - Y a D * X D b)

/-- **The spin lift is a Lie algebra homomorphism** (with the sign of the conventions):
`[X_W, X_Y] = -X_{[W,Y]}` for antisymmetric `W, Y`. -/
theorem spin_comm (X Y : Fin 4 → Fin 4 → ℝ) (hX : ∀ a b, X b a = -X a b) :
    spinPart Fr X * spinPart Fr Y - spinPart Fr Y * spinPart Fr X =
      -spinPart Fr (brk Fr.ε X Y) := by
  have h1 : spinPart Fr X * spinPart Fr Y - spinPart Fr Y * spinPart Fr X =
      (1 / 4 : ℝ) • ∑ a, ∑ b, (Fr.ε a * Fr.ε b * Y a b) •
        (spinPart Fr X * (Fr.c a * Fr.c b) - Fr.c a * Fr.c b * spinPart Fr X) := by
    conv_lhs => rw [show spinPart Fr Y = (1 / 4 : ℝ) • ∑ a, ∑ b, (Fr.ε a * Fr.ε b * Y a b) •
      (Fr.c a * Fr.c b) from rfl]
    simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, ← smul_sub,
      ← Finset.sum_sub_distrib]
  rw [h1]
  simp only [comm_spinPart_pair Fr X hX]
  have h2 : ∀ a b, (Fr.ε a * Fr.ε b * Y a b) • ((∑ d, (Fr.ε d * X a d) • Fr.c d) * Fr.c b +
        Fr.c a * ∑ d, (Fr.ε d * X b d) • Fr.c d) =
      ∑ d, (Fr.ε a * Fr.ε b * Y a b * (Fr.ε d * X a d)) • (Fr.c d * Fr.c b) +
        ∑ d, (Fr.ε a * Fr.ε b * Y a b * (Fr.ε d * X b d)) • (Fr.c a * Fr.c d) := by
    intro a b
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_add,
      Finset.smul_sum, smul_smul]
  simp only [h2, Finset.sum_add_distrib, smul_add]
  -- the first triple sum
  have hA : ∑ a, ∑ b, ∑ d, (Fr.ε a * Fr.ε b * Y a b * (Fr.ε d * X a d)) • (Fr.c d * Fr.c b) =
      ∑ x, ∑ y, (-(Fr.ε x * Fr.ε y * ∑ D, Fr.ε D * (X x D * Y D y))) • (Fr.c x * Fr.c y) := by
    rw [sum3_rev]
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hX a d]
    ring
  have hB : ∑ a, ∑ b, ∑ d, (Fr.ε a * Fr.ε b * Y a b * (Fr.ε d * X b d)) • (Fr.c a * Fr.c d) =
      ∑ x, ∑ y, (Fr.ε x * Fr.ε y * ∑ D, Fr.ε D * (Y x D * X D y)) • (Fr.c x * Fr.c y) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hA, hB]
  unfold spinPart brk
  rw [← smul_add, ← Finset.sum_add_distrib, ← smul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← add_smul, ← neg_smul]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- The rotated connection array `N_C = -[G_C, M]`,
`N_{Cxy} = Σ_D ε_D(M_{xD}G_{CDy} + M_{yD}G_{CxD})`. -/
def rotN (ε : Fin 4 → ℝ) (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (M : Fin 4 → Fin 4 → ℝ) (C x y : Fin 4) :
    ℝ :=
  ∑ D, ε D * (M x D * G C D y + M y D * G C x D)

theorem rotN_eq (ε : Fin 4 → ℝ) (G : Fin 4 → Fin 4 → Fin 4 → ℝ) {M : Fin 4 → Fin 4 → ℝ}
    (hM : ∀ a b, M b a = -M a b) (C : Fin 4) :
    rotN ε G M C = fun x y => -brk ε (G C) M x y := by
  funext x y
  unfold rotN brk
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [hM y D]; ring

/-- **The operator form of the local Lorentz identity**:
`Σ_Cε_C{c_C, X_{N_C}} = Σ_Cε_C(div(e_C){c_C, X_M} + [X_{G_C}, {c_C, X_M}])`, with the frame
divergence `div(e_C) = Σ_Dε_DG_{DCD}`. -/
theorem lorentz_op {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C)
    {M : Fin 4 → Fin 4 → ℝ} (hM : ∀ a b, M b a = -M a b) :
    ∑ C, Fr.ε C • (Fr.c C * spinPart Fr (rotN Fr.ε G M C) +
        spinPart Fr (rotN Fr.ε G M C) * Fr.c C) =
      ∑ C, Fr.ε C • ((∑ D, Fr.ε D * G D C D) • (Fr.c C * spinPart Fr M + spinPart Fr M * Fr.c C) +
        (spinPart Fr (G C) * (Fr.c C * spinPart Fr M + spinPart Fr M * Fr.c C) -
          (Fr.c C * spinPart Fr M + spinPart Fr M * Fr.c C) * spinPart Fr (G C))) := by
  -- the commutator expansion
  have hcom : ∀ C, spinPart Fr (G C) * (Fr.c C * spinPart Fr M + spinPart Fr M * Fr.c C) -
      (Fr.c C * spinPart Fr M + spinPart Fr M * Fr.c C) * spinPart Fr (G C) =
      ((spinPart Fr (G C) * Fr.c C - Fr.c C * spinPart Fr (G C)) * spinPart Fr M +
        spinPart Fr M * (spinPart Fr (G C) * Fr.c C - Fr.c C * spinPart Fr (G C))) +
      (Fr.c C * (spinPart Fr (G C) * spinPart Fr M - spinPart Fr M * spinPart Fr (G C)) +
        (spinPart Fr (G C) * spinPart Fr M - spinPart Fr M * spinPart Fr (G C)) * Fr.c C) := by
    intro C; noncomm_ring
  have hsp : ∀ C, spinPart Fr (G C) * spinPart Fr M - spinPart Fr M * spinPart Fr (G C) =
      spinPart Fr (rotN Fr.ε G M C) := by
    intro C
    rw [spin_comm Fr (G C) M (fun a b => hG C a b), rotN_eq Fr.ε G hM C]
    unfold spinPart
    rw [← smul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← neg_smul]; congr 1; ring
  have hcl : ∀ C, spinPart Fr (G C) * Fr.c C - Fr.c C * spinPart Fr (G C) =
      ∑ d, (Fr.ε d * G C C d) • Fr.c d :=
    fun C => comm_spinPart Fr (G C) (fun x y => hG C x y) C
  set O : Fin 4 → A := fun C => Fr.c C * spinPart Fr M + spinPart Fr M * Fr.c C with hO
  have hR : ∀ C, Fr.ε C • ((∑ D, Fr.ε D * G D C D) • O C +
      (spinPart Fr (G C) * O C - O C * spinPart Fr (G C))) =
      Fr.ε C • ((∑ D, Fr.ε D * G D C D) • O C) +
      Fr.ε C • ((spinPart Fr (G C) * Fr.c C - Fr.c C * spinPart Fr (G C)) * spinPart Fr M +
        spinPart Fr M * (spinPart Fr (G C) * Fr.c C - Fr.c C * spinPart Fr (G C))) +
      Fr.ε C • (Fr.c C * spinPart Fr (rotN Fr.ε G M C) + spinPart Fr (rotN Fr.ε G M C) * Fr.c C) := by
    intro C
    simp only [hO]
    rw [hcom, hsp]
    simp only [smul_add]
    abel
  rw [Finset.sum_congr rfl (fun C _ => hR C), Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hdiv : ∑ C, Fr.ε C • ((spinPart Fr (G C) * Fr.c C - Fr.c C * spinPart Fr (G C)) *
      spinPart Fr M + spinPart Fr M * (spinPart Fr (G C) * Fr.c C - Fr.c C * spinPart Fr (G C))) =
      -∑ C, Fr.ε C • ((∑ D, Fr.ε D * G D C D) • O C) := by
    simp only [hcl, hO, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      ← Finset.sum_add_distrib, ← smul_add, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul, ← neg_smul]
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [hG C C d]; ring
  rw [hdiv]
  abel

end Cliff

/-! ### Antisymmetry of the variations -/

section Anti

variable (ε : Fin 4 → ℝ)

theorem omG_anti (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (B A C : Fin 4) : omG G A B C = -omG G B A C := by
  unfold omG; ring

theorem dOm_anti {Ω : Fin 4 → Fin 4 → Fin 4 → ℝ} (hΩ : ∀ B A C, Ω A B C = -Ω B A C)
    (Λ k : Fin 4 → Fin 4 → ℝ) (dΛ : Fin 4 → Fin 4 → Fin 4 → ℝ) (B A C : Fin 4) :
    dOm ε Ω Λ k dΛ A B C = -dOm ε Ω Λ k dΛ B A C := by
  unfold dOm
  have : ∑ D, ε D * (Ω A B D * k D C + Λ A D * Ω D B C + Λ B D * Ω A D C + Ω A B D * Λ C D) =
      -∑ D, ε D * (Ω B A D * k D C + Λ B D * Ω D A C + Λ A D * Ω B D C + Ω B A D * Λ C D) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [hΩ B A D, hΩ D B C, hΩ A D C]
    ring
  rw [this]; ring

theorem koszul_anti {Ω : Fin 4 → Fin 4 → Fin 4 → ℝ} (hΩ : ∀ B A C, Ω A B C = -Ω B A C)
    (B A C : Fin 4) : koszul Ω B C A = -koszul Ω B A C := by
  unfold koszul
  rw [hΩ C A B, hΩ A B C, hΩ B C A]
  ring

end Anti

/-! ### The variation of the Dirac density along a frame variation -/

section Pairing

open ActualJetSystem GenDStress GenDiracCur ActualJetSmooth

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']


theorem ls_sq (A : Fin 4) : lorentzSign A * lorentzSign A = 1 := by
  unfold lorentzSign; split_ifs <;> norm_num

/-- The covariant frame jet `X_C = e_CΨ + X_{G_C}Ψ + ρ(a_C)Ψ` from frame data. -/
def covX {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (a : Fin 4 → MatLie m) (ψ : S₀) (Dψ : Fin 4 → S₀)
    (C : Fin 4) : S₀ :=
  Dψ C + spinPart D.Fr (G C) ψ + D.ρ (a C) ψ

/-- The variation of the covariant frame jet with `Ψ` fixed:
`δX_C = Σ_E ε_EΛ_{CE}(e_EΨ + ρ(a_E)Ψ) + X_{δG_C}Ψ`. -/
def varX {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (a : Fin 4 → MatLie m) (ψ : S₀) (Dψ : Fin 4 → S₀) (Λ : Fin 4 → Fin 4 → ℝ)
    (δG : Fin 4 → Fin 4 → Fin 4 → ℝ) (C : Fin 4) : S₀ :=
  ∑ E, (lorentzSign E * Λ C E) • (Dψ E + D.ρ (a E) ψ) + spinPart D.Fr (δG C) ψ

variable {SM : SMData (MatLie m) V S S'} (hP : DiracPairing SM)

/-- The variation of the Dirac Lagrangian `δL_D = ½Σ_Cε_C(⟨Ψ̄, c_CδX_C⟩ - ⟨δX̄_C, c_CΨ⟩)`. -/
def varL (a : Fin 4 → MatLie m) (ψ : S) (Dψ : Fin 4 → S) (ψb : S') (Dψb : Fin 4 → S')
    (Λ : Fin 4 → Fin 4 → ℝ) (δG : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ C, lorentzSign C * (hP.P ψb (SM.D.Fr.c C (varX SM.D a ψ Dψ Λ δG C)) -
    hP.P (varX SM.Db a ψb Dψb Λ δG C) (SM.D.Fr.c C ψ))

theorem varX_eq {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (a : Fin 4 → MatLie m) (ψ : S₀) (Dψ : Fin 4 → S₀)
    (Λ : Fin 4 → Fin 4 → ℝ) (δG : Fin 4 → Fin 4 → Fin 4 → ℝ) (C : Fin 4) :
    varX D a ψ Dψ Λ δG C = ∑ E, (lorentzSign E * Λ C E) • covX D G a ψ Dψ E +
      spinPart D.Fr (fun x y => δG C x y - ∑ E, lorentzSign E * Λ C E * G E x y) ψ := by
  unfold varX covX
  rw [spinPart_sub]
  have hs : spinPart D.Fr (fun x y => ∑ E, lorentzSign E * Λ C E * G E x y) =
      ∑ E, (lorentzSign E * Λ C E) • spinPart D.Fr (G E) :=
    spinPart_sum_smul D.Fr (fun E => lorentzSign E * Λ C E) G
  rw [hs]
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_add,
    Finset.sum_add_distrib]
  abel

/-- The transposition of an antisymmetric spin lift through the pairing,
`⟨Ψ̄, c_CX_WΨ⟩ - ⟨X̄_WΨ̄, c_CΨ⟩ = ⟨Ψ̄, (c_CX_W + X_Wc_C)Ψ⟩`. -/
theorem P_spin_anticomm (W : Fin 4 → Fin 4 → ℝ) (hW : ∀ c d, W d c = -W c d) (C : Fin 4)
    (ψ : S) (ψb : S') :
    hP.P ψb (SM.D.Fr.c C (spinPart SM.D.Fr W ψ)) - hP.P (spinPart SM.Db.Fr W ψb) (SM.D.Fr.c C ψ) =
      hP.P ψb ((SM.D.Fr.c C * spinPart SM.D.Fr W + spinPart SM.D.Fr W * SM.D.Fr.c C) ψ) := by
  rw [hP.P_spin W hW]
  simp only [LinearMap.add_apply, Module.End.mul_apply, map_add]
  ring

/-- The kinetic bookkeeping of the symmetric frame variation. -/
theorem kin_sum (ℓ : ℝ) (p q : Fin 4 → Fin 4 → ℝ) {k : Fin 4 → Fin 4 → ℝ}
    (hk : ∀ A B, k B A = k A B) :
    (1 / 2 : ℝ) * (∑ A, lorentzSign A * k A A) * ℓ +
      ((1 / 2 : ℝ) * ∑ C, lorentzSign C * ∑ E, lorentzSign E * (-(1 / 2 : ℝ) * k C E) *
        (p C E - q C E) + (1 / 2 : ℝ) * 0) =
      (1 / 2 : ℝ) * ∑ A, ∑ B, lorentzSign A * lorentzSign B *
        (-(1 / 4 : ℝ) * (p A B + p B A - q A B - q B A) + etaL A B * ℓ) * k A B := by
  obtain ⟨k', rfl⟩ : ∃ k' : Fin 4 → Fin 4 → ℝ, k = fun x y => k' x y + k' y x :=
    ⟨fun x y => k x y / 2, by
      funext x y; show k x y = k x y / 2 + k y x / 2; rw [hk x y]; ring⟩
  simp only [Fin.sum_univ_four, etaL, lorentzSign, Fin.isValue]
  simp (config := { decide := true }) only [ite_true, ite_false]
  ring

/-- **Spin-lift contribution of an array with vanishing cyclic sum**: if `W` is antisymmetric
in its last two slots and `W_{Cab} + W_{abC} + W_{bCa} = 0`, then
`Σ_Cε_C(⟨Ψ̄, c_CX_{W_C}Ψ⟩ - ⟨X̄_{W_C}Ψ̄, c_CΨ⟩) = 0`. -/
theorem spin_cyc_zero (W : Fin 4 → Fin 4 → Fin 4 → ℝ) (hWa : ∀ C a b, W C b a = -W C a b)
    (hcyc : ∀ C a b, W C a b + W a b C + W b C a = 0) (ψ : S) (ψb : S') :
    ∑ C, lorentzSign C * (hP.P ψb (SM.D.Fr.c C (spinPart SM.D.Fr (W C) ψ)) -
      hP.P (spinPart SM.Db.Fr (W C) ψb) (SM.D.Fr.c C ψ)) = 0 := by
  simp only [P_spin_anticomm hP (W _) (fun c d => hWa _ c d)]
  have e : ∑ C, lorentzSign C * hP.P ψb ((SM.D.Fr.c C * spinPart SM.D.Fr (W C) +
      spinPart SM.D.Fr (W C) * SM.D.Fr.c C) ψ) =
      hP.P ψb ((∑ C, SM.D.Fr.ε C • (SM.D.Fr.c C * spinPart SM.D.Fr (W C) +
        spinPart SM.D.Fr (W C) * SM.D.Fr.c C)) ψ) := by
    rw [eps_D_eq]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  rw [e, anticomm_spin_cyc SM.D.Fr W hWa]
  simp only [hcyc, mul_zero, zero_smul, Finset.sum_const_zero, smul_zero, LinearMap.zero_apply,
    map_zero]

set_option maxHeartbeats 1000000 in
/-- **The Hilbert stress of the Dirac density is its symmetric frame variation**: for the
symmetric variation `δe_A = -½Σ_Dε_Dk_{AD}e_D`, `δg = k` (with arbitrary frame derivatives `dk`
of `k`), `½ tr_g(k) L_D + δL_D = ½ Σ_{A,B} ε_Aε_B T_{AB}k_{AB}` with `T` the symmetric Dirac stress
`GenDStress.symTD`: the spin-connection variation does not contribute. -/
theorem sym_identity (H : V) {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C)
    (a : Fin 4 → MatLie m) (ψ : S) (Dψ : Fin 4 → S) (ψb : S') (Dψb : Fin 4 → S')
    {k : Fin 4 → Fin 4 → ℝ} (hk : ∀ A B, k B A = k A B) {dk : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hdk : ∀ B A C, dk B C A = dk B A C) :
    (1 / 2 : ℝ) * (∑ A, lorentzSign A * k A A) *
        lagD SM.D hP.P H ψ (covX SM.D G a ψ Dψ) ψb (covX SM.Db G a ψb Dψb) +
      varL hP a ψ Dψ ψb Dψb (fun x y => -(1 / 2 : ℝ) * k x y)
        (koszul (dOm lorentzSign (omG G) (fun x y => -(1 / 2 : ℝ) * k x y) k
          (fun x y z => -(1 / 2 : ℝ) * dk x y z))) =
      (1 / 2 : ℝ) * ∑ A, ∑ B, lorentzSign A * lorentzSign B *
        (symTD SM.D hP.P).frame H ψ (covX SM.D G a ψ Dψ) ψb (covX SM.Db G a ψb Dψb) A B * k A B := by
  set X := covX SM.D G a ψ Dψ with hXdef
  set Xb := covX SM.Db G a ψb Dψb with hXbdef
  set δG := koszul (dOm lorentzSign (omG G) (fun x y => -(1 / 2 : ℝ) * k x y) k
    (fun x y z => -(1 / 2 : ℝ) * dk x y z)) with hδG
  set W : Fin 4 → Fin 4 → Fin 4 → ℝ := fun C x y =>
    δG C x y - ∑ E, lorentzSign E * (-(1 / 2 : ℝ) * k C E) * G E x y with hW
  have hWa : ∀ C x y, W C y x = -W C x y := by
    intro C x y
    simp only [hW, hδG]
    rw [koszul_anti (dOm_anti lorentzSign (omG_anti G) _ _ _)]
    have : ∑ E, lorentzSign E * (-(1 / 2 : ℝ) * k C E) * G E y x =
        -∑ E, lorentzSign E * (-(1 / 2 : ℝ) * k C E) * G E x y := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun E _ => by rw [hG E x y]; ring
    rw [this]; ring
  have hcyc : ∀ C x y, W C x y + W x y C + W y C x = 0 := by
    intro C x y
    have h := cyc_koszul_sym lorentzSign hG hk hdk C x y
    simp only at h
    simp only [hW, hδG]
    have e : ∀ C' x' y', -∑ E, lorentzSign E * (-(1 / 2 : ℝ) * k C' E) * G E x' y' =
        (1 / 2 : ℝ) * ∑ E, lorentzSign E * k C' E * G E x' y' := fun C' x' y' => by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun E _ => by ring
    simp only [sub_eq_add_neg, e]
    linarith
  have hspin := spin_cyc_zero hP W hWa hcyc ψ ψb
  -- the kinetic part
  have hvX : ∀ C, varX SM.D a ψ Dψ (fun x y => -(1 / 2 : ℝ) * k x y) δG C =
      ∑ E, (lorentzSign E * (-(1 / 2 : ℝ) * k C E)) • X E + spinPart SM.D.Fr (W C) ψ :=
    fun C => varX_eq SM.D G a ψ Dψ _ δG C
  have hvXb : ∀ C, varX SM.Db a ψb Dψb (fun x y => -(1 / 2 : ℝ) * k x y) δG C =
      ∑ E, (lorentzSign E * (-(1 / 2 : ℝ) * k C E)) • Xb E + spinPart SM.Db.Fr (W C) ψb :=
    fun C => varX_eq SM.Db G a ψb Dψb _ δG C
  have hsplit : varL hP a ψ Dψ ψb Dψb (fun x y => -(1 / 2 : ℝ) * k x y) δG =
      (1 / 2 : ℝ) * ∑ C, lorentzSign C * ∑ E, lorentzSign E * (-(1 / 2 : ℝ) * k C E) *
        (hP.P ψb (SM.D.Fr.c C (X E)) - hP.P (Xb E) (SM.D.Fr.c C ψ)) +
      (1 / 2 : ℝ) * ∑ C, lorentzSign C * (hP.P ψb (SM.D.Fr.c C (spinPart SM.D.Fr (W C) ψ)) -
        hP.P (spinPart SM.Db.Fr (W C) ψb) (SM.D.Fr.c C ψ)) := by
    unfold varL
    simp only [hvX, hvXb, map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun C _ => ?_
    simp only [mul_sub, mul_add, Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  rw [hsplit, hspin]
  simp only [frame_symTD, kinT]
  exact kin_sum _ (fun C E => hP.P ψb (SM.D.Fr.c C (X E))) (fun C E => hP.P (Xb E) (SM.D.Fr.c C ψ))
    hk

/-! #### The local Lorentz identity -/

/-- The Dirac residual `r_D = Σ_Bε_Bc_BX_B - 𝓜(H)Ψ` from frame data. -/
def rDf {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (a : Fin 4 → MatLie m) (H : V) (ψ : S₀) (Dψ : Fin 4 → S₀) :
    S₀ :=
  ∑ B, lorentzSign B • D.Fr.c B (covX D G a ψ Dψ B) - mass D.m0 D.L H ψ

/-- The frame divergence `div(e_C) = Σ_Dε_DG_{DCD}`. -/
def divEf (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (C : Fin 4) : ℝ := ∑ D, lorentzSign D * G D C D

/-- The spin flux of a local Lorentz rotation,
`Fl_C = ½ε_C(⟨Ψ̄, c_CσΨ⟩ - ⟨σ̄Ψ̄, c_CΨ⟩)`, `σ = -X_M`. -/
def lorFl (M : Fin 4 → Fin 4 → ℝ) (ψ : S) (ψb : S') (C : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * lorentzSign C * (hP.P ψb (SM.D.Fr.c C ((-spinPart SM.D.Fr M) ψ)) -
    hP.P ((-spinPart SM.Db.Fr M) ψb) (SM.D.Fr.c C ψ))

/-- The frame derivative `e_C(Fl_C)` of the spin flux (product rule on jets, with
`e_C(M) = dM_C`). -/
def lorFlD (M : Fin 4 → Fin 4 → ℝ) (dM : Fin 4 → Fin 4 → Fin 4 → ℝ) (ψ : S) (Dψ : Fin 4 → S)
    (ψb : S') (Dψb : Fin 4 → S') (C : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * lorentzSign C *
    (hP.P (Dψb C) (SM.D.Fr.c C ((-spinPart SM.D.Fr M) ψ)) +
      hP.P ψb (SM.D.Fr.c C ((-spinPart SM.D.Fr (dM C)) ψ)) +
      hP.P ψb (SM.D.Fr.c C ((-spinPart SM.D.Fr M) (Dψ C))) -
      hP.P ((-spinPart SM.Db.Fr (dM C)) ψb) (SM.D.Fr.c C ψ) -
      hP.P ((-spinPart SM.Db.Fr M) (Dψb C)) (SM.D.Fr.c C ψ) -
      hP.P ((-spinPart SM.Db.Fr M) ψb) (SM.D.Fr.c C (Dψ C)))

/-- The varied connection minus the rotated frame part, for a local Lorentz rotation, is
`rotN + dM`. -/
theorem lorentz_W {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C)
    {M : Fin 4 → Fin 4 → ℝ} (hM : ∀ A B, M B A = -M A B) {dM : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hdM : ∀ B A C, dM B C A = -dM B A C) (C x y : Fin 4) :
    koszul (dOm lorentzSign (omG G) M 0 dM) C x y - ∑ E, lorentzSign E * M C E * G E x y =
      rotN lorentzSign G M C x y + dM C x y := by
  rw [koszul_dOm_lorentz lorentzSign hG hM hdM]
  unfold gM rotN
  have : ∑ D, lorentzSign D * (M C D * G D x y + M x D * G C D y + M y D * G C x D) =
      ∑ E, lorentzSign E * M C E * G E x y +
        ∑ D, lorentzSign D * (M x D * G C D y + M y D * G C x D) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun D _ => by ring
  rw [this]; ring

theorem rotN_anti {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C)
    {M : Fin 4 → Fin 4 → ℝ} (hM : ∀ A B, M B A = -M A B) (C x y : Fin 4) :
    rotN lorentzSign G M C y x = -rotN lorentzSign G M C x y := by
  unfold rotN
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [hG C D x, hG C y D]; ring

/-- The mass operator commutes with every spin lift. -/
theorem mass_spin {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (H : V) (W : Fin 4 → Fin 4 → ℝ) :
    mass D.m0 D.L H * spinPart D.Fr W = spinPart D.Fr W * mass D.m0 D.L H :=
  commute_spinPart D.Fr _ (fun c d => D.mass_cl H c d) W

/-- The gauge action commutes with every spin lift. -/
theorem rho_spin' {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (y : MatLie m) (W : Fin 4 → Fin 4 → ℝ) : D.ρ y * spinPart D.Fr W = spinPart D.Fr W * D.ρ y :=
  commute_spinPart D.Fr _ (commute_pair_of_commute D.Fr _ (fun b => D.comm y b)) W

theorem P_mass (H : V) (φ : S') (x : S) :
    hP.P (mass SM.Db.m0 SM.Db.L H φ) x = -hP.P φ (mass SM.D.m0 SM.D.L H x) := by
  simp only [mass, LinearMap.add_apply, map_add, LinearMap.add_apply, hP.m0_tr, hP.L_tr]
  ring

/-- **The kinetic and spin parts of the canonical form** (the right side of the local Lorentz
identity after the transpositions). -/
theorem lorentz_rhs_R1 (H : V) (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (a : Fin 4 → MatLie m) (ψ : S)
    (Dψ : Fin 4 → S) (ψb : S') (Dψb : Fin 4 → S') {M : Fin 4 → Fin 4 → ℝ}
    (hM : ∀ A B, M B A = -M A B) :
    hP.P (rDf SM.Db G a H ψb Dψb) ((-spinPart SM.D.Fr M) ψ) -
      hP.P ((-spinPart SM.Db.Fr M) ψb) (rDf SM.D G a H ψ Dψ) =
      -∑ B, lorentzSign B * (hP.P (covX SM.Db G a ψb Dψb B) (SM.D.Fr.c B (spinPart SM.D.Fr M ψ)) +
        hP.P ψb (spinPart SM.D.Fr M (SM.D.Fr.c B (covX SM.D G a ψ Dψ B)))) := by
  have hPs := hP.P_spin M (fun c d => hM c d)
  unfold rDf
  simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.neg_apply, map_neg, smul_eq_mul, hP.c_tr, hPs, P_mass hP]
  have hmc : spinPart SM.D.Fr M (mass SM.D.m0 SM.D.L H ψ) =
      mass SM.D.m0 SM.D.L H (spinPart SM.D.Fr M ψ) := by
    have := congrArg (fun F : Module.End ℝ S => F ψ) (mass_spin SM.D H M)
    simpa using this.symm
  rw [hmc]
  simp only [mul_add, Finset.sum_add_distrib]
  ring_nf

/-- **The flux terms of the local Lorentz identity**, with `O_C = c_CX_M + X_Mc_C`. -/
theorem lorentz_rhs_flux {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C)
    (a : Fin 4 → MatLie m) (ψ : S) (Dψ : Fin 4 → S) (ψb : S') (Dψb : Fin 4 → S')
    {M : Fin 4 → Fin 4 → ℝ} (hM : ∀ A B, M B A = -M A B) {dM : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hdM : ∀ B A C, dM B C A = -dM B A C) (C : Fin 4) :
    divEf G C * lorFl hP M ψ ψb C + lorFlD hP M dM ψ Dψ ψb Dψb C =
      -((1 / 2 : ℝ) * lorentzSign C *
        (divEf G C * hP.P ψb ((SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C) ψ) +
          hP.P (covX SM.Db G a ψb Dψb C)
            ((SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C) ψ) +
          hP.P ψb ((SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C)
            (covX SM.D G a ψ Dψ C)) +
          hP.P ψb ((spinPart SM.D.Fr (G C) *
              (SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C) -
            (SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C) *
              spinPart SM.D.Fr (G C)) ψ) +
          hP.P ψb ((SM.D.Fr.c C * spinPart SM.D.Fr (dM C) + spinPart SM.D.Fr (dM C) * SM.D.Fr.c C) ψ))) := by
  have hPM := hP.P_spin M (fun c d => hM c d)
  have hPdM := hP.P_spin (dM C) (fun c d => hdM C c d)
  have hPG := hP.P_spin (G C) (fun c d => hG C c d)
  have hDψ : Dψ C = covX SM.D G a ψ Dψ C - spinPart SM.D.Fr (G C) ψ - SM.D.ρ (a C) ψ := by
    unfold covX; abel
  have hDψb : Dψb C = covX SM.Db G a ψb Dψb C - spinPart SM.Db.Fr (G C) ψb -
      SM.Db.ρ (a C) ψb := by
    unfold covX; abel
  -- the gauge action commutes with `O_C`
  have hρc : SM.D.ρ (a C) * SM.D.Fr.c C = SM.D.Fr.c C * SM.D.ρ (a C) := SM.D.comm (a C) C
  have hρs : SM.D.ρ (a C) * spinPart SM.D.Fr M = spinPart SM.D.Fr M * SM.D.ρ (a C) :=
    rho_spin' SM.D (a C) M
  have hρO : ∀ x : S, (SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C)
      (SM.D.ρ (a C) x) =
      SM.D.ρ (a C) ((SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C) x) := by
    intro x
    have h : (SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C) * SM.D.ρ (a C) =
        SM.D.ρ (a C) * (SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C) := by
      have h1 : SM.D.ρ (a C) * (SM.D.Fr.c C * spinPart SM.D.Fr M) =
          SM.D.Fr.c C * spinPart SM.D.Fr M * SM.D.ρ (a C) := by
        rw [← mul_assoc, hρc, mul_assoc, hρs, ← mul_assoc]
      have h2 : SM.D.ρ (a C) * (spinPart SM.D.Fr M * SM.D.Fr.c C) =
          spinPart SM.D.Fr M * SM.D.Fr.c C * SM.D.ρ (a C) := by
        rw [← mul_assoc, hρs, mul_assoc, hρc, ← mul_assoc]
      rw [add_mul, mul_add, h1, h2]
    have := congrArg (fun F : Module.End ℝ S => F x) h
    simpa using this
  have hρs' : ∀ x : S, spinPart SM.D.Fr M (SM.D.ρ (a C) x) =
      SM.D.ρ (a C) (spinPart SM.D.Fr M x) := fun x => by
    have := congrArg (fun F : Module.End ℝ S => F x) hρs
    simpa using this.symm
  have hρc' : ∀ x : S, SM.D.Fr.c C (SM.D.ρ (a C) x) = SM.D.ρ (a C) (SM.D.Fr.c C x) := fun x => by
    have := congrArg (fun F : Module.End ℝ S => F x) hρc
    simpa using this.symm
  unfold lorFl lorFlD
  rw [hDψ, hDψb]
  simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.add_apply,
    Module.End.mul_apply, map_add, hP.c_tr, hPM, hPdM, hPG, hP.ρ_tr, hρs', hρc']
  ring

/-- The canonical form of both sides of the local Lorentz identity. -/
def lorCF (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (a : Fin 4 → MatLie m) (ψ : S) (Dψ : Fin 4 → S)
    (ψb : S') (Dψb : Fin 4 → S') (M : Fin 4 → Fin 4 → ℝ) (dM : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ B, (1 / 2 : ℝ) * lorentzSign B *
    ((∑ d, lorentzSign d * M B d * hP.P (covX SM.Db G a ψb Dψb B) (SM.D.Fr.c d ψ)) -
      ∑ d, lorentzSign d * M B d * hP.P ψb (SM.D.Fr.c d (covX SM.D G a ψ Dψ B)) +
      (divEf G B * hP.P ψb ((SM.D.Fr.c B * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c B) ψ) +
        hP.P ψb ((spinPart SM.D.Fr (G B) *
            (SM.D.Fr.c B * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c B) -
          (SM.D.Fr.c B * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c B) *
            spinPart SM.D.Fr (G B)) ψ) +
        hP.P ψb ((SM.D.Fr.c B * spinPart SM.D.Fr (dM B) + spinPart SM.D.Fr (dM B) * SM.D.Fr.c B) ψ)))

theorem lorentz_rhs_cf (H : V) {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C)
    (a : Fin 4 → MatLie m) (ψ : S) (Dψ : Fin 4 → S) (ψb : S') (Dψb : Fin 4 → S')
    {M : Fin 4 → Fin 4 → ℝ} (hM : ∀ A B, M B A = -M A B) {dM : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hdM : ∀ B A C, dM B C A = -dM B A C) :
    hP.P (rDf SM.Db G a H ψb Dψb) ((-spinPart SM.D.Fr M) ψ) -
      hP.P ((-spinPart SM.Db.Fr M) ψb) (rDf SM.D G a H ψ Dψ) -
      ∑ C, (divEf G C * lorFl hP M ψ ψb C + lorFlD hP M dM ψ Dψ ψb Dψb C) =
      lorCF hP G a ψ Dψ ψb Dψb M dM := by
  rw [lorentz_rhs_R1 hP H G a ψ Dψ ψb Dψb hM,
    Finset.sum_congr rfl fun C _ => lorentz_rhs_flux hP hG a ψ Dψ ψb Dψb hM hdM C]
  unfold lorCF
  rw [Finset.sum_neg_distrib, sub_neg_eq_add, neg_add_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun B _ => ?_
  have hcB : ∀ x : S, spinPart SM.D.Fr M (SM.D.Fr.c B x) =
      SM.D.Fr.c B (spinPart SM.D.Fr M x) + ∑ d, (lorentzSign d * M B d) • SM.D.Fr.c d x := by
    intro x
    have h := comm_spinPart SM.D.Fr M (fun c d => hM c d) B
    rw [eps_D_eq] at h
    have := congrArg (fun F : Module.End ℝ S => F x) h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply] at this
    rw [← this]; abel
  simp only [LinearMap.add_apply, Module.End.mul_apply, map_add, hcB, map_sum, map_smul,
    smul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in
theorem lorentz_lhs_cf {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C)
    (a : Fin 4 → MatLie m) (ψ : S) (Dψ : Fin 4 → S) (ψb : S') (Dψb : Fin 4 → S')
    {M : Fin 4 → Fin 4 → ℝ} (hM : ∀ A B, M B A = -M A B) {dM : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hdM : ∀ B A C, dM B C A = -dM B A C) :
    varL hP a ψ Dψ ψb Dψb M (koszul (dOm lorentzSign (omG G) M 0 dM)) =
      lorCF hP G a ψ Dψ ψb Dψb M dM := by
  set X := covX SM.D G a ψ Dψ with hX
  set Xb := covX SM.Db G a ψb Dψb with hXb
  set δG := koszul (dOm lorentzSign (omG G) M 0 dM) with hδG
  have hWf : ∀ C, (fun x y => δG C x y - ∑ E, lorentzSign E * M C E * G E x y) =
      fun x y => rotN lorentzSign G M C x y + dM C x y := fun C => by
    funext x y; exact lorentz_W hG hM hdM C x y
  have hvX : ∀ C, varX SM.D a ψ Dψ M δG C = ∑ E, (lorentzSign E * M C E) • X E +
      (spinPart SM.D.Fr (rotN lorentzSign G M C) ψ + spinPart SM.D.Fr (dM C) ψ) := fun C => by
    rw [varX_eq SM.D G a ψ Dψ M δG C, hWf C, spinPart_add, LinearMap.add_apply]
  have hvXb : ∀ C, varX SM.Db a ψb Dψb M δG C = ∑ E, (lorentzSign E * M C E) • Xb E +
      (spinPart SM.Db.Fr (rotN lorentzSign G M C) ψb + spinPart SM.Db.Fr (dM C) ψb) := fun C => by
    rw [varX_eq SM.Db G a ψb Dψb M δG C, hWf C, spinPart_add, LinearMap.add_apply]
  have hPr : ∀ C, ∀ (φ : S') (x : S), hP.P (spinPart SM.Db.Fr (rotN lorentzSign G M C) φ) x =
      -hP.P φ (spinPart SM.D.Fr (rotN lorentzSign G M C) x) := fun C =>
    hP.P_spin _ (fun c d => rotN_anti hG hM C c d)
  have hPd : ∀ C, ∀ (φ : S') (x : S), hP.P (spinPart SM.Db.Fr (dM C) φ) x =
      -hP.P φ (spinPart SM.D.Fr (dM C) x) := fun C => hP.P_spin _ (fun c d => hdM C c d)
  unfold varL lorCF
  simp only [hvX, hvXb, map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, hPr, hPd]
  -- kinetic relabelling
  have hkin : ∑ C, lorentzSign C * ∑ E, lorentzSign E * M C E *
      (hP.P ψb (SM.D.Fr.c C (X E)) - hP.P (Xb E) (SM.D.Fr.c C ψ)) =
      ∑ B, lorentzSign B * (∑ d, lorentzSign d * M B d * hP.P (Xb B) (SM.D.Fr.c d ψ) -
        ∑ d, lorentzSign d * M B d * hP.P ψb (SM.D.Fr.c d (X B))) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hM B d]; ring
  -- the rotation part through the operator identity
  have e1 : ∑ x, lorentzSign x * (hP.P ψb (SM.D.Fr.c x (spinPart SM.D.Fr (rotN lorentzSign G M x) ψ)) +
      hP.P ψb (spinPart SM.D.Fr (rotN lorentzSign G M x) (SM.D.Fr.c x ψ))) =
      hP.P ψb ((∑ C, SM.D.Fr.ε C • (SM.D.Fr.c C * spinPart SM.D.Fr (rotN SM.D.Fr.ε G M C) +
        spinPart SM.D.Fr (rotN SM.D.Fr.ε G M C) * SM.D.Fr.c C)) ψ) := by
    rw [eps_D_eq]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul,
      LinearMap.add_apply, Module.End.mul_apply, map_add]
  have e2 : hP.P ψb ((∑ C, SM.D.Fr.ε C • ((∑ D, SM.D.Fr.ε D * G D C D) •
        (SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C) +
      (spinPart SM.D.Fr (G C) * (SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C) -
        (SM.D.Fr.c C * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c C) *
          spinPart SM.D.Fr (G C)))) ψ) =
      ∑ x, lorentzSign x * (divEf G x * (hP.P ψb ((SM.D.Fr.c x * spinPart SM.D.Fr M) ψ) +
        hP.P ψb ((spinPart SM.D.Fr M * SM.D.Fr.c x) ψ)) +
        hP.P ψb ((spinPart SM.D.Fr (G x) *
            (SM.D.Fr.c x * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c x) -
          (SM.D.Fr.c x * spinPart SM.D.Fr M + spinPart SM.D.Fr M * SM.D.Fr.c x) *
            spinPart SM.D.Fr (G x)) ψ)) := by
    rw [eps_D_eq]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul,
      LinearMap.add_apply, map_add, divEf]
  have hrot := e1.trans ((congrArg (fun F : Module.End ℝ S => hP.P ψb (F ψ))
    (lorentz_op SM.D.Fr hG hM)).trans e2)
  have hkin' : ∑ C, lorentzSign C * (∑ E, lorentzSign E * M C E * hP.P ψb (SM.D.Fr.c C (X E)) -
      ∑ E, lorentzSign E * M C E * hP.P (Xb E) (SM.D.Fr.c C ψ)) =
      ∑ B, lorentzSign B * (∑ d, lorentzSign d * M B d * hP.P (Xb B) (SM.D.Fr.c d ψ) -
        ∑ d, lorentzSign d * M B d * hP.P ψb (SM.D.Fr.c d (X B))) := by
    rw [← hkin]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun E _ => ?_
    ring
  calc _ = (1 / 2 : ℝ) * ∑ C, lorentzSign C *
          (∑ E, lorentzSign E * M C E * hP.P ψb (SM.D.Fr.c C (X E)) -
            ∑ E, lorentzSign E * M C E * hP.P (Xb E) (SM.D.Fr.c C ψ)) +
        (1 / 2 : ℝ) * ∑ x, lorentzSign x *
          (hP.P ψb (SM.D.Fr.c x (spinPart SM.D.Fr (rotN lorentzSign G M x) ψ)) +
            hP.P ψb (spinPart SM.D.Fr (rotN lorentzSign G M x) (SM.D.Fr.c x ψ))) +
        (1 / 2 : ℝ) * ∑ x, lorentzSign x *
          (hP.P ψb ((SM.D.Fr.c x * spinPart SM.D.Fr (dM x)) ψ) +
            hP.P ψb ((spinPart SM.D.Fr (dM x) * SM.D.Fr.c x) ψ)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Module.End.mul_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = _ := by
        rw [hkin', hrot]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

/-- **The local Lorentz identity of the Dirac density**: rotating the frame by a local Lorentz
rotation `δe_A = Σ_Dε_DM_{AD}e_D` (with frame derivatives `dM`) at fixed spinors changes the Dirac
Lagrangian by the Dirac residuals paired with the induced spin rotation `σ = -X_M`, minus the
frame divergence `div(e_C)Fl_C + e_C(Fl_C)` of the spin flux. -/
theorem lorentz_identity (H : V) {G : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hG : ∀ B A C, G B C A = -G B A C) (a : Fin 4 → MatLie m) (ψ : S) (Dψ : Fin 4 → S) (ψb : S')
    (Dψb : Fin 4 → S') {M : Fin 4 → Fin 4 → ℝ} (hM : ∀ A B, M B A = -M A B)
    {dM : Fin 4 → Fin 4 → Fin 4 → ℝ} (hdM : ∀ B A C, dM B C A = -dM B A C) :
    varL hP a ψ Dψ ψb Dψb M (koszul (dOm lorentzSign (omG G) M 0 dM)) =
      hP.P (rDf SM.Db G a H ψb Dψb) ((-spinPart SM.D.Fr M) ψ) -
        hP.P ((-spinPart SM.Db.Fr M) ψb) (rDf SM.D G a H ψ Dψ) -
        ∑ C, (divEf G C * lorFl hP M ψ ψb C + lorFlD hP M dM ψ Dψ ψb Dψb C) :=
  (lorentz_lhs_cf hP hG a ψ Dψ ψb Dψb hM hdM).trans
    (lorentz_rhs_cf hP H hG a ψ Dψ ψb Dψb hM hdM).symm

/-! #### The spinor rows -/

/-- **The `Ψ`-row of the Dirac density**: the variation of `L_D` along a spinor variation `φ`
(with frame derivatives `Dφ`) is minus the dual Dirac residual paired with `φ`, plus the frame
divergence of the flux `f_C = ½ε_C⟨Ψ̄, c_Cφ⟩`. -/
theorem psi_row (H : V) {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C)
    (a : Fin 4 → MatLie m) (ψb : S') (Dψb : Fin 4 → S') (φ : S) (Dφ : Fin 4 → S) :
    (1 / 2 : ℝ) * ∑ C, lorentzSign C * (hP.P ψb (SM.D.Fr.c C (covX SM.D G a φ Dφ C)) -
        hP.P (covX SM.Db G a ψb Dψb C) (SM.D.Fr.c C φ)) - hP.P ψb (mass SM.D.m0 SM.D.L H φ) =
      ∑ C, (divEf G C * ((1 / 2 : ℝ) * lorentzSign C * hP.P ψb (SM.D.Fr.c C φ)) +
        (1 / 2 : ℝ) * lorentzSign C * (hP.P (Dψb C) (SM.D.Fr.c C φ) +
          hP.P ψb (SM.D.Fr.c C (Dφ C)))) - hP.P (rDf SM.Db G a H ψb Dψb) φ := by
  have hPG : ∀ C, ∀ (φ' : S') (x : S), hP.P (spinPart SM.Db.Fr (G C) φ') x =
      -hP.P φ' (spinPart SM.D.Fr (G C) x) := fun C => hP.P_spin _ (fun c d => hG C c d)
  have hcl : ∀ C, ∀ x : S, spinPart SM.D.Fr (G C) (SM.D.Fr.c C x) =
      SM.D.Fr.c C (spinPart SM.D.Fr (G C) x) + ∑ d, (lorentzSign d * G C C d) • SM.D.Fr.c d x := by
    intro C x
    have h := comm_spinPart SM.D.Fr (G C) (fun c d => hG C c d) C
    rw [eps_D_eq] at h
    have := congrArg (fun F : Module.End ℝ S => F x) h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply] at this
    rw [← this]; abel
  have hρc : ∀ C, ∀ x : S, SM.D.ρ (a C) (SM.D.Fr.c C x) = SM.D.Fr.c C (SM.D.ρ (a C) x) := by
    intro C x
    have := congrArg (fun F : Module.End ℝ S => F x) (SM.D.comm (a C) C)
    simpa using this
  -- the frame-divergence terms
  have hdiv : ∑ C, lorentzSign C * ∑ d, lorentzSign d * G C C d * hP.P ψb (SM.D.Fr.c d φ) =
      -∑ C, lorentzSign C * divEf G C * hP.P ψb (SM.D.Fr.c C φ) := by
    simp only [Finset.mul_sum, divEf]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [hG C C d]; ring
  have hpt : ∀ x, (1 / 2 : ℝ) * (lorentzSign x * (hP.P ψb (SM.D.Fr.c x (covX SM.D G a φ Dφ x)) -
      hP.P (covX SM.Db G a ψb Dψb x) (SM.D.Fr.c x φ))) -
      (divEf G x * ((1 / 2 : ℝ) * lorentzSign x * hP.P ψb (SM.D.Fr.c x φ)) +
        (1 / 2 : ℝ) * lorentzSign x * (hP.P (Dψb x) (SM.D.Fr.c x φ) +
          hP.P ψb (SM.D.Fr.c x (Dφ x)))) +
      lorentzSign x * hP.P (covX SM.Db G a ψb Dψb x) (SM.D.Fr.c x φ) =
      -(1 / 2 : ℝ) * (lorentzSign x * ∑ d, lorentzSign d * G x x d * hP.P ψb (SM.D.Fr.c d φ) +
        lorentzSign x * divEf G x * hP.P ψb (SM.D.Fr.c x φ)) := by
    intro x
    simp only [covX, map_add, map_sub, map_sum, map_smul, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hPG, hP.ρ_tr,
      hcl, hρc]
    ring
  have hRdf : hP.P (rDf SM.Db G a H ψb Dψb) φ =
      ∑ x, lorentzSign x * hP.P (covX SM.Db G a ψb Dψb x) (SM.D.Fr.c x φ) +
        hP.P ψb (mass SM.D.m0 SM.D.L H φ) := by
    unfold rDf
    simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hP.c_tr, P_mass hP]
    ring
  rw [hRdf, ← sub_eq_zero]
  have hsum : (1 / 2 : ℝ) * ∑ C, lorentzSign C * (hP.P ψb (SM.D.Fr.c C (covX SM.D G a φ Dφ C)) -
        hP.P (covX SM.Db G a ψb Dψb C) (SM.D.Fr.c C φ)) -
      ∑ C, (divEf G C * ((1 / 2 : ℝ) * lorentzSign C * hP.P ψb (SM.D.Fr.c C φ)) +
        (1 / 2 : ℝ) * lorentzSign C * (hP.P (Dψb C) (SM.D.Fr.c C φ) +
          hP.P ψb (SM.D.Fr.c C (Dφ C)))) +
      ∑ x, lorentzSign x * hP.P (covX SM.Db G a ψb Dψb x) (SM.D.Fr.c x φ) =
      -(1 / 2 : ℝ) * (∑ x, lorentzSign x * ∑ d, lorentzSign d * G x x d * hP.P ψb (SM.D.Fr.c d φ) +
        ∑ x, lorentzSign x * divEf G x * hP.P ψb (SM.D.Fr.c x φ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => hpt x
  rw [hdiv, neg_add_cancel, mul_zero] at hsum
  linear_combination hsum

/-- The frame-divergence cancellation of the spinor rows. -/
theorem div_cancel {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C) (f : Fin 4 → ℝ) :
    ∑ x, lorentzSign x * ∑ d, lorentzSign d * G x x d * f d +
      ∑ x, lorentzSign x * divEf G x * f x = 0 := by
  have h : ∑ x, lorentzSign x * ∑ d, lorentzSign d * G x x d * f d =
      -∑ x, lorentzSign x * divEf G x * f x := by
    simp only [Finset.mul_sum, divEf]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [hG C C d]; ring
  rw [h, neg_add_cancel]

/-- **The `Ψ̄`-row of the Dirac density**: the variation of `L_D` along a co-spinor variation `φ̄`
is the Dirac residual paired with `φ̄`, minus the frame divergence of the flux
`f̄_C = ½ε_C⟨φ̄, c_CΨ⟩`. -/
theorem psib_row (H : V) {G : Fin 4 → Fin 4 → Fin 4 → ℝ} (hG : ∀ B A C, G B C A = -G B A C)
    (a : Fin 4 → MatLie m) (ψ : S) (Dψ : Fin 4 → S) (φb : S') (Dφb : Fin 4 → S') :
    (1 / 2 : ℝ) * ∑ C, lorentzSign C * (hP.P φb (SM.D.Fr.c C (covX SM.D G a ψ Dψ C)) -
        hP.P (covX SM.Db G a φb Dφb C) (SM.D.Fr.c C ψ)) - hP.P φb (mass SM.D.m0 SM.D.L H ψ) =
      hP.P φb (rDf SM.D G a H ψ Dψ) -
        ∑ C, (divEf G C * ((1 / 2 : ℝ) * lorentzSign C * hP.P φb (SM.D.Fr.c C ψ)) +
          (1 / 2 : ℝ) * lorentzSign C * (hP.P (Dφb C) (SM.D.Fr.c C ψ) +
            hP.P φb (SM.D.Fr.c C (Dψ C)))) := by
  have hPG : ∀ C, ∀ (φ' : S') (x : S), hP.P (spinPart SM.Db.Fr (G C) φ') x =
      -hP.P φ' (spinPart SM.D.Fr (G C) x) := fun C => hP.P_spin _ (fun c d => hG C c d)
  have hcl : ∀ C, ∀ x : S, spinPart SM.D.Fr (G C) (SM.D.Fr.c C x) =
      SM.D.Fr.c C (spinPart SM.D.Fr (G C) x) + ∑ d, (lorentzSign d * G C C d) • SM.D.Fr.c d x := by
    intro C x
    have h := comm_spinPart SM.D.Fr (G C) (fun c d => hG C c d) C
    rw [eps_D_eq] at h
    have := congrArg (fun F : Module.End ℝ S => F x) h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply] at this
    rw [← this]; abel
  have hρc : ∀ C, ∀ x : S, SM.D.ρ (a C) (SM.D.Fr.c C x) = SM.D.Fr.c C (SM.D.ρ (a C) x) := by
    intro C x
    have := congrArg (fun F : Module.End ℝ S => F x) (SM.D.comm (a C) C)
    simpa using this
  have hpt : ∀ x, (1 / 2 : ℝ) * (lorentzSign x * (hP.P φb (SM.D.Fr.c x (covX SM.D G a ψ Dψ x)) -
      hP.P (covX SM.Db G a φb Dφb x) (SM.D.Fr.c x ψ))) -
      lorentzSign x * hP.P φb (SM.D.Fr.c x (covX SM.D G a ψ Dψ x)) +
      (divEf G x * ((1 / 2 : ℝ) * lorentzSign x * hP.P φb (SM.D.Fr.c x ψ)) +
        (1 / 2 : ℝ) * lorentzSign x * (hP.P (Dφb x) (SM.D.Fr.c x ψ) +
          hP.P φb (SM.D.Fr.c x (Dψ x)))) =
      (1 / 2 : ℝ) * (lorentzSign x * ∑ d, lorentzSign d * G x x d * hP.P φb (SM.D.Fr.c d ψ) +
        lorentzSign x * divEf G x * hP.P φb (SM.D.Fr.c x ψ)) := by
    intro x
    simp only [covX, map_add, map_sum, map_smul, LinearMap.add_apply, smul_eq_mul, hPG, hP.ρ_tr,
      hcl, hρc]
    ring
  have hRdf : hP.P φb (rDf SM.D G a H ψ Dψ) =
      ∑ x, lorentzSign x * hP.P φb (SM.D.Fr.c x (covX SM.D G a ψ Dψ x)) -
        hP.P φb (mass SM.D.m0 SM.D.L H ψ) := by
    unfold rDf
    simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  rw [hRdf, ← sub_eq_zero]
  have hsum : (1 / 2 : ℝ) * ∑ C, lorentzSign C * (hP.P φb (SM.D.Fr.c C (covX SM.D G a ψ Dψ C)) -
        hP.P (covX SM.Db G a φb Dφb C) (SM.D.Fr.c C ψ)) -
      ∑ x, lorentzSign x * hP.P φb (SM.D.Fr.c x (covX SM.D G a ψ Dψ x)) +
      ∑ C, (divEf G C * ((1 / 2 : ℝ) * lorentzSign C * hP.P φb (SM.D.Fr.c C ψ)) +
        (1 / 2 : ℝ) * lorentzSign C * (hP.P (Dφb C) (SM.D.Fr.c C ψ) +
          hP.P φb (SM.D.Fr.c C (Dψ C)))) =
      (1 / 2 : ℝ) * (∑ x, lorentzSign x * ∑ d, lorentzSign d * G x x d * hP.P φb (SM.D.Fr.c d ψ) +
        ∑ x, lorentzSign x * divEf G x * hP.P φb (SM.D.Fr.c x ψ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => hpt x
  rw [div_cancel hG (fun d => hP.P φb (SM.D.Fr.c d ψ)), mul_zero] at hsum
  linear_combination hsum

/-! #### The general frame variation -/

theorem varX_add {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (a : Fin 4 → MatLie m) (ψ : S₀) (Dψ : Fin 4 → S₀) (Λ Λ' : Fin 4 → Fin 4 → ℝ)
    (δG δG' : Fin 4 → Fin 4 → Fin 4 → ℝ) (C : Fin 4) :
    varX D a ψ Dψ (fun x y => Λ x y + Λ' x y) (fun x y z => δG x y z + δG' x y z) C =
      varX D a ψ Dψ Λ δG C + varX D a ψ Dψ Λ' δG' C := by
  unfold varX
  have hs : spinPart D.Fr (fun y z => δG C y z + δG' C y z) = spinPart D.Fr (δG C) +
      spinPart D.Fr (δG' C) := spinPart_add D.Fr (δG C) (δG' C)
  rw [hs, LinearMap.add_apply]
  simp only [mul_add, add_smul, Finset.sum_add_distrib]
  abel

theorem varL_add (a : Fin 4 → MatLie m) (ψ : S) (Dψ : Fin 4 → S) (ψb : S') (Dψb : Fin 4 → S')
    (Λ Λ' : Fin 4 → Fin 4 → ℝ) (δG δG' : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    varL hP a ψ Dψ ψb Dψb (fun x y => Λ x y + Λ' x y) (fun x y z => δG x y z + δG' x y z) =
      varL hP a ψ Dψ ψb Dψb Λ δG + varL hP a ψ Dψ ψb Dψb Λ' δG' := by
  unfold varL
  simp only [varX_add, map_add, LinearMap.add_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun C _ => ?_
  ring

/-- **The frame variation of the Dirac density** (general `δe_A = Σ_Dε_DΛ_{AD}e_D`, metric
variation `k_{AB} = -(Λ_{AB} + Λ_{BA})`, frame derivatives `dΛ`): with the antisymmetric part
`M = ½(Λ - Λᵀ)` and `dM = ½(dΛ - dΛ^{T₂₃})`,
`½tr(k)L_D + δL_D = ½Σε_Aε_BT_{AB}k_{AB} + ⟨r̄_D, σΨ⟩ - ⟨σ̄Ψ̄, r_D⟩ - Σ_C(div(e_C)Fl_C + e_C(Fl_C))`,
`σ = -X_M`: the Hilbert stress plus Dirac-residual terms plus a frame divergence. -/
theorem frame_variation (H : V) {G : Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hG : ∀ B A C, G B C A = -G B A C) (a : Fin 4 → MatLie m) (ψ : S) (Dψ : Fin 4 → S) (ψb : S')
    (Dψb : Fin 4 → S') (Λ : Fin 4 → Fin 4 → ℝ) (dΛ : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (1 / 2 : ℝ) * (∑ A, lorentzSign A * (-(Λ A A + Λ A A))) *
        lagD SM.D hP.P H ψ (covX SM.D G a ψ Dψ) ψb (covX SM.Db G a ψb Dψb) +
      varL hP a ψ Dψ ψb Dψb Λ
        (koszul (dOm lorentzSign (omG G) Λ (fun A B => -(Λ A B + Λ B A)) dΛ)) =
      (1 / 2 : ℝ) * ∑ A, ∑ B, lorentzSign A * lorentzSign B *
          (symTD SM.D hP.P).frame H ψ (covX SM.D G a ψ Dψ) ψb (covX SM.Db G a ψb Dψb) A B *
            (-(Λ A B + Λ B A)) +
        (hP.P (rDf SM.Db G a H ψb Dψb) ((-spinPart SM.D.Fr (fun A B => (1 / 2 : ℝ) * (Λ A B - Λ B A))) ψ) -
          hP.P ((-spinPart SM.Db.Fr (fun A B => (1 / 2 : ℝ) * (Λ A B - Λ B A))) ψb)
            (rDf SM.D G a H ψ Dψ) -
          ∑ C, (divEf G C * lorFl hP (fun A B => (1 / 2 : ℝ) * (Λ A B - Λ B A)) ψ ψb C +
            lorFlD hP (fun A B => (1 / 2 : ℝ) * (Λ A B - Λ B A))
              (fun B A C => (1 / 2 : ℝ) * (dΛ B A C - dΛ B C A)) ψ Dψ ψb Dψb C)) := by
  set k : Fin 4 → Fin 4 → ℝ := fun A B => -(Λ A B + Λ B A) with hk
  set M : Fin 4 → Fin 4 → ℝ := fun A B => (1 / 2 : ℝ) * (Λ A B - Λ B A) with hMd
  set dk : Fin 4 → Fin 4 → Fin 4 → ℝ := fun B A C => -(dΛ B A C + dΛ B C A) with hdk
  set dM : Fin 4 → Fin 4 → Fin 4 → ℝ := fun B A C => (1 / 2 : ℝ) * (dΛ B A C - dΛ B C A) with hdMd
  have hks : ∀ A B, k B A = k A B := fun A B => by simp only [hk]; ring
  have hdks : ∀ B A C, dk B C A = dk B A C := fun B A C => by simp only [hdk]; ring
  have hMa : ∀ A B, M B A = -M A B := fun A B => by simp only [hMd]; ring
  have hdMa : ∀ B A C, dM B C A = -dM B A C := fun B A C => by simp only [hdMd]; ring
  have hΛp : ∀ x y, Λ x y = -(1 / 2 : ℝ) * k x y + M x y := fun x y => by
    simp only [hk, hMd]; ring
  have hdΛp : ∀ x y z, dΛ x y z = -(1 / 2 : ℝ) * dk x y z + dM x y z := fun x y z => by
    simp only [hdk, hdMd]; ring
  have hΛ : Λ = fun x y => (fun x y => -(1 / 2 : ℝ) * k x y) x y + M x y := by
    funext x y; exact hΛp x y
  have hdOm : koszul (dOm lorentzSign (omG G) Λ k dΛ) = fun x y z =>
      koszul (dOm lorentzSign (omG G) (fun x y => -(1 / 2 : ℝ) * k x y) k
        (fun x y z => -(1 / 2 : ℝ) * dk x y z)) x y z +
      koszul (dOm lorentzSign (omG G) M 0 dM) x y z := by
    funext x y z
    rw [← koszul_add]
    congr 1
    funext B A C
    unfold dOm
    have hsum : ∑ D, lorentzSign D * (omG G B A D * k D C + Λ B D * omG G D A C +
        Λ A D * omG G B D C + omG G B A D * Λ C D) =
        ∑ D, lorentzSign D * (omG G B A D * k D C + -(1 / 2 : ℝ) * k B D * omG G D A C +
          -(1 / 2 : ℝ) * k A D * omG G B D C + omG G B A D * (-(1 / 2 : ℝ) * k C D)) +
        ∑ D, lorentzSign D * (omG G B A D * (0 : Fin 4 → Fin 4 → ℝ) D C + M B D * omG G D A C +
          M A D * omG G B D C + omG G B A D * M C D) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun D _ => ?_
      rw [hΛp B D, hΛp A D, hΛp C D]
      simp only [Pi.zero_apply]
      ring
    rw [hsum, hdΛp B A C, hdΛp A B C]
    ring
  have htr : (∑ A, lorentzSign A * (-(Λ A A + Λ A A))) = ∑ A, lorentzSign A * k A A := rfl
  rw [htr, hdOm]
  conv_lhs => rw [hΛ]
  rw [varL_add, ← add_assoc, sym_identity hP H hG a ψ Dψ ψb Dψb hks hdks,
    lorentz_identity hP H hG a ψ Dψ ψb Dψb hMa hdMa]

end Pairing









end RenewalGeometry.GenDAlg
