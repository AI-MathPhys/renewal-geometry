/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.CommonOriginBalance
import NCG.Upstream.PrimitiveWeight
import NCG.Algebra.ChoiCriterion

/-!
# The common-origin resolved instrument: UCP law, marginal, deck

Operator layer of the common-origin model
(`prop:common-origin-ucp` and the internal-map self-adjointness
clause of `thm:common-origin-balance` in `manuscripts/renewal_emergence/renewal_emergence.tex`).

The resolved observable algebra is `Obs ι = C(Ω_Λ) ⊗ M₄(ℂ)`
realized as matrix-valued configuration observables.  The resolved
Heisenberg branch (`eq:common-origin-branch`) is

`(K̂_{i,s,a,b} F)(η) = ν_i q_i(s|η) r_{i,a}(η_i s) κ_b Ψ_{a,b}(F(η^{i,s}))`.

We prove, with the internal maps `Ψ_{a,b}` abstracted by their
matrix complete positivity / unitality hypotheses (instantiated
below by `adMap`/`trMap`):

* `w_nonneg`, `branch_posSemidef`, `branch_cp` — every branch is
  positive and completely positive: its extension by a `k`-level
  ancilla preserves pointwise positive semidefiniteness;
* `totalChannel_scalar` — on scalar observables `f ⊗ 1` the total
  channel acts as `(K_Λ f) ⊗ 1` with `K_Λ` the random-scan Ising
  heat-bath channel (`heatBath`);
* `totalChannel_unital` — `K̂_Λ(1) = 1` (UCP normalization, using
  `Σν = 1`, `Σκ = 1`, `Σ_a r = 1`, and the heat-bath `Σ_s q = 1`);
* `branch_deck` — deck covariance `Θ K̂_{i,s,a,b} = K̂_{i,−s,a,b} Θ`;
* `adMap_*` / `trMap_*` — the manuscript's internal maps
  `Ad(R_a)`, `Ad(JR_a)`, `τ_S(·)1` are unital, completely positive
  (via the Choi criterion) and self-adjoint for the Hilbert–Schmidt
  trace pairing (`adMap_hs_selfadjoint` covers both the Hermitian
  `R_a` and the skew-Hermitian `J R_a`, `trMap_hs_selfadjoint` the
  tracial mode) — the internal-map clause of
  `thm:common-origin-balance`.
-/

namespace NCG.CommonOrigin

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The resolved observable algebra `C(Ω_Λ) ⊗ M₄(ℂ)`, realized as
matrix-valued configuration observables. -/
abbrev Obs (ι : Type*) := (ι → ℝ) → Matrix (Fin 4) (Fin 4) ℂ

/-- Positive semidefiniteness is preserved by nonnegative real
scalars (arbitrary index type). -/
theorem posSemidef_ofReal_smul {n : Type*}
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (((c : ℝ) : ℂ) • A).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 : star ((c : ℝ) : ℂ) = ((c : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    have h2 : Aᴴ = A := hA.1
    change (((c : ℝ) : ℂ) • A)ᴴ = ((c : ℝ) : ℂ) • A
    rw [Matrix.conjTranspose_smul, h1, h2]
  · have h2 := hA.2 x
    have h3 : (x.sum fun i xi => x.sum fun j xj =>
        star xi * (((c : ℝ) : ℂ) • A) i j * xj)
        = ((c : ℝ) : ℂ) * (x.sum fun i xi => x.sum fun j xj =>
            star xi * A i j * xj) := by
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun i _ => ?_
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun j _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [h3]
    refine mul_nonneg ?_ h2
    exact_mod_cast hc

namespace IsingData

variable (D : IsingData ι)

/-- **The resolved Heisenberg branch** `K̂_{i,s,a,b}`
(`eq:common-origin-branch`). -/
noncomputable def branch (ν : ι → ℝ) (r : ι → Fin 3 → ℝ → ℝ)
    (κ : Fin 3 → ℝ)
    (Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ))
    (i : ι) (s : ℝ) (a b : Fin 3) (F : Obs ι) : Obs ι :=
  fun η => ((D.w ν r κ i s a b η : ℝ) : ℂ)
    • Ψ a b (F (Function.update η i s))

/-- The complete resolved channel `K̂_Λ = Σ_{i,s,a,b} K̂_{i,s,a,b}`
(redraw values `s = ±1`). -/
noncomputable def totalChannel (ν : ι → ℝ) (r : ι → Fin 3 → ℝ → ℝ)
    (κ : Fin 3 → ℝ)
    (Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ))
    (F : Obs ι) : Obs ι :=
  fun η => ∑ i, ∑ a, ∑ b,
    (D.branch ν r κ Ψ i 1 a b F η
      + D.branch ν r κ Ψ i (-1) a b F η)

omit [DecidableEq ι] [Fintype ι] in
/-- The resolved transition weight is nonnegative on the spin box. -/
theorem w_nonneg {ν : ι → ℝ} {r : ι → Fin 3 → ℝ → ℝ}
    {κ : Fin 3 → ℝ} (hν : ∀ i, 0 ≤ ν i)
    (hr : ∀ i a u, |u| ≤ 1 → 0 ≤ r i a u) (hκ : ∀ b, 0 ≤ κ b)
    (i : ι) (a b : Fin 3) {s : ℝ} (hs : |s| ≤ 1) {η : ι → ℝ}
    (hη : ∀ j, |η j| ≤ 1) :
    0 ≤ D.w ν r κ i s a b η := by
  have hu : |η i * s| ≤ 1 := by
    rw [abs_mul]
    calc |η i| * |s| ≤ 1 * 1 :=
      mul_le_mul (hη i) hs (abs_nonneg s) zero_le_one
    _ = 1 := mul_one 1
  rw [w]
  exact mul_nonneg (mul_nonneg (mul_nonneg (hν i)
    (D.q_pos i s η).le) (hr i a _ hu)) (hκ b)

omit [Fintype ι] in
/-- **Proposition `prop:common-origin-ucp` (positivity)**: every
resolved branch preserves pointwise positive semidefiniteness. -/
theorem branch_posSemidef {ν : ι → ℝ} {r : ι → Fin 3 → ℝ → ℝ}
    {κ : Fin 3 → ℝ}
    {Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)}
    (hν : ∀ i, 0 ≤ ν i) (hr : ∀ i a u, |u| ≤ 1 → 0 ≤ r i a u)
    (hκ : ∀ b, 0 ≤ κ b) (i : ι) (a b : Fin 3)
    (hΨ : ∀ X : Matrix (Fin 4) (Fin 4) ℂ,
      X.PosSemidef → (Ψ a b X).PosSemidef)
    {s : ℝ} (hs : |s| ≤ 1) {F : Obs ι}
    (hF : ∀ η', (F η').PosSemidef) {η : ι → ℝ}
    (hη : ∀ j, |η j| ≤ 1) :
    (D.branch ν r κ Ψ i s a b F η).PosSemidef :=
  posSemidef_ofReal_smul
    (hΨ _ (hF _)) (D.w_nonneg hν hr hκ i a b hs hη)

omit [Fintype ι] in
/-- **Proposition `prop:common-origin-ucp` (complete positivity)**:
the extension of every resolved branch by the identity on a
`k`-level complex ancilla preserves pointwise positive
semidefiniteness — the branch is CP. -/
theorem branch_cp {ν : ι → ℝ} {r : ι → Fin 3 → ℝ → ℝ}
    {κ : Fin 3 → ℝ}
    {Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)}
    (hν : ∀ i, 0 ≤ ν i) (hr : ∀ i a u, |u| ≤ 1 → 0 ≤ r i a u)
    (hκ : ∀ b, 0 ≤ κ b) (i : ι) (a b : Fin 3)
    (hΨ : IsMatrixCompletelyPositive (Ψ a b)) (k : ℕ)
    {s : ℝ} (hs : |s| ≤ 1)
    (G : (ι → ℝ) → Matrix (Fin k × Fin 4) (Fin k × Fin 4) ℂ)
    (hG : ∀ η', (G η').PosSemidef) {η : ι → ℝ}
    (hη : ∀ j, |η j| ≤ 1) :
    (((D.w ν r κ i s a b η : ℝ) : ℂ)
      • ampliate k (Ψ a b) (G (Function.update η i s))).PosSemidef :=
  posSemidef_ofReal_smul
    (hΨ k (G (Function.update η i s)) (hG _))
    (D.w_nonneg hν hr hκ i a b hs hη)

/-- The classical random-scan Ising heat-bath channel `K_Λ`. -/
noncomputable def heatBath (ν : ι → ℝ) (f : (ι → ℝ) → ℂ) :
    (ι → ℝ) → ℂ :=
  fun η => ∑ i,
    ((((ν i * D.q i 1 η : ℝ)) : ℂ) * f (Function.update η i 1)
      + (((ν i * D.q i (-1) η : ℝ)) : ℂ)
          * f (Function.update η i (-1)))

omit [DecidableEq ι] [Fintype ι] in
/-- The branch weights collapse over the direction and internal
records: `Σ_{a,b} w_{i,s,a,b}(η) = ν_i q_i(s|η)`. -/
theorem w_sum_records {ν : ι → ℝ} {r : ι → Fin 3 → ℝ → ℝ}
    {κ : Fin 3 → ℝ} (hκ1 : ∑ b, κ b = 1)
    (hr1 : ∀ i u, |u| ≤ 1 → ∑ a, r i a u = 1) (i : ι) {s : ℝ}
    (hs : |s| ≤ 1) {η : ι → ℝ} (hη : ∀ j, |η j| ≤ 1) :
    ∑ a, ∑ b, D.w ν r κ i s a b η = ν i * D.q i s η := by
  have hu : |η i * s| ≤ 1 := by
    rw [abs_mul]
    calc |η i| * |s| ≤ 1 * 1 :=
      mul_le_mul (hη i) hs (abs_nonneg s) zero_le_one
    _ = 1 := mul_one 1
  have h1 : ∀ a : Fin 3, ∑ b, D.w ν r κ i s a b η
      = ν i * D.q i s η * r i a (η i * s) := by
    intro a
    have h2 : ∑ b, D.w ν r κ i s a b η
        = ∑ b, (ν i * D.q i s η * r i a (η i * s)) * κ b := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [w]
    rw [h2, ← Finset.mul_sum, hκ1, mul_one]
  rw [Finset.sum_congr rfl fun a _ => h1 a]
  have h3 : ∑ a, ν i * D.q i s η * r i a (η i * s)
      = (ν i * D.q i s η) * ∑ a, r i a (η i * s) := by
    rw [Finset.mul_sum]
  rw [h3, hr1 i _ hu, mul_one]

/-- **Proposition `prop:common-origin-ucp` (scalar marginal)**: on
scalar observables `f ⊗ 1` the complete channel acts as
`(K_Λ f) ⊗ 1` with `K_Λ` the random-scan heat-bath channel. -/
theorem totalChannel_scalar {ν : ι → ℝ} {r : ι → Fin 3 → ℝ → ℝ}
    {κ : Fin 3 → ℝ}
    {Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)}
    (hΨ1 : ∀ a b, Ψ a b 1 = 1) (hκ1 : ∑ b, κ b = 1)
    (hr1 : ∀ i u, |u| ≤ 1 → ∑ a, r i a u = 1)
    (f : (ι → ℝ) → ℂ) {η : ι → ℝ} (hη : ∀ j, |η j| ≤ 1) :
    D.totalChannel ν r κ Ψ (fun η' => f η' • 1) η
      = D.heatBath ν f η • 1 := by
  have habs1 : |(1 : ℝ)| ≤ 1 := by norm_num
  have habs2 : |(-1 : ℝ)| ≤ 1 := by norm_num
  have hbr : ∀ (i : ι) (s : ℝ) (a b : Fin 3),
      D.branch ν r κ Ψ i s a b (fun η' => f η' • 1) η
        = (((D.w ν r κ i s a b η : ℝ) : ℂ)
            * f (Function.update η i s)) • 1 := by
    intro i s a b
    change ((D.w ν r κ i s a b η : ℝ) : ℂ)
        • Ψ a b (f (Function.update η i s) • 1) = _
    rw [map_smul, hΨ1, smul_smul]
  have hcollapse : ∀ (i : ι) (s : ℝ), |s| ≤ 1 →
      ∑ a, ∑ b, (((D.w ν r κ i s a b η : ℝ) : ℂ)
          * f (Function.update η i s))
        = ((ν i * D.q i s η : ℝ) : ℂ)
            * f (Function.update η i s) := by
    intro i s hs
    have h4 : ∑ a, ∑ b, (((D.w ν r κ i s a b η : ℝ) : ℂ)
        * f (Function.update η i s))
        = (∑ a, ∑ b, ((D.w ν r κ i s a b η : ℝ) : ℂ))
            * f (Function.update η i s) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
    have h5 : (∑ a, ∑ b, ((D.w ν r κ i s a b η : ℝ) : ℂ))
        = ((ν i * D.q i s η : ℝ) : ℂ) := by
      have h6 := D.w_sum_records (ν := ν) hκ1 hr1 i hs hη
      push_cast [← h6]
      norm_cast
    rw [h4, h5]
  change ∑ i, ∑ a, ∑ b,
      (D.branch ν r κ Ψ i 1 a b (fun η' => f η' • 1) η
        + D.branch ν r κ Ψ i (-1) a b (fun η' => f η' • 1) η)
      = D.heatBath ν f η • 1
  have hstep : ∀ i : ι, ∑ a, ∑ b,
      (D.branch ν r κ Ψ i 1 a b (fun η' => f η' • 1) η
        + D.branch ν r κ Ψ i (-1) a b (fun η' => f η' • 1) η)
      = ((((ν i * D.q i 1 η : ℝ)) : ℂ)
          * f (Function.update η i 1)
        + (((ν i * D.q i (-1) η : ℝ)) : ℂ)
            * f (Function.update η i (-1))) • 1 := by
    intro i
    have h7 : ∀ (a b : Fin 3),
        D.branch ν r κ Ψ i 1 a b (fun η' => f η' • 1) η
          + D.branch ν r κ Ψ i (-1) a b (fun η' => f η' • 1) η
        = ((((D.w ν r κ i 1 a b η : ℝ) : ℂ)
              * f (Function.update η i 1))
            + (((D.w ν r κ i (-1) a b η : ℝ) : ℂ)
                * f (Function.update η i (-1)))) • 1 := by
      intro a b
      rw [hbr, hbr, add_smul]
    rw [Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => h7 a b]
    simp only [← Finset.sum_smul]
    congr 1
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) =>
      Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
    rw [hcollapse i 1 habs1, hcollapse i (-1) habs2]
  rw [Finset.sum_congr rfl fun i _ => hstep i]
  rw [← Finset.sum_smul]
  rfl

/-- **Proposition `prop:common-origin-ucp` (UCP normalization)**:
the complete resolved channel is unital. -/
theorem totalChannel_unital {ν : ι → ℝ} {r : ι → Fin 3 → ℝ → ℝ}
    {κ : Fin 3 → ℝ}
    {Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)}
    (hΨ1 : ∀ a b, Ψ a b 1 = 1) (hν1 : ∑ i, ν i = 1)
    (hκ1 : ∑ b, κ b = 1)
    (hr1 : ∀ i u, |u| ≤ 1 → ∑ a, r i a u = 1)
    {η : ι → ℝ} (hη : ∀ j, |η j| ≤ 1) :
    D.totalChannel ν r κ Ψ (1 : Obs ι) η = 1 := by
  have h1 : (1 : Obs ι) = fun _ => (1 : ℂ) • 1 := by
    funext η'
    rw [one_smul]
    rfl
  rw [h1, D.totalChannel_scalar hΨ1 hκ1 hr1 (fun _ => 1) hη]
  have h2 : D.heatBath ν (fun _ => (1 : ℂ)) η = 1 := by
    rw [heatBath]
    have h3 : ∀ i : ι,
        (((ν i * D.q i 1 η : ℝ)) : ℂ) * 1
          + (((ν i * D.q i (-1) η : ℝ)) : ℂ) * 1
        = ((ν i : ℝ) : ℂ) := by
      intro i
      rw [mul_one, mul_one]
      push_cast
      have h4 := D.q_sum i η
      have h5 : (D.q i 1 η : ℂ) + (D.q i (-1) η : ℂ)
          = ((1 : ℝ) : ℂ) := by
        exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) h4
      calc (ν i : ℂ) * (D.q i 1 η : ℂ)
            + (ν i : ℂ) * (D.q i (-1) η : ℂ)
          = (ν i : ℂ) * ((D.q i 1 η : ℂ) + (D.q i (-1) η : ℂ))
            := by ring
        _ = (ν i : ℂ) * 1 := by rw [h5]; norm_num
        _ = (ν i : ℂ) := mul_one _
    rw [Finset.sum_congr rfl fun i _ => h3 i]
    have h6 : ∑ i, ((ν i : ℝ) : ℂ) = ((∑ i, ν i : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [h6, hν1]
    norm_num
  rw [h2, one_smul]

/-- Deck reversal on resolved observables `(ΘF)(η) = F(−η)`. -/
def deck (F : Obs ι) : Obs ι := fun η => F (-η)

omit [Fintype ι] in
/-- **Proposition `prop:common-origin-ucp` (deck covariance)**:
`Θ K̂_{i,s,a,b} = K̂_{i,−s,a,b} Θ` — the record transforms as
`(s,a,b) ↦ (−s,a,b)` under deck reversal. -/
theorem branch_deck {ν : ι → ℝ} {r : ι → Fin 3 → ℝ → ℝ}
    {κ : Fin 3 → ℝ}
    {Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)}
    (i : ι) (s : ℝ) (a b : Fin 3) (F : Obs ι) :
    deck (D.branch ν r κ Ψ i s a b F)
      = D.branch ν r κ Ψ i (-s) a b (deck F) := by
  funext η
  change ((D.w ν r κ i s a b (-η) : ℝ) : ℂ)
      • Ψ a b (F (Function.update (-η) i s))
    = ((D.w ν r κ i (-s) a b η : ℝ) : ℂ)
        • Ψ a b (F (-(Function.update η i (-s))))
  have hw : D.w ν r κ i s a b (-η) = D.w ν r κ i (-s) a b η := by
    rw [w, w, D.q_deck]
    have harg : (-η) i * s = η i * -s := by
      rw [Pi.neg_apply]
      ring
    rw [harg]
  rw [hw, update_neg]

end IsingData

/-! ## The internal maps: `Ad(R_a)`, `Ad(JR_a)`, `τ_S(·)1` -/

/-- Unitary conjugation `Ad(U)(X) = U X Uᴴ` as a linear map. -/
noncomputable def adMap (U : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun X := U * X * Uᴴ
  map_add' X Y := by
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

@[simp] theorem adMap_apply (U X : Matrix (Fin 4) (Fin 4) ℂ) :
    adMap U X = U * X * Uᴴ := rfl

/-- The tracial internal mode `Ψ_{a,2}(X) = τ_S(X) 1 = (Tr X / 4) 1`
as a linear map. -/
noncomputable def trMap :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun X := (X.trace / 4) • 1
  map_add' X Y := by
    rw [Matrix.trace_add, add_div, add_smul]
  map_smul' c X := by
    rw [Matrix.trace_smul, smul_eq_mul, mul_div_assoc, mul_smul,
      RingHom.id_apply]

@[simp] theorem trMap_apply (X : Matrix (Fin 4) (Fin 4) ℂ) :
    trMap X = (X.trace / 4) • 1 := rfl

theorem adMap_unital {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : U * Uᴴ = 1) : adMap U 1 = 1 := by
  rw [adMap_apply, Matrix.mul_one, hU]

theorem trMap_unital : trMap (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
  rw [trMap_apply, Matrix.trace_one]
  norm_num

theorem adMap_positive (U : Matrix (Fin 4) (Fin 4) ℂ)
    {X : Matrix (Fin 4) (Fin 4) ℂ} (hX : X.PosSemidef) :
    (adMap U X).PosSemidef := by
  rw [adMap_apply]
  exact hX.mul_mul_conjTranspose_same U

theorem trMap_positive {X : Matrix (Fin 4) (Fin 4) ℂ}
    (hX : X.PosSemidef) : (trMap X).PosSemidef := by
  rw [trMap_apply]
  have h0 : 0 ≤ X.trace := Upstream.PrimitiveWeight.psd_trace_nonneg hX
  have h1 : X.trace = ((X.trace.re : ℝ) : ℂ) := by
    have h2 := (Complex.le_def.mp h0).2
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, ← h2]
      rfl
  have h3 : X.trace / 4 = (((X.trace.re / 4 : ℝ)) : ℂ) := by
    rw [h1]
    push_cast
    rfl
  rw [h3]
  refine Upstream.PrimitiveWeight.posSemidef_real_smul
    Matrix.PosSemidef.one ?_
  have h4 := (Complex.le_def.mp h0).1
  simp only [Complex.zero_re] at h4
  exact div_nonneg h4 (by norm_num)

/-- The Choi matrix of a conjugation is the rank-one outer product
of the vectorized unitary — hence positive. -/
theorem adMap_matrixCP (U : Matrix (Fin 4) (Fin 4) ℂ) :
    IsMatrixCompletelyPositive (adMap U) := by
  refine cp_of_choiMatrix_posSemidef ?_
  have h1 : choiMatrix (adMap U)
      = vecMulVec (fun p : Fin 4 × Fin 4 => U p.2 p.1)
          (star fun p : Fin 4 × Fin 4 => U p.2 p.1) := by
    ext ⟨p1, p2⟩ ⟨q1, q2⟩
    change (U * Matrix.single p1 q1 (1 : ℂ) * Uᴴ) p2 q2 = _
    rw [vecMulVec_apply]
    have h2 : (Matrix.single p1 q1 (1 : ℂ) * Uᴴ) p1 q2
        = Uᴴ q1 q2 := by
      rw [Matrix.single_mul_apply_same, one_mul]
    have h3 : ∀ l, l ≠ p1 →
        (Matrix.single p1 q1 (1 : ℂ) * Uᴴ) l q2 = 0 := by
      intro l hl
      rw [Matrix.single_mul_apply_of_ne (h := hl)]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    rw [Finset.sum_eq_single p1]
    · rw [h2, Matrix.conjTranspose_apply]
      simp [Pi.star_apply]
    · intro l _ hl
      rw [h3 l hl, mul_zero]
    · intro hp
      exact absurd (Finset.mem_univ p1) hp
  rw [h1]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- The Choi matrix of the tracial mode is `(1/4) • 1` — hence
positive. -/
theorem trMap_matrixCP : IsMatrixCompletelyPositive trMap := by
  refine cp_of_choiMatrix_posSemidef ?_
  have h1 : choiMatrix trMap
      = (((1 / 4 : ℝ)) : ℂ)
          • (1 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) := by
    ext p q
    change (((Matrix.single p.1 q.1 (1 : ℂ)).trace / 4)
        • (1 : Matrix (Fin 4) (Fin 4) ℂ)) p.2 q.2
      = ((((1 / 4 : ℝ)) : ℂ)
          • (1 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)) p q
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
      smul_eq_mul]
    by_cases hfst : p.1 = q.1
    · rw [hfst, Matrix.trace_single_eq_same]
      by_cases hsnd : p.2 = q.2
      · have hpq : p = q := Prod.ext hfst hsnd
        rw [hsnd, hpq, Matrix.one_apply_eq, Matrix.one_apply_eq]
        norm_num
      · rw [Matrix.one_apply_ne hsnd,
          Matrix.one_apply_ne (fun h => hsnd (congrArg Prod.snd h))]
        simp
    · rw [Matrix.trace_single_eq_of_ne _ _ _ hfst,
        Matrix.one_apply_ne (fun h => hfst (congrArg Prod.fst h))]
      simp
  rw [h1]
  refine posSemidef_ofReal_smul Matrix.PosSemidef.one ?_
  norm_num

/-- **Theorem `thm:common-origin-balance` (internal-map
self-adjointness)**: the conjugation `Ad(U)` is self-adjoint for the
Hilbert–Schmidt trace pairing whenever `U` is Hermitian (the `R_a`)
or skew-Hermitian (the `J R_a`). -/
theorem adMap_hs_selfadjoint {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : Uᴴ = U ∨ Uᴴ = -U) (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    ((adMap U X)ᴴ * Y).trace = (Xᴴ * adMap U Y).trace := by
  change ((U * X * Uᴴ)ᴴ * Y).trace = (Xᴴ * (U * Y * Uᴴ)).trace
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  rcases hU with h | h
  · rw [h]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm U (Xᴴ * (U * Y))]
    simp only [Matrix.mul_assoc]
  · rw [h]
    simp only [Matrix.neg_mul, Matrix.mul_neg,
      Matrix.trace_neg, Matrix.mul_assoc]
    rw [neg_inj]
    rw [Matrix.trace_mul_comm U (Xᴴ * (U * Y))]
    simp only [Matrix.mul_assoc]

/-- **Theorem `thm:common-origin-balance` (internal-map
self-adjointness, tracial mode)**: the tracial internal mode is
self-adjoint for the Hilbert–Schmidt trace pairing. -/
theorem trMap_hs_selfadjoint (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    ((trMap X)ᴴ * Y).trace = (Xᴴ * trMap Y).trace := by
  change (((X.trace / 4) • (1 : Matrix (Fin 4) (Fin 4) ℂ))ᴴ
      * Y).trace = (Xᴴ * ((Y.trace / 4)
        • (1 : Matrix (Fin 4) (Fin 4) ℂ))).trace
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_conjTranspose]
  rw [smul_eq_mul, smul_eq_mul, star_div₀]
  have h4 : star (4 : ℂ) = 4 := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
      Complex.star_def, Complex.conj_ofReal]
  rw [h4]
  ring

end NCG.CommonOrigin
