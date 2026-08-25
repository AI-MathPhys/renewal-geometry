/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Command quotient, palindromic Hessian, and harmonic lift

Exact formalization for `thm:SM-command-quotient-hessian` (RG.8/RG.9).

* **Second-order command calculus** (`Jet2`, `expJet`): commands are tracked through their
  exact two-jets `1 + h c₁ + h² c₂`.  The commutator square reconstructs the bracket
  (`commWord_eq`, the second-order definition of the Lie bracket); the raw sequential probe
  carries the quadratic Baker–Campbell–Hausdorff alias `½[X,Y]` (`logJet₂_seqWord`,
  `seq_response_alias`), while the palindromic command `g_X(h/2) g_Y(h) g_X(h/2)` has no
  quadratic BCH term (`palWord_eq_expJet_add`, `logJet₂_palWord`) and reconstructs the
  Hessian `B(X,Y)` by polarization (`pal_reconstructs`).
* **RG.8** (`descends_iff`): the quadratic response `F(z) = Jz + ½B(z,z)` descends
  intrinsically through the operation fibre `𝔨` exactly when `J|𝔨 = 0` and `B(𝔨,·) = 0` —
  changing a local lift adds vertical first and mixed second response terms whose vanishing
  is exactly this pair of conditions.
* **RG.9** (`harmonicLift`, `action_decomposition`, `action_lift_le`, `action_eq_iff_lift`,
  `opAction_posSemidef`): if the common-action block `[[A,C],[Cᵀ,D]] ⪰ 0` has `D ≻ 0`, the
  unique minimum-action representative over the fibre is the harmonic lift
  `z_𝔨 = -D⁻¹Cᵀ z_ab` with reduced action `S_op = A - CD⁻¹Cᵀ ⪰ 0`.
-/

open Matrix

namespace NCG
namespace CommandQuotient

/-! ### Exact second-order command jets -/

/-- A two-jet `c₀ + h c₁ + h² c₂` in a noncommutative algebra: the exact second-order
truncation of a shrinking command word. -/
structure Jet2 (𝔄 : Type*) where
  /-- constant coefficient -/
  c0 : 𝔄
  /-- first-order coefficient -/
  c1 : 𝔄
  /-- second-order coefficient -/
  c2 : 𝔄

namespace Jet2

variable {𝔄 : Type*} [Ring 𝔄] [Algebra ℝ 𝔄]

omit [Ring 𝔄] [Algebra ℝ 𝔄] in
theorem ext' {a b : Jet2 𝔄} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; simp_all

instance : Mul (Jet2 𝔄) :=
  ⟨fun a b => ⟨a.c0 * b.c0, a.c0 * b.c1 + a.c1 * b.c0,
    a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0⟩⟩

omit [Algebra ℝ 𝔄] in
@[simp] theorem mul_c0 (a b : Jet2 𝔄) : (a * b).c0 = a.c0 * b.c0 := rfl
omit [Algebra ℝ 𝔄] in
@[simp] theorem mul_c1 (a b : Jet2 𝔄) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl
omit [Algebra ℝ 𝔄] in
@[simp] theorem mul_c2 (a b : Jet2 𝔄) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 := rfl

/-- The exact two-jet of the exponential command `exp(h X)`. -/
noncomputable def expJet (X : 𝔄) : Jet2 𝔄 := ⟨1, X, (2 : ℝ)⁻¹ • (X * X)⟩

@[simp] theorem expJet_c0 (X : 𝔄) : (expJet X).c0 = 1 := rfl
@[simp] theorem expJet_c1 (X : 𝔄) : (expJet X).c1 = X := rfl
@[simp] theorem expJet_c2 (X : 𝔄) : (expJet X).c2 = (2 : ℝ)⁻¹ • (X * X) := rfl

/-- The second-order coefficient of the logarithm of a group-like two-jet. -/
noncomputable def logJet₂ (w : Jet2 𝔄) : 𝔄 := w.c2 - (2 : ℝ)⁻¹ • (w.c1 * w.c1)

/-- The raw sequential command word `g_X(h) g_Y(h)`. -/
noncomputable def seqWord (X Y : 𝔄) : Jet2 𝔄 := expJet X * expJet Y

/-- The palindromic command word `g_X(h/2) g_Y(h) g_X(h/2)`. -/
noncomputable def palWord (X Y : 𝔄) : Jet2 𝔄 :=
  expJet ((2 : ℝ)⁻¹ • X) * expJet Y * expJet ((2 : ℝ)⁻¹ • X)

/-- The commutator square `g_X(h) g_Y(h) g_X(h)⁻¹ g_Y(h)⁻¹` (at second order the inverses
are the exponentials of the negated generators). -/
noncomputable def commWord (X Y : 𝔄) : Jet2 𝔄 :=
  expJet X * expJet Y * expJet (-X) * expJet (-Y)

/-- **The commutator square reconstructs the bracket**: at second order,
`g_X(h) g_Y(h) g_X(h)⁻¹ g_Y(h)⁻¹ = 1 + h² [X, Y]` — the second-order definition of the
Lie bracket. -/
theorem commWord_eq (X Y : 𝔄) : commWord X Y = ⟨1, 0, X * Y - Y * X⟩ := by
  have h0 : (commWord X Y).c0 = 1 := by simp [commWord]
  have h1 : (commWord X Y).c1 = 0 := by
    simp only [commWord, mul_c0, mul_c1, expJet_c0, expJet_c1, one_mul, mul_one]
    abel
  have h2 : (commWord X Y).c2 = X * Y - Y * X := by
    simp only [commWord, mul_c0, mul_c1, mul_c2, expJet_c0, expJet_c1, expJet_c2,
      one_mul, mul_one, mul_neg, neg_mul, neg_neg, mul_smul_comm, add_mul]
    module
  exact ext' h0 h1 h2

@[simp] theorem seqWord_c1 (X Y : 𝔄) : (seqWord X Y).c1 = X + Y := by
  simp only [seqWord, mul_c1, expJet_c0, expJet_c1, one_mul, mul_one]
  abel

/-- **No quadratic BCH term in the palindromic word**: the palindromic command agrees with
the single command `exp(h(X+Y))` exactly through second order. -/
theorem palWord_eq_expJet_add (X Y : 𝔄) : palWord X Y = expJet (X + Y) := by
  have h0 : (palWord X Y).c0 = 1 := by simp [palWord]
  have h1 : (palWord X Y).c1 = X + Y := by
    simp only [palWord, mul_c0, mul_c1, expJet_c0, expJet_c1, one_mul, mul_one]
    module
  have h2 : (palWord X Y).c2 = (2 : ℝ)⁻¹ • ((X + Y) * (X + Y)) := by
    simp only [palWord, mul_c0, mul_c1, mul_c2, expJet_c0, expJet_c1, expJet_c2,
      one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, mul_add, add_mul,
      smul_add]
    module
  exact ext' h0 h1 h2

@[simp] theorem palWord_c1 (X Y : 𝔄) : (palWord X Y).c1 = X + Y := by
  rw [palWord_eq_expJet_add, expJet_c1]

/-- The palindromic log has no second-order term. -/
theorem logJet₂_palWord (X Y : 𝔄) : logJet₂ (palWord X Y) = 0 := by
  rw [palWord_eq_expJet_add, logJet₂]
  simp

/-- **The sequential alias**: the raw sequential probe's log carries the quadratic
Baker–Campbell–Hausdorff term `½[X,Y]`. -/
theorem logJet₂_seqWord (X Y : 𝔄) :
    logJet₂ (seqWord X Y) = (2 : ℝ)⁻¹ • (X * Y - Y * X) := by
  simp only [logJet₂, seqWord, mul_c1, mul_c2, expJet_c0, expJet_c1, expJet_c2,
    one_mul, mul_one, mul_add, add_mul, smul_add, smul_sub]
  module

end Jet2

/-! ### The response read through command words -/

section Response

variable {𝔄 V : Type*} [Ring 𝔄] [Algebra ℝ 𝔄] [AddCommGroup V] [Module ℝ V]

open Jet2

/-- The exact second-order coefficient of the calibrated shell response
`F(z) = Jz + ½B(z,z) + O(‖z‖³)` read along a command word: the log's second jet passes
through `J` and the first jet feeds the Hessian. -/
noncomputable def responseSecond (J : 𝔄 →ₗ[ℝ] V) (B : 𝔄 →ₗ[ℝ] 𝔄 →ₗ[ℝ] V)
    (w : Jet2 𝔄) : V :=
  J (logJet₂ w) + (2 : ℝ)⁻¹ • B w.c1 w.c1

/-- **The raw sequential mixed probe contains the alias `½J[X,Y]`.** -/
theorem seq_response_alias (J : 𝔄 →ₗ[ℝ] V) (B : 𝔄 →ₗ[ℝ] 𝔄 →ₗ[ℝ] V) (X Y : 𝔄) :
    responseSecond J B (seqWord X Y)
      = (2 : ℝ)⁻¹ • J (X * Y - Y * X) + (2 : ℝ)⁻¹ • B (X + Y) (X + Y) := by
  rw [responseSecond, logJet₂_seqWord, map_smul, seqWord_c1]

/-- The palindromic probe has no alias: only the Hessian responds at second order. -/
theorem pal_response (J : 𝔄 →ₗ[ℝ] V) (B : 𝔄 →ₗ[ℝ] 𝔄 →ₗ[ℝ] V) (X Y : 𝔄) :
    responseSecond J B (palWord X Y) = (2 : ℝ)⁻¹ • B (X + Y) (X + Y) := by
  rw [responseSecond, logJet₂_palWord, map_zero, zero_add, palWord_c1]

/-- **The palindromic command reconstructs `B(X,Y)`** by polarization of the alias-free
second-order responses. -/
theorem pal_reconstructs (J : 𝔄 →ₗ[ℝ] V) (B : 𝔄 →ₗ[ℝ] 𝔄 →ₗ[ℝ] V)
    (hsym : ∀ u v, B u v = B v u) (X Y : 𝔄) :
    B X Y = responseSecond J B (palWord X Y)
      - responseSecond J B (palWord X 0) - responseSecond J B (palWord 0 Y) := by
  rw [pal_response, pal_response, pal_response]
  simp only [add_zero, zero_add, map_add, LinearMap.add_apply, smul_add]
  rw [hsym Y X]
  module

end Response

/-! ### RG.8: intrinsic descent through the operation fibre -/

section Descent

variable {E V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]

/-- The exact quadratic response `F(z) = Jz + ½B(z,z)`. -/
noncomputable def response (J : E →ₗ[ℝ] V) (B : E →ₗ[ℝ] E →ₗ[ℝ] V) (z : E) : V :=
  J z + (2 : ℝ)⁻¹ • B z z

/-- Changing a local lift adds the vertical first response and the mixed second response. -/
theorem response_add (J : E →ₗ[ℝ] V) (B : E →ₗ[ℝ] E →ₗ[ℝ] V) (z k : E) :
    response J B (z + k) = response J B z
      + (J k + (2 : ℝ)⁻¹ • B z k + (2 : ℝ)⁻¹ • B k z + (2 : ℝ)⁻¹ • B k k) := by
  simp only [response, map_add, LinearMap.add_apply, smul_add]
  abel

/-- **RG.8**: the response descends intrinsically through the operation fibre `𝔨` — i.e. is
invariant under every change of local lift `z ↦ z + k`, `k ∈ 𝔨` — exactly when `J|𝔨 = 0`
and `B(𝔨, 𝔤) = 0`. -/
theorem descends_iff (J : E →ₗ[ℝ] V) (B : E →ₗ[ℝ] E →ₗ[ℝ] V)
    (hsym : ∀ u v, B u v = B v u) (𝔨 : Submodule ℝ E) :
    (∀ z : E, ∀ k ∈ 𝔨, response J B (z + k) = response J B z) ↔
      (∀ k ∈ 𝔨, J k = 0) ∧ ∀ k ∈ 𝔨, ∀ g : E, B k g = 0 := by
  constructor
  · intro h
    have hvert : ∀ k ∈ 𝔨, ∀ z : E,
        J k + (2 : ℝ)⁻¹ • B z k + (2 : ℝ)⁻¹ • B k z + (2 : ℝ)⁻¹ • B k k = 0 := by
      intro k hk z
      have h' := h z k hk
      rw [response_add] at h'
      have h2 := congrArg (fun w => w - response J B z) h'
      simpa using h2
    have hzero : ∀ k ∈ 𝔨, J k + (2 : ℝ)⁻¹ • B k k = 0 := by
      intro k hk
      have := hvert k hk 0
      simpa using this
    have hmix : ∀ k ∈ 𝔨, ∀ z : E, B k z = 0 := by
      intro k hk z
      have hpair : (2 : ℝ)⁻¹ • B z k + (2 : ℝ)⁻¹ • B k z = 0 := by
        calc (2 : ℝ)⁻¹ • B z k + (2 : ℝ)⁻¹ • B k z
            = (J k + (2 : ℝ)⁻¹ • B z k + (2 : ℝ)⁻¹ • B k z + (2 : ℝ)⁻¹ • B k k)
              - (J k + (2 : ℝ)⁻¹ • B k k) := by abel
          _ = 0 - 0 := by rw [hvert k hk z, hzero k hk]
          _ = 0 := by abel
      rw [hsym z k] at hpair
      have hdouble : (2 : ℝ)⁻¹ • B k z + (2 : ℝ)⁻¹ • B k z = B k z := by
        rw [← add_smul]
        norm_num
      rw [← hdouble]
      exact hpair
    refine ⟨fun k hk => ?_, hmix⟩
    have := hzero k hk
    rw [hmix k hk k, smul_zero, add_zero] at this
    exact this
  · rintro ⟨hJ, hB⟩ z k hk
    rw [response_add, hJ k hk, hB k hk z, hB k hk k,
      show B z k = 0 from by rw [hsym]; exact hB k hk z]
    simp

end Descent

/-! ### RG.9: the harmonic lift and reduced operation action -/

section Harmonic

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The harmonic lift `z_𝔨 = -D⁻¹ Cᵀ z_ab` of an abelianized coordinate. -/
noncomputable def harmonicLift (C : Matrix m n ℝ) (D : Matrix n n ℝ) (x : m → ℝ) :
    n → ℝ :=
  -((D⁻¹ * Cᵀ) *ᵥ x)

/-- The reduced operation action `S_op = A - C D⁻¹ Cᵀ`. -/
noncomputable def opAction (A : Matrix m m ℝ) (C : Matrix m n ℝ) (D : Matrix n n ℝ) :
    Matrix m m ℝ :=
  A - C * D⁻¹ * Cᵀ

/-- The common-action quadratic form of the block `[[A,C],[Cᵀ,D]]`. -/
noncomputable def blockAction (A : Matrix m m ℝ) (C : Matrix m n ℝ) (D : Matrix n n ℝ)
    (x : m → ℝ) (y : n → ℝ) : ℝ :=
  Sum.elim x y ⬝ᵥ (fromBlocks A C Cᵀ D) *ᵥ Sum.elim x y

omit [DecidableEq n] in
/-- Dot products split across a `Sum.elim` decomposition. -/
theorem sum_elim_dot (u p : m → ℝ) (v q : n → ℝ) :
    Sum.elim u v ⬝ᵥ Sum.elim p q = u ⬝ᵥ p + v ⬝ᵥ q := by
  simp [dotProduct, Fintype.sum_sum_type]

omit [DecidableEq n] in
theorem blockAction_expand (A : Matrix m m ℝ) (C : Matrix m n ℝ) (D : Matrix n n ℝ)
    (x : m → ℝ) (y : n → ℝ) :
    blockAction A C D x y
      = x ⬝ᵥ A *ᵥ x + x ⬝ᵥ C *ᵥ y + y ⬝ᵥ Cᵀ *ᵥ x + y ⬝ᵥ D *ᵥ y := by
  simp only [blockAction, fromBlocks_mulVec, sum_elim_dot, dotProduct_add,
    Sum.elim_comp_inl, Sum.elim_comp_inr]
  ring

omit [DecidableEq n] in
/-- Transpose swap for the cross form. -/
theorem cross_swap (C : Matrix m n ℝ) (u : m → ℝ) (v : n → ℝ) :
    u ⬝ᵥ C *ᵥ v = v ⬝ᵥ Cᵀ *ᵥ u := by
  rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

/-- **Completion of the square** over the operation fibre: with `u = y - z_𝔨(x)`,
`⟨M(x,y),(x,y)⟩ = ⟨S_op x, x⟩ + ⟨D u, u⟩`. -/
theorem action_decomposition (A : Matrix m m ℝ) (C : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) (x : m → ℝ) (y : n → ℝ) :
    blockAction A C D x y
      = x ⬝ᵥ opAction A C D *ᵥ x
        + (y - harmonicLift C D x) ⬝ᵥ D *ᵥ (y - harmonicLift C D x) := by
  have hDsym : Dᵀ = D := by
    have := hD.1.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hDD : D * (D⁻¹ * Cᵀ) = Cᵀ := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv D (isUnit_iff_ne_zero.mpr hD.det_pos.ne'),
      Matrix.one_mul]
  have hcollapse : D *ᵥ ((D⁻¹ * Cᵀ) *ᵥ x) = Cᵀ *ᵥ x := by
    rw [mulVec_mulVec, hDD]
  have hDswap : ∀ v w : n → ℝ, v ⬝ᵥ D *ᵥ w = w ⬝ᵥ D *ᵥ v := by
    intro v w
    rw [cross_swap (C := D), hDsym]
  rw [blockAction_expand, harmonicLift, opAction, sub_neg_eq_add]
  simp only [mulVec_add, dotProduct_add, add_dotProduct, sub_mulVec,
    dotProduct_sub, hcollapse]
  have h1 : (D⁻¹ * Cᵀ) *ᵥ x ⬝ᵥ D *ᵥ y = y ⬝ᵥ Cᵀ *ᵥ x := by
    rw [hDswap, hcollapse]
  have h2 : (D⁻¹ * Cᵀ) *ᵥ x ⬝ᵥ Cᵀ *ᵥ x = x ⬝ᵥ (C * D⁻¹ * Cᵀ) *ᵥ x := by
    rw [← cross_swap C x ((D⁻¹ * Cᵀ) *ᵥ x), mulVec_mulVec, ← Matrix.mul_assoc]
  have h3 : x ⬝ᵥ C *ᵥ y = y ⬝ᵥ Cᵀ *ᵥ x := cross_swap C x y
  rw [h1, h2, h3]
  ring

/-- The harmonic lift attains the reduced action. -/
theorem action_lift_eq (A : Matrix m m ℝ) (C : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) (x : m → ℝ) :
    blockAction A C D x (harmonicLift C D x) = x ⬝ᵥ opAction A C D *ᵥ x := by
  rw [action_decomposition A C hD, sub_self]
  simp

/-- **RG.9, minimality**: the harmonic lift is the minimum-action representative. -/
theorem action_lift_le (A : Matrix m m ℝ) (C : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) (x : m → ℝ) (y : n → ℝ) :
    x ⬝ᵥ opAction A C D *ᵥ x ≤ blockAction A C D x y := by
  rw [action_decomposition A C hD]
  have h := hD.posSemidef.dotProduct_mulVec_nonneg (y - harmonicLift C D x)
  simp only [star_trivial] at h
  linarith

/-- **RG.9, uniqueness**: the harmonic lift is the unique minimum-action representative. -/
theorem action_eq_iff_lift (A : Matrix m m ℝ) (C : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) (x : m → ℝ) (y : n → ℝ) :
    blockAction A C D x y = x ⬝ᵥ opAction A C D *ᵥ x ↔ y = harmonicLift C D x := by
  constructor
  · intro hmin
    rw [action_decomposition A C hD] at hmin
    have hzero : (y - harmonicLift C D x) ⬝ᵥ D *ᵥ (y - harmonicLift C D x) = 0 := by
      linarith
    by_contra hne
    have hsub : y - harmonicLift C D x ≠ 0 := sub_ne_zero.mpr hne
    have h := hD.dotProduct_mulVec_pos hsub
    simp only [star_trivial] at h
    linarith
  · intro hy
    rw [hy]
    exact action_lift_eq A C hD x

/-- **RG.9, positivity**: the reduced operation action `S_op = A - CD⁻¹Cᵀ` is positive
semidefinite whenever the common-action block is. -/
theorem opAction_posSemidef {A : Matrix m m ℝ} (C : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hM : (fromBlocks A C Cᵀ D).PosSemidef) (hD : D.PosDef) :
    ∀ x : m → ℝ, 0 ≤ x ⬝ᵥ opAction A C D *ᵥ x := by
  intro x
  have h := hM.dotProduct_mulVec_nonneg (Sum.elim x (harmonicLift C D x))
  simp only [star_trivial] at h
  have : blockAction A C D x (harmonicLift C D x)
      = Sum.elim x (harmonicLift C D x) ⬝ᵥ
        (fromBlocks A C Cᵀ D) *ᵥ Sum.elim x (harmonicLift C D x) := rfl
  rw [← action_lift_eq A C hD x, this]
  exact h

end Harmonic

/-- **Bundle for `thm:SM-command-quotient-hessian`**: the commutator square reconstructs the
bracket; the palindromic command has no quadratic BCH term and reconstructs `B(X,Y)`; the
response descends through the operation fibre iff `J|𝔨 = 0` and `B(𝔨,𝔤) = 0` (RG.8); and
under `[[A,C],[Cᵀ,D]] ⪰ 0`, `D ≻ 0`, the harmonic lift `-D⁻¹Cᵀ z_ab` is the unique
minimum-action representative with positive reduced action `S_op = A - CD⁻¹Cᵀ` (RG.9). -/
theorem sm_command_quotient_hessian
    {𝔄 V : Type*} [Ring 𝔄] [Algebra ℝ 𝔄] [AddCommGroup V] [Module ℝ V]
    (J : 𝔄 →ₗ[ℝ] V) (B : 𝔄 →ₗ[ℝ] 𝔄 →ₗ[ℝ] V) (hsym : ∀ u v, B u v = B v u)
    {E W : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup W] [Module ℝ W]
    (J' : E →ₗ[ℝ] W) (B' : E →ₗ[ℝ] E →ₗ[ℝ] W) (hsym' : ∀ u v, B' u v = B' v u)
    (𝔨 : Submodule ℝ E)
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℝ} (C : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hM : (fromBlocks A C Cᵀ D).PosSemidef) (hD : D.PosDef) :
    (∀ X Y : 𝔄, Jet2.commWord X Y = ⟨1, 0, X * Y - Y * X⟩) ∧
    (∀ X Y : 𝔄, Jet2.logJet₂ (Jet2.palWord X Y) = 0) ∧
    (∀ X Y : 𝔄, B X Y = responseSecond J B (Jet2.palWord X Y)
      - responseSecond J B (Jet2.palWord X 0) - responseSecond J B (Jet2.palWord 0 Y)) ∧
    ((∀ z : E, ∀ k ∈ 𝔨, response J' B' (z + k) = response J' B' z) ↔
      (∀ k ∈ 𝔨, J' k = 0) ∧ ∀ k ∈ 𝔨, ∀ g : E, B' k g = 0) ∧
    (∀ x y, blockAction A C D x y = x ⬝ᵥ opAction A C D *ᵥ x ↔ y = harmonicLift C D x) ∧
    ∀ x, 0 ≤ x ⬝ᵥ opAction A C D *ᵥ x :=
  ⟨Jet2.commWord_eq, Jet2.logJet₂_palWord, pal_reconstructs J B hsym,
   descends_iff J' B' hsym' 𝔨, action_eq_iff_lift A C hD, opAction_posSemidef C hM hD⟩

end CommandQuotient
end NCG
