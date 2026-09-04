/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EasyExact05

/-!
# Medium exact records, batch 00 (Gran-Tensor manuscript, projective-head cluster)

Exact formalizations of the following manuscript records:

* `thm:GT-projective-head-Pythagoras` — martingale increments of a finite
  filtration, positivity of every displayed packet, the exact head/irreducible/
  response-null decomposition (ML.7), and cross-level orthogonality (ML.8).
* `thm:GT-projective-head-replay` — the pseudoinverse source action (ML.14) as
  an attained minimum, the bounds (ML.15), the positive unbiased replay
  estimator with variance bound (ML.16–ML.17), the sharp continuous allocation
  (ML.18), and the single-level implementation with its optimal drawing law
  (ML.18a–ML.18b).
* `thm:GT-projective-head-heldout` — the vanishing cross-level response row
  (ML.19) and the cutoff transport identities (ML.20–ML.21) with composition.
* `thm:GT-ancestry-response-nonduplication` — the ancestry projection packet
  (AN.1–AN.2), the follower Pythagoras (AN.3), the exact-follower criterion
  (AN.4), the polar synthesis and rank minimality (AN.5), and cross-level
  additivity of ancestry residuals (AN.6).
* `thm:GT-stage-product-interval` — the sharp rearrangement interval
  (STG.11) over positive same-history couplings of two uniform-carrier
  marginals, endpoint attainment, and the exact residual (STG.12).
* `thm:GT-canonical-record-likelihood` — the record-likelihood tower
  (STG.15–STG.20): martingale property, uniqueness, absolute continuity and
  canonical stage factors, the entropy chain rule, the `L²` innovation
  Pythagoras, and the Fisher increments with their rank identity.
* `thm:GT-record-factor-audit` — the four-way factor audit equivalence, the
  approximate-recovery bound (STG.22), and the cofinal transport limits
  (STG.23) with entropy convergence and summable-defect limits.
* `thm:GT-physical-stage-alternative` — the first-match stage-attribution
  alternatives (S1)–(S6) over the framework certificates, with substantive
  payloads in every branch.
* `thm:GT-physical-source-Pythagoras` — the routed/mediated least-squares
  Pythagoras (PSR.3–PSR.4), the residual monotonicity chain (PSR.5), and the
  two explicit witnesses refuting a universal order.
* `thm:GT-physical-source-transport` — the exact three-term source defect
  (PSR.14), the Gram transport identities (PSR.15–PSR.16), and the
  summable-defect limit (PSR.17).
* `thm:GT-source-short-rotation` — the energy-dual rotation bound (ST.8) for
  the variational source short.

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset Filter
open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank NCG.PsdBlockSchur
open scoped ComplexOrder Topology

-- decidability/fintype instances enter only through the spectral support calculus in proofs
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace NCG

/-! ### Shared machinery: conditional expectation along a finite filtration

The occurring history law of the projective records is rendered as a finite
carrier `Ω` with strictly positive weights (a full-support finite probability
law; zero-mass atoms may be dropped without loss).  A record is a map
`f : Ω → ι` into a finite value space, and a filtration is a chain of records
each refining the previous one.  `MgtFilt.cexp` is the module-valued
conditional expectation; `MgtFilt.master` is the partial-averaging identity
against record-determined linear observables, from which the tower rule,
martingale-increment orthogonality, and all `L²` identities follow. -/

section MgtFiltSection

namespace MgtFilt

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- A writer `V` is determined by (measurable with respect to) the record `f`. -/
def DetOn {γ : Type*} (f : Ω → ι) (V : Ω → γ) : Prop :=
  ∀ x y, f x = f y → V x = V y

/-- The record `g` refines `f`: the `g`-value determines the `f`-value. -/
def Refines (f g : Ω → ι) : Prop :=
  ∀ x y, g x = g y → f x = f y

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- A record determined at a coarser level is determined at any refining level. -/
theorem DetOn.mono {γ : Type*} {f g : Ω → ι} (href : Refines f g) {V : Ω → γ}
    (h : DetOn f V) : DetOn g V :=
  fun x y hxy => h x y (href x y hxy)

/-- A finite filtration: each later record refines every earlier one. -/
def Chain (f : ℕ → Ω → ι) : Prop :=
  ∀ ⦃j k : ℕ⦄, j ≤ k → Refines (f j) (f k)

/-- The mass of the record fiber `{f = t}`. -/
noncomputable def mass (w : Ω → ℝ) (f : Ω → ι) (t : ι) : ℝ :=
  ∑ x ∈ Finset.univ.filter fun x => f x = t, w x

/-- Conditional expectation of the module-valued writer `V` given the record
`f` under the weight `w`. -/
noncomputable def cexp (w : Ω → ℝ) (f : Ω → ι) (V : Ω → M) : Ω → M :=
  fun x => (mass w f (f x))⁻¹ •
    ∑ y ∈ Finset.univ.filter fun y => f y = f x, w y • V y

omit [Fintype ι] in
/-- Every occupied fiber has strictly positive mass. -/
theorem mass_pos {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (f : Ω → ι) (x : Ω) :
    0 < mass w f (f x) := by
  refine Finset.sum_pos' (fun y _ => (hw y).le) ⟨x, ?_, hw x⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype ι] in
/-- The conditional expectation is determined by the conditioning record. -/
theorem detOn_cexp (w : Ω → ℝ) (f : Ω → ι) (V : Ω → M) : DetOn f (cexp w f V) := by
  intro x y hxy
  unfold cexp
  rw [hxy]

omit [Fintype ι] in
/-- **Atomwise averaging**: on each record fiber, the weighted fiber sum of the
conditional expectation equals the weighted fiber sum of the writer. -/
theorem fiber_avg {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (f : Ω → ι) (V : Ω → M) (t : ι) :
    ∑ x ∈ Finset.univ.filter fun x => f x = t, w x • cexp w f V x
      = ∑ x ∈ Finset.univ.filter fun x => f x = t, w x • V x := by
  rcases (Finset.univ.filter fun x => f x = t).eq_empty_or_nonempty with h | h
  · rw [h, Finset.sum_empty, Finset.sum_empty]
  · obtain ⟨x0, hx0⟩ := h
    have hfx0 : f x0 = t := (Finset.mem_filter.mp hx0).2
    have hmass : 0 < mass w f t := by
      have h1 := mass_pos hw f x0
      rwa [hfx0] at h1
    have hconst : ∀ x ∈ Finset.univ.filter fun x => f x = t,
        w x • cexp w f V x
          = w x • (mass w f t)⁻¹ •
              ∑ y ∈ Finset.univ.filter fun y => f y = t, w y • V y := by
      intro x hx
      have hfx : f x = t := (Finset.mem_filter.mp hx).2
      unfold cexp
      rw [hfx]
    rw [Finset.sum_congr rfl hconst, ← Finset.sum_smul, smul_smul,
      show (∑ x ∈ Finset.univ.filter fun x => f x = t, w x) = mass w f t from rfl,
      mul_inv_cancel₀ hmass.ne', one_smul]

/-- **Partial averaging**: against every record-determined family of linear
observables, the conditional expectation may be replaced by the writer. -/
theorem master {N : Type*} [AddCommGroup N] [Module ℝ N] {w : Ω → ℝ}
    (hw : ∀ x, 0 < w x) (f : Ω → ι) (V : Ω → M)
    (φ : Ω → M →ₗ[ℝ] N) (hφ : DetOn f φ) :
    ∑ x, w x • φ x (cexp w f V x) = ∑ x, w x • φ x (V x) := by
  rw [← Finset.sum_fiberwise Finset.univ f fun x => w x • φ x (cexp w f V x),
    ← Finset.sum_fiberwise Finset.univ f fun x => w x • φ x (V x)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rcases (Finset.univ.filter fun x => f x = t).eq_empty_or_nonempty with h | h
  · rw [h, Finset.sum_empty, Finset.sum_empty]
  · obtain ⟨x0, hx0⟩ := h
    have hfx0 : f x0 = t := (Finset.mem_filter.mp hx0).2
    have hconst : ∀ X : Ω → M, ∀ x ∈ Finset.univ.filter fun x => f x = t,
        w x • φ x (X x) = φ x0 (w x • X x) := by
      intro X x hx
      have hfx : f x = t := (Finset.mem_filter.mp hx).2
      rw [hφ x x0 (by rw [hfx, hfx0]), map_smul]
    rw [Finset.sum_congr rfl (hconst _), Finset.sum_congr rfl (hconst _),
      ← map_sum, ← map_sum, fiber_avg hw f V t]

/-- Total expectation: `𝔼[𝔼[V|f]] = 𝔼[V]`. -/
theorem sum_cexp {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (f : Ω → ι) (V : Ω → M) :
    ∑ x, w x • cexp w f V x = ∑ x, w x • V x :=
  master hw f V (fun _ => LinearMap.id) fun _ _ _ => rfl

/-- Partial averaging with a record-determined scalar prefactor. -/
theorem master_smul {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : Ω → ι} (V : Ω → M)
    {a : Ω → ℝ} (ha : DetOn f a) :
    ∑ x, w x • a x • cexp w f V x = ∑ x, w x • a x • V x := by
  have h := master hw f V (fun x => a x • (LinearMap.id : M →ₗ[ℝ] M))
    (fun x y hxy => congrArg (· • (LinearMap.id : M →ₗ[ℝ] M)) (ha x y hxy))
  simpa only [LinearMap.smul_apply, LinearMap.id_apply] using h

/-- Left matrix multiplication as a real-linear map on rectangular matrices. -/
def mulLeftLM {P S E : Type*} [Fintype S] (A : Matrix P S ℂ) :
    Matrix S E ℂ →ₗ[ℝ] Matrix P E ℂ where
  toFun X := A * X
  map_add' X Y := Matrix.mul_add A X Y
  map_smul' c X := by
    simp only [RingHom.id_apply]
    exact Matrix.mul_smul A c X

/-- Partial averaging with a record-determined matrix prefactor. -/
theorem master_mul {P S E : Type*} [Fintype S] {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : Ω → ι} (A : Ω → Matrix P S ℂ) (V : Ω → Matrix S E ℂ) (hA : DetOn f A) :
    ∑ x, w x • (A x * cexp w f V x) = ∑ x, w x • (A x * V x) :=
  master hw f V (fun x => mulLeftLM (A x)) fun x y hxy =>
    congrArg mulLeftLM (hA x y hxy)

omit [Fintype ι] in
/-- A record-determined writer is fixed by its own conditional expectation. -/
theorem cexp_of_detOn {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : Ω → ι} {V : Ω → M}
    (hV : DetOn f V) : cexp w f V = V := by
  funext x
  unfold cexp
  have hconst : ∀ y ∈ Finset.univ.filter fun y => f y = f x, w y • V y = w y • V x := by
    intro y hy
    rw [hV y x (Finset.mem_filter.mp hy).2]
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_smul, smul_smul,
    show (∑ y ∈ Finset.univ.filter fun y => f y = f x, w y) = mass w f (f x) from rfl,
    inv_mul_cancel₀ (mass_pos hw f x).ne', one_smul]

/-- **Tower rule**: conditioning on a coarser record after a finer one equals
conditioning on the coarser record alone. -/
theorem cexp_cexp {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {fc ff : Ω → ι}
    (href : Refines fc ff) (V : Ω → M) :
    cexp w fc (cexp w ff V) = cexp w fc V := by
  funext x
  have key : ∀ X : Ω → M,
      ∑ y, w y • (if fc y = fc x then LinearMap.id else (0 : M →ₗ[ℝ] M)) (X y)
        = ∑ y ∈ Finset.univ.filter fun y => fc y = fc x, w y • X y := by
    intro X
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs with h
    · rw [LinearMap.id_apply]
    · rw [LinearMap.zero_apply, smul_zero]
  have hm := master hw ff V
    (fun y => if fc y = fc x then LinearMap.id else (0 : M →ₗ[ℝ] M))
    (fun y z hyz => congrArg
      (fun t => if t = fc x then LinearMap.id else (0 : M →ₗ[ℝ] M)) (href y z hyz))
  change (mass w fc (fc x))⁻¹ •
      ∑ y ∈ Finset.univ.filter fun y => fc y = fc x, w y • cexp w ff V y
    = (mass w fc (fc x))⁻¹ •
        ∑ y ∈ Finset.univ.filter fun y => fc y = fc x, w y • V y
  rw [← key (cexp w ff V), ← key V, hm]

omit [Fintype ι] in
/-- Conditional expectation commutes with every fixed linear postcomposition. -/
theorem cexp_comp_linear {N : Type*} [AddCommGroup N] [Module ℝ N]
    (w : Ω → ℝ) (f : Ω → ι) (ψ : M →ₗ[ℝ] N) (V : Ω → M) :
    cexp w f (fun x => ψ (V x)) = fun x => ψ (cexp w f V x) := by
  funext x
  unfold cexp
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_smul]

omit [Fintype ι] in
/-- Additivity of the conditional expectation. -/
theorem cexp_add (w : Ω → ℝ) (f : Ω → ι) (V W : Ω → M) :
    cexp w f (fun x => V x + W x) = fun x => cexp w f V x + cexp w f W x := by
  funext x
  unfold cexp
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_add]

omit [Fintype ι] in
/-- Subtractivity of the conditional expectation. -/
theorem cexp_sub (w : Ω → ℝ) (f : Ω → ι) (V W : Ω → M) :
    cexp w f (fun x => V x - W x) = fun x => cexp w f V x - cexp w f W x := by
  funext x
  unfold cexp
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_sub]

omit [Fintype ι] in
/-- The conditional expectation of a constant writer. -/
theorem cexp_const {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (f : Ω → ι) (c : M) :
    cexp w f (fun _ => c) = fun _ => c :=
  cexp_of_detOn hw fun _ _ _ => rfl

omit [Fintype ι] in
/-- The conditional expectation of a nonnegative scalar writer is nonnegative. -/
theorem cexp_nonneg {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x) (f : Ω → ι) {V : Ω → ℝ}
    (hV : ∀ x, 0 ≤ V x) (x : Ω) : 0 ≤ cexp w f V x := by
  unfold cexp
  refine smul_nonneg (inv_nonneg.mpr (Finset.sum_nonneg fun y _ => hw y))
    (Finset.sum_nonneg fun y _ => smul_nonneg (hw y) (hV y))

omit [Fintype ι] in
/-- Monotonicity of the scalar conditional expectation. -/
theorem cexp_mono {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (f : Ω → ι) {V W : Ω → ℝ}
    (h : ∀ x, V x ≤ W x) (x : Ω) : cexp w f V x ≤ cexp w f W x := by
  have h0 : 0 ≤ cexp w f (fun y => W y - V y) x :=
    cexp_nonneg (fun y => (hw y).le) f (fun y => sub_nonneg.mpr (h y)) x
  rw [cexp_sub] at h0
  linarith [h0]

/-- The martingale `M_ℓ = 𝔼[V | 𝓕_ℓ]` of a writer along a filtration (ML.1). -/
noncomputable def marti (w : Ω → ℝ) (f : ℕ → Ω → ι) (V : Ω → M) (ℓ : ℕ) : Ω → M :=
  cexp w (f ℓ) V

/-- The martingale increments `D_0 = M_0`, `D_ℓ = M_ℓ - M_{ℓ-1}` (ML.1). -/
noncomputable def dinc (w : Ω → ℝ) (f : ℕ → Ω → ι) (V : Ω → M) : ℕ → Ω → M
  | 0 => marti w f V 0
  | ℓ + 1 => fun x => marti w f V (ℓ + 1) x - marti w f V ℓ x

omit [Fintype ι] in
/-- Each martingale level is determined by its own record. -/
theorem detOn_marti (w : Ω → ℝ) (f : ℕ → Ω → ι) (V : Ω → M) (ℓ : ℕ) :
    DetOn (f ℓ) (marti w f V ℓ) :=
  detOn_cexp w (f ℓ) V

omit [Fintype ι] in
/-- Each martingale increment is determined by its own record. -/
theorem detOn_dinc {w : Ω → ℝ} {f : ℕ → Ω → ι} (hchain : Chain f) (V : Ω → M)
    (ℓ : ℕ) : DetOn (f ℓ) (dinc w f V ℓ) := by
  cases ℓ with
  | zero => exact detOn_marti w f V 0
  | succ ℓ =>
    intro x y hxy
    have h1 := detOn_marti w f V (ℓ + 1) x y hxy
    have h2 := (detOn_marti w f V ℓ).mono (hchain (Nat.le_succ ℓ)) x y hxy
    change marti w f V (ℓ + 1) x - marti w f V ℓ x
      = marti w f V (ℓ + 1) y - marti w f V ℓ y
    rw [h1, h2]

omit [Fintype ι] in
/-- The increments telescope back to the martingale (levels `0,…,L`). -/
theorem sum_dinc (w : Ω → ℝ) (f : ℕ → Ω → ι) (V : Ω → M) (L : ℕ) (x : Ω) :
    ∑ ℓ ∈ Finset.range (L + 1), dinc w f V ℓ x = marti w f V L x := by
  induction L with
  | zero => rw [Finset.range_one, Finset.sum_singleton]; rfl
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    change marti w f V L x + (marti w f V (L + 1) x - marti w f V L x) = _
    abel

/-- The defining martingale property: each positive-level increment has
vanishing conditional expectation on the previous record. -/
theorem cexp_dinc_succ {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (hchain : Chain f) (V : Ω → M) (ℓ : ℕ) :
    cexp w (f ℓ) (dinc w f V (ℓ + 1)) = fun _ => 0 := by
  change cexp w (f ℓ) (fun x => marti w f V (ℓ + 1) x - marti w f V ℓ x) = fun _ => 0
  rw [cexp_sub]
  have h1 : cexp w (f ℓ) (marti w f V (ℓ + 1)) = cexp w (f ℓ) V :=
    cexp_cexp hw (hchain (Nat.le_succ ℓ)) V
  have h2 : cexp w (f ℓ) (marti w f V ℓ) = marti w f V ℓ :=
    cexp_of_detOn hw (detOn_marti w f V ℓ)
  funext x
  rw [h1, h2]
  show cexp w (f ℓ) V x - marti w f V ℓ x = 0
  rw [sub_eq_zero]
  rfl

/-- **Increment orthogonality**: a later increment is annihilated in
expectation by every earlier-record-determined linear observable. -/
theorem dinc_master_zero {N : Type*} [AddCommGroup N] [Module ℝ N] {w : Ω → ℝ}
    (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι} (hchain : Chain f) (V : Ω → M)
    {j k : ℕ} (hjk : j < k) (φ : Ω → M →ₗ[ℝ] N) (hφ : DetOn (f j) φ) :
    ∑ x, w x • φ x (dinc w f V k x) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hjk
  set k' := j + k with hk'
  have hφ' : DetOn (f k') φ := hφ.mono (hchain (Nat.le_add_right j k))
  have hφ'' : DetOn (f (k' + 1)) φ := hφ.mono (hchain (Nat.le_succ_of_le
    (Nat.le_add_right j k)))
  have hsplit : ∀ x, w x • φ x (dinc w f V (k' + 1) x)
      = w x • φ x (marti w f V (k' + 1) x) - w x • φ x (marti w f V k' x) := by
    intro x
    change w x • φ x (marti w f V (k' + 1) x - marti w f V k' x) = _
    rw [map_sub, smul_sub]
  rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_sub_distrib,
    show (∑ x, w x • φ x (marti w f V (k' + 1) x)) = ∑ x, w x • φ x (V x) from
      master hw (f (k' + 1)) V φ hφ'',
    show (∑ x, w x • φ x (marti w f V k' x)) = ∑ x, w x • φ x (V x) from
      master hw (f k') V φ hφ', sub_self]

/-- Matrix form of the increment orthogonality (ML.8 core). -/
theorem dinc_orth_mul {P S E : Type*} [Fintype S] {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) (V : Ω → Matrix S E ℂ) {j k : ℕ}
    (hjk : j < k) (A : Ω → Matrix P S ℂ) (hA : DetOn (f j) A) :
    ∑ x, w x • (A x * dinc w f V k x) = 0 :=
  dinc_master_zero hw hchain V hjk (fun x => mulLeftLM (A x))
    fun x y hxy => congrArg mulLeftLM (hA x y hxy)

end MgtFilt

end MgtFiltSection

/-! ### Shared positivity helpers for weighted matrix expectations -/

section MgtPosSection

variable {n : Type*} [Fintype n]

/-- A nonnegative real multiple of a PSD complex matrix is PSD. -/
theorem mgt_smul_posSemidef {c : ℝ} (hc : 0 ≤ c) {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : (c • A).PosSemidef := by
  refine posSemidef_of_re_form ?_ fun x => ?_
  · change (c • A)ᴴ = c • A
    rw [conjTranspose_smul, star_trivial, hA.1.eq]
  · rw [smul_mulVec, dotProduct_smul, Complex.smul_re]
    exact mul_nonneg hc (re_form_nonneg hA x)

/-- A weighted expectation of PSD matrices with nonnegative weights is PSD. -/
theorem mgt_promoExpect_posSemidef {Ω : Type*} [Fintype Ω] {w : Ω → ℝ}
    (hw : ∀ x, 0 ≤ w x) {F : Ω → Matrix n n ℂ} (hF : ∀ x, (F x).PosSemidef) :
    (promoExpect w F).PosSemidef := by
  unfold promoExpect
  exact posSemidef_sum Finset.univ fun x _ => mgt_smul_posSemidef (hw x) (hF x)

/-- A weighted sum of PSD matrices vanishes only if every strictly weighted
summand vanishes. -/
theorem mgt_promoExpect_eq_zero {Ω : Type*} [Fintype Ω] {w : Ω → ℝ}
    (hw : ∀ x, 0 ≤ w x) {F : Ω → Matrix n n ℂ} (hF : ∀ x, (F x).PosSemidef)
    (h0 : promoExpect w F = 0) : ∀ x, w x ≠ 0 → F x = 0 := by
  intro x hx
  have hterm : ∀ y ∈ Finset.univ, ((w y • F y : Matrix n n ℂ)).PosSemidef :=
    fun y _ => mgt_smul_posSemidef (hw y) (hF y)
  have hz := prune_eq_zero_of_sum_eq_zero (fun y => w y • F y)
    (fun y => mgt_smul_posSemidef (hw y) (hF y)) Finset.univ h0 x (Finset.mem_univ x)
  have hwx : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hx)
  have := congrArg (fun A => (w x)⁻¹ • A) hz
  simpa only [smul_smul, inv_mul_cancel₀ hwx.ne', one_smul, smul_zero] using this

omit [Fintype n] in
/-- Conjugate transposes pass through weighted matrix expectations. -/
theorem mgt_promoExpect_conjTranspose {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (F : Ω → Matrix n n ℂ) :
    (promoExpect w F)ᴴ = promoExpect w fun x => (F x)ᴴ := by
  unfold promoExpect
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [conjTranspose_smul, star_trivial]

omit [Fintype n] in
/-- Finite sums of observables pass through weighted matrix expectations. -/
theorem mgt_promoExpect_sum {Ω κ : Type*} [Fintype Ω] (w : Ω → ℝ)
    (s : Finset κ) (F : κ → Ω → Matrix n n ℂ) :
    promoExpect w (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, promoExpect w (F i) := by
  unfold promoExpect
  calc ∑ x, w x • ∑ i ∈ s, F i x
      = ∑ x, ∑ i ∈ s, w x • F i x :=
        Finset.sum_congr rfl fun x _ => Finset.smul_sum
    _ = ∑ i ∈ s, ∑ x, w x • F i x := Finset.sum_comm

/-- Equal Hermitian matrices have equal spectral support projections. -/
theorem mgt_supportProj_congr {A B : Matrix n n ℂ} [DecidableEq n] (h : A = B)
    (hA : A.IsHermitian) (hB : B.IsHermitian) : supportProj hA = supportProj hB := by
  subst h
  rfl

/-- Conjugating a PSD matrix by its Moore–Penrose inverse square root yields
its spectral support projection. -/
theorem mgt_pinvSqrt_conj_support {C : Matrix n n ℂ} [DecidableEq n]
    (hC : C.PosSemidef) :
    SourceAction.pinvSqrtSA hC.1 * C * SourceAction.pinvSqrtSA hC.1
      = supportProj hC.1 := by
  have h1 : SourceAction.pinvSqrtSA hC.1 * C * SourceAction.pinvSqrtSA hC.1
      = SourceAction.pinvSqrtSA hC.1 * spectralFunction hC.1 id
        * SourceAction.pinvSqrtSA hC.1 := by
    rw [spectralFunction_id]
  rw [h1]
  unfold SourceAction.pinvSqrtSA supportProj
  rw [spectralFunction_mul, spectralFunction_mul]
  refine spectralFunction_congr hC.1 fun i => ?_
  simp only [id_eq]
  split_ifs with hpos
  · have hs : Real.sqrt (hC.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have hm : Real.sqrt (hC.1.eigenvalues i) * Real.sqrt (hC.1.eigenvalues i)
        = hC.1.eigenvalues i := Real.mul_self_sqrt hpos.le
    field_simp
    linarith [hm, Real.sq_sqrt hpos.le]
  · rw [zero_mul, zero_mul]

/-- The Moore–Penrose inverse square root times the spectral square root of a
PSD matrix is its spectral support projection. -/
theorem mgt_pinvSqrt_mul_sqrt {C : Matrix n n ℂ} [DecidableEq n]
    (hC : C.PosSemidef) :
    SourceAction.pinvSqrtSA hC.1 * spectralFunction hC.1 Real.sqrt
      = supportProj hC.1 := by
  unfold SourceAction.pinvSqrtSA supportProj
  rw [spectralFunction_mul]
  refine spectralFunction_congr hC.1 fun i => ?_
  split_ifs with hpos
  · exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hpos).ne'
  · rw [zero_mul]

end MgtPosSection

/-! ### `thm:GT-projective-head-Pythagoras` — Projective common-response Pythagoras

Rendering: the occurring history law is a full-support weighted finite carrier
`(Ω, w)`; the filtration `𝓕_0 ⊆ ⋯ ⊆ 𝓕_L` is a `MgtFilt.Chain` of finite
records; `V` is the operator-valued writer, `marti`/`dinc` its martingale and
increments (ML.1).  The protocol data are the contraction `𝓡` (rendered by
`(1 - 𝓡ᴴ𝓡).PosSemidef`) and the nested projections `Π_0 ≤ ⋯ ≤ Π_H` (ML.2),
with `Π_{-1} = 0` absorbed into `headQ` (ML.3).  `head_pythagoras` is the boxed
decomposition (ML.7), `displayed_forms_posSemidef` the positivity of all
displayed packets (ML.4–ML.6), `cross_level_orthogonality` the boxed (ML.8)
for an arbitrary deterministic `B`, and `level_packets_additive` the closing
clause: packets sum across levels without cross-level correction. -/

section ProjHeadSection

namespace ProjHead

open MgtFilt

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E S Y : Type*} [Fintype E] [Fintype S] [Fintype Y] [DecidableEq Y]
  [DecidableEq S]

/-- An orthogonal projection: Hermitian and idempotent. -/
def IsOrthProj (P : Matrix Y Y ℂ) : Prop := Pᴴ = P ∧ P * P = P

/-- The head packets `Q_0 = Π_0`, `Q_h = Π_h - Π_{h-1}` (ML.3), with the
manuscript convention `Π_{-1} = 0` built in. -/
def headQ (P : ℕ → Matrix Y Y ℂ) : ℕ → Matrix Y Y ℂ
  | 0 => P 0
  | h + 1 => P (h + 1) - P h

omit [Fintype Y] [DecidableEq Y] in
/-- The head packets telescope to the final head `Π_H`. -/
theorem headQ_sum (P : ℕ → Matrix Y Y ℂ) (H : ℕ) :
    ∑ h ∈ Finset.range (H + 1), headQ P h = P H := by
  induction H with
  | zero => rw [Finset.range_one, Finset.sum_singleton]; rfl
  | succ H ih =>
    rw [Finset.sum_range_succ, ih]
    change P H + (P (H + 1) - P H) = P (H + 1)
    abel

omit [DecidableEq Y] in
/-- A PSD matrix whose negative is also PSD vanishes. -/
theorem psd_neg_zero {A : Matrix Y Y ℂ} (h1 : A.PosSemidef)
    (h2 : (-A).PosSemidef) : A = 0 := by
  rw [ext_iff_mulVec]
  intro v
  rw [zero_mulVec]
  refine (h1.dotProduct_mulVec_zero_iff v).mp ?_
  have ha := h1.dotProduct_mulVec_nonneg v
  have hb := h2.dotProduct_mulVec_nonneg v
  rw [neg_mulVec, dotProduct_neg] at hb
  have hle : star v ⬝ᵥ (A *ᵥ v) ≤ 0 := by
    have := neg_nonneg.mp hb
    exact this
  exact le_antisymm hle ha

/-- **Nested-projection absorption**: if `P ≤ Q` in the Loewner order for
orthogonal projections `P, Q`, then `QP = P = PQ`. -/
theorem proj_absorb {P Q : Matrix Y Y ℂ} (hP : IsOrthProj P) (hQ : IsOrthProj Q)
    (hle : (Q - P).PosSemidef) : Q * P = P ∧ P * Q = P := by
  have h1Q : ((1 : Matrix Y Y ℂ) - Q)ᴴ = 1 - Q := by
    rw [conjTranspose_sub, conjTranspose_one, hQ.1]
  have h1Qidem : ((1 : Matrix Y Y ℂ) - Q) * (1 - Q) = 1 - Q := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hQ.2]
    abel
  -- the defect `X = (1-Q)P` has Gram `P - PQP`, which is also `⪯ 0`
  have hgram : (((1 : Matrix Y Y ℂ) - Q) * P)ᴴ * (((1 : Matrix Y Y ℂ) - Q) * P)
      = P - P * Q * P := by
    rw [conjTranspose_mul, h1Q, hP.1]
    calc P * (1 - Q) * ((1 - Q) * P)
        = P * ((1 - Q) * (1 - Q)) * P := by simp only [Matrix.mul_assoc]
      _ = P * (1 - Q) * P := by rw [h1Qidem]
      _ = P - P * Q * P := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP.2]
  have hpos : (P - P * Q * P).PosSemidef := by
    rw [← hgram]
    exact posSemidef_conjTranspose_mul_self _
  have hneg : (-(P - P * Q * P)).PosSemidef := by
    have hcon := hle.conjTranspose_mul_mul_same P
    have heq : Pᴴ * (Q - P) * P = -(P - P * Q * P) := by
      rw [hP.1]
      simp only [Matrix.mul_sub, Matrix.sub_mul, hP.2]
      abel
    rwa [heq] at hcon
  have hzero : ((1 : Matrix Y Y ℂ) - Q) * P = 0 := by
    refine conjTranspose_mul_self_eq_zero.mp ?_
    rw [hgram]
    exact psd_neg_zero hpos hneg
  have hQP : Q * P = P := by
    have := hzero
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    exact this.symm
  refine ⟨hQP, ?_⟩
  have := congrArg conjTranspose hQP
  rwa [conjTranspose_mul, hP.1, hQ.1] at this

/-- Under nesting, every head packet is an orthogonal projection. -/
theorem headQ_isOrthProj {P : ℕ → Matrix Y Y ℂ} {H : ℕ}
    (hproj : ∀ h ≤ H, IsOrthProj (P h))
    (hmono : ∀ h < H, (P (h + 1) - P h).PosSemidef) :
    ∀ h ≤ H, IsOrthProj (headQ P h) := by
  intro h hh
  cases h with
  | zero => exact hproj 0 (Nat.zero_le H)
  | succ h =>
    have hP := hproj h (le_of_lt (Nat.lt_of_succ_le hh))
    have hP1 := hproj (h + 1) hh
    obtain ⟨habs1, habs2⟩ := proj_absorb hP hP1 (hmono h (Nat.lt_of_succ_le hh))
    constructor
    · change (P (h + 1) - P h)ᴴ = P (h + 1) - P h
      rw [conjTranspose_sub, hP1.1, hP.1]
    · change (P (h + 1) - P h) * (P (h + 1) - P h) = P (h + 1) - P h
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, hP1.2, habs1, habs2, hP.2]
      abel

/-- The complementary packet `Q_irr = 1 - Π_H` is an orthogonal projection. -/
theorem irrQ_isOrthProj {P : Matrix Y Y ℂ} (hP : IsOrthProj P) :
    IsOrthProj ((1 : Matrix Y Y ℂ) - P) := by
  constructor
  · rw [conjTranspose_sub, conjTranspose_one, hP.1]
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hP.2]
    abel

omit [DecidableEq Y] [DecidableEq S] in
/-- A projection-sandwiched response form is PSD in expectation. -/
theorem sandwich_posSemidef {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    {Q : Matrix Y Y ℂ} (hQ : IsOrthProj Q) (R : Matrix Y S ℂ)
    (D : Ω → Matrix S E ℂ) :
    (promoExpect w fun x => (D x)ᴴ * Rᴴ * Q * R * D x).PosSemidef := by
  refine mgt_promoExpect_posSemidef hw fun x => ?_
  have hkey : (D x)ᴴ * Rᴴ * Q * R * D x
      = (Q * R * D x)ᴴ * (Q * R * D x) := by
    rw [conjTranspose_mul, conjTranspose_mul, hQ.1]
    calc (D x)ᴴ * Rᴴ * Q * R * D x
        = (D x)ᴴ * Rᴴ * (Q * Q) * R * D x := by rw [hQ.2]
      _ = (D x)ᴴ * (Rᴴ * (Q * (Q * (R * D x)))) := by simp only [Matrix.mul_assoc]
      _ = (D x)ᴴ * Rᴴ * Q * (Q * R * D x) := by simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hkey]
  exact posSemidef_conjTranspose_mul_self _

omit [Fintype ι] in
/-- **Positivity of all displayed forms** (ML.4–ML.6): the increment Gram
`G_ℓ`, every represented-head packet `G_{ℓ,h}^head`, the irreducible packet
`G_ℓ^irr`, and the response-null packet `G_ℓ^null` are PSD. -/
theorem displayed_forms_posSemidef {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (V : Ω → Matrix S E ℂ) (ℓ : ℕ) (R : Matrix Y S ℂ)
    (hR : ((1 : Matrix S S ℂ) - Rᴴ * R).PosSemidef)
    {P : ℕ → Matrix Y Y ℂ} {H : ℕ} (hproj : ∀ h ≤ H, IsOrthProj (P h))
    (hmono : ∀ h < H, (P (h + 1) - P h).PosSemidef) :
    (promoExpect w fun x => (dinc w f V ℓ x)ᴴ * dinc w f V ℓ x).PosSemidef ∧
    (∀ h ≤ H, (promoExpect w fun x =>
      (dinc w f V ℓ x)ᴴ * Rᴴ * headQ P h * R * dinc w f V ℓ x).PosSemidef) ∧
    (promoExpect w fun x => (dinc w f V ℓ x)ᴴ * Rᴴ * ((1 : Matrix Y Y ℂ) - P H)
      * R * dinc w f V ℓ x).PosSemidef ∧
    (promoExpect w fun x => (dinc w f V ℓ x)ᴴ * ((1 : Matrix S S ℂ) - Rᴴ * R)
      * dinc w f V ℓ x).PosSemidef := by
  have hw' : ∀ x, 0 ≤ w x := fun x => (hw x).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mgt_promoExpect_posSemidef hw' fun x => posSemidef_conjTranspose_mul_self _
  · intro h hh
    exact sandwich_posSemidef hw' (headQ_isOrthProj hproj hmono h hh) R _
  · exact sandwich_posSemidef hw' (irrQ_isOrthProj (hproj H le_rfl)) R _
  · refine mgt_promoExpect_posSemidef hw' fun x => ?_
    exact hR.conjTranspose_mul_mul_same (dinc w f V ℓ x)

omit [Fintype E] in
/-- **(ML.7)** The exact head/irreducible/response-null decomposition of the
increment Gram: `G_ℓ = ∑_h G_{ℓ,h}^head + G_ℓ^irr + G_ℓ^null`. -/
theorem head_pythagoras (w : Ω → ℝ) (D : Ω → Matrix S E ℂ) (R : Matrix Y S ℂ)
    (P : ℕ → Matrix Y Y ℂ) (H : ℕ) :
    promoExpect w (fun x => (D x)ᴴ * D x)
      = (∑ h ∈ Finset.range (H + 1),
          promoExpect w fun x => (D x)ᴴ * Rᴴ * headQ P h * R * D x)
        + (promoExpect w fun x =>
            (D x)ᴴ * Rᴴ * ((1 : Matrix Y Y ℂ) - P H) * R * D x)
        + promoExpect w fun x =>
            (D x)ᴴ * ((1 : Matrix S S ℂ) - Rᴴ * R) * D x := by
  unfold promoExpect
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.smul_sum, ← smul_add, ← smul_add]
  congr 1
  have hsum : ∑ h ∈ Finset.range (H + 1), (D x)ᴴ * Rᴴ * headQ P h * R * D x
      = (D x)ᴴ * Rᴴ * P H * R * D x := by
    calc ∑ h ∈ Finset.range (H + 1), (D x)ᴴ * Rᴴ * headQ P h * R * D x
        = ∑ h ∈ Finset.range (H + 1), (D x)ᴴ * Rᴴ * (headQ P h * (R * D x)) :=
          Finset.sum_congr rfl fun h _ => by simp only [Matrix.mul_assoc]
      _ = (D x)ᴴ * Rᴴ * (∑ h ∈ Finset.range (H + 1), headQ P h * (R * D x)) := by
          rw [Matrix.mul_sum]
      _ = (D x)ᴴ * Rᴴ * (P H * (R * D x)) := by rw [← Matrix.sum_mul, headQ_sum]
      _ = (D x)ᴴ * Rᴴ * P H * R * D x := by simp only [Matrix.mul_assoc]
  rw [hsum]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

omit [Fintype E] [DecidableEq S] in
/-- **(ML.8)** Cross-level orthogonality: for every deterministic `B` and
`j < k`, the mixed increment expectation vanishes. -/
theorem cross_level_orthogonality {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) (V : Ω → Matrix S E ℂ)
    (B : Matrix S S ℂ) {j k : ℕ} (hjk : j < k) :
    promoExpect w (fun x => (dinc w f V j x)ᴴ * B * dinc w f V k x) = 0 := by
  have h := dinc_orth_mul hw hchain V hjk (fun x => (dinc w f V j x)ᴴ * B)
    fun x y hxy =>
      congrArg (· * B) (congrArg conjTranspose (detOn_dinc hchain V j x y hxy))
  exact h

omit [Fintype E] [DecidableEq S] in
/-- The closing clause of ML.8: the level packets of any deterministic bounded
observable sum across levels without a cross-level correction. -/
theorem level_packets_additive {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) (V : Ω → Matrix S E ℂ)
    (B : Matrix S S ℂ) (L : ℕ) :
    promoExpect w (fun x => (marti w f V L x)ᴴ * B * marti w f V L x)
      = ∑ ℓ ∈ Finset.range (L + 1),
          promoExpect w fun x => (dinc w f V ℓ x)ᴴ * B * dinc w f V ℓ x := by
  have hpt : ∀ x, (marti w f V L x)ᴴ * B * marti w f V L x
      = ∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (L + 1),
          (dinc w f V j x)ᴴ * B * dinc w f V k x := by
    intro x
    rw [show marti w f V L x = ∑ ℓ ∈ Finset.range (L + 1), dinc w f V ℓ x from
      (sum_dinc w f V L x).symm]
    calc (∑ j ∈ Finset.range (L + 1), dinc w f V j x)ᴴ * B
          * ∑ k ∈ Finset.range (L + 1), dinc w f V k x
        = (∑ j ∈ Finset.range (L + 1), (dinc w f V j x)ᴴ * B)
            * ∑ k ∈ Finset.range (L + 1), dinc w f V k x := by
          rw [conjTranspose_sum, Matrix.sum_mul]
      _ = ∑ j ∈ Finset.range (L + 1), (dinc w f V j x)ᴴ * B
            * ∑ k ∈ Finset.range (L + 1), dinc w f V k x := by
          rw [Matrix.sum_mul]
      _ = ∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (L + 1),
            (dinc w f V j x)ᴴ * B * dinc w f V k x :=
          Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_sum]
  have hdouble : promoExpect w (fun x => (marti w f V L x)ᴴ * B * marti w f V L x)
      = ∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range (L + 1),
          promoExpect w fun x => (dinc w f V j x)ᴴ * B * dinc w f V k x := by
    calc promoExpect w (fun x => (marti w f V L x)ᴴ * B * marti w f V L x)
        = promoExpect w fun x => ∑ j ∈ Finset.range (L + 1),
            ∑ k ∈ Finset.range (L + 1), (dinc w f V j x)ᴴ * B * dinc w f V k x :=
          congrArg (promoExpect w) (funext hpt)
      _ = _ := by
          rw [mgt_promoExpect_sum]
          exact Finset.sum_congr rfl fun j _ => mgt_promoExpect_sum ..
  rw [hdouble]
  refine Finset.sum_congr rfl fun j hj => ?_
  refine Finset.sum_eq_single_of_mem j hj fun k _ hkj => ?_
  rcases lt_or_gt_of_ne (Ne.symm hkj) with hlt | hgt
  · -- `j < k`: direct cross-level orthogonality
    exact cross_level_orthogonality hw hchain V B hlt
  · -- `k < j`: conjugate-transposed cross-level orthogonality
    have h0 := cross_level_orthogonality hw hchain V Bᴴ hgt
    have hconj := congrArg conjTranspose h0
    rw [mgt_promoExpect_conjTranspose, conjTranspose_zero] at hconj
    calc promoExpect w (fun x => (dinc w f V j x)ᴴ * B * dinc w f V k x)
        = promoExpect w fun x =>
            ((dinc w f V k x)ᴴ * Bᴴ * dinc w f V j x)ᴴ :=
          congrArg (promoExpect w) (funext fun x => by
            simp only [conjTranspose_mul, conjTranspose_conjTranspose,
              Matrix.mul_assoc])
      _ = 0 := hconj

end ProjHead

end ProjHeadSection

/-! ### `thm:GT-projective-head-heldout` — Cross-level held-out and cutoff transport

Rendering: (ML.19) is the boxed vanishing of the mixed response row, an
instance of the projective cross-level orthogonality; the surrounding held-out
prose carries no further mathematical claim.  For (ML.20)–(ML.21), two
adjacent cutoffs carry source/terminal spaces and level writers over one
carrier; the cutoff-`X` conditional `𝔼[·|𝓕_X]` is `MgtFilt.cexp` on the
cutoff-`X` record `g`.  `head_block_compress` and `irr_block_compress` are the
map-level componentwise compressions of every represented-head and
final-irreducible block, `packet_compress` the pointwise packet consequence
through (ML.20), `gram_block_compress` the Gram-level consequence, and
`transport_compose` shows staged transport data compose to direct transport
data, so direct and staged transport agree. -/

section HeadHeldoutSection

namespace HeadHeldout

open MgtFilt ProjHead

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E S : Type*} [Fintype E] [Fintype S]

omit [Fintype E] in
/-- **(ML.19)** The cross-level mixed response row vanishes:
`C_jk^resp = 𝔼[D_j^* 𝓡^* 𝓡 D_k] = 0` for `j < k`. -/
theorem cross_response_zero {Y : Type*} [Fintype Y] {w : Ω → ℝ}
    (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι} (hchain : Chain f)
    (V : Ω → Matrix S E ℂ) (R : Matrix Y S ℂ) {j k : ℕ} (hjk : j < k) :
    promoExpect w (fun x => (dinc w f V j x)ᴴ * (Rᴴ * R) * dinc w f V k x) = 0 :=
  cross_level_orthogonality hw hchain V (Rᴴ * R) hjk

variable {SX SY TX TY : Type*} [Fintype SX] [Fintype SY] [Fintype TX] [Fintype TY]
variable [DecidableEq TX] [DecidableEq TY]

omit [Fintype SX] [DecidableEq TX] [DecidableEq TY] in
/-- **(ML.21, head blocks)** Every represented-head block compresses
separately: `Q_{h,X} 𝓡_X = R^term Q_{h,Y} 𝓡_Y J^src`. -/
theorem head_block_compress {RX : Matrix TX SX ℂ} {RY : Matrix TY SY ℂ}
    {Jsrc : Matrix SY SX ℂ} {Rterm : Matrix TX TY ℂ}
    {PX : ℕ → Matrix TX TX ℂ} {PY : ℕ → Matrix TY TY ℂ} {H : ℕ}
    (hR : Rterm * RY * Jsrc = RX)
    (hP : ∀ h ≤ H, Rterm * PY h = PX h * Rterm) :
    ∀ h ≤ H, headQ PX h * RX = Rterm * headQ PY h * RY * Jsrc := by
  intro h hh
  have hcomm : headQ PX h * Rterm = Rterm * headQ PY h := by
    cases h with
    | zero => exact (hP 0 (Nat.zero_le H)).symm
    | succ h =>
      change (PX (h + 1) - PX h) * Rterm = Rterm * (PY (h + 1) - PY h)
      rw [Matrix.sub_mul, Matrix.mul_sub, hP (h + 1) hh,
        hP h (le_of_lt (Nat.lt_of_succ_le hh))]
  calc headQ PX h * RX = headQ PX h * Rterm * RY * Jsrc := by
        rw [← hR]; simp only [Matrix.mul_assoc]
    _ = Rterm * headQ PY h * RY * Jsrc := by rw [hcomm]

omit [Fintype SX] in
/-- **(ML.21, final-irreducible block)** The final-irreducible block compresses
separately: `Q_{irr,X} 𝓡_X = R^term Q_{irr,Y} 𝓡_Y J^src`, given that the
terminal transport is a coisometry on the represented sector
(`R^term (R^term)ᴴ = 1`, the identification of the two cutoff terminal
carriers on the compressed range). -/
theorem irr_block_compress {RX : Matrix TX SX ℂ} {RY : Matrix TY SY ℂ}
    {Jsrc : Matrix SY SX ℂ} {Rterm : Matrix TX TY ℂ}
    {PX : ℕ → Matrix TX TX ℂ} {PY : ℕ → Matrix TY TY ℂ} {H : ℕ}
    (hR : Rterm * RY * Jsrc = RX)
    (hP : ∀ h ≤ H, Rterm * PY h = PX h * Rterm) :
    ((1 : Matrix TX TX ℂ) - PX H) * RX
      = Rterm * ((1 : Matrix TY TY ℂ) - PY H) * RY * Jsrc := by
  have hcomm : ((1 : Matrix TX TX ℂ) - PX H) * Rterm
      = Rterm * ((1 : Matrix TY TY ℂ) - PY H) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP H le_rfl]
  calc ((1 : Matrix TX TX ℂ) - PX H) * RX
      = ((1 : Matrix TX TX ℂ) - PX H) * Rterm * RY * Jsrc := by
        rw [← hR]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hcomm]

omit [Fintype ι] [Fintype E] [DecidableEq TX] [DecidableEq TY] in
/-- **(ML.20 + ML.21, pointwise packets)** Under the conditional-expectation
transport (ML.20), each head component at cutoff `X` is the terminal
compression of the cutoff-`X` conditional of the cutoff-`Y` head component. -/
theorem packet_compress {w : Ω → ℝ} {g : Ω → ι}
    {RX : Matrix TX SX ℂ} {RY : Matrix TY SY ℂ} {Jsrc : Matrix SY SX ℂ}
    {Rterm : Matrix TX TY ℂ} {PX : ℕ → Matrix TX TX ℂ} {PY : ℕ → Matrix TY TY ℂ}
    {H : ℕ} (hR : Rterm * RY * Jsrc = RX)
    (hP : ∀ h ≤ H, Rterm * PY h = PX h * Rterm)
    {DX : Ω → Matrix SX E ℂ} {DY : Ω → Matrix SY E ℂ}
    (hJ : ∀ x, Jsrc * DX x = cexp w g DY x) :
    ∀ h ≤ H, ∀ x, headQ PX h * RX * DX x
      = Rterm * (headQ PY h * RY * cexp w g DY x) := by
  intro h hh x
  rw [head_block_compress hR hP h hh]
  rw [show Rterm * headQ PY h * RY * Jsrc * DX x
      = Rterm * (headQ PY h * RY * (Jsrc * DX x)) by simp only [Matrix.mul_assoc]]
  rw [hJ x]

omit [Fintype ι] [Fintype E] [DecidableEq TY] in
/-- **(ML.21, Gram level)** The represented-head Gram packet at cutoff `X` is
the `R^term`-compressed Gram of the conditioned cutoff-`Y` head component. -/
theorem gram_block_compress {w : Ω → ℝ} {g : Ω → ι}
    {RX : Matrix TX SX ℂ} {RY : Matrix TY SY ℂ} {Jsrc : Matrix SY SX ℂ}
    {Rterm : Matrix TX TY ℂ} {PX : ℕ → Matrix TX TX ℂ} {PY : ℕ → Matrix TY TY ℂ}
    {H : ℕ} (hR : Rterm * RY * Jsrc = RX)
    (hP : ∀ h ≤ H, Rterm * PY h = PX h * Rterm)
    (hprojX : ∀ h ≤ H, IsOrthProj (PX h))
    (hmonoX : ∀ h < H, (PX (h + 1) - PX h).PosSemidef)
    {DX : Ω → Matrix SX E ℂ} {DY : Ω → Matrix SY E ℂ}
    (hJ : ∀ x, Jsrc * DX x = cexp w g DY x) :
    ∀ h ≤ H, promoExpect w (fun x => (DX x)ᴴ * RXᴴ * headQ PX h * RX * DX x)
      = promoExpect w fun x => (headQ PY h * RY * cexp w g DY x)ᴴ
          * (Rtermᴴ * Rterm) * (headQ PY h * RY * cexp w g DY x) := by
  intro h hh
  refine congrArg (promoExpect w) (funext fun x => ?_)
  have hQ := headQ_isOrthProj hprojX hmonoX h hh
  have hfact : (DX x)ᴴ * RXᴴ * headQ PX h * RX * DX x
      = (headQ PX h * RX * DX x)ᴴ * (headQ PX h * RX * DX x) := by
    rw [conjTranspose_mul, conjTranspose_mul, hQ.1]
    calc (DX x)ᴴ * RXᴴ * headQ PX h * RX * DX x
        = (DX x)ᴴ * RXᴴ * (headQ PX h * headQ PX h) * RX * DX x := by rw [hQ.2]
      _ = (DX x)ᴴ * (RXᴴ * (headQ PX h)) * (headQ PX h * RX * DX x) := by
          simp only [Matrix.mul_assoc]
  rw [hfact, packet_compress hR hP hJ h hh x, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

omit [Fintype E] [DecidableEq TX] [DecidableEq TY] in
/-- **(ML.20–ML.21, composition)** Composable stage transport data induce the
direct transport data across a double cutoff step, so direct and staged
transport agree. -/
theorem transport_compose {SZ TZ : Type*} [Fintype SZ] [Fintype TZ]
    {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {gX gY : Ω → ι} (href : Refines gX gY)
    {RX : Matrix TX SX ℂ} {RY : Matrix TY SY ℂ} {RZ : Matrix TZ SZ ℂ}
    {J1 : Matrix SY SX ℂ} {J2 : Matrix SZ SY ℂ}
    {T1 : Matrix TX TY ℂ} {T2 : Matrix TY TZ ℂ}
    {PX : ℕ → Matrix TX TX ℂ} {PY : ℕ → Matrix TY TY ℂ} {PZ : ℕ → Matrix TZ TZ ℂ}
    {H : ℕ} (hR1 : T1 * RY * J1 = RX) (hR2 : T2 * RZ * J2 = RY)
    (hP1 : ∀ h ≤ H, T1 * PY h = PX h * T1) (hP2 : ∀ h ≤ H, T2 * PZ h = PY h * T2)
    {DX : Ω → Matrix SX E ℂ} {DY : Ω → Matrix SY E ℂ} {DZ : Ω → Matrix SZ E ℂ}
    (hJ1 : ∀ x, J1 * DX x = cexp w gX DY x) (hJ2 : ∀ x, J2 * DY x = cexp w gY DZ x) :
    (T1 * T2) * RZ * (J2 * J1) = RX ∧
    (∀ h ≤ H, (T1 * T2) * PZ h = PX h * (T1 * T2)) ∧
    ∀ x, (J2 * J1) * DX x = cexp w gX DZ x := by
  refine ⟨?_, ?_, ?_⟩
  · have hmid : T1 * (T2 * RZ * J2) * J1 = RX := by rw [hR2]; exact hR1
    calc (T1 * T2) * RZ * (J2 * J1)
        = T1 * (T2 * RZ * J2) * J1 := by simp only [Matrix.mul_assoc]
      _ = RX := hmid
  · intro h hh
    calc (T1 * T2) * PZ h = T1 * (T2 * PZ h) := by rw [Matrix.mul_assoc]
      _ = T1 * (PY h * T2) := by rw [hP2 h hh]
      _ = (T1 * PY h) * T2 := by rw [Matrix.mul_assoc]
      _ = PX h * (T1 * T2) := by rw [hP1 h hh, Matrix.mul_assoc]
  · intro x
    have hstep : (J2 * J1) * DX x = J2 * cexp w gX DY x := by
      rw [Matrix.mul_assoc, hJ1 x]
    have hcomm : (fun y => J2 * cexp w gX DY y) = cexp w gX fun y => J2 * DY y := by
      have h := cexp_comp_linear (N := Matrix SZ E ℂ) w gX (mulLeftLM J2) DY
      exact h.symm
    have hfun : (fun y => J2 * DY y) = cexp w gY DZ := funext hJ2
    calc (J2 * J1) * DX x = J2 * cexp w gX DY x := hstep
      _ = cexp w gX (fun y => J2 * DY y) x := congrFun hcomm x
      _ = cexp w gX (cexp w gY DZ) x := by rw [hfun]
      _ = cexp w gX DZ x := congrFun (cexp_cexp hw href DZ) x

end HeadHeldout

end HeadHeldoutSection

/-! ### `thm:GT-ancestry-response-nonduplication` — Ancestry-resolved terminal response

Rendering: the follower packet (AN.1) is `follGram J = JᴴJ`,
`follProj J = J (JᴴJ)† Jᴴ` (the repo `colProj`), and
`follTheta J T = (JᴴJ)† Jᴴ T`; the ancestry residual (AN.2) is
`ancRes J T = Tᴴ(1 - P_J)T`.  (A1) is `follProj_props` (orthogonal projection
onto `Ran J`, rendered by Hermitian idempotence, `P_J J = J`, and a column
factorization through `J`) together with the Pythagoras `ancestry_pythagoras`
(AN.3) and positivity `ancRes_posSemidef`.  (A2) is `ancRes_eq_zero_iff`
(AN.4).  (A3) renders the polar synthesis `ancJ = (1-P_J)T ℂ_anc^{†/2}`:
`ancJ_partial_isometry` (isometry on the residual support),
`ancJ_polar` (exact polar reconstruction against the spectral square root),
`ancJ_range_proj` (its range projection is the projection onto the
unexplained response range), `ancRes_rank` and the two minimality clauses
`anc_rank_min` (every enlarged follower dictionary reproducing the response
needs at least `rank ℂ_anc` new coordinates) and `anc_rank_attained`
(a follower-sector dictionary of exactly `rank ℂ_anc` coordinates suffices).
(A4) is `ancestry_cross_level_zero` (AN.6) and `ancestry_residual_additive`
(cross-level additivity); the componentwise-transport clause is the
intertwining statement of the heldout record above. -/

section AncestrySection

namespace AncestryND

open MgtFilt ProjHead

variable {Y U E : Type*} [Fintype Y] [Fintype U] [Fintype E]
variable [DecidableEq Y] [DecidableEq U] [DecidableEq E]

/-- The follower Gram `G_J = JᴴJ` (AN.1). -/
def follGram (J : Matrix Y U ℂ) : Matrix U U ℂ := Jᴴ * J

/-- The follower range projection `P_J = J G_J† Jᴴ` (AN.1); definitionally the
repo column-range projection `colProj J`. -/
noncomputable def follProj (J : Matrix Y U ℂ) : Matrix Y Y ℂ := colProj J

/-- The follower coefficient map `Θ_J = G_J† Jᴴ T` (AN.1). -/
noncomputable def follTheta (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) : Matrix U E ℂ :=
  pinv (posSemidef_conjTranspose_mul_self J).1 * Jᴴ * T

/-- The ancestry residual `ℂ_anc(T|J) = Tᴴ(1 - P_J)T` (AN.2). -/
noncomputable def ancRes (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) : Matrix E E ℂ :=
  Tᴴ * ((1 : Matrix Y Y ℂ) - follProj J) * T

/-- The unexplained response component `(1 - P_J)T`. -/
noncomputable def ancX (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) : Matrix Y E ℂ :=
  ((1 : Matrix Y Y ℂ) - follProj J) * T

omit [DecidableEq Y] in
/-- **(A1, projection clause)** `P_J` is the orthogonal projection onto
`Ran J`: Hermitian, idempotent, fixing `J`, and factoring through `J`. -/
theorem follProj_props (J : Matrix Y U ℂ) :
    IsOrthProj (follProj J) ∧ follProj J * J = J
      ∧ ∃ W : Matrix U Y ℂ, follProj J = J * W := by
  refine ⟨⟨colProj_isHermitian J, colProj_idem J⟩, colProj_mul_self J,
    ⟨pinv (posSemidef_conjTranspose_mul_self J).1 * Jᴴ, ?_⟩⟩
  unfold follProj colProj
  rw [Matrix.mul_assoc]

omit [Fintype E] [DecidableEq E] in
/-- The ancestry residual in explicit Gram form. -/
theorem ancRes_eq_gram (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) :
    ancRes J T = (ancX J T)ᴴ * ancX J T :=
  one_sub_colProj_gram J T

omit [DecidableEq E] in
/-- **(AN.2)** The ancestry residual is PSD. -/
theorem ancRes_posSemidef (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) :
    (ancRes J T).PosSemidef :=
  one_sub_colProj_gram_posSemidef J T

omit [Fintype E] [DecidableEq E] in
/-- **(AN.3)** The follower Pythagoras:
`TᴴT = Θ_Jᴴ G_J Θ_J + ℂ_anc(T|J)`. -/
theorem ancestry_pythagoras (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) :
    Tᴴ * T = (follTheta J T)ᴴ * follGram J * follTheta J T + ancRes J T := by
  have hG := posSemidef_conjTranspose_mul_self J
  have hheta : (follTheta J T)ᴴ * follGram J * follTheta J T
      = Tᴴ * follProj J * T := by
    unfold follTheta follGram follProj colProj
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      (pinv_isHermitian hG.1).eq]
    calc Tᴴ * (J * pinv hG.1) * (Jᴴ * J) * (pinv hG.1 * Jᴴ * T)
        = Tᴴ * (J * (pinv hG.1 * (Jᴴ * J) * pinv hG.1) * (Jᴴ * T)) := by
          simp only [Matrix.mul_assoc]
      _ = Tᴴ * (J * pinv hG.1 * (Jᴴ * T)) := by rw [pinv_mul_self_mul_pinv]
      _ = Tᴴ * (J * pinv hG.1 * Jᴴ) * T := by simp only [Matrix.mul_assoc]
  rw [hheta]
  unfold ancRes
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

omit [Fintype E] [DecidableEq E] in
/-- **(A2 / AN.4)** The ancestry residual vanishes exactly when the response is
a deterministic follower of the occurring source: `T = J Θ_J`. -/
theorem ancRes_eq_zero_iff (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) :
    ancRes J T = 0 ↔ T = J * follTheta J T := by
  constructor
  · intro h
    have hX : ancX J T = 0 := by
      refine conjTranspose_mul_self_eq_zero.mp ?_
      rw [← ancRes_eq_gram, h]
    have hPT : T = follProj J * T := by
      have h1 : ancX J T = T - follProj J * T := by
        unfold ancX
        rw [Matrix.sub_mul, Matrix.one_mul]
      rw [h1] at hX
      rw [← sub_eq_zero]
      rw [sub_eq_zero] at hX ⊢
      exact hX
    calc T = follProj J * T := hPT
      _ = J * follTheta J T := by
          unfold follProj colProj follTheta
          simp only [Matrix.mul_assoc]
  · intro h
    have hzero : ((1 : Matrix Y Y ℂ) - follProj J) * J = 0 := by
      unfold follProj
      rw [Matrix.sub_mul, Matrix.one_mul, colProj_mul_self, sub_self]
    unfold ancRes
    calc Tᴴ * ((1 : Matrix Y Y ℂ) - follProj J) * T
        = Tᴴ * (((1 : Matrix Y Y ℂ) - follProj J) * (J * follTheta J T)) := by
          rw [← h]
          simp only [Matrix.mul_assoc]
      _ = Tᴴ * (((1 : Matrix Y Y ℂ) - follProj J) * J * follTheta J T) := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hzero, Matrix.zero_mul, Matrix.mul_zero]

/-- The polar ancestry synthesis `J_anc = (1-P_J)T ℂ_anc^{†/2}` (AN.5). -/
noncomputable def ancJ (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) : Matrix Y E ℂ :=
  ancX J T * SourceAction.pinvSqrtSA (ancRes_posSemidef J T).1

/-- The spectral square root `ℂ_anc^{1/2}` of the ancestry residual. -/
noncomputable def ancSqrt (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) : Matrix E E ℂ :=
  spectralFunction (ancRes_posSemidef J T).1 Real.sqrt

/-- The spectral square root squares back to the ancestry residual. -/
theorem ancSqrt_mul_self (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) :
    ancSqrt J T * ancSqrt J T = ancRes J T := by
  unfold ancSqrt
  rw [spectralFunction_mul]
  have hid := spectralFunction_id (ancRes_posSemidef J T).1
  calc spectralFunction (ancRes_posSemidef J T).1 (fun l => Real.sqrt l * Real.sqrt l)
      = spectralFunction (ancRes_posSemidef J T).1 id := by
        refine spectralFunction_congr _ fun i => ?_
        exact Real.mul_self_sqrt ((ancRes_posSemidef J T).eigenvalues_nonneg i)
    _ = ancRes J T := hid

/-- **(A3, partial isometry)** `J_ancᴴ J_anc` is the support projection of the
ancestry residual: the polar synthesis is an isometry on the residual
support. -/
theorem ancJ_partial_isometry (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) :
    (ancJ J T)ᴴ * ancJ J T = supportProj (ancRes_posSemidef J T).1 := by
  have hC : (ancRes J T).IsHermitian := (ancRes_posSemidef J T).1
  have hg : (SourceAction.pinvSqrtSA hC)ᴴ = SourceAction.pinvSqrtSA hC :=
    (SourceAction.pinvSqrtSA_isHermitian hC).eq
  unfold ancJ
  rw [conjTranspose_mul, hg]
  calc SourceAction.pinvSqrtSA hC * (ancX J T)ᴴ
        * (ancX J T * SourceAction.pinvSqrtSA hC)
      = SourceAction.pinvSqrtSA hC * ((ancX J T)ᴴ * ancX J T)
          * SourceAction.pinvSqrtSA hC := by simp only [Matrix.mul_assoc]
    _ = SourceAction.pinvSqrtSA hC * ancRes J T * SourceAction.pinvSqrtSA hC := by
        rw [← ancRes_eq_gram]
    _ = supportProj hC := mgt_pinvSqrt_conj_support (ancRes_posSemidef J T)

/-- **(A3, polar reconstruction)** `J_anc ℂ_anc^{1/2} = (1-P_J)T`: the polar
synthesis exactly reconstructs the unexplained response component. -/
theorem ancJ_polar (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) :
    ancJ J T * ancSqrt J T = ancX J T := by
  have hC := (ancRes_posSemidef J T).1
  have hXX := posSemidef_conjTranspose_mul_self (ancX J T)
  unfold ancJ ancSqrt
  rw [Matrix.mul_assoc, mgt_pinvSqrt_mul_sqrt (ancRes_posSemidef J T),
    mgt_supportProj_congr (ancRes_eq_gram J T) (ancRes_posSemidef J T).1 hXX.1]
  exact mul_supportProj_gram (ancX J T)

/-- **(A3, range projection)** `J_anc J_ancᴴ` is the orthogonal projection
onto the unexplained response range `Ran((1-P_J)T)`. -/
theorem ancJ_range_proj (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) :
    ancJ J T * (ancJ J T)ᴴ = colProj (ancX J T) := by
  have hC := (ancRes_posSemidef J T).1
  have hXX := posSemidef_conjTranspose_mul_self (ancX J T)
  have hg : (SourceAction.pinvSqrtSA hC)ᴴ = SourceAction.pinvSqrtSA hC :=
    (SourceAction.pinvSqrtSA_isHermitian hC).eq
  unfold ancJ colProj
  rw [conjTranspose_mul, hg]
  calc ancX J T * SourceAction.pinvSqrtSA hC
        * (SourceAction.pinvSqrtSA hC * (ancX J T)ᴴ)
      = ancX J T * (SourceAction.pinvSqrtSA hC * SourceAction.pinvSqrtSA hC)
          * (ancX J T)ᴴ := by simp only [Matrix.mul_assoc]
    _ = ancX J T * pinv hC * (ancX J T)ᴴ := by rw [SourceAction.pinvSqrtSA_mul_self]
    _ = ancX J T * pinv hXX.1 * (ancX J T)ᴴ := by
        rw [pinv_congr (ancRes_eq_gram J T) hC hXX.1]

omit [DecidableEq E] in
/-- The rank of the ancestry residual equals the rank of the unexplained
response component. -/
theorem ancRes_rank (J : Matrix Y U ℂ) (T : Matrix Y E ℂ) :
    (ancRes J T).rank = (ancX J T).rank := by
  rw [ancRes_eq_gram]
  exact Matrix.rank_conjTranspose_mul_self (ancX J T)

omit [DecidableEq E] in
/-- **(A3, minimality)** Any enlarged follower dictionary reproducing the
response needs at least `rank ℂ_anc(T|J)` additional coordinates. -/
theorem anc_rank_min {U' : Type*} [Fintype U'] (J : Matrix Y U ℂ)
    (T : Matrix Y E ℂ) (J' : Matrix Y U' ℂ) (Θ₁ : Matrix U E ℂ)
    (Θ₂ : Matrix U' E ℂ) (hdec : T = J * Θ₁ + J' * Θ₂) :
    (ancRes J T).rank ≤ Fintype.card U' := by
  classical
  have hXe : ancX J T = ((1 : Matrix Y Y ℂ) - follProj J) * J' * Θ₂ := by
    unfold ancX
    have hzero : ((1 : Matrix Y Y ℂ) - follProj J) * (J * Θ₁) = 0 := by
      unfold follProj
      rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, colProj_mul_self,
        sub_self, Matrix.zero_mul]
    calc ((1 : Matrix Y Y ℂ) - follProj J) * T
        = ((1 : Matrix Y Y ℂ) - follProj J) * (J * Θ₁)
            + ((1 : Matrix Y Y ℂ) - follProj J) * (J' * Θ₂) := by
          rw [← Matrix.mul_add, ← hdec]
      _ = ((1 : Matrix Y Y ℂ) - follProj J) * J' * Θ₂ := by
          rw [hzero, zero_add, Matrix.mul_assoc]
  rw [ancRes_rank, hXe]
  calc (((1 : Matrix Y Y ℂ) - follProj J) * J' * Θ₂).rank
      ≤ (((1 : Matrix Y Y ℂ) - follProj J) * J').rank := Matrix.rank_mul_le_left _ _
    _ ≤ J'.rank := Matrix.rank_mul_le_right _ _
    _ ≤ Fintype.card U' := Matrix.rank_le_card_width _

/-- **(A3, attainment)** A follower-sector dictionary of exactly
`rank ℂ_anc(T|J)` additional response-source coordinates reproduces the
response: `T = J Θ_J + J' Θ₂` with `Q J' = J'` whenever `Q` fixes `T`
and `J`. -/
theorem anc_rank_attained (J : Matrix Y U ℂ) (T : Matrix Y E ℂ)
    (Q : Matrix Y Y ℂ) (hQT : Q * T = T) (hQJ : Q * J = J) :
    ∃ (J' : Matrix Y (Fin (ancRes J T).rank) ℂ)
      (Θ₂ : Matrix (Fin (ancRes J T).rank) E ℂ),
      T = J * follTheta J T + J' * Θ₂ ∧ Q * J' = J' := by
  classical
  set X := ancX J T with hXdef
  -- `Q` fixes the unexplained component
  have hQX : Q * X = X := by
    have hQP : Q * follProj J = follProj J := by
      unfold follProj colProj
      calc Q * (J * pinv (posSemidef_conjTranspose_mul_self J).1 * Jᴴ)
          = Q * J * pinv (posSemidef_conjTranspose_mul_self J).1 * Jᴴ := by
            simp only [Matrix.mul_assoc]
        _ = J * pinv (posSemidef_conjTranspose_mul_self J).1 * Jᴴ := by rw [hQJ]
    calc Q * X = Q * T - Q * follProj J * T := by
          rw [hXdef]
          unfold ancX
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_assoc]
      _ = T - follProj J * T := by rw [hQT, hQP]
      _ = X := by
          rw [hXdef]
          unfold ancX
          rw [Matrix.sub_mul, Matrix.one_mul]
  -- rank factorization of `X` through a basis of its column range
  have hr : Module.finrank ℂ ↥(LinearMap.range X.mulVecLin) = (ancRes J T).rank :=
    (ancRes_rank J T).symm
  let β : Module.Basis (Fin (ancRes J T).rank) ℂ ↥(LinearMap.range X.mulVecLin) :=
    Module.finBasisOfFinrankEq ℂ ↥(LinearMap.range X.mulVecLin) hr
  have hmem : ∀ e : E, X.col e ∈ LinearMap.range X.mulVecLin := by
    intro e
    refine ⟨Pi.single e 1, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single]
    funext i
    simp only [Matrix.col_apply, MulOpposite.op_one, one_smul]
  refine ⟨Matrix.of fun i k => (β k : Y → ℂ) i,
    Matrix.of fun k e => β.repr ⟨X.col e, hmem e⟩ k, ?_, ?_⟩
  · -- `T = J Θ_J + B K` with `B K = X` columnwise via `Basis.sum_repr`
    have hBK : (Matrix.of fun i k => (β k : Y → ℂ) i)
          * (Matrix.of fun k e => β.repr ⟨X.col e, hmem e⟩ k)
        = X := by
      ext i e
      have hrepr := β.sum_repr ⟨X.col e, hmem e⟩
      have hlhs : ((↑(∑ k, β.repr ⟨X.col e, hmem e⟩ k • β k) : Y → ℂ)) i
          = ∑ k, β.repr ⟨X.col e, hmem e⟩ k * (β k : Y → ℂ) i := by
        rw [show ((↑(∑ k, β.repr ⟨X.col e, hmem e⟩ k • β k) : Y → ℂ))
            = ∑ k, β.repr ⟨X.col e, hmem e⟩ k • (β k : Y → ℂ) by
          simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul]]
        rw [Finset.sum_apply]
        rfl
      rw [Matrix.mul_apply]
      simp only [Matrix.of_apply]
      calc ∑ k, (β k : Y → ℂ) i * β.repr ⟨X.col e, hmem e⟩ k
          = ∑ k, β.repr ⟨X.col e, hmem e⟩ k * (β k : Y → ℂ) i :=
            Finset.sum_congr rfl fun k _ => mul_comm _ _
        _ = ((↑(∑ k, β.repr ⟨X.col e, hmem e⟩ k • β k) : Y → ℂ)) i := hlhs.symm
        _ = X i e := by rw [hrepr]; rfl
    rw [hBK, hXdef]
    unfold ancX follTheta follProj colProj
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel
  · -- `Q` fixes the dictionary columns, which lie in `Ran X`
    ext i k
    obtain ⟨u, hu⟩ := (β k).2
    rw [Matrix.mulVecLin_apply] at hu
    have hcol : (fun j => (β k : Y → ℂ) j) = X *ᵥ u := by
      funext j
      rw [hu]
    calc (Q * Matrix.of fun i k => (β k : Y → ℂ) i) i k
        = (Q *ᵥ fun j => (β k : Y → ℂ) j) i := by
          rw [Matrix.mul_apply]
          simp only [Matrix.of_apply]
          rfl
      _ = (Q *ᵥ (X *ᵥ u)) i := by rw [hcol]
      _ = ((Q * X) *ᵥ u) i := by rw [Matrix.mulVec_mulVec]
      _ = (X *ᵥ u) i := by rw [hQX]
      _ = (β k : Y → ℂ) i := by rw [hu]

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S Es : Type*} [Fintype S] [Fintype Es]

omit [Fintype Es] in
/-- **(A4 / AN.6)** For frozen `𝓡, Π, J`, the ancestry-residual cross terms of
the projective source levels vanish: for `j < k`,
`𝔼[D_jᴴ 𝓡ᴴ Q (1-P_J) Q 𝓡 D_k] = 0`. -/
theorem ancestry_cross_level_zero {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) (V : Ω → Matrix S Es ℂ)
    (R : Matrix Y S ℂ) (Q : Matrix Y Y ℂ) (J : Matrix Y U ℂ)
    {j k : ℕ} (hjk : j < k) :
    promoExpect w (fun x => (dinc w f V j x)ᴴ * Rᴴ * Q
      * ((1 : Matrix Y Y ℂ) - follProj J) * Q * R * dinc w f V k x) = 0 := by
  have h := cross_level_orthogonality hw hchain V
    (Rᴴ * Q * ((1 : Matrix Y Y ℂ) - follProj J) * Q * R) hjk
  calc promoExpect w (fun x => (dinc w f V j x)ᴴ * Rᴴ * Q
        * ((1 : Matrix Y Y ℂ) - follProj J) * Q * R * dinc w f V k x)
      = promoExpect w (fun x => (dinc w f V j x)ᴴ
          * (Rᴴ * Q * ((1 : Matrix Y Y ℂ) - follProj J) * Q * R)
          * dinc w f V k x) :=
        congrArg (promoExpect w) (funext fun x => by simp only [Matrix.mul_assoc])
    _ = 0 := h

omit [Fintype Es] in
/-- **(A4, additivity)** The ancestry residuals of the projective source
levels add without a cross-level correction. -/
theorem ancestry_residual_additive {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) (V : Ω → Matrix S Es ℂ)
    (R : Matrix Y S ℂ) (Q : Matrix Y Y ℂ) (J : Matrix Y U ℂ) (L : ℕ) :
    promoExpect w (fun x => (marti w f V L x)ᴴ * Rᴴ * Q
        * ((1 : Matrix Y Y ℂ) - follProj J) * Q * R * marti w f V L x)
      = ∑ ℓ ∈ Finset.range (L + 1),
          promoExpect w fun x => (dinc w f V ℓ x)ᴴ * Rᴴ * Q
            * ((1 : Matrix Y Y ℂ) - follProj J) * Q * R * dinc w f V ℓ x := by
  have h := level_packets_additive hw hchain V
    (Rᴴ * Q * ((1 : Matrix Y Y ℂ) - follProj J) * Q * R) L
  calc promoExpect w (fun x => (marti w f V L x)ᴴ * Rᴴ * Q
        * ((1 : Matrix Y Y ℂ) - follProj J) * Q * R * marti w f V L x)
      = promoExpect w (fun x => (marti w f V L x)ᴴ
          * (Rᴴ * Q * ((1 : Matrix Y Y ℂ) - follProj J) * Q * R)
          * marti w f V L x) :=
        congrArg (promoExpect w) (funext fun x => by simp only [Matrix.mul_assoc])
    _ = ∑ ℓ ∈ Finset.range (L + 1),
          promoExpect w fun x => (dinc w f V ℓ x)ᴴ
            * (Rᴴ * Q * ((1 : Matrix Y Y ℂ) - follProj J) * Q * R)
            * dinc w f V ℓ x := h
    _ = _ := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        exact congrArg (promoExpect w)
          (funext fun x => by simp only [Matrix.mul_assoc])

end AncestryND

end AncestrySection

/-! ### `thm:GT-physical-source-Pythagoras` — Routed/mediated Pythagoras

Rendering: the packet of `def:GT-routed-mediated-source` is the matrix data
`B : E₀ → ℋ`, `Y : F → ℋ`, router `R : E → E₀` and mediator contraction
`T : ℋ → 𝒦`, with `S = TBR`, `Z = TY`, `G = SᴴS`, `C = SᴴZ`,
`P_S = S G† Sᴴ` (the repo `colProj S` — the projection on the supported range),
`𝕽_{T,R} = Zᴴ(1-P_S)Z` (`medResidual`), and `L_T(Y) = Yᴴ(1-TᴴT)Y`
(`medLoss`).  `resid_pythagoras` is the general least-squares completion,
`routed_pythagoras` the boxed (PSR.3), `routed_energy_split` the boxed
(PSR.4), positivity of the three terms is recorded, `resid_narrow`,
`resid_contract` and the three instantiations give the chain (PSR.5), and
`no_universal_resid_order` provides the two explicit `1×1` witnesses showing
that no universal Loewner order relates `𝕽(B;Y)` and `𝕽(TBR;TY)`. -/

section RoutedSourceSection

namespace RoutedSource

variable {m e f g : Type*} [Fintype m] [Fintype e] [Fintype f] [Fintype g]
variable [DecidableEq m] [DecidableEq e] [DecidableEq f]

/-- The mediated residual `𝕽(A;W) = Wᴴ(1 - P_A)W` (PSR.2/PSR.5). -/
noncomputable def medResidual (A : Matrix m e ℂ) (W : Matrix m f ℂ) : Matrix f f ℂ :=
  Wᴴ * ((1 : Matrix m m ℂ) - colProj A) * W

/-- The mediator loss `L_T(Y) = Yᴴ(1 - TᴴT)Y` (PSR.2). -/
def medLoss {H : Type*} [Fintype H] [DecidableEq H] (T : Matrix m H ℂ)
    (Ym : Matrix H f ℂ) : Matrix f f ℂ :=
  Ymᴴ * ((1 : Matrix H H ℂ) - Tᴴ * T) * Ym

omit [DecidableEq f] in
/-- The mediated residual is PSD. -/
theorem medResidual_posSemidef (A : Matrix m e ℂ) (W : Matrix m f ℂ) :
    (medResidual A W).PosSemidef :=
  one_sub_colProj_gram_posSemidef A W

omit [DecidableEq m] [DecidableEq f] in
/-- The mediator loss is PSD for a contraction `T`. -/
theorem medLoss_posSemidef {H : Type*} [Fintype H] [DecidableEq H]
    (T : Matrix m H ℂ) (Ym : Matrix H f ℂ)
    (hT : ((1 : Matrix H H ℂ) - Tᴴ * T).PosSemidef) :
    (medLoss T Ym).PosSemidef := by
  unfold medLoss
  exact hT.conjTranspose_mul_mul_same Ym

omit [Fintype f] [DecidableEq f] in
/-- **(PSR.3, general form)** The exact least-squares completion: for every
coefficient map `X`,
`(W - AX)ᴴ(W - AX) = 𝕽(A;W) + (X - X_*)ᴴ (AᴴA) (X - X_*)`
with `X_* = (AᴴA)† Aᴴ W`. -/
theorem resid_pythagoras (A : Matrix m e ℂ) (W : Matrix m f ℂ) (X : Matrix e f ℂ) :
    (W - A * X)ᴴ * (W - A * X)
      = medResidual A W
        + (X - pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * W))ᴴ
          * (Aᴴ * A)
          * (X - pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * W)) := by
  set V := pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * W) with hV
  have hGV : Aᴴ * A * V = Aᴴ * W := by
    rw [hV, ← Matrix.mul_assoc, gram_range_condition]
  have hVG : Vᴴ * (Aᴴ * A) = Wᴴ * A := by
    have h := congrArg conjTranspose hGV
    rwa [conjTranspose_mul (Aᴴ * A) V, conjTranspose_mul Aᴴ A,
      conjTranspose_mul Aᴴ W, conjTranspose_conjTranspose] at h
  have hexp : (W - A * X)ᴴ * (W - A * X)
      = Wᴴ * W - Wᴴ * (A * X) - Xᴴ * (Aᴴ * W) + Xᴴ * (Aᴴ * (A * X)) := by
    rw [conjTranspose_sub, conjTranspose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have hexp2 : (X - V)ᴴ * (Aᴴ * A) * (X - V)
      = Xᴴ * (Aᴴ * (A * X)) - Xᴴ * (Aᴴ * W) - Wᴴ * (A * X) + Wᴴ * (A * V) := by
    rw [conjTranspose_sub]
    have h1 : Xᴴ * (Aᴴ * A) * V = Xᴴ * (Aᴴ * W) := by
      rw [Matrix.mul_assoc, hGV]
    have h2 : Vᴴ * (Aᴴ * A) * X = Wᴴ * (A * X) := by
      rw [hVG, Matrix.mul_assoc]
    have h3 : Vᴴ * (Aᴴ * A) * V = Wᴴ * (A * V) := by
      rw [hVG, Matrix.mul_assoc]
    have h4 : Xᴴ * (Aᴴ * A) * X = Xᴴ * (Aᴴ * (A * X)) := by
      simp only [Matrix.mul_assoc]
    calc (Xᴴ - Vᴴ) * (Aᴴ * A) * (X - V)
        = Xᴴ * (Aᴴ * A) * X - Xᴴ * (Aᴴ * A) * V - Vᴴ * (Aᴴ * A) * X
            + Vᴴ * (Aᴴ * A) * V := by
          simp only [Matrix.mul_sub, Matrix.sub_mul]
          abel
      _ = _ := by rw [h1, h2, h3, h4]
  have hcol : Wᴴ * colProj A * W = Wᴴ * (A * V) := by
    unfold colProj
    rw [hV]
    simp only [Matrix.mul_assoc]
  have hres : medResidual A W = Wᴴ * W - Wᴴ * (A * V) := by
    unfold medResidual
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hcol]
  rw [hexp, hexp2, hres]
  abel

omit [Fintype f] [DecidableEq f] in
/-- The residual is attained at the pseudoinverse coefficient `X_*`. -/
theorem resid_attained (A : Matrix m e ℂ) (W : Matrix m f ℂ) :
    (W - A * (pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * W)))ᴴ
      * (W - A * (pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * W)))
      = medResidual A W := by
  rw [resid_pythagoras A W (pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * W)),
    sub_self, conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul, add_zero]

variable {E E0 F H K : Type*} [Fintype E] [Fintype E0] [Fintype F] [Fintype H]
  [Fintype K] [DecidableEq E] [DecidableEq E0] [DecidableEq F] [DecidableEq H]
  [DecidableEq K]

omit [Fintype F] [DecidableEq E0] [DecidableEq F] [DecidableEq H] in
/-- **(PSR.3)** The routed/mediated least-squares Pythagoras for the packet
`S = TBR`, `Z = TY`, `X_* = G†C`. -/
theorem routed_pythagoras (B : Matrix H E0 ℂ) (Ym : Matrix H F ℂ)
    (R : Matrix E0 E ℂ) (T : Matrix K H ℂ) (X : Matrix E F ℂ) :
    (T * Ym - T * B * R * X)ᴴ * (T * Ym - T * B * R * X)
      = medResidual (T * B * R) (T * Ym)
        + (X - pinv (posSemidef_conjTranspose_mul_self (T * B * R)).1
            * ((T * B * R)ᴴ * (T * Ym)))ᴴ
          * ((T * B * R)ᴴ * (T * B * R))
          * (X - pinv (posSemidef_conjTranspose_mul_self (T * B * R)).1
              * ((T * B * R)ᴴ * (T * Ym))) :=
  resid_pythagoras (T * B * R) (T * Ym) X

omit [Fintype F] [DecidableEq E0] [DecidableEq F] in
/-- **(PSR.4)** The exact three-term energy split
`YᴴY = L_T(Y) + CᴴG†C + 𝕽_{T,R}`: mediator loss, physical-source following,
and record-visible innovation. -/
theorem routed_energy_split (B : Matrix H E0 ℂ) (Ym : Matrix H F ℂ)
    (R : Matrix E0 E ℂ) (T : Matrix K H ℂ) :
    Ymᴴ * Ym
      = medLoss T Ym
        + ((T * B * R)ᴴ * (T * Ym))ᴴ
            * pinv (posSemidef_conjTranspose_mul_self (T * B * R)).1
            * ((T * B * R)ᴴ * (T * Ym))
        + medResidual (T * B * R) (T * Ym) := by
  have hcol : ((T * B * R)ᴴ * (T * Ym))ᴴ
        * pinv (posSemidef_conjTranspose_mul_self (T * B * R)).1
        * ((T * B * R)ᴴ * (T * Ym))
      = (T * Ym)ᴴ * colProj (T * B * R) * (T * Ym) := by
    unfold colProj
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [hcol]
  unfold medLoss medResidual
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, conjTranspose_mul,
    Matrix.mul_assoc]
  abel

omit [DecidableEq f] in
/-- **(PSR.5, dictionary narrowing)** Restricting the dictionary through a
router enlarges the residual: `𝕽(A;W) ⪯ 𝕽(A R;W)`. -/
theorem resid_narrow (A : Matrix m e ℂ) (Rm : Matrix e g ℂ) (W : Matrix m f ℂ)
    [DecidableEq g] :
    (medResidual (A * Rm) W - medResidual A W).PosSemidef := by
  have habs1 : colProj A * colProj (A * Rm) = colProj (A * Rm) := by
    conv_lhs =>
      rw [show colProj (A * Rm)
          = A * Rm * pinv (posSemidef_conjTranspose_mul_self (A * Rm)).1
            * (A * Rm)ᴴ from rfl]
    calc colProj A * (A * Rm * pinv (posSemidef_conjTranspose_mul_self (A * Rm)).1
          * (A * Rm)ᴴ)
        = colProj A * A * (Rm * (pinv (posSemidef_conjTranspose_mul_self (A * Rm)).1
            * (A * Rm)ᴴ)) := by simp only [Matrix.mul_assoc]
      _ = A * (Rm * (pinv (posSemidef_conjTranspose_mul_self (A * Rm)).1
            * (A * Rm)ᴴ)) := by rw [colProj_mul_self]
      _ = colProj (A * Rm) := by
          rw [show colProj (A * Rm)
            = A * Rm * pinv (posSemidef_conjTranspose_mul_self (A * Rm)).1
              * (A * Rm)ᴴ from rfl]
          simp only [Matrix.mul_assoc]
  have habs2 : colProj (A * Rm) * colProj A = colProj (A * Rm) := by
    have h := congrArg conjTranspose habs1
    rwa [conjTranspose_mul, (colProj_isHermitian A).eq,
      (colProj_isHermitian (A * Rm)).eq] at h
  set D := colProj A - colProj (A * Rm) with hD
  have hDH : Dᴴ = D := by
    rw [hD, conjTranspose_sub, (colProj_isHermitian A).eq,
      (colProj_isHermitian (A * Rm)).eq]
  have hDidem : D * D = D := by
    rw [hD]
    simp only [Matrix.mul_sub, Matrix.sub_mul, colProj_idem, habs1, habs2]
    abel
  have hdiff : medResidual (A * Rm) W - medResidual A W = Wᴴ * D * W := by
    unfold medResidual
    rw [hD]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  rw [hdiff]
  have hgram : Wᴴ * D * W = (D * W)ᴴ * (D * W) := by
    calc Wᴴ * D * W = Wᴴ * (D * D) * W := by rw [hDidem]
      _ = (D * W)ᴴ * (D * W) := by
          rw [conjTranspose_mul, hDH]
          simp only [Matrix.mul_assoc]
  rw [hgram]
  exact posSemidef_conjTranspose_mul_self _

omit [DecidableEq f] in
/-- **(PSR.5, mediation contraction)** Mediating both the dictionary and the
target through a contraction shrinks the residual:
`𝕽(TA;TW) ⪯ 𝕽(A;W)`. -/
theorem resid_contract {Kc : Type*} [Fintype Kc] [DecidableEq Kc]
    (A : Matrix m e ℂ) (W : Matrix m f ℂ) (T : Matrix Kc m ℂ)
    (hT : ((1 : Matrix m m ℂ) - Tᴴ * T).PosSemidef) :
    (medResidual A W - medResidual (T * A) (T * W)).PosSemidef := by
  set V := pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * W) with hV
  set Res := W - A * V with hRes
  -- first defect: the mediated residual is dominated by the mediated misfit
  have h1 : ((T * Res)ᴴ * (T * Res) - medResidual (T * A) (T * W)).PosSemidef := by
    have hpy := resid_pythagoras (T * A) (T * W) V
    have hTRes : T * W - T * A * V = T * Res := by
      rw [hRes, Matrix.mul_sub, Matrix.mul_assoc]
    rw [hTRes] at hpy
    rw [hpy]
    have heq : medResidual (T * A) (T * W)
          + (V - pinv (posSemidef_conjTranspose_mul_self (T * A)).1
              * ((T * A)ᴴ * (T * W)))ᴴ * ((T * A)ᴴ * (T * A))
            * (V - pinv (posSemidef_conjTranspose_mul_self (T * A)).1
                * ((T * A)ᴴ * (T * W)))
          - medResidual (T * A) (T * W)
        = (V - pinv (posSemidef_conjTranspose_mul_self (T * A)).1
              * ((T * A)ᴴ * (T * W)))ᴴ * ((T * A)ᴴ * (T * A))
            * (V - pinv (posSemidef_conjTranspose_mul_self (T * A)).1
                * ((T * A)ᴴ * (T * W))) := by abel
    rw [heq]
    have hfact : (V - pinv (posSemidef_conjTranspose_mul_self (T * A)).1
            * ((T * A)ᴴ * (T * W)))ᴴ * ((T * A)ᴴ * (T * A))
          * (V - pinv (posSemidef_conjTranspose_mul_self (T * A)).1
              * ((T * A)ᴴ * (T * W)))
        = (T * A * (V - pinv (posSemidef_conjTranspose_mul_self (T * A)).1
            * ((T * A)ᴴ * (T * W))))ᴴ
          * (T * A * (V - pinv (posSemidef_conjTranspose_mul_self (T * A)).1
              * ((T * A)ᴴ * (T * W)))) := by
      conv_rhs => rw [conjTranspose_mul (T * A)
        (V - pinv (posSemidef_conjTranspose_mul_self (T * A)).1
          * ((T * A)ᴴ * (T * W)))]
      simp only [Matrix.mul_assoc]
    rw [hfact]
    exact posSemidef_conjTranspose_mul_self _
  -- second defect: the contraction loss on the unmediated misfit
  have h2 : (Resᴴ * Res - (T * Res)ᴴ * (T * Res)).PosSemidef := by
    have hc := hT.conjTranspose_mul_mul_same Res
    have heq : Resᴴ * ((1 : Matrix m m ℂ) - Tᴴ * T) * Res
        = Resᴴ * Res - (T * Res)ᴴ * (T * Res) := by
      rw [conjTranspose_mul]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    rwa [heq] at hc
  -- the unmediated misfit at `X_*` is exactly the unmediated residual
  have h3 : Resᴴ * Res = medResidual A W := by
    rw [hRes, hV]
    exact resid_attained A W
  have hsum := h1.add h2
  have heq2 : (T * Res)ᴴ * (T * Res) - medResidual (T * A) (T * W)
        + (Resᴴ * Res - (T * Res)ᴴ * (T * Res))
      = medResidual A W - medResidual (T * A) (T * W) := by
    rw [h3] at *
    abel
  rwa [heq2] at hsum

omit [DecidableEq F] in
/-- **(PSR.5, chain)** `𝕽(TB;TY) ⪯ 𝕽(TBR;TY) ⪯ 𝕽(BR;Y)` and
`𝕽(TB;TY) ⪯ 𝕽(B;Y)` for a mediator contraction `T`. -/
theorem resid_chain (B : Matrix H E0 ℂ) (Ym : Matrix H F ℂ)
    (R : Matrix E0 E ℂ) (T : Matrix K H ℂ)
    (hT : ((1 : Matrix H H ℂ) - Tᴴ * T).PosSemidef) :
    (medResidual (T * B * R) (T * Ym) - medResidual (T * B) (T * Ym)).PosSemidef ∧
    (medResidual (B * R) Ym - medResidual (T * B * R) (T * Ym)).PosSemidef ∧
    (medResidual B Ym - medResidual (T * B) (T * Ym)).PosSemidef := by
  refine ⟨resid_narrow (T * B) R (T * Ym), ?_, resid_contract B Ym T hT⟩
  have h := resid_contract (B * R) Ym T hT
  rwa [show T * (B * R) = T * B * R from (Matrix.mul_assoc T B R).symm] at h

/-- **(PSR.5, no universal order)** Two explicit `1×1` packets with contraction
mediators witnessing that neither `𝕽(B;Y) ⪯ 𝕽(TBR;TY)` nor the reverse holds
universally. -/
theorem no_universal_resid_order :
    ∃ B₁ R₁ T₁ Y₁ B₂ R₂ T₂ Y₂ : Matrix (Fin 1) (Fin 1) ℂ,
      ((1 : Matrix (Fin 1) (Fin 1) ℂ) - T₁ᴴ * T₁).PosSemidef ∧
      ((1 : Matrix (Fin 1) (Fin 1) ℂ) - T₂ᴴ * T₂).PosSemidef ∧
      ¬(medResidual B₁ Y₁ - medResidual (T₁ * B₁ * R₁) (T₁ * Y₁)).PosSemidef ∧
      ¬(medResidual (T₂ * B₂ * R₂) (T₂ * Y₂) - medResidual B₂ Y₂).PosSemidef := by
  have hcol1 : colProj (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    have h := colProj_mul_self (1 : Matrix (Fin 1) (Fin 1) ℂ)
    rwa [Matrix.mul_one] at h
  have hcol0 : colProj (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    have h := mul_colProj_eq_zero (q := Fin 1) (X := (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (M := (0 : Matrix (Fin 1) (Fin 1) ℂ))
      (Matrix.mul_zero (1 : Matrix (Fin 1) (Fin 1) ℂ))
    rwa [Matrix.one_mul] at h
  have hm11 : medResidual (1 : Matrix (Fin 1) (Fin 1) ℂ)
      (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    unfold medResidual
    rw [hcol1, sub_self, Matrix.mul_zero, Matrix.zero_mul]
  have hm01 : medResidual (0 : Matrix (Fin 1) (Fin 1) ℂ)
      (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    unfold medResidual
    rw [hcol0, sub_zero, conjTranspose_one, Matrix.one_mul, Matrix.one_mul]
  have hm00 : medResidual (0 : Matrix (Fin 1) (Fin 1) ℂ)
      (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    unfold medResidual
    rw [conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
  have hneg : ¬(-(1 : Matrix (Fin 1) (Fin 1) ℂ)).PosSemidef := by
    intro h
    have h2 := re_form_nonneg h fun _ => (1 : ℂ)
    have hval : star (fun _ => (1 : ℂ))
        ⬝ᵥ ((-(1 : Matrix (Fin 1) (Fin 1) ℂ)) *ᵥ fun _ => (1 : ℂ)) = -1 := by
      rw [Matrix.neg_mulVec, Matrix.one_mulVec]
      simp only [dotProduct, Fin.sum_univ_one, Pi.star_apply, Pi.neg_apply,
        star_one, mul_neg, mul_one]
    rw [hval] at h2
    norm_num [Complex.neg_re, Complex.one_re] at h2
  refine ⟨1, 0, 1, 1, 0, 0, 0, 1, ?_, ?_, ?_, ?_⟩
  · rw [conjTranspose_one, Matrix.one_mul, sub_self]
    exact Matrix.PosSemidef.zero
  · rw [conjTranspose_zero, Matrix.zero_mul, sub_zero]
    exact Matrix.PosSemidef.one
  · rw [Matrix.mul_zero, Matrix.one_mul, hm11, hm01, zero_sub]
    exact hneg
  · rw [Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul, hm00, hm01, zero_sub]
    exact hneg

end RoutedSource

end RoutedSourceSection

/-! ### `thm:GT-physical-source-transport` — Primitive transport of a source

Rendering: (PSR.13)–(PSR.14) are the exact three-term defect decomposition for
arbitrary carriers at the two cutoffs, (PSR.15) the Gram transport under an
isometric mediated-carrier transport, and (PSR.16) the positive-form
transport (an exact identity needing no isometry).  For (PSR.17) the
manuscript works after isometric identification on one common finite screen;
we render the primitive maps and forms as sequences on that fixed screen,
summable defects as summable entrywise-distance bounds between adjacent
cutoffs, prove that all primitive limits exist, that the transported source
Gram and physical form converge, and that the stable window and physical
lower bounds pass to the limit: `Q_∞ ⪰ c_* G_∞ ⪰ c_* g₋ P`.  Uniqueness of
entrywise limits (`entrywise_limit_unique`) renders the agreement of direct
and staged limits. -/

section SourceTransportSection

namespace SourceTransportP

variable {Ec E0 Hr Hm Ec' E0' Hr' Hm' : Type*}
variable [Fintype Ec] [Fintype E0] [Fintype Hr] [Fintype Hm]
variable [Fintype Ec'] [Fintype E0'] [Fintype Hr'] [Fintype Hm']

omit [Fintype Ec] [Fintype Hm'] in
/-- **(PSR.13–PSR.14)** The full source defect decomposes exactly into the
router, coefficient, and mediator defects:
`S₁V - ZS₀ = T₁B₁Δᴿ + T₁Δᴮ R₀ + Δᵀ B₀R₀`. -/
theorem source_defect_decomposition
    (T0 : Matrix Hm Hr ℂ) (B0 : Matrix Hr E0 ℂ) (R0 : Matrix E0 Ec ℂ)
    (T1 : Matrix Hm' Hr' ℂ) (B1 : Matrix Hr' E0' ℂ) (R1 : Matrix E0' Ec' ℂ)
    (V : Matrix Ec' Ec ℂ) (U : Matrix E0' E0 ℂ) (W : Matrix Hr' Hr ℂ)
    (Z : Matrix Hm' Hm ℂ) :
    T1 * B1 * R1 * V - Z * (T0 * B0 * R0)
      = T1 * B1 * (R1 * V - U * R0) + T1 * (B1 * U - W * B0) * R0
        + (T1 * W - Z * T0) * (B0 * R0) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

omit [Fintype Ec] in
/-- **(PSR.15)** Under an isometric mediated-carrier transport `Z`, the source
Gram transports exactly through the full defect `Δˢ = S₁V - ZS₀`. -/
theorem gram_transport [DecidableEq Hm] (S0 : Matrix Hm Ec ℂ)
    (S1 : Matrix Hm' Ec' ℂ) (V : Matrix Ec' Ec ℂ) (Z : Matrix Hm' Hm ℂ)
    (hZ : Zᴴ * Z = 1) :
    Vᴴ * (S1ᴴ * S1) * V - S0ᴴ * S0
      = S0ᴴ * Zᴴ * (S1 * V - Z * S0) + (S1 * V - Z * S0)ᴴ * (Z * S0)
        + (S1 * V - Z * S0)ᴴ * (S1 * V - Z * S0) := by
  have hZS : Zᴴ * (Z * S0) = S0 := by
    rw [← Matrix.mul_assoc, hZ, Matrix.one_mul]
  simp only [conjTranspose_sub, conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, hZS]
  abel

omit [Fintype Ec] in
/-- **(PSR.16)** The transported physical form `Q_i = S_iᴴ A_i S_i` obeys the
exact four-term identity through the form defect `Δᴬ = Zᴴ A₁ Z - A₀` and the
source defect `Δˢ`; no isometry is needed for this identity. -/
theorem form_transport (S0 : Matrix Hm Ec ℂ) (S1 : Matrix Hm' Ec' ℂ)
    (V : Matrix Ec' Ec ℂ) (Z : Matrix Hm' Hm ℂ)
    (A0 : Matrix Hm Hm ℂ) (A1 : Matrix Hm' Hm' ℂ) :
    Vᴴ * (S1ᴴ * A1 * S1) * V - S0ᴴ * A0 * S0
      = S0ᴴ * (Zᴴ * A1 * Z - A0) * S0
        + S0ᴴ * Zᴴ * A1 * (S1 * V - Z * S0)
        + (S1 * V - Z * S0)ᴴ * A1 * (Z * S0)
        + (S1 * V - Z * S0)ᴴ * A1 * (S1 * V - Z * S0) := by
  simp only [conjTranspose_sub, conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc]
  abel

/-- Summable adjacent entrywise defects produce an entrywise limit matrix. -/
theorem entrywise_limit_of_summable {n p : Type*} (M : ℕ → Matrix n p ℂ)
    (d : ℕ → ℝ) (hd : Summable d)
    (hM : ∀ i a b, dist (M i a b) (M (i + 1) a b) ≤ d i) :
    ∃ L : Matrix n p ℂ, ∀ a b, Tendsto (fun i => M i a b) atTop (𝓝 (L a b)) := by
  have hc : ∀ a b, ∃ l : ℂ, Tendsto (fun i => M i a b) atTop (𝓝 l) := fun a b =>
    cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable d (fun i => hM i a b) hd)
  choose L hL using hc
  exact ⟨Matrix.of L, hL⟩

/-- Entrywise limits are unique: direct and staged limits agree. -/
theorem entrywise_limit_unique {n p : Type*} {M : ℕ → Matrix n p ℂ}
    {L L' : Matrix n p ℂ}
    (h : ∀ a b, Tendsto (fun i => M i a b) atTop (𝓝 (L a b)))
    (h' : ∀ a b, Tendsto (fun i => M i a b) atTop (𝓝 (L' a b))) : L = L' := by
  ext a b
  exact tendsto_nhds_unique (h a b) (h' a b)

/-- Entrywise limits multiply: the product of entrywise-convergent matrix
sequences converges entrywise to the product of the limits. -/
theorem entrywise_limit_mul {n p q : Type*} [Fintype p] {M : ℕ → Matrix n p ℂ}
    {N : ℕ → Matrix p q ℂ} {L : Matrix n p ℂ} {L' : Matrix p q ℂ}
    (hM : ∀ a b, Tendsto (fun i => M i a b) atTop (𝓝 (L a b)))
    (hN : ∀ a b, Tendsto (fun i => N i a b) atTop (𝓝 (L' a b))) :
    ∀ a b, Tendsto (fun i => (M i * N i) a b) atTop (𝓝 ((L * L') a b)) := by
  intro a b
  have h : Tendsto (fun i => ∑ c, M i a c * N i c b) atTop
      (𝓝 (∑ c, L a c * L' c b)) :=
    tendsto_finsetSum Finset.univ fun c _ => (hM a c).mul (hN c b)
  have he : (fun i => (M i * N i) a b) = fun i => ∑ c, M i a c * N i c b := by
    funext i
    rw [Matrix.mul_apply]
  rw [he, Matrix.mul_apply]
  exact h

/-- Entrywise limits pass through conjugate transposes. -/
theorem entrywise_limit_conjTranspose {n p : Type*} {M : ℕ → Matrix n p ℂ}
    {L : Matrix n p ℂ}
    (hM : ∀ a b, Tendsto (fun i => M i a b) atTop (𝓝 (L a b))) :
    ∀ a b, Tendsto (fun i => (M i)ᴴ a b) atTop (𝓝 (Lᴴ a b)) := by
  intro a b
  have h := (hM b a).star
  simpa only [Matrix.conjTranspose_apply] using h

/-- PSD passes to entrywise limits. -/
theorem posSemidef_of_entrywise_limit {n : Type*} [Fintype n]
    {M : ℕ → Matrix n n ℂ} {L : Matrix n n ℂ}
    (hlim : ∀ a b, Tendsto (fun i => M i a b) atTop (𝓝 (L a b)))
    (hpsd : ∀ i, (M i).PosSemidef) : L.PosSemidef := by
  refine posSemidef_of_re_form ?_ fun x => ?_
  · ext a b
    have h1 : Tendsto (fun i => (M i)ᴴ a b) atTop (𝓝 (Lᴴ a b)) :=
      entrywise_limit_conjTranspose hlim a b
    have h2 : (fun i => (M i)ᴴ a b) = fun i => M i a b := by
      funext i
      rw [(hpsd i).1.eq]
    rw [h2] at h1
    exact tendsto_nhds_unique h1 (hlim a b)
  · have hform : Tendsto (fun i => (star x ⬝ᵥ (M i *ᵥ x)).re) atTop
        (𝓝 ((star x ⬝ᵥ (L *ᵥ x)).re)) := by
      have hdot : ∀ (A : Matrix n n ℂ), star x ⬝ᵥ (A *ᵥ x)
          = ∑ a, star (x a) * ∑ b, A a b * x b := by
        intro A
        rfl
      have h1 : Tendsto (fun i => star x ⬝ᵥ (M i *ᵥ x)) atTop
          (𝓝 (star x ⬝ᵥ (L *ᵥ x))) := by
        rw [hdot L]
        have h2 : (fun i => star x ⬝ᵥ (M i *ᵥ x))
            = fun i => ∑ a, star (x a) * ∑ b, M i a b * x b := by
          funext i
          rw [hdot (M i)]
        rw [h2]
        refine tendsto_finsetSum Finset.univ fun a _ => ?_
        exact tendsto_const_nhds.mul
          (tendsto_finsetSum Finset.univ fun b _ => (hlim a b).mul tendsto_const_nhds)
      exact (Complex.continuous_re.tendsto _).comp h1
    exact ge_of_tendsto hform (Eventually.of_forall fun i => re_form_nonneg (hpsd i) x)

/-- **(PSR.17)** After isometric identification on one common finite screen,
summable primitive defects give convergent primitives; the source Gram and
the physical form converge, the stable window and the physical lower bound
pass to the limit, and `Q_∞ ⪰ c_* G_∞ ⪰ c_* g₋ P`. -/
theorem primitive_transport_limit
    (T : ℕ → Matrix Hm Hr ℂ) (B : ℕ → Matrix Hr E0 ℂ) (R : ℕ → Matrix E0 Ec ℂ)
    (A : ℕ → Matrix Hm Hm ℂ) (dT dB dR dA : ℕ → ℝ)
    (hdT : Summable dT) (hdB : Summable dB) (hdR : Summable dR) (hdA : Summable dA)
    (hTd : ∀ i a b, dist (T i a b) (T (i + 1) a b) ≤ dT i)
    (hBd : ∀ i a b, dist (B i a b) (B (i + 1) a b) ≤ dB i)
    (hRd : ∀ i a b, dist (R i a b) (R (i + 1) a b) ≤ dR i)
    (hAd : ∀ i a b, dist (A i a b) (A (i + 1) a b) ≤ dA i)
    (P : Matrix Ec Ec ℂ) {c gm : ℝ} (hc : 0 ≤ c)
    (hQG : ∀ i, ((T i * B i * R i)ᴴ * A i * (T i * B i * R i)
      - c • ((T i * B i * R i)ᴴ * (T i * B i * R i))).PosSemidef)
    (hGP : ∀ i, ((T i * B i * R i)ᴴ * (T i * B i * R i) - gm • P).PosSemidef) :
    ∃ (Tl : Matrix Hm Hr ℂ) (Bl : Matrix Hr E0 ℂ) (Rl : Matrix E0 Ec ℂ)
      (Al : Matrix Hm Hm ℂ),
      (∀ a b, Tendsto (fun i => T i a b) atTop (𝓝 (Tl a b))) ∧
      (∀ a b, Tendsto (fun i => B i a b) atTop (𝓝 (Bl a b))) ∧
      (∀ a b, Tendsto (fun i => R i a b) atTop (𝓝 (Rl a b))) ∧
      (∀ a b, Tendsto (fun i => A i a b) atTop (𝓝 (Al a b))) ∧
      ((Tl * Bl * Rl)ᴴ * Al * (Tl * Bl * Rl)
        - c • ((Tl * Bl * Rl)ᴴ * (Tl * Bl * Rl))).PosSemidef ∧
      ((Tl * Bl * Rl)ᴴ * (Tl * Bl * Rl) - gm • P).PosSemidef ∧
      ((Tl * Bl * Rl)ᴴ * Al * (Tl * Bl * Rl) - (c * gm) • P).PosSemidef := by
  obtain ⟨Tl, hTl⟩ := entrywise_limit_of_summable T dT hdT hTd
  obtain ⟨Bl, hBl⟩ := entrywise_limit_of_summable B dB hdB hBd
  obtain ⟨Rl, hRl⟩ := entrywise_limit_of_summable R dR hdR hRd
  obtain ⟨Al, hAl⟩ := entrywise_limit_of_summable A dA hdA hAd
  have hS : ∀ a b, Tendsto (fun i => (T i * B i * R i) a b) atTop
      (𝓝 ((Tl * Bl * Rl) a b)) :=
    entrywise_limit_mul (entrywise_limit_mul hTl hBl) hRl
  have hSH := entrywise_limit_conjTranspose hS
  have hG : ∀ a b, Tendsto (fun i => ((T i * B i * R i)ᴴ * (T i * B i * R i)) a b)
      atTop (𝓝 (((Tl * Bl * Rl)ᴴ * (Tl * Bl * Rl)) a b)) :=
    entrywise_limit_mul hSH hS
  have hQ : ∀ a b, Tendsto
      (fun i => ((T i * B i * R i)ᴴ * A i * (T i * B i * R i)) a b) atTop
      (𝓝 (((Tl * Bl * Rl)ᴴ * Al * (Tl * Bl * Rl)) a b)) :=
    entrywise_limit_mul (entrywise_limit_mul hSH hAl) hS
  have hQGl : ((Tl * Bl * Rl)ᴴ * Al * (Tl * Bl * Rl)
      - c • ((Tl * Bl * Rl)ᴴ * (Tl * Bl * Rl))).PosSemidef := by
    refine posSemidef_of_entrywise_limit (fun a b => ?_) hQG
    have h1 : Tendsto (fun i => ((T i * B i * R i)ᴴ * A i * (T i * B i * R i)) a b
        - (c • ((T i * B i * R i)ᴴ * (T i * B i * R i))) a b) atTop
        (𝓝 (((Tl * Bl * Rl)ᴴ * Al * (Tl * Bl * Rl)) a b
          - (c • ((Tl * Bl * Rl)ᴴ * (Tl * Bl * Rl))) a b)) := by
      simp only [Matrix.smul_apply]
      exact (hQ a b).sub ((hG a b).const_smul c)
    simpa only [Matrix.sub_apply] using h1
  have hGPl : ((Tl * Bl * Rl)ᴴ * (Tl * Bl * Rl) - gm • P).PosSemidef := by
    refine posSemidef_of_entrywise_limit (fun a b => ?_) hGP
    have h1 : Tendsto (fun i => ((T i * B i * R i)ᴴ * (T i * B i * R i)) a b
        - (gm • P) a b) atTop
        (𝓝 (((Tl * Bl * Rl)ᴴ * (Tl * Bl * Rl)) a b - (gm • P) a b)) :=
      (hG a b).sub tendsto_const_nhds
    simpa only [Matrix.sub_apply] using h1
  refine ⟨Tl, Bl, Rl, Al, hTl, hBl, hRl, hAl, hQGl, hGPl, ?_⟩
  have hsum := hQGl.add (mgt_smul_posSemidef hc hGPl)
  have heq : (Tl * Bl * Rl)ᴴ * Al * (Tl * Bl * Rl)
        - c • ((Tl * Bl * Rl)ᴴ * (Tl * Bl * Rl))
        + c • ((Tl * Bl * Rl)ᴴ * (Tl * Bl * Rl) - gm • P)
      = (Tl * Bl * Rl)ᴴ * Al * (Tl * Bl * Rl) - (c * gm) • P := by
    rw [smul_sub, smul_smul]
    abel
  rwa [heq] at hsum

end SourceTransportP

end SourceTransportSection

/-! ### `thm:GT-source-short-rotation` — Energy-dual control of source rotation

Rendering: the packet follows the repo rendering of ST.1–ST.7
(`EasyExact00.short_exists`): the source shorts `K_n`, `K_{n+1}` are Hermitian
matrices carrying the attained variational property of (ST.1) — for `K_n` only
the lower-bound half is needed, for `K_{n+1}` the attained `IsLeast`.  The
energy inequality is the PSD form of the displayed hypothesis, the coarse
floor `d_n = λ_min(K_n - D_n) > 0` is any certified Loewner floor, and the
energy-dual norm `α_n = ‖Q_n A_{n+1}^{-1/2}‖` is rendered by its defining
quadratic bound `‖Q_n u‖² ≤ α² ⟨u, A_{n+1} u⟩` (equivalent to the operator
norm bound after the substitution `u = A_{n+1}^{-1/2} y`).  The boxed (ST.8)
is `source_rotation_bound` in Loewner form,
`K_{n+1} ⪰ (d^{-1/2} + α)⁻² · 1`, and `source_rotation_lamMin` restates it
for the least source reserve `c_{n+1} = λ_min(K_{n+1})`. -/

section SourceRotationSection

namespace SourceRotation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Euclidean length of a complex vector through the dot-product form. -/
noncomputable def vnorm (x : ι → ℂ) : ℝ := Real.sqrt ((star x ⬝ᵥ x).re)

omit [DecidableEq ι] in
/-- The self-pairing has nonnegative real part. -/
theorem form_self_nonneg (x : ι → ℂ) : 0 ≤ (star x ⬝ᵥ x).re := by
  rw [star_dot_self_eq_sum_sq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

omit [DecidableEq ι] in
/-- The bridge to the Euclidean norm. -/
theorem vnorm_eq (x : ι → ℂ) :
    vnorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ := by
  unfold vnorm
  rw [star_dot_self_eq_sum_sq, Complex.ofReal_re, EuclideanSpace.norm_eq]

omit [DecidableEq ι] in
/-- The square of the Euclidean length recovers the self-pairing. -/
theorem vnorm_sq (x : ι → ℂ) : vnorm x ^ 2 = (star x ⬝ᵥ x).re := by
  unfold vnorm
  exact Real.sq_sqrt (form_self_nonneg x)

omit [DecidableEq ι] in
/-- The Euclidean length is nonnegative. -/
theorem vnorm_nonneg (x : ι → ℂ) : 0 ≤ vnorm x := Real.sqrt_nonneg _

omit [DecidableEq ι] in
/-- Triangle inequality for the Euclidean length. -/
theorem vnorm_add_le (x y : ι → ℂ) : vnorm (x + y) ≤ vnorm x + vnorm y := by
  rw [vnorm_eq, vnorm_eq, vnorm_eq]
  exact norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

omit [DecidableEq ι] in
/-- A quadratic bound converts to a length bound. -/
theorem vnorm_le_of_sq_le {x : ι → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : (star x ⬝ᵥ x).re ≤ c ^ 2) : vnorm x ≤ c := by
  unfold vnorm
  calc Real.sqrt ((star x ⬝ᵥ x).re) ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h
    _ = c := Real.sqrt_sq hc

/-- **(ST.8)** Energy-dual control of source rotation: if the retraction obeys
the energy inequality, the coarse short has floor `d > 0` past the debit, and
the rotation defect `Q = T_{n+1} - U T_n R_n` has energy-dual bound `α`, then
`K_{n+1} ⪰ (d^{-1/2} + α)⁻² · 1`. -/
theorem source_rotation_bound {Hn Hn1 : Type*} [Fintype Hn] [Fintype Hn1]
    {An : Matrix Hn Hn ℂ} {An1 : Matrix Hn1 Hn1 ℂ}
    {Tn : Matrix ι Hn ℂ} {Tn1 : Matrix ι Hn1 ℂ} {Rn : Matrix Hn Hn1 ℂ}
    {U : Matrix ι ι ℂ} {Kn Kn1 Dn : Matrix ι ι ℂ} {d α : ℝ}
    (hKh : Kn1.IsHermitian) (hU : Uᴴ * U = 1)
    (hKn : ∀ u : Hn → ℂ,
      (star (Tn *ᵥ u) ⬝ᵥ (Kn *ᵥ (Tn *ᵥ u))).re ≤ (star u ⬝ᵥ (An *ᵥ u)).re)
    (hKn1 : ∀ s : ι → ℂ,
      IsLeast {r : ℝ | ∃ u, Tn1 *ᵥ u = s ∧ r = (star u ⬝ᵥ (An1 *ᵥ u)).re}
        ((star s ⬝ᵥ (Kn1 *ᵥ s)).re))
    (henergy : (An1 + (Tn * Rn)ᴴ * Dn * (Tn * Rn) - Rnᴴ * An * Rn).PosSemidef)
    (hd : 0 < d) (hfloor : (Kn - Dn - (d : ℂ) • 1).PosSemidef) (hα : 0 ≤ α)
    (hangle : ∀ u : Hn1 → ℂ,
      (star ((Tn1 - U * (Tn * Rn)) *ᵥ u) ⬝ᵥ ((Tn1 - U * (Tn * Rn)) *ᵥ u)).re
        ≤ α ^ 2 * (star u ⬝ᵥ (An1 *ᵥ u)).re) :
    (Kn1 - ((((Real.sqrt d)⁻¹ + α) ^ 2)⁻¹ : ℝ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
  set γ : ℝ := (Real.sqrt d)⁻¹ + α with hγ
  have hγpos : 0 < γ := by
    have := inv_pos.mpr (Real.sqrt_pos.mpr hd)
    rw [hγ]
    linarith
  refine posSemidef_of_re_form ?_ fun s => ?_
  · change (Kn1 - ((γ ^ 2)⁻¹ : ℝ) • (1 : Matrix ι ι ℂ))ᴴ = _
    rw [conjTranspose_sub, hKh.eq, conjTranspose_smul, conjTranspose_one,
      star_trivial]
  · obtain ⟨⟨u, hu, hval⟩, -⟩ := hKn1 s
    set E2 := (star u ⬝ᵥ (An1 *ᵥ u)).re with hE2
    set x : ι → ℂ := (Tn * Rn) *ᵥ u with hx
    -- energy inequality at `u`
    have hdeb := re_form_nonneg henergy u
    rw [sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add,
      conj_form_move (Tn * Rn) Dn u, conj_form_move Rn An u] at hdeb
    simp only [Complex.add_re, Complex.sub_re] at hdeb
    -- coarse variational bound at the retracted vector
    have hlow := hKn (Rn *ᵥ u)
    have hxeq : Tn *ᵥ (Rn *ᵥ u) = x := by
      rw [hx, mulVec_mulVec]
    rw [hxeq] at hlow
    -- coarse floor at `x`
    have hfl := re_form_nonneg hfloor x
    rw [sub_mulVec, sub_mulVec, dotProduct_sub, dotProduct_sub, smul_mulVec,
      one_mulVec, dotProduct_smul] at hfl
    simp only [Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at hfl
    have hdx : d * (star x ⬝ᵥ x).re ≤ E2 := by
      have h1 : (star x ⬝ᵥ (Kn *ᵥ x)).re ≤ E2 + (star x ⬝ᵥ (Dn *ᵥ x)).re := by
        calc (star x ⬝ᵥ (Kn *ᵥ x)).re
            ≤ (star (Rn *ᵥ u) ⬝ᵥ (An *ᵥ (Rn *ᵥ u))).re := hlow
          _ ≤ E2 + (star x ⬝ᵥ (Dn *ᵥ x)).re := by
              rw [hE2, hx]
              linarith [hdeb]
      linarith [hfl]
    have hE2nn : 0 ≤ E2 :=
      le_trans (mul_nonneg hd.le (form_self_nonneg x)) hdx
    -- decompose `s = Ux + Qu`
    have hsplit : s = U *ᵥ x + (Tn1 - U * (Tn * Rn)) *ᵥ u := by
      rw [sub_mulVec, hu, hx, mulVec_mulVec]
      abel
    -- length of the rotated coarse component
    have hUx : (star (U *ᵥ x) ⬝ᵥ (U *ᵥ x)).re = (star x ⬝ᵥ x).re := by
      rw [adjoint_dot U (U *ᵥ x) x]
      have hUUx : Uᴴ *ᵥ (U *ᵥ x) = x := by
        rw [mulVec_mulVec, hU, one_mulVec]
      rw [hUUx]
    have hnx : vnorm (U *ᵥ x) ≤ (Real.sqrt d)⁻¹ * Real.sqrt E2 := by
      refine vnorm_le_of_sq_le
        (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg d)) (Real.sqrt_nonneg E2)) ?_
      rw [hUx, mul_pow, ← Real.sqrt_inv, Real.sq_sqrt (inv_nonneg.mpr hd.le),
        Real.sq_sqrt hE2nn, le_inv_mul_iff₀ hd]
      exact hdx
    have hnq : vnorm ((Tn1 - U * (Tn * Rn)) *ᵥ u) ≤ α * Real.sqrt E2 := by
      refine vnorm_le_of_sq_le (mul_nonneg hα (Real.sqrt_nonneg E2)) ?_
      rw [mul_pow, Real.sq_sqrt hE2nn]
      exact hangle u
    have hns : vnorm s ≤ γ * Real.sqrt E2 := by
      rw [hsplit]
      calc vnorm (U *ᵥ x + (Tn1 - U * (Tn * Rn)) *ᵥ u)
          ≤ vnorm (U *ᵥ x) + vnorm ((Tn1 - U * (Tn * Rn)) *ᵥ u) := vnorm_add_le _ _
        _ ≤ (Real.sqrt d)⁻¹ * Real.sqrt E2 + α * Real.sqrt E2 := by
            linarith [hnx, hnq]
        _ = γ * Real.sqrt E2 := by rw [hγ]; ring
    -- square and conclude
    have hs2 : (star s ⬝ᵥ s).re ≤ γ ^ 2 * E2 := by
      have h1 : vnorm s ^ 2 ≤ (γ * Real.sqrt E2) ^ 2 :=
        pow_le_pow_left₀ (vnorm_nonneg s) hns 2
      rw [vnorm_sq] at h1
      calc (star s ⬝ᵥ s).re ≤ (γ * Real.sqrt E2) ^ 2 := h1
        _ = γ ^ 2 * E2 := by rw [mul_pow, Real.sq_sqrt hE2nn]
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul]
    simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul]
    have hK1 : (star s ⬝ᵥ (Kn1 *ᵥ s)).re = E2 := hval
    rw [hK1]
    have hβE : (γ ^ 2)⁻¹ * (star s ⬝ᵥ s).re ≤ E2 := by
      have hγ2 : (0 : ℝ) < γ ^ 2 := by positivity
      calc (γ ^ 2)⁻¹ * (star s ⬝ᵥ s).re ≤ (γ ^ 2)⁻¹ * (γ ^ 2 * E2) := by
            have := inv_nonneg.mpr hγ2.le
            exact mul_le_mul_of_nonneg_left hs2 this
        _ = E2 := by
            rw [← mul_assoc, inv_mul_cancel₀ hγ2.ne', one_mul]
    linarith

/-- **(ST.8, least-reserve form)** The least source reserve obeys
`c_{n+1} = λ_min(K_{n+1}) ≥ (d^{-1/2} + α)⁻²`. -/
theorem source_rotation_lamMin [Nonempty ι] {Hn Hn1 : Type*} [Fintype Hn]
    [Fintype Hn1] {An : Matrix Hn Hn ℂ} {An1 : Matrix Hn1 Hn1 ℂ}
    {Tn : Matrix ι Hn ℂ} {Tn1 : Matrix ι Hn1 ℂ} {Rn : Matrix Hn Hn1 ℂ}
    {U : Matrix ι ι ℂ} {Kn Kn1 Dn : Matrix ι ι ℂ} {d α : ℝ}
    (hKh : Kn1.IsHermitian) (hU : Uᴴ * U = 1)
    (hKn : ∀ u : Hn → ℂ,
      (star (Tn *ᵥ u) ⬝ᵥ (Kn *ᵥ (Tn *ᵥ u))).re ≤ (star u ⬝ᵥ (An *ᵥ u)).re)
    (hKn1 : ∀ s : ι → ℂ,
      IsLeast {r : ℝ | ∃ u, Tn1 *ᵥ u = s ∧ r = (star u ⬝ᵥ (An1 *ᵥ u)).re}
        ((star s ⬝ᵥ (Kn1 *ᵥ s)).re))
    (henergy : (An1 + (Tn * Rn)ᴴ * Dn * (Tn * Rn) - Rnᴴ * An * Rn).PosSemidef)
    (hd : 0 < d) (hfloor : (Kn - Dn - (d : ℂ) • 1).PosSemidef) (hα : 0 ≤ α)
    (hangle : ∀ u : Hn1 → ℂ,
      (star ((Tn1 - U * (Tn * Rn)) *ᵥ u) ⬝ᵥ ((Tn1 - U * (Tn * Rn)) *ᵥ u)).re
        ≤ α ^ 2 * (star u ⬝ᵥ (An1 *ᵥ u)).re) :
    (((Real.sqrt d)⁻¹ + α) ^ 2)⁻¹ ≤ hermLamMin hKh := by
  have h := source_rotation_bound hKh hU hKn hKn1 henergy hd hfloor hα hangle
  refine le_hermLamMin_of_loewner hKh ?_
  have hcast : ((((Real.sqrt d)⁻¹ + α) ^ 2)⁻¹ : ℝ) • (1 : Matrix ι ι ℂ)
      = (((((Real.sqrt d)⁻¹ + α) ^ 2)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [Complex.coe_smul]
  rwa [hcast] at h

end SourceRotation

end SourceRotationSection

/-! ### `thm:GT-canonical-record-likelihood` — Record-likelihood, entropy, Fisher

Rendering: the packet of `def:GT-record-likelihood-tower` is a full-support
finite reference law `(Ω, w)` (`0 < w`, total mass one where displayed), a
terminal density `L ≥ 0`, and a filtration of physical records
(`MgtFilt.Chain`); `towerL j = 𝔼_λ[L|𝓕_j]` renders `L_j = P_j L` and
`π_j = L_j λ`.  (R1) is `towerL_project` (STG.15), `towerL_nonneg`,
`towerL_mean` (mean preservation), and `towerL_unique` (the unique
record-measurable density reproducing every record-visible expectation).
(R2) is `towerL_absCont`, the zero-safe canonical factor `canFactor`
(STG.16, indexed so that `canFactor j` is the stage-`(j+1)` factor
`dπ_{j+1}/dπ_j`), its record measurability, the pointwise
Radon–Nikodym identity `canFactor_rn`, the unit conditional mean
`canFactor_unit_mean`, and the surviving-support product recovery
`canFactor_partial_prod`.  (R3) is the exact entropy chain rule
`entropy_chain` (STG.17) with `entRel_nonneg` (finite Gibbs) and the
duplication-free telescope `entropy_telescope`.  (R4) is the mutual
orthogonality of likelihood innovations (`innovations_orthogonal`) and the
two Pythagoras identities (STG.18–STG.19).  (R5) is the Fisher increment
identity `scoreGram_increment` (STG.20), its positivity, and the exact rank
identity `scoreGram_increment_rank`: the increment rank is the rank of the
weighted newly visible score family. -/

section RecordTowerSection

namespace RecordTower

open MgtFilt

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The record-likelihood tower `L_j = 𝔼_λ[L | 𝓕_j]` (STG.14). -/
noncomputable def towerL (w : Ω → ℝ) (f : ℕ → Ω → ι) (L : Ω → ℝ) (j : ℕ) : Ω → ℝ :=
  cexp w (f j) L

/-- **(STG.15)** The densities form a martingale: `P_i L_j = L_i` for `i ≤ j`. -/
theorem towerL_project {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (hchain : Chain f) (L : Ω → ℝ) {i j : ℕ} (hij : i ≤ j) :
    cexp w (f i) (towerL w f L j) = towerL w f L i :=
  cexp_cexp hw (hchain hij) L

omit [Fintype ι] in
/-- The tower densities are nonnegative. -/
theorem towerL_nonneg {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (f : ℕ → Ω → ι)
    {L : Ω → ℝ} (hL : ∀ x, 0 ≤ L x) (j : ℕ) (x : Ω) : 0 ≤ towerL w f L j x :=
  cexp_nonneg (fun y => (hw y).le) (f j) hL x

/-- The tower preserves the terminal mean: each `π_j` has the mass of `π`. -/
theorem towerL_mean {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (f : ℕ → Ω → ι) (L : Ω → ℝ)
    (j : ℕ) : ∑ x, w x * towerL w f L j x = ∑ x, w x * L x := by
  unfold towerL
  have h := sum_cexp hw (f j) L
  simpa only [smul_eq_mul] using h

omit [Fintype ι] in
/-- **(R1, uniqueness)** `π_j` is the unique record-measurable-density law
reproducing every terminal expectation visible on the `j`-th record. -/
theorem towerL_unique {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (f : ℕ → Ω → ι) (L : Ω → ℝ)
    (j : ℕ) (ρ : Ω → ℝ) (hmeas : DetOn (f j) ρ)
    (hrep : ∀ g : ι → ℝ, ∑ x, w x * (ρ x * g (f j x))
      = ∑ x, w x * (L x * g (f j x))) :
    ρ = towerL w f L j := by
  funext x0
  have hkey := hrep fun t => if t = f j x0 then 1 else 0
  have hconv : ∀ X : Ω → ℝ,
      ∑ x, w x * (X x * if f j x = f j x0 then 1 else 0)
        = ∑ x ∈ Finset.univ.filter fun x => f j x = f j x0, w x * X x := by
    intro X
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [mul_one]
    · rw [mul_zero, mul_zero]
  rw [hconv ρ, hconv L] at hkey
  have hρconst : ∀ x ∈ Finset.univ.filter fun x => f j x = f j x0,
      w x * ρ x = w x * ρ x0 := fun x hx => by
    rw [hmeas x x0 (Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hρconst, ← Finset.sum_mul] at hkey
  have hmass : 0 < mass w (f j) (f j x0) := mass_pos hw (f j) x0
  have hLsum : ∑ x ∈ Finset.univ.filter fun x => f j x = f j x0, w x * L x
      = mass w (f j) (f j x0) * towerL w f L j x0 := by
    change _ = mass w (f j) (f j x0) * cexp w (f j) L x0
    unfold cexp
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hmass.ne', one_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_eq_mul]
  rw [hLsum] at hkey
  have hm : (∑ x ∈ Finset.univ.filter fun x => f j x = f j x0, w x)
      = mass w (f j) (f j x0) := rfl
  rw [hm] at hkey
  have := mul_left_cancel₀ hmass.ne' hkey
  exact this

omit [Fintype ι] in
/-- **(R2, absolute continuity)** `π_{j+1} ≪ π_j`: a vanishing stage density
forces the next stage density to vanish. -/
theorem towerL_absCont {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (hchain : Chain f) {L : Ω → ℝ} (hL : ∀ x, 0 ≤ L x) (j : ℕ) (x : Ω)
    (h0 : towerL w f L j x = 0) : towerL w f L (j + 1) x = 0 := by
  have hmass : 0 < mass w (f j) (f j x) := mass_pos hw (f j) x
  have hsum0 : ∑ y ∈ Finset.univ.filter fun y => f j y = f j x, w y * L y = 0 := by
    have h1 : towerL w f L j x
        = (mass w (f j) (f j x))⁻¹
          * ∑ y ∈ Finset.univ.filter fun y => f j y = f j x, w y * L y := by
      change cexp w (f j) L x = _
      unfold cexp
      rw [smul_eq_mul]
      congr 1
    rw [h1] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (inv_ne_zero hmass.ne')
    · exact h
  have hzero : ∀ y ∈ Finset.univ.filter fun y => f j y = f j x, w y * L y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun y _ =>
      mul_nonneg (hw y).le (hL y)).mp hsum0
  have hLzero : ∀ y, f j y = f j x → L y = 0 := by
    intro y hy
    have h := hzero y (by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      hy])
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (hw y).ne'
    · exact h'
  change cexp w (f (j + 1)) L x = 0
  unfold cexp
  rw [smul_eq_mul]
  have hall : ∀ y ∈ Finset.univ.filter fun y => f (j + 1) y = f (j + 1) x,
      w y • L y = 0 := by
    intro y hy
    have hfy : f (j + 1) y = f (j + 1) x := (Finset.mem_filter.mp hy).2
    rw [hLzero y (hchain (Nat.le_succ j) y x hfy), smul_zero]
  rw [Finset.sum_eq_zero hall, mul_zero]

/-- The zero-safe canonical stage factor (STG.16): `canFactor j` renders
`a_{j+1}^can = 1_{L_j > 0} L_{j+1}/L_j`. -/
noncomputable def canFactor (w : Ω → ℝ) (f : ℕ → Ω → ι) (L : Ω → ℝ) (j : ℕ) :
    Ω → ℝ := fun x =>
  if 0 < towerL w f L j x then towerL w f L (j + 1) x / towerL w f L j x else 0

omit [Fintype ι] in
/-- The canonical stage factor is determined by the finer record. -/
theorem canFactor_detOn {w : Ω → ℝ} {f : ℕ → Ω → ι} (hchain : Chain f)
    (L : Ω → ℝ) (j : ℕ) : DetOn (f (j + 1)) (canFactor w f L j) := by
  intro x y hxy
  unfold canFactor towerL
  rw [detOn_cexp w (f (j + 1)) L x y hxy,
    (detOn_cexp w (f j) L).mono (hchain (Nat.le_succ j)) x y hxy]

omit [Fintype ι] in
/-- **(R2, Radon–Nikodym identity)** `a_{j+1}^can · L_j = L_{j+1}` pointwise:
the zero-safe factor is the density of `π_{j+1}` against `π_j`. -/
theorem canFactor_rn {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (hchain : Chain f) {L : Ω → ℝ} (hL : ∀ x, 0 ≤ L x) (j : ℕ) (x : Ω) :
    canFactor w f L j x * towerL w f L j x = towerL w f L (j + 1) x := by
  unfold canFactor
  split_ifs with hpos
  · exact div_mul_cancel₀ _ hpos.ne'
  · have h0 : towerL w f L j x = 0 :=
      le_antisymm (not_lt.mp hpos) (towerL_nonneg hw f hL j x)
    rw [zero_mul, towerL_absCont hw hchain hL j x h0]

/-- **(R2, unit conditional mean)** The canonical factor has unit conditional
mean under `π_j`: it integrates to one against every record-visible writer
weighted by the stage density. -/
theorem canFactor_unit_mean {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (hchain : Chain f) {L : Ω → ℝ} (hL : ∀ x, 0 ≤ L x) (j : ℕ) (g : ι → ℝ) :
    ∑ x, w x * (towerL w f L j x * (canFactor w f L j x * g (f j x)))
      = ∑ x, w x * (towerL w f L j x * g (f j x)) := by
  have hgj1 : DetOn (f (j + 1)) fun x => g (f j x) := fun x y hxy =>
    congrArg g (hchain (Nat.le_succ j) x y hxy)
  have h1 := master_smul hw (V := L) (f := f (j + 1))
    (a := fun x => g (f j x)) hgj1
  have h2 := master_smul hw (V := L) (f := f j)
    (a := fun x => g (f j x)) fun x y hxy => congrArg g hxy
  calc ∑ x, w x * (towerL w f L j x * (canFactor w f L j x * g (f j x)))
      = ∑ x, w x * (g (f j x) * towerL w f L (j + 1) x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← canFactor_rn hw hchain hL j x]
        ring
    _ = ∑ x, w x * (g (f j x) * L x) := by
        have h := h1
        simp only [smul_eq_mul] at h
        exact h
    _ = ∑ x, w x * (g (f j x) * towerL w f L j x) := by
        have h := h2
        simp only [smul_eq_mul] at h
        exact h.symm
    _ = ∑ x, w x * (towerL w f L j x * g (f j x)) :=
        Finset.sum_congr rfl fun x _ => by ring

omit [Fintype ι] in
/-- **(R2, product recovery)** On the surviving support, the partial products
of the canonical factors recover the stage density over the base stage. -/
theorem canFactor_partial_prod {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (hchain : Chain f) {L : Ω → ℝ} (hL : ∀ x, 0 ≤ L x) (j : ℕ) (x : Ω)
    (hsupp : ∀ k, k < j → 0 < towerL w f L k x) :
    towerL w f L j x
      = towerL w f L 0 x * ∏ k ∈ Finset.range j, canFactor w f L k x := by
  induction j with
  | zero => rw [Finset.range_zero, Finset.prod_empty, mul_one]
  | succ j ih =>
    have hsupp' : ∀ k, k < j → 0 < towerL w f L k x := fun k hk =>
      hsupp k (Nat.lt_succ_of_lt hk)
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih hsupp',
      ← canFactor_rn hw hchain hL j x, mul_comm]

/-- The finite relative entropy `D(p·λ ‖ q·λ)` of two stage densities. -/
noncomputable def entRel (w p q : Ω → ℝ) : ℝ :=
  ∑ x, w x * (p x * (Real.log (p x) - Real.log (q x)))

/-- The finite entropy `D(p·λ ‖ λ)` of a stage density. -/
noncomputable def entAbs (w p : Ω → ℝ) : ℝ :=
  ∑ x, w x * (p x * Real.log (p x))

/-- **(R3 / STG.17, chain rule)** The entropy increments are exactly the
adjacent relative entropies:
`D(π_{j+1}‖λ) - D(π_j‖λ) = D(π_{j+1}‖π_j)`. -/
theorem entropy_chain {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (hchain : Chain f) (L : Ω → ℝ) (j : ℕ) :
    entAbs w (towerL w f L (j + 1)) - entAbs w (towerL w f L j)
      = entRel w (towerL w f L (j + 1)) (towerL w f L j) := by
  have ha : DetOn (f j) fun x => Real.log (towerL w f L j x) := fun x y hxy =>
    congrArg Real.log (detOn_cexp w (f j) L x y hxy)
  have h1 := master_smul hw (V := L) (f := f (j + 1))
    (a := fun x => Real.log (towerL w f L j x)) (ha.mono (hchain (Nat.le_succ j)))
  have h2 := master_smul hw (V := L) (f := f j)
    (a := fun x => Real.log (towerL w f L j x)) ha
  simp only [smul_eq_mul] at h1 h2
  have hcross : ∑ x, w x * (Real.log (towerL w f L j x) * towerL w f L (j + 1) x)
      = ∑ x, w x * (Real.log (towerL w f L j x) * towerL w f L j x) := by
    rw [show (∑ x, w x * (Real.log (towerL w f L j x) * towerL w f L (j + 1) x))
        = ∑ x, w x * (Real.log (towerL w f L j x) * L x) from h1]
    exact h2.symm
  unfold entRel entAbs
  rw [← Finset.sum_sub_distrib]
  calc ∑ x, (w x * (towerL w f L (j + 1) x * Real.log (towerL w f L (j + 1) x))
        - w x * (towerL w f L j x * Real.log (towerL w f L j x)))
      = (∑ x, w x * (towerL w f L (j + 1) x
            * (Real.log (towerL w f L (j + 1) x)
              - Real.log (towerL w f L j x))))
        + ((∑ x, w x * (Real.log (towerL w f L j x) * towerL w f L (j + 1) x))
          - ∑ x, w x * (Real.log (towerL w f L j x) * towerL w f L j x)) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = ∑ x, w x * (towerL w f L (j + 1) x
          * (Real.log (towerL w f L (j + 1) x) - Real.log (towerL w f L j x))) := by
        rw [hcross, sub_self, add_zero]

/-- The pointwise finite Gibbs inequality with the zero-safe conventions. -/
theorem gibbs_pointwise {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (habs : q = 0 → p = 0) : p - q ≤ p * (Real.log p - Real.log q) := by
  rcases eq_or_lt_of_le hp with hp0 | hppos
  · rw [← hp0, zero_mul, zero_sub]
    linarith
  · have hqpos : 0 < q := by
      rcases eq_or_lt_of_le hq with hq0 | h
      · exact absurd (habs hq0.symm) hppos.ne'
      · exact h
    have hlog : Real.log (q / p) ≤ q / p - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hqpos hppos)
    have hlogdiv : Real.log (q / p) = Real.log q - Real.log p :=
      Real.log_div hqpos.ne' hppos.ne'
    rw [hlogdiv] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hp
    have hpq : p * (q / p) = q := by
      field_simp
    nlinarith [hmul, hpq]

/-- **(R3, positivity)** Each entropy increment is nonnegative — the finite
Gibbs inequality for the adjacent stage laws. -/
theorem entRel_nonneg {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (hchain : Chain f) {L : Ω → ℝ} (hL : ∀ x, 0 ≤ L x) (j : ℕ) :
    0 ≤ entRel w (towerL w f L (j + 1)) (towerL w f L j) := by
  have hmean : ∑ x, w x * towerL w f L (j + 1) x
      = ∑ x, w x * towerL w f L j x := by
    rw [towerL_mean hw f L (j + 1), towerL_mean hw f L j]
  have hterm : ∀ x, w x * (towerL w f L (j + 1) x - towerL w f L j x)
      ≤ w x * (towerL w f L (j + 1) x
        * (Real.log (towerL w f L (j + 1) x) - Real.log (towerL w f L j x))) := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (hw x).le
    refine gibbs_pointwise (towerL_nonneg hw f hL (j + 1) x)
      (towerL_nonneg hw f hL j x) fun h0 => ?_
    exact towerL_absCont hw hchain hL j x h0
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hterm x
  unfold entRel
  have hzero : ∑ x, w x * (towerL w f L (j + 1) x - towerL w f L j x) = 0 := by
    rw [show (∑ x, w x * (towerL w f L (j + 1) x - towerL w f L j x))
        = (∑ x, w x * towerL w f L (j + 1) x) - ∑ x, w x * towerL w f L j x by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring]
    rw [hmean, sub_self]
  linarith [hsum, hzero.symm.le, hzero.le]

omit [Fintype ι] in
/-- **(R3, telescope)** The entropy increments telescope without
duplication. -/
theorem entropy_telescope {w : Ω → ℝ} (f : ℕ → Ω → ι) (L : Ω → ℝ) (r : ℕ) :
    ∑ j ∈ Finset.range r,
        (entAbs w (towerL w f L (j + 1)) - entAbs w (towerL w f L j))
      = entAbs w (towerL w f L r) - entAbs w (towerL w f L 0) :=
  Finset.sum_range_sub (fun j => entAbs w (towerL w f L j)) r

/-- The weighted squared `L²(λ)` norm. -/
noncomputable def wnormSq (w g : Ω → ℝ) : ℝ := ∑ x, w x * g x ^ 2

/-- **(R4, orthogonality)** The likelihood innovations are mutually
orthogonal in `L²(λ)`. -/
theorem innovations_orthogonal {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (hchain : Chain f) (L : Ω → ℝ) {j k : ℕ} (hjk : j < k) :
    ∑ x, w x * (dinc w f L j x * dinc w f L k x) = 0 := by
  have h := dinc_master_zero hw hchain L hjk
    (fun x => dinc w f L j x • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    (fun x y hxy => congrArg (· • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
      (detOn_dinc hchain L j x y hxy))
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] using h

/-- Cross terms against record-determined scalar writers vanish. -/
theorem residual_orthogonal {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (L : Ω → ℝ) (j : ℕ) {a : Ω → ℝ} (ha : DetOn (f j) a) :
    ∑ x, w x * (a x * (L x - marti w f L j x)) = 0 := by
  have h := master_smul hw (V := L) (f := f j) (a := a) ha
  simp only [smul_eq_mul] at h
  rw [show (∑ x, w x * (a x * (L x - marti w f L j x)))
      = (∑ x, w x * (a x * L x)) - ∑ x, w x * (a x * marti w f L j x) by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring]
  rw [show (∑ x, w x * (a x * marti w f L j x)) = ∑ x, w x * (a x * L x) from h,
    sub_self]

/-- **(R4 / STG.18)** The `L²` innovation Pythagoras along the record tower. -/
theorem innovation_pythagoras {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (hchain : Chain f) (L : Ω → ℝ) (j : ℕ) :
    wnormSq w (fun x => marti w f L j x - marti w f L 0 x)
      = ∑ k ∈ Finset.range j, wnormSq w (dinc w f L (k + 1)) := by
  induction j with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    unfold wnormSq
    refine Finset.sum_eq_zero fun x _ => ?_
    beta_reduce
    rw [sub_self, zero_pow (by norm_num), mul_zero]
  | succ j ih =>
    have hsplit : ∀ x, marti w f L (j + 1) x - marti w f L 0 x
        = (marti w f L j x - marti w f L 0 x) + dinc w f L (j + 1) x := by
      intro x
      change _ = _ + (marti w f L (j + 1) x - marti w f L j x)
      ring
    have hcross : ∑ x, w x * ((marti w f L j x - marti w f L 0 x)
        * dinc w f L (j + 1) x) = 0 := by
      have h := dinc_master_zero hw hchain L (Nat.lt_succ_self j)
        (fun x => (marti w f L j x - marti w f L 0 x)
          • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
        (fun x y hxy => by
          have h1 := detOn_marti w f L j x y hxy
          have h2 := (detOn_marti w f L 0).mono (hchain (Nat.zero_le j)) x y hxy
          exact congrArg (· • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) (by rw [h1, h2]))
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] using h
    calc wnormSq w (fun x => marti w f L (j + 1) x - marti w f L 0 x)
        = wnormSq w (fun x => marti w f L j x - marti w f L 0 x)
          + wnormSq w (dinc w f L (j + 1))
          + 2 * ∑ x, w x * ((marti w f L j x - marti w f L 0 x)
              * dinc w f L (j + 1) x) := by
          unfold wnormSq
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          beta_reduce
          rw [hsplit x]
          ring
      _ = ∑ k ∈ Finset.range (j + 1), wnormSq w (dinc w f L (k + 1)) := by
          rw [hcross, ih, Finset.sum_range_succ]
          ring

/-- **(R4 / STG.19)** The terminal `L²` Pythagoras: the innovation energies
and the unresolved remainder split the terminal deviation exactly. -/
theorem terminal_pythagoras {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι}
    (hchain : Chain f) (L : Ω → ℝ) (j : ℕ) :
    wnormSq w (fun x => L x - marti w f L 0 x)
      = ∑ k ∈ Finset.range j, wnormSq w (dinc w f L (k + 1))
        + wnormSq w (fun x => L x - marti w f L j x) := by
  have hcross : ∑ x, w x * ((marti w f L j x - marti w f L 0 x)
      * (L x - marti w f L j x)) = 0 := by
    refine residual_orthogonal hw L j fun x y hxy => ?_
    have h1 := detOn_marti w f L j x y hxy
    have h2 := (detOn_marti w f L 0).mono (hchain (Nat.zero_le j)) x y hxy
    rw [h1, h2]
  calc wnormSq w (fun x => L x - marti w f L 0 x)
      = wnormSq w (fun x => marti w f L j x - marti w f L 0 x)
        + wnormSq w (fun x => L x - marti w f L j x)
        + 2 * ∑ x, w x * ((marti w f L j x - marti w f L 0 x)
            * (L x - marti w f L j x)) := by
        unfold wnormSq
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = _ := by
        rw [hcross, innovation_pythagoras hw hchain L j]
        ring

/-- The record-visible score Gram `G_j = 𝒮ᴴ P_j 𝒮` (STG.20). -/
noncomputable def scoreGram {Es : Type*} [Fintype Es] (w : Ω → ℝ)
    (f : ℕ → Ω → ι) (S : Ω → Es → ℝ) (j : ℕ) : Matrix Es Es ℝ :=
  Matrix.of fun e e' =>
    ∑ x, w x * (S x e * cexp w (f j) (fun y => S y e') x)

/-- The weighted newly visible score family: the `√w`-weighted difference of
the two adjacent record compressions of the score bank. -/
noncomputable def scoreInnovation {Es : Type*} [Fintype Es] (w : Ω → ℝ)
    (f : ℕ → Ω → ι) (S : Ω → Es → ℝ) (j : ℕ) : Matrix Ω Es ℝ :=
  Matrix.of fun x e => Real.sqrt (w x)
    * (cexp w (f (j + 1)) (fun y => S y e) x - cexp w (f j) (fun y => S y e) x)

/-- **(R5 / STG.20)** The Fisher increment is the Gram of the weighted newly
visible score family: `G_{j+1} - G_j = Kᵀ K ⪰ 0` in exact form. -/
theorem scoreGram_increment {Es : Type*} [Fintype Es] {w : Ω → ℝ}
    (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι} (hchain : Chain f)
    (S : Ω → Es → ℝ) (j : ℕ) :
    scoreGram w f S (j + 1) - scoreGram w f S j
      = (scoreInnovation w f S j)ᵀ * scoreInnovation w f S j := by
  ext e e'
  have key : ∀ (lv : ℕ) (b : Ω → ℝ), DetOn (f lv) b →
      (∑ x, w x * (b x * cexp w (f lv) (fun y => S y e') x))
        = ∑ x, w x * (b x * S x e') := by
    intro lv b hb
    have h := master_smul hw (V := fun y => S y e') (f := f lv) (a := b) hb
    simpa only [smul_eq_mul] using h
  -- self-adjoint moves for the four blocks
  have hP1 : DetOn (f (j + 1)) (cexp w (f (j + 1)) fun y => S y e) :=
    detOn_cexp _ _ _
  have hP0 : DetOn (f j) (cexp w (f j) fun y => S y e) := detOn_cexp _ _ _
  have hSe1 : ∀ lv : ℕ, ∀ b : Ω → ℝ, DetOn (f lv) b →
      (∑ x, w x * (S x e * b x)) = ∑ x, w x * (b x * S x e) :=
    fun lv b _ => Finset.sum_congr rfl fun x _ => by ring
  -- block identities
  have h11 : ∑ x, w x * (S x e * cexp w (f (j + 1)) (fun y => S y e') x)
      = ∑ x, w x * (cexp w (f (j + 1)) (fun y => S y e) x
          * cexp w (f (j + 1)) (fun y => S y e') x) := by
    have ha := master_smul hw (V := fun y => S y e) (f := f (j + 1))
      (a := cexp w (f (j + 1)) fun y => S y e') (detOn_cexp _ _ _)
    simp only [smul_eq_mul] at ha
    calc ∑ x, w x * (S x e * cexp w (f (j + 1)) (fun y => S y e') x)
        = ∑ x, w x * (cexp w (f (j + 1)) (fun y => S y e') x * S x e) :=
          Finset.sum_congr rfl fun x _ => by ring
      _ = ∑ x, w x * (cexp w (f (j + 1)) (fun y => S y e') x
            * cexp w (f (j + 1)) (fun y => S y e) x) := ha.symm
      _ = _ := Finset.sum_congr rfl fun x _ => by ring
  have h00 : ∑ x, w x * (S x e * cexp w (f j) (fun y => S y e') x)
      = ∑ x, w x * (cexp w (f j) (fun y => S y e) x
          * cexp w (f j) (fun y => S y e') x) := by
    have ha := master_smul hw (V := fun y => S y e) (f := f j)
      (a := cexp w (f j) fun y => S y e') (detOn_cexp _ _ _)
    simp only [smul_eq_mul] at ha
    calc ∑ x, w x * (S x e * cexp w (f j) (fun y => S y e') x)
        = ∑ x, w x * (cexp w (f j) (fun y => S y e') x * S x e) :=
          Finset.sum_congr rfl fun x _ => by ring
      _ = ∑ x, w x * (cexp w (f j) (fun y => S y e') x
            * cexp w (f j) (fun y => S y e) x) := ha.symm
      _ = _ := Finset.sum_congr rfl fun x _ => by ring
  -- cross blocks collapse to the coarse block
  have hcross1 : ∑ x, w x * (cexp w (f (j + 1)) (fun y => S y e) x
        * cexp w (f j) (fun y => S y e') x)
      = ∑ x, w x * (cexp w (f j) (fun y => S y e) x
          * cexp w (f j) (fun y => S y e') x) := by
    have ha1 := master_smul hw (V := fun y => S y e) (f := f (j + 1))
      (a := cexp w (f j) fun y => S y e')
      ((detOn_cexp _ _ _).mono (hchain (Nat.le_succ j)))
    have ha0 := master_smul hw (V := fun y => S y e) (f := f j)
      (a := cexp w (f j) fun y => S y e') (detOn_cexp _ _ _)
    simp only [smul_eq_mul] at ha1 ha0
    calc ∑ x, w x * (cexp w (f (j + 1)) (fun y => S y e) x
          * cexp w (f j) (fun y => S y e') x)
        = ∑ x, w x * (cexp w (f j) (fun y => S y e') x
            * cexp w (f (j + 1)) (fun y => S y e) x) :=
          Finset.sum_congr rfl fun x _ => by ring
      _ = ∑ x, w x * (cexp w (f j) (fun y => S y e') x * S x e) := ha1
      _ = ∑ x, w x * (cexp w (f j) (fun y => S y e') x
            * cexp w (f j) (fun y => S y e) x) := ha0.symm
      _ = _ := Finset.sum_congr rfl fun x _ => by ring
  have hcross2 : ∑ x, w x * (cexp w (f j) (fun y => S y e) x
        * cexp w (f (j + 1)) (fun y => S y e') x)
      = ∑ x, w x * (cexp w (f j) (fun y => S y e) x
          * cexp w (f j) (fun y => S y e') x) := by
    have ha1 := master_smul hw (V := fun y => S y e') (f := f (j + 1))
      (a := cexp w (f j) fun y => S y e)
      ((detOn_cexp _ _ _).mono (hchain (Nat.le_succ j)))
    have ha0 := master_smul hw (V := fun y => S y e') (f := f j)
      (a := cexp w (f j) fun y => S y e) (detOn_cexp _ _ _)
    simp only [smul_eq_mul] at ha1 ha0
    calc ∑ x, w x * (cexp w (f j) (fun y => S y e) x
          * cexp w (f (j + 1)) (fun y => S y e') x)
        = ∑ x, w x * (cexp w (f j) (fun y => S y e) x * S x e') := ha1
      _ = _ := ha0.symm
  -- assemble the Gram entry
  change scoreGram w f S (j + 1) e e' - scoreGram w f S j e e'
    = ((scoreInnovation w f S j)ᵀ * scoreInnovation w f S j) e e'
  rw [Matrix.mul_apply]
  unfold scoreGram scoreInnovation
  simp only [Matrix.of_apply, Matrix.transpose_apply]
  rw [h11, h00]
  rw [show (∑ x, Real.sqrt (w x)
        * (cexp w (f (j + 1)) (fun y => S y e) x
          - cexp w (f j) (fun y => S y e) x)
        * (Real.sqrt (w x) * (cexp w (f (j + 1)) (fun y => S y e') x
          - cexp w (f j) (fun y => S y e') x)))
      = ∑ x, w x * ((cexp w (f (j + 1)) (fun y => S y e) x
          - cexp w (f j) (fun y => S y e) x)
        * (cexp w (f (j + 1)) (fun y => S y e') x
          - cexp w (f j) (fun y => S y e') x)) from
    Finset.sum_congr rfl fun x _ => by
      rw [show Real.sqrt (w x) * (cexp w (f (j + 1)) (fun y => S y e) x
            - cexp w (f j) (fun y => S y e) x)
          * (Real.sqrt (w x) * (cexp w (f (j + 1)) (fun y => S y e') x
            - cexp w (f j) (fun y => S y e') x))
          = Real.sqrt (w x) * Real.sqrt (w x)
            * ((cexp w (f (j + 1)) (fun y => S y e) x
              - cexp w (f j) (fun y => S y e) x)
            * (cexp w (f (j + 1)) (fun y => S y e') x
              - cexp w (f j) (fun y => S y e') x)) from by ring,
        Real.mul_self_sqrt (hw x).le]]
  have hexpand : ∀ x, w x * ((cexp w (f (j + 1)) (fun y => S y e) x
        - cexp w (f j) (fun y => S y e) x)
      * (cexp w (f (j + 1)) (fun y => S y e') x
        - cexp w (f j) (fun y => S y e') x))
      = w x * (cexp w (f (j + 1)) (fun y => S y e) x
          * cexp w (f (j + 1)) (fun y => S y e') x)
        - w x * (cexp w (f (j + 1)) (fun y => S y e) x
            * cexp w (f j) (fun y => S y e') x)
        - w x * (cexp w (f j) (fun y => S y e) x
            * cexp w (f (j + 1)) (fun y => S y e') x)
        + w x * (cexp w (f j) (fun y => S y e) x
            * cexp w (f j) (fun y => S y e') x) := fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => hexpand x]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hcross1, hcross2]
  ring

/-- **(R5, positivity)** The Fisher increment is PSD. -/
theorem scoreGram_increment_posSemidef {Es : Type*} [Fintype Es] {w : Ω → ℝ}
    (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι} (hchain : Chain f)
    (S : Ω → Es → ℝ) (j : ℕ) :
    (scoreGram w f S (j + 1) - scoreGram w f S j).PosSemidef := by
  rw [scoreGram_increment hw hchain S j]
  have h : (scoreInnovation w f S j)ᵀ = (scoreInnovation w f S j)ᴴ := by
    ext e x
    rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
  rw [h]
  exact posSemidef_conjTranspose_mul_self _

/-- **(R5, rank identity)** The rank of the Fisher increment is exactly the
rank of the weighted newly visible score family: the newly visible score
dimension. -/
theorem scoreGram_increment_rank {Es : Type*} [Fintype Es] {w : Ω → ℝ}
    (hw : ∀ x, 0 < w x) {f : ℕ → Ω → ι} (hchain : Chain f)
    (S : Ω → Es → ℝ) (j : ℕ) :
    (scoreGram w f S (j + 1) - scoreGram w f S j).rank
      = (scoreInnovation w f S j).rank := by
  rw [scoreGram_increment hw hchain S j]
  exact Matrix.rank_transpose_mul_self (scoreInnovation w f S j)

end RecordTower

end RecordTowerSection

/-! ### `thm:GT-record-factor-audit` — Factor audit, recovery, cofinal transport

Rendering: the packet of `def:GT-record-factor-residual` consists of proposed
partial densities `A 0, …, A r` with `A 0 = L_0` against the record tower of
the previous section; the residual (STG.21) is `facResidual`.  The four-way
equivalence is split into the three iffs `facResidual_eq_zero_iff`
((A1) ⟺ (A2)), `audit_martingale_iff_canonical` ((A2) ⟺ (A3), under the
packet's terminal record-visibility `DetOn (f r) L`), and
`audit_canonical_iff_factors` ((A3) ⟺ (A4), the canonical-increment
factorization on the surviving supports in zero-safe multiplicative form).
`factor_recovery_bound` is the boxed (STG.22) with `ε_k^mart` indexed from
the bottom stage.  (STG.23) is `cutoff_transport_bound` (the contraction) and
`cutoff_transport_tendsto`; `entropy_stage_tendsto` and
`entRel_increment_tendsto` give the entropy convergence under a common
collar; `summable_defect_limit` and `wnorm_limit_unique` give the unique
route-independent limit under summable adjacent `L²` defects; and
`approx_factors_tendsto` renders the closing clause: proposed
cutoff-dependent partial products with vanishing terminal and
backward-martingale residuals converge to the canonical stage `P_j L` at
every stage. -/

section RecordAuditSection

namespace RecordAudit

open MgtFilt RecordTower

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The record-martingale factor residual (STG.21): terminal defect plus the
backward-conditional stage defects. -/
noncomputable def facResidual (w : Ω → ℝ) (f : ℕ → Ω → ι) (L : Ω → ℝ)
    (A : ℕ → Ω → ℝ) (r : ℕ) : ℝ :=
  wnormSq w (fun x => A r x - L x)
    + ∑ j ∈ Finset.range r,
        wnormSq w (fun x => A j x - cexp w (f j) (A (j + 1)) x)

omit [Fintype ι] in
/-- A weighted square norm vanishes iff the writer vanishes (full support). -/
theorem wnormSq_eq_zero_iff {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (g : Ω → ℝ) :
    wnormSq w g = 0 ↔ ∀ x, g x = 0 := by
  unfold wnormSq
  rw [Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
    mul_nonneg (hw x).le (sq_nonneg _)]
  constructor
  · intro h x
    have hx := h x (Finset.mem_univ x)
    rcases mul_eq_zero.mp hx with h' | h'
    · exact absurd h' (hw x).ne'
    · exact pow_eq_zero_iff (by norm_num) |>.mp h'
  · intro h x _
    rw [h x, zero_pow (by norm_num), mul_zero]

omit [Fintype ι] in
/-- The weighted square norm is nonnegative. -/
theorem wnormSq_nonneg {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (g : Ω → ℝ) :
    0 ≤ wnormSq w g :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x).le (sq_nonneg _)

omit [Fintype ι] in
/-- **(A1 ⟺ A2)** The residual vanishes exactly when the terminal defect and
every backward-martingale defect vanish pointwise. -/
theorem facResidual_eq_zero_iff {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    (f : ℕ → Ω → ι) (L : Ω → ℝ) (A : ℕ → Ω → ℝ) (r : ℕ) :
    facResidual w f L A r = 0
      ↔ (∀ x, A r x = L x)
        ∧ ∀ j < r, ∀ x, A j x = cexp w (f j) (A (j + 1)) x := by
  unfold facResidual
  constructor
  · intro h
    have hterm : wnormSq w (fun x => A r x - L x) = 0 := by
      have h1 := wnormSq_nonneg hw fun x => A r x - L x
      have h2 : 0 ≤ ∑ j ∈ Finset.range r,
          wnormSq w (fun x => A j x - cexp w (f j) (A (j + 1)) x) :=
        Finset.sum_nonneg fun j _ => wnormSq_nonneg hw _
      linarith
    have hsum : ∑ j ∈ Finset.range r,
        wnormSq w (fun x => A j x - cexp w (f j) (A (j + 1)) x) = 0 := by
      have h1 := wnormSq_nonneg hw fun x => A r x - L x
      linarith
    have hstage := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      wnormSq_nonneg hw _).mp hsum
    refine ⟨fun x => ?_, fun j hj x => ?_⟩
    · have := (wnormSq_eq_zero_iff hw _).mp hterm x
      linarith [this]
    · have := (wnormSq_eq_zero_iff hw _).mp
        (hstage j (Finset.mem_range.mpr hj)) x
      linarith [this]
  · rintro ⟨hterm, hstage⟩
    have h1 : wnormSq w (fun x => A r x - L x) = 0 :=
      (wnormSq_eq_zero_iff hw _).mpr fun x => by rw [hterm x, sub_self]
    have h2 : ∀ j ∈ Finset.range r,
        wnormSq w (fun x => A j x - cexp w (f j) (A (j + 1)) x) = 0 := by
      intro j hj
      exact (wnormSq_eq_zero_iff hw _).mpr fun x => by
        rw [hstage j (Finset.mem_range.mp hj) x, sub_self]
    rw [h1, Finset.sum_eq_zero h2, add_zero]

/-- **(A2 ⟺ A3)** With the terminal density visible on the finest record, the
martingale-consistency clauses hold exactly when every proposed stage equals
the canonical stage `L_j = P_j L`. -/
theorem audit_martingale_iff_canonical {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) {L : Ω → ℝ} (hLr : DetOn (f r) L)
    (A : ℕ → Ω → ℝ) :
    ((∀ x, A r x = L x)
        ∧ ∀ j < r, ∀ x, A j x = cexp w (f j) (A (j + 1)) x)
      ↔ ∀ j ≤ r, ∀ x, A j x = towerL w f L j x := by
  have htop : towerL w f L r = L := cexp_of_detOn hw hLr
  constructor
  · rintro ⟨hterm, hstage⟩
    have hdesc : ∀ k, k ≤ r → ∀ x, A (r - k) x = towerL w f L (r - k) x := by
      intro k
      induction k with
      | zero =>
        intro _ x
        rw [Nat.sub_zero, hterm x, htop]
      | succ k ih =>
        intro hk x
        have hklt : r - (k + 1) < r := by omega
        have hsucc : r - (k + 1) + 1 = r - k := by omega
        have h1 := hstage (r - (k + 1)) hklt x
        rw [hsucc] at h1
        have h2 : cexp w (f (r - (k + 1))) (A (r - k))
            = cexp w (f (r - (k + 1))) (towerL w f L (r - k)) := by
          have hAk : A (r - k) = towerL w f L (r - k) :=
            funext (ih (by omega))
          rw [hAk]
        rw [h1, h2, towerL_project hw hchain L (by omega : r - (k + 1) ≤ r - k)]
    intro j hj x
    have h := hdesc (r - j) (by omega) x
    rwa [show r - (r - j) = j by omega] at h
  · intro hcan
    refine ⟨fun x => by rw [hcan r le_rfl x, htop], fun j hj x => ?_⟩
    rw [hcan j (le_of_lt hj) x,
      show cexp w (f j) (A (j + 1)) = cexp w (f j) (towerL w f L (j + 1)) from by
        rw [funext fun y => hcan (j + 1) hj y],
      towerL_project hw hchain L (Nat.le_succ j)]

omit [Fintype ι] in
/-- **(A3 ⟺ A4)** Given the packet base `A 0 = L_0`, every stage is canonical
exactly when the proposed stages factor through the canonical zero-safe
increments (STG.16) on the surviving supports. -/
theorem audit_canonical_iff_factors {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) {L : Ω → ℝ} (hL : ∀ x, 0 ≤ L x)
    {r : ℕ} (A : ℕ → Ω → ℝ) (hA0 : ∀ x, A 0 x = towerL w f L 0 x) :
    (∀ j ≤ r, ∀ x, A j x = towerL w f L j x)
      ↔ ∀ j < r, ∀ x, A (j + 1) x = canFactor w f L j x * A j x := by
  constructor
  · intro hcan j hj x
    rw [hcan (j + 1) hj x, hcan j (le_of_lt hj) x,
      canFactor_rn hw hchain hL j x]
  · intro hfac
    have hup : ∀ j ≤ r, ∀ x, A j x = towerL w f L j x := by
      intro j
      induction j with
      | zero => exact fun _ x => hA0 x
      | succ j ih =>
        intro hj x
        rw [hfac j hj x, ih (by omega) x, canFactor_rn hw hchain hL j x]
    exact hup

/-- The weighted `L²(λ)` norm. -/
noncomputable def wnorm (w g : Ω → ℝ) : ℝ := Real.sqrt (wnormSq w g)

omit [Fintype ι] in
/-- The weighted norm is nonnegative. -/
theorem wnorm_nonneg (w g : Ω → ℝ) : 0 ≤ wnorm w g := Real.sqrt_nonneg _

omit [Fintype ι] in
/-- The weighted norm through the Euclidean norm of the `√w`-rescaled writer. -/
theorem wnorm_eq {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (g : Ω → ℝ) :
    wnorm w g
      = ‖(WithLp.toLp 2 (fun x => Real.sqrt (w x) * g x) : EuclideanSpace ℝ Ω)‖ := by
  unfold wnorm wnormSq
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hw x).le]

omit [Fintype ι] in
/-- Triangle inequality for the weighted norm, in difference form. -/
theorem wnorm_triangle {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (a b c : Ω → ℝ) :
    wnorm w (fun x => a x - c x)
      ≤ wnorm w (fun x => a x - b x) + wnorm w (fun x => b x - c x) := by
  rw [wnorm_eq hw, wnorm_eq hw, wnorm_eq hw]
  have hfun : (fun x => Real.sqrt (w x) * (a x - c x))
      = (fun x => Real.sqrt (w x) * (a x - b x))
        + fun x => Real.sqrt (w x) * (b x - c x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [hfun, WithLp.toLp_add]
  exact norm_add_le _ _

omit [Fintype ι] in
/-- The weighted norm of a pointwise-congruent writer. -/
theorem wnorm_congr {w : Ω → ℝ} {a b : Ω → ℝ} (h : ∀ x, a x = b x) :
    wnorm w a = wnorm w b := by
  rw [funext h]

/-- **Record contraction**: conditional expectation contracts the weighted
norm. -/
theorem wnorm_cexp_le {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (f : Ω → ι) (g : Ω → ℝ) :
    wnorm w (cexp w f g) ≤ wnorm w g := by
  have hcross : ∑ x, w x * (cexp w f g x * (g x - cexp w f g x)) = 0 := by
    have h := master_smul hw (V := g) (f := f) (a := cexp w f g)
      (detOn_cexp w f g)
    simp only [smul_eq_mul] at h
    rw [show (∑ x, w x * (cexp w f g x * (g x - cexp w f g x)))
        = (∑ x, w x * (cexp w f g x * g x))
          - ∑ x, w x * (cexp w f g x * cexp w f g x) from by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring]
    rw [← h, sub_self]
  have hpyth : wnormSq w g
      = wnormSq w (cexp w f g) + wnormSq w (fun x => g x - cexp w f g x) := by
    unfold wnormSq
    rw [← Finset.sum_add_distrib]
    have hexp : ∀ x, w x * g x ^ 2
        = w x * cexp w f g x ^ 2 + w x * (g x - cexp w f g x) ^ 2
          + 2 * (w x * (cexp w f g x * (g x - cexp w f g x))) := fun x => by ring
    rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_add_distrib,
      ← Finset.mul_sum, hcross, mul_zero, add_zero]
  unfold wnorm
  refine Real.sqrt_le_sqrt ?_
  have h2 := wnormSq_nonneg hw fun x => g x - cexp w f g x
  linarith [hpyth]

/-- **(STG.22)** Approximate recovery: the deviation of every proposed stage
from the canonical stage is controlled by the terminal defect plus the later
backward-martingale defects. -/
theorem factor_recovery_bound {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) {L : Ω → ℝ} {r : ℕ}
    (hLr : DetOn (f r) L) (A : ℕ → Ω → ℝ) :
    ∀ j ≤ r, wnorm w (fun x => A j x - towerL w f L j x)
      ≤ wnorm w (fun x => A r x - L x)
        + ∑ k ∈ Finset.Ico j r,
            wnorm w (fun x => A k x - cexp w (f k) (A (k + 1)) x) := by
  have htop : towerL w f L r = L := cexp_of_detOn hw hLr
  have key : ∀ d, ∀ j, j + d = r → wnorm w (fun x => A j x - towerL w f L j x)
      ≤ wnorm w (fun x => A r x - L x)
        + ∑ k ∈ Finset.Ico j r,
            wnorm w (fun x => A k x - cexp w (f k) (A (k + 1)) x) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      subst hj
      rw [Finset.Ico_self, Finset.sum_empty, add_zero, htop]
    | succ d ih =>
      intro j hj
      have hjr : j < r := by omega
      have hstep := ih (j + 1) (by omega)
      have htri := wnorm_triangle hw (fun x => A j x)
        (fun x => cexp w (f j) (A (j + 1)) x) (fun x => towerL w f L j x)
      have hcontr : wnorm w (fun x => cexp w (f j) (A (j + 1)) x
          - towerL w f L j x)
          ≤ wnorm w (fun x => A (j + 1) x - towerL w f L (j + 1) x) := by
        have heq : (fun x => cexp w (f j) (A (j + 1)) x - towerL w f L j x)
            = cexp w (f j) fun x => A (j + 1) x - towerL w f L (j + 1) x := by
          rw [cexp_sub w (f j) (A (j + 1)) (towerL w f L (j + 1))]
          funext x
          rw [towerL_project hw hchain L (Nat.le_succ j)]
        rw [heq]
        exact wnorm_cexp_le hw (f j) _
      have hsum : ∑ k ∈ Finset.Ico j r,
          wnorm w (fun x => A k x - cexp w (f k) (A (k + 1)) x)
          = wnorm w (fun x => A j x - cexp w (f j) (A (j + 1)) x)
            + ∑ k ∈ Finset.Ico (j + 1) r,
                wnorm w (fun x => A k x - cexp w (f k) (A (k + 1)) x) :=
        Finset.sum_eq_sum_Ico_succ_bot hjr _
      rw [hsum]
      linarith [htri, hcontr, hstep]
  intro j hj
  exact key (r - j) j (by omega)

/-- **(STG.23, contraction)** On a fixed transported screen, every stage
compression contracts the terminal deviation. -/
theorem cutoff_transport_bound {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (f : Ω → ι)
    (Ln L : Ω → ℝ) :
    wnorm w (fun x => cexp w f Ln x - cexp w f L x)
      ≤ wnorm w (fun x => Ln x - L x) := by
  have heq : (fun x => cexp w f Ln x - cexp w f L x)
      = cexp w f fun x => Ln x - L x := by
    rw [cexp_sub w f Ln L]
  rw [heq]
  exact wnorm_cexp_le hw f _

/-- **(STG.23, convergence)** Terminal `L²` convergence transports to every
stage: every likelihood stage and hence every finite likelihood innovation
converges. -/
theorem cutoff_transport_tendsto {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    (f : ℕ → Ω → ι) {Ln : ℕ → Ω → ℝ} {L : Ω → ℝ}
    (hconv : Tendsto (fun n => wnorm w (fun x => Ln n x - L x)) atTop (𝓝 0))
    (j : ℕ) :
    Tendsto (fun n => wnorm w (fun x => towerL w f (Ln n) j x - towerL w f L j x))
      atTop (𝓝 0) := by
  refine squeeze_zero (fun n => wnorm_nonneg _ _) (fun n => ?_) hconv
  exact cutoff_transport_bound hw (f j) (Ln n) L

omit [Fintype ι] in
/-- Weighted-norm convergence forces pointwise convergence on the
full-support carrier. -/
theorem pointwise_of_wnorm_tendsto {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {gn : ℕ → Ω → ℝ}
    (h : Tendsto (fun n => wnorm w (gn n)) atTop (𝓝 0)) (x : Ω) :
    Tendsto (fun n => gn n x) atTop (𝓝 0) := by
  have hbound : ∀ n, ‖gn n x‖ ≤ (Real.sqrt (w x))⁻¹ * wnorm w (gn n) := by
    intro n
    have h1 : w x * gn n x ^ 2 ≤ wnormSq w (gn n) := by
      unfold wnormSq
      exact Finset.single_le_sum
        (fun y (_ : y ∈ Finset.univ) => mul_nonneg (hw y).le (sq_nonneg _))
        (Finset.mem_univ x)
    have h2 : ‖gn n x‖ = Real.sqrt (gn n x ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
    rw [h2]
    have h3 : gn n x ^ 2 ≤ (w x)⁻¹ * wnormSq w (gn n) := by
      rw [le_inv_mul_iff₀ (hw x)]
      exact h1
    calc Real.sqrt (gn n x ^ 2) ≤ Real.sqrt ((w x)⁻¹ * wnormSq w (gn n)) :=
          Real.sqrt_le_sqrt h3
      _ = (Real.sqrt (w x))⁻¹ * wnorm w (gn n) := by
          rw [Real.sqrt_mul (inv_nonneg.mpr (hw x).le), Real.sqrt_inv]
          rfl
  have hlim : Tendsto (fun n => (Real.sqrt (w x))⁻¹ * wnorm w (gn n)) atTop
      (𝓝 0) := by
    have := h.const_mul (Real.sqrt (w x))⁻¹
    rwa [mul_zero] at this
  exact squeeze_zero_norm hbound hlim

omit [Fintype ι] in
/-- Stage densities inherit a lower collar. -/
theorem towerL_lower_collar {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (f : ℕ → Ω → ι)
    {L : Ω → ℝ} {c : ℝ} (hcol : ∀ x, c ≤ L x) (j : ℕ) (x : Ω) :
    c ≤ towerL w f L j x := by
  have h := cexp_mono hw (f j) hcol x
  rwa [show cexp w (f j) (fun _ => c) x = c from congrFun (cexp_const hw (f j) c) x]
    at h

/-- **(STG.23, entropy)** Under a common collar the stage entropies converge
along the transported terminal densities. -/
theorem entropy_stage_tendsto {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    (f : ℕ → Ω → ι) {Ln : ℕ → Ω → ℝ} {L : Ω → ℝ} {c : ℝ} (hc : 0 < c)
    (hcolL : ∀ x, c ≤ L x)
    (hconv : Tendsto (fun n => wnorm w (fun x => Ln n x - L x)) atTop (𝓝 0))
    (j : ℕ) :
    Tendsto (fun n => entAbs w (towerL w f (Ln n) j)) atTop
      (𝓝 (entAbs w (towerL w f L j))) := by
  have hpt : ∀ x, Tendsto (fun n => towerL w f (Ln n) j x) atTop
      (𝓝 (towerL w f L j x)) := by
    intro x
    have h1 := pointwise_of_wnorm_tendsto hw
      (gn := fun n x => towerL w f (Ln n) j x - towerL w f L j x)
      (cutoff_transport_tendsto hw f hconv j) x
    exact tendsto_sub_nhds_zero_iff.mp h1
  unfold entAbs
  refine tendsto_finsetSum Finset.univ fun x _ => ?_
  have hpos : 0 < towerL w f L j x :=
    lt_of_lt_of_le hc (towerL_lower_collar hw f hcolL j x)
  have hcont : ContinuousAt (fun t : ℝ => t * Real.log t) (towerL w f L j x) :=
    continuousAt_id.mul (Real.continuousAt_log hpos.ne')
  exact (tendsto_const_nhds.mul (hcont.tendsto.comp (hpt x)))

/-- **(STG.23, entropy increments)** Under a common collar the adjacent
relative-entropy increments converge as well. -/
theorem entRel_increment_tendsto {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) {Ln : ℕ → Ω → ℝ} {L : Ω → ℝ} {c : ℝ}
    (hc : 0 < c) (hcolL : ∀ x, c ≤ L x)
    (hconv : Tendsto (fun n => wnorm w (fun x => Ln n x - L x)) atTop (𝓝 0))
    (j : ℕ) :
    Tendsto (fun n => entRel w (towerL w f (Ln n) (j + 1)) (towerL w f (Ln n) j))
      atTop (𝓝 (entRel w (towerL w f L (j + 1)) (towerL w f L j))) := by
  have h1 := (entropy_stage_tendsto hw f hc hcolL hconv (j + 1)).sub
    (entropy_stage_tendsto hw f hc hcolL hconv j)
  rw [entropy_chain hw hchain L j] at h1
  refine h1.congr fun n => ?_
  exact entropy_chain hw hchain (Ln n) j

omit [Fintype ι] in
/-- **(cofinal limit)** Summable adjacent `L²` defects give a stage-law
limit: there is a terminal density to which the cutoff densities converge in
the weighted norm. -/
theorem summable_defect_limit {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {Ln : ℕ → Ω → ℝ} {d : ℕ → ℝ} (hd : Summable d)
    (hdef : ∀ n, wnorm w (fun x => Ln (n + 1) x - Ln n x) ≤ d n) :
    ∃ Linf : Ω → ℝ,
      Tendsto (fun n => wnorm w (fun x => Ln n x - Linf x)) atTop (𝓝 0) := by
  have hptc : ∀ x : Ω, ∃ l : ℝ, Tendsto (fun n => Ln n x) atTop (𝓝 l) := by
    intro x
    refine cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable
        (fun n => (Real.sqrt (w x))⁻¹ * d n) (fun n => ?_)
        (hd.mul_left (Real.sqrt (w x))⁻¹))
    have h1 : dist (Ln n x) (Ln (n + 1) x) = ‖Ln (n + 1) x - Ln n x‖ := by
      rw [dist_comm, Real.dist_eq, Real.norm_eq_abs]
    rw [h1]
    have hb : ‖Ln (n + 1) x - Ln n x‖
        ≤ (Real.sqrt (w x))⁻¹ * wnorm w (fun y => Ln (n + 1) y - Ln n y) := by
      have h2 : w x * (Ln (n + 1) x - Ln n x) ^ 2
          ≤ wnormSq w fun y => Ln (n + 1) y - Ln n y := by
        unfold wnormSq
        exact Finset.single_le_sum
          (f := fun y => w y * (Ln (n + 1) y - Ln n y) ^ 2)
          (fun y (_ : y ∈ Finset.univ) => mul_nonneg (hw y).le (sq_nonneg _))
          (Finset.mem_univ x)
      have h3 : (Ln (n + 1) x - Ln n x) ^ 2
          ≤ (w x)⁻¹ * wnormSq w fun y => Ln (n + 1) y - Ln n y := by
        rw [le_inv_mul_iff₀ (hw x)]
        exact h2
      calc ‖Ln (n + 1) x - Ln n x‖
          = Real.sqrt ((Ln (n + 1) x - Ln n x) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
        _ ≤ Real.sqrt ((w x)⁻¹ * wnormSq w fun y => Ln (n + 1) y - Ln n y) :=
            Real.sqrt_le_sqrt h3
        _ = (Real.sqrt (w x))⁻¹ * wnorm w (fun y => Ln (n + 1) y - Ln n y) := by
            rw [Real.sqrt_mul (inv_nonneg.mpr (hw x).le), Real.sqrt_inv]
            rfl
    calc ‖Ln (n + 1) x - Ln n x‖
        ≤ (Real.sqrt (w x))⁻¹ * wnorm w (fun y => Ln (n + 1) y - Ln n y) := hb
      _ ≤ (Real.sqrt (w x))⁻¹ * d n := by
          refine mul_le_mul_of_nonneg_left (hdef n)
            (inv_nonneg.mpr (Real.sqrt_nonneg _))
  choose Linf hLinf using hptc
  refine ⟨Linf, ?_⟩
  have hsq : Tendsto (fun n => wnormSq w (fun x => Ln n x - Linf x)) atTop
      (𝓝 0) := by
    have h0 : (0 : ℝ) = ∑ x : Ω, w x * (0 : ℝ) ^ 2 := by
      simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        mul_zero, Finset.sum_const_zero]
    unfold wnormSq
    rw [h0]
    refine tendsto_finsetSum Finset.univ fun x _ => ?_
    have h1 : Tendsto (fun n => Ln n x - Linf x) atTop (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.mpr (hLinf x)
    have h2 : Tendsto (fun n => (Ln n x - Linf x) ^ 2) atTop (𝓝 (0 ^ 2)) :=
      (continuous_pow 2).continuousAt.tendsto.comp h1
    exact tendsto_const_nhds.mul h2
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  unfold wnorm
  rwa [Real.sqrt_zero] at this

omit [Fintype ι] in
/-- **(cofinal uniqueness)** Weighted-norm limits are unique on the
full-support carrier: direct and staged limits agree. -/
theorem wnorm_limit_unique {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {Ln : ℕ → Ω → ℝ}
    {Linf Linf' : Ω → ℝ}
    (h : Tendsto (fun n => wnorm w (fun x => Ln n x - Linf x)) atTop (𝓝 0))
    (h' : Tendsto (fun n => wnorm w (fun x => Ln n x - Linf' x)) atTop (𝓝 0)) :
    Linf = Linf' := by
  funext x
  have h1 := pointwise_of_wnorm_tendsto hw
    (gn := fun n x => Ln n x - Linf x) h x
  have h2 := pointwise_of_wnorm_tendsto hw
    (gn := fun n x => Ln n x - Linf' x) h' x
  have h3 := tendsto_sub_nhds_zero_iff.mp h1
  have h4 := tendsto_sub_nhds_zero_iff.mp h2
  exact tendsto_nhds_unique h3 h4

/-- **(closing clause)** Proposed cutoff-dependent partial products whose
terminal and backward-martingale residuals vanish converge to the canonical
stage `P_j L` at every stage. -/
theorem approx_factors_tendsto {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) {Ln : ℕ → Ω → ℝ} {L : Ω → ℝ} {r : ℕ}
    (hLnr : ∀ n, DetOn (f r) (Ln n))
    (hconv : Tendsto (fun n => wnorm w (fun x => Ln n x - L x)) atTop (𝓝 0))
    (A : ℕ → ℕ → Ω → ℝ)
    (hterm : Tendsto (fun n => wnorm w (fun x => A n r x - Ln n x)) atTop (𝓝 0))
    (hmart : ∀ k, Tendsto (fun n =>
      wnorm w (fun x => A n k x - cexp w (f k) (A n (k + 1)) x)) atTop (𝓝 0))
    {j : ℕ} (hj : j ≤ r) :
    Tendsto (fun n => wnorm w (fun x => A n j x - towerL w f L j x)) atTop
      (𝓝 0) := by
  have hbound : ∀ n, wnorm w (fun x => A n j x - towerL w f L j x)
      ≤ (wnorm w (fun x => A n r x - Ln n x)
          + ∑ k ∈ Finset.Ico j r,
              wnorm w (fun x => A n k x - cexp w (f k) (A n (k + 1)) x))
        + wnorm w (fun x => towerL w f (Ln n) j x - towerL w f L j x) := by
    intro n
    have htri := wnorm_triangle hw (fun x => A n j x)
      (fun x => towerL w f (Ln n) j x) (fun x => towerL w f L j x)
    have hrec := factor_recovery_bound hw hchain (hLnr n) (A n) j hj
    linarith [htri, hrec]
  have hlim : Tendsto (fun n =>
      (wnorm w (fun x => A n r x - Ln n x)
        + ∑ k ∈ Finset.Ico j r,
            wnorm w (fun x => A n k x - cexp w (f k) (A n (k + 1)) x))
      + wnorm w (fun x => towerL w f (Ln n) j x - towerL w f L j x)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n => ∑ k ∈ Finset.Ico j r,
        wnorm w (fun x => A n k x - cexp w (f k) (A n (k + 1)) x)) atTop
        (𝓝 0) := by
      have h0 : (0 : ℝ) = ∑ k ∈ Finset.Ico j r, (0 : ℝ) := by
        rw [Finset.sum_const, smul_zero]
      rw [h0]
      exact tendsto_finsetSum (Finset.Ico j r) fun k _ => hmart k
    have h2 := (hterm.add h1).add (cutoff_transport_tendsto hw f hconv j)
    rwa [add_zero, add_zero] at h2
  exact squeeze_zero (fun n => wnorm_nonneg _ _) hbound hlim

end RecordAudit

end RecordAuditSection

/-! ### `thm:GT-stage-product-interval` — Sharp common-history product interval

Rendering: the two marginal laws live on one uniform carrier of `n` atoms; the
decreasing quantile functions `F↓, G↓` are antitone nonnegative vectors
`a, b : Fin n → ℝ`, and `G↑(u) = G↓(1-u)` is `b ∘ Fin.rev`.  A positive
same-history coupling is a joint law `p` on the product carrier with both
uniform marginals (`IsCoupling`); its product mean is `cmean`.  The sharp
interval (STG.11) is `cmean_le_upper`/`lower_le_cmean` — proved by the finite
layer-cake (Hardy–Littlewood) argument through the overlap functional `ovl` —
with both endpoints attained by the comonotone and countermonotone couplings
(`comonotone_coupling_attains`, `countermonotone_coupling_attains`), and every
intermediate value attained by mixing (`intermediate_attained`).  The residual
(STG.12) is `coupResidual`, and `coupResidual_eq_zero_iff` renders its
exactness: it vanishes precisely when some positive same-history coupling
realizes the claimed product mean.  The closing sentence (vanishing does not
select the physical coupling) is prose and carries no separate claim. -/

section ProdIntervalSection

namespace ProdInterval

variable {n : ℕ}

/-- Extension of a carrier vector to `ℕ` by zero. -/
def ext (a : Fin n → ℝ) : ℕ → ℝ := fun k => if h : k < n then a ⟨k, h⟩ else 0

/-- The layer increments of the extended vector. -/
def lay (a : Fin n → ℝ) : ℕ → ℝ := fun k => ext a k - ext a (k + 1)

/-- The extension of an antitone nonnegative vector is antitone on `ℕ`. -/
theorem ext_antitone {a : Fin n → ℝ} (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i) :
    Antitone (ext a) := by
  intro k l hkl
  unfold ext
  split_ifs with hl hk hk
  · exact ha (by exact_mod_cast hkl)
  · exact absurd (lt_of_le_of_lt hkl hl) hk
  · exact ha0 _
  · exact le_rfl

/-- The layer increments are nonnegative. -/
theorem lay_nonneg {a : Fin n → ℝ} (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i)
    (k : ℕ) : 0 ≤ lay a k :=
  sub_nonneg.mpr (ext_antitone ha ha0 (Nat.le_succ k))

/-- **Layer-cake representation** of an antitone nonnegative vector. -/
theorem layer_repr (a : Fin n → ℝ) (i : Fin n) :
    a i = ∑ k ∈ Finset.range n, if (i : ℕ) ≤ k then lay a k else 0 := by
  have hfilter : (Finset.range n).filter (fun k => (i : ℕ) ≤ k)
      = Finset.Ico (i : ℕ) n := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter, hfilter]
  have htel : ∑ k ∈ Finset.Ico (i : ℕ) n, lay a k
      = (ext a 0 - ext a n) - (ext a 0 - ext a (i : ℕ)) := by
    unfold lay
    rw [Finset.sum_Ico_eq_sub _ (le_of_lt i.2), Finset.sum_range_sub' (ext a),
      Finset.sum_range_sub' (ext a)]
  rw [htel]
  have h1 : ext a n = 0 := by
    unfold ext
    rw [dite_eq_right (lt_irrefl n)]
  have h2 : ext a (i : ℕ) = a i := by
    unfold ext
    rw [dite_eq_left i.2]
  rw [h1, h2]
  ring

/-- The uniform indicator count below a level. -/
theorem count_le (m : ℕ) :
    (∑ i : Fin n, if (i : ℕ) ≤ m then (1 : ℝ) else 0)
      = ((min (m + 1) n : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range fun v => if v ≤ m then (1 : ℝ) else 0,
    Finset.sum_boole]
  have hfilter : (Finset.range n).filter (fun v => v ≤ m)
      = Finset.range (min (m + 1) n) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    omega
  rw [hfilter, Finset.card_range]

/-- The overlap functional of a joint weight against nested corners. -/
def ovl (q : Fin n → Fin n → ℝ) (k l : ℕ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) ≤ k ∧ (j : ℕ) ≤ l then q i j else 0

/-- The overlap of a nonnegative weight is nonnegative. -/
theorem ovl_nonneg {q : Fin n → Fin n → ℝ} (hq : ∀ i j, 0 ≤ q i j) (k l : ℕ) :
    0 ≤ ovl q k l := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with h
  · exact hq i j
  · exact le_rfl

/-- Row splitting of the overlap functional. -/
theorem ovl_row_split (q : Fin n → Fin n → ℝ) (k l : ℕ) :
    ovl q k l = ∑ i : Fin n, if (i : ℕ) ≤ k
      then (∑ j : Fin n, if (j : ℕ) ≤ l then q i j else 0) else 0 := by
  unfold ovl
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hik
  · refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hjl : (j : ℕ) ≤ l
    · rw [ite_eq_left (⟨hik, hjl⟩ : (i : ℕ) ≤ k ∧ (j : ℕ) ≤ l), ite_eq_left hjl]
    · rw [ite_eq_right fun h => hjl h.2, ite_eq_right hjl]
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right fun h => hik h.1]

/-- **Overlap upper bound** through the row marginals. -/
theorem ovl_le_left {q : Fin n → Fin n → ℝ} (hq : ∀ i j, 0 ≤ q i j)
    (hrow : ∀ i, ∑ j, q i j = 1) (k l : ℕ) :
    ovl q k l ≤ ((min (k + 1) n : ℕ) : ℝ) := by
  rw [ovl_row_split, ← count_le k]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with h
  · rw [← hrow i]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with h2
    · exact le_rfl
    · exact hq i j
  · exact le_rfl

/-- **Overlap upper bound** through the column marginals. -/
theorem ovl_le_right {q : Fin n → Fin n → ℝ} (hq : ∀ i j, 0 ≤ q i j)
    (hcol : ∀ j, ∑ i, q i j = 1) (k l : ℕ) :
    ovl q k l ≤ ((min (l + 1) n : ℕ) : ℝ) := by
  have hswap : ovl q k l = ovl (fun j i => q i j) l k := by
    unfold ovl
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : (i : ℕ) ≤ k
    · by_cases h2 : (j : ℕ) ≤ l
      · rw [ite_eq_left (⟨h1, h2⟩ : (i : ℕ) ≤ k ∧ (j : ℕ) ≤ l),
          ite_eq_left (⟨h2, h1⟩ : (j : ℕ) ≤ l ∧ (i : ℕ) ≤ k)]
      · rw [ite_eq_right fun h => h2 h.2, ite_eq_right fun h => h2 h.1]
    · rw [ite_eq_right fun h => h1 h.1, ite_eq_right fun h => h1 h.2]
  rw [hswap]
  exact ovl_le_left (fun j i => hq i j) hcol l k

/-- **Overlap lower bound**: the two-marginal counting floor. -/
theorem ovl_ge {q : Fin n → Fin n → ℝ} (hq : ∀ i j, 0 ≤ q i j)
    (hrow : ∀ i, ∑ j, q i j = 1) (hcol : ∀ j, ∑ i, q i j = 1)
    {k l : ℕ} (hk : k < n) (hl : l < n) :
    ((k : ℝ) + 1) + (((l : ℝ) + 1) - n) ≤ ovl q k l := by
  rw [ovl_row_split]
  have hinner : ∀ i : Fin n, (∑ j : Fin n, if (j : ℕ) ≤ l then q i j else 0)
      = 1 - ∑ j : Fin n, if l < (j : ℕ) then q i j else 0 := by
    intro i
    have hsum : (∑ j : Fin n, if (j : ℕ) ≤ l then q i j else 0)
        + (∑ j : Fin n, if l < (j : ℕ) then q i j else 0) = 1 := by
      rw [← hrow i, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : (j : ℕ) ≤ l
      · rw [ite_eq_left h, ite_eq_right (not_lt.mpr h), add_zero]
      · rw [ite_eq_right h, ite_eq_left (not_le.mp h), zero_add]
    linarith
  have hstep : ∀ i : Fin n,
      (if (i : ℕ) ≤ k then (1 : ℝ) else 0)
        - (∑ j : Fin n, if l < (j : ℕ) then q i j else 0)
      ≤ if (i : ℕ) ≤ k
          then (∑ j : Fin n, if (j : ℕ) ≤ l then q i j else 0) else 0 := by
    intro i
    have hT : 0 ≤ ∑ j : Fin n, if l < (j : ℕ) then q i j else 0 :=
      Finset.sum_nonneg fun j _ => by
        split_ifs with h
        · exact hq i j
        · exact le_rfl
    split_ifs with h
    · rw [hinner i]
    · linarith
  have hsumT : ∑ i : Fin n, ∑ j : Fin n, (if l < (j : ℕ) then q i j else 0)
      = (n : ℝ) - ((l : ℝ) + 1) := by
    rw [Finset.sum_comm]
    have h1 : ∀ j : Fin n, (∑ i : Fin n, if l < (j : ℕ) then q i j else 0)
        = if l < (j : ℕ) then (1 : ℝ) else 0 := by
      intro j
      by_cases h : l < (j : ℕ)
      · rw [ite_eq_left h]
        rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
          (ite_eq_left h : (if l < (j : ℕ) then q i j else 0) = q i j)]
        exact hcol j
      · rw [ite_eq_right h]
        exact Finset.sum_eq_zero fun i _ => ite_eq_right h
    rw [Finset.sum_congr rfl fun j _ => h1 j]
    have h2 : ∀ j : Fin n, (if l < (j : ℕ) then (1 : ℝ) else 0)
        = 1 - if (j : ℕ) ≤ l then (1 : ℝ) else 0 := by
      intro j
      by_cases h : (j : ℕ) ≤ l
      · rw [ite_eq_right (not_lt.mpr h), ite_eq_left h, sub_self]
      · rw [ite_eq_left (not_le.mp h), ite_eq_right h, sub_zero]
    rw [Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_sub_distrib, count_le,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hmin : min (l + 1) n = l + 1 := by omega
    rw [hmin]
    push_cast
    ring
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hstep i
  rw [Finset.sum_sub_distrib, count_le, hsumT] at hsum
  have hmin : min (k + 1) n = k + 1 := by omega
  rw [hmin] at hsum
  push_cast at hsum
  linarith

/-- **Layer-cake expansion** of a joint pairing against two antitone
nonnegative vectors, through the overlap functional. -/
theorem pairing_expand (q : Fin n → Fin n → ℝ) (a b : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, q i j * (a i * b j))
      = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          (lay a k * lay b l) * ovl q k l := by
  have hterm : ∀ i j, q i j * (a i * b j)
      = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          (lay a k * lay b l)
            * (if (i : ℕ) ≤ k ∧ (j : ℕ) ≤ l then q i j else 0) := by
    intro i j
    rw [layer_repr a i, layer_repr b j]
    rw [Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h1 : (i : ℕ) ≤ k
    · by_cases h2 : (j : ℕ) ≤ l
      · rw [ite_eq_left h1, ite_eq_left h2,
          ite_eq_left (⟨h1, h2⟩ : (i : ℕ) ≤ k ∧ (j : ℕ) ≤ l)]
        ring
      · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right fun h => h2 h.2]
        ring
    · rw [ite_eq_right h1,
        ite_eq_right (show ¬((i : ℕ) ≤ k ∧ (j : ℕ) ≤ l) from fun h => h1 h.1)]
      ring
  calc ∑ i : Fin n, ∑ j : Fin n, q i j * (a i * b j)
      = ∑ i : Fin n, ∑ j : Fin n, ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          (lay a k * lay b l)
            * (if (i : ℕ) ≤ k ∧ (j : ℕ) ≤ l then q i j else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
    _ = ∑ i : Fin n, ∑ k ∈ Finset.range n, ∑ j : Fin n, ∑ l ∈ Finset.range n,
          (lay a k * lay b l)
            * (if (i : ℕ) ≤ k ∧ (j : ℕ) ≤ l then q i j else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k ∈ Finset.range n, ∑ i : Fin n, ∑ j : Fin n, ∑ l ∈ Finset.range n,
          (lay a k * lay b l)
            * (if (i : ℕ) ≤ k ∧ (j : ℕ) ≤ l then q i j else 0) :=
        Finset.sum_comm
    _ = ∑ k ∈ Finset.range n, ∑ i : Fin n, ∑ l ∈ Finset.range n, ∑ j : Fin n,
          (lay a k * lay b l)
            * (if (i : ℕ) ≤ k ∧ (j : ℕ) ≤ l then q i j else 0) :=
        Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, ∑ i : Fin n, ∑ j : Fin n,
          (lay a k * lay b l)
            * (if (i : ℕ) ≤ k ∧ (j : ℕ) ≤ l then q i j else 0) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          (lay a k * lay b l) * ovl q k l := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        unfold ovl
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]

/-- The comonotone (diagonal) unit-marginal weight. -/
def diagW : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0

/-- The countermonotone (antidiagonal) unit-marginal weight. -/
def antidiagW : Fin n → Fin n → ℝ := fun i j => if j = Fin.rev i then 1 else 0

/-- The diagonal weight is nonnegative. -/
theorem diagW_nonneg (i j : Fin n) : 0 ≤ diagW i j := by
  unfold diagW
  split_ifs
  · norm_num
  · exact le_rfl

/-- The antidiagonal weight is nonnegative. -/
theorem antidiagW_nonneg (i j : Fin n) : 0 ≤ antidiagW i j := by
  unfold antidiagW
  split_ifs
  · norm_num
  · exact le_rfl

/-- The diagonal pairing collapses to the comonotone sum. -/
theorem diagW_pairing (a b : Fin n → ℝ) :
    (∑ i, ∑ j, diagW i j * (a i * b j)) = ∑ i, a i * b i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold diagW
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl, one_mul]
  · intro j _ hj
    rw [ite_eq_right fun h => hj h.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The antidiagonal pairing collapses to the countermonotone sum. -/
theorem antidiagW_pairing (a b : Fin n → ℝ) :
    (∑ i, ∑ j, antidiagW i j * (a i * b j)) = ∑ i, a i * b (Fin.rev i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold antidiagW
  rw [Finset.sum_eq_single (Fin.rev i)]
  · rw [ite_eq_left rfl, one_mul]
  · intro j _ hj
    rw [ite_eq_right hj, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (Fin.rev i)) h

/-- The diagonal weight has unit row sums. -/
theorem diagW_row (i : Fin n) : ∑ j, diagW i j = 1 := by
  unfold diagW
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl]
  · intro j _ hj
    rw [ite_eq_right fun h => hj h.symm]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The diagonal weight has unit column sums. -/
theorem diagW_col (j : Fin n) : ∑ i, diagW i j = 1 := by
  unfold diagW
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl]
  · intro i _ hi
    rw [ite_eq_right hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The antidiagonal weight has unit row sums. -/
theorem antidiagW_row (i : Fin n) : ∑ j, antidiagW i j = 1 := by
  unfold antidiagW
  rw [Finset.sum_eq_single (Fin.rev i)]
  · rw [ite_eq_left rfl]
  · intro j _ hj
    rw [ite_eq_right hj]
  · intro h
    exact absurd (Finset.mem_univ (Fin.rev i)) h

/-- The antidiagonal weight has unit column sums. -/
theorem antidiagW_col (j : Fin n) : ∑ i, antidiagW i j = 1 := by
  unfold antidiagW
  rw [Finset.sum_eq_single (Fin.rev j)]
  · rw [ite_eq_left (by rw [Fin.rev_rev])]
  · intro i _ hi
    rw [ite_eq_right fun h => hi (by rw [h, Fin.rev_rev])]
  · intro h
    exact absurd (Finset.mem_univ (Fin.rev j)) h

/-- **Core rearrangement upper bound**: any doubly stochastic pairing of two
antitone nonnegative vectors is dominated by the comonotone pairing. -/
theorem pairing_le_comonotone {q : Fin n → Fin n → ℝ} (hq : ∀ i j, 0 ≤ q i j)
    (hrow : ∀ i, ∑ j, q i j = 1) (hcol : ∀ j, ∑ i, q i j = 1)
    {a b : Fin n → ℝ} (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i)
    (hb : Antitone b) (hb0 : ∀ i, 0 ≤ b i) :
    (∑ i, ∑ j, q i j * (a i * b j)) ≤ ∑ i, a i * b i := by
  rw [← diagW_pairing a b, pairing_expand q a b, pairing_expand diagW a b]
  refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (lay_nonneg ha ha0 k) (lay_nonneg hb hb0 l))
  -- `ovl q ≤ min(k+1, l+1) = ovl diagW`
  have h1 := ovl_le_left hq hrow k l
  have h2 := ovl_le_right hq hcol k l
  have hdiag : ovl (diagW (n := n)) k l
      = ((min (min k l + 1) n : ℕ) : ℝ) := by
    rw [ovl_row_split, ← count_le (min k l)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hin : (∑ j : Fin n, if (j : ℕ) ≤ l then diagW i j else 0)
        = if (i : ℕ) ≤ l then (1 : ℝ) else 0 := by
      unfold diagW
      rw [Finset.sum_eq_single i]
      · by_cases hil : (i : ℕ) ≤ l
        · rw [ite_eq_left hil, ite_eq_left (rfl : i = i), ite_eq_left hil]
        · rw [ite_eq_right hil, ite_eq_right hil]
      · intro j _ hj
        by_cases hjl : (j : ℕ) ≤ l
        · rw [ite_eq_left hjl, ite_eq_right fun h => hj h.symm]
        · rw [ite_eq_right hjl]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hin]
    by_cases h1' : (i : ℕ) ≤ k
    · by_cases h2' : (i : ℕ) ≤ l
      · rw [ite_eq_left h1', ite_eq_left h2', ite_eq_left (le_min h1' h2')]
      · rw [ite_eq_left h1', ite_eq_right h2',
          ite_eq_right fun h => h2' (le_trans h (min_le_right k l))]
    · rw [ite_eq_right h1',
        ite_eq_right fun h => h1' (le_trans h (min_le_left k l))]
  rw [hdiag]
  have hminlt : min (min k l + 1) n = min k l + 1 := by
    rw [Finset.mem_range] at hk hl
    omega
  rw [hminlt]
  rw [Finset.mem_range] at hk hl
  rcases le_total k l with hkl | hkl
  · have : min k l = k := min_eq_left hkl
    rw [this]
    calc ovl q k l ≤ ((min (k + 1) n : ℕ) : ℝ) := h1
      _ = ((k + 1 : ℕ) : ℝ) := by rw [show min (k + 1) n = k + 1 by omega]
      _ = _ := by push_cast; ring
  · have : min k l = l := min_eq_right hkl
    rw [this]
    calc ovl q k l ≤ ((min (l + 1) n : ℕ) : ℝ) := h2
      _ = ((l + 1 : ℕ) : ℝ) := by rw [show min (l + 1) n = l + 1 by omega]
      _ = _ := by push_cast; ring

/-- **Core rearrangement lower bound**: any doubly stochastic pairing of two
antitone nonnegative vectors dominates the countermonotone pairing. -/
theorem countermonotone_le_pairing {q : Fin n → Fin n → ℝ} (hq : ∀ i j, 0 ≤ q i j)
    (hrow : ∀ i, ∑ j, q i j = 1) (hcol : ∀ j, ∑ i, q i j = 1)
    {a b : Fin n → ℝ} (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i)
    (hb : Antitone b) (hb0 : ∀ i, 0 ≤ b i) :
    (∑ i, a i * b (Fin.rev i)) ≤ ∑ i, ∑ j, q i j * (a i * b j) := by
  rw [← antidiagW_pairing a b, pairing_expand q a b, pairing_expand antidiagW a b]
  refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (lay_nonneg ha ha0 k) (lay_nonneg hb hb0 l))
  rw [Finset.mem_range] at hk hl
  -- `ovl antidiagW = (k+1) + (l+1) - n` truncated at zero, `≤ ovl q`
  have hanti : ovl (antidiagW (n := n)) k l
      = ((k + 1 - (n - 1 - l) : ℕ) : ℝ) := by
    rw [ovl_row_split]
    have hin : ∀ i : Fin n, (∑ j : Fin n, if (j : ℕ) ≤ l then antidiagW i j else 0)
        = if n - 1 - l ≤ (i : ℕ) then (1 : ℝ) else 0 := by
      intro i
      unfold antidiagW
      rw [Finset.sum_eq_single (Fin.rev i)]
      · rw [ite_eq_left rfl]
        have hrev : (Fin.rev i : ℕ) = n - ((i : ℕ) + 1) := Fin.val_rev i
        by_cases h : (Fin.rev i : ℕ) ≤ l
        · rw [ite_eq_left h, ite_eq_left (by omega : n - 1 - l ≤ (i : ℕ))]
        · rw [ite_eq_right h, ite_eq_right (by
            rw [hrev] at h
            have := i.2
            omega)]
      · intro j _ hj
        by_cases hjl : (j : ℕ) ≤ l
        · rw [ite_eq_left hjl, ite_eq_right hj]
        · rw [ite_eq_right hjl]
      · intro h
        exact absurd (Finset.mem_univ (Fin.rev i)) h
    rw [Finset.sum_congr rfl fun i _ => by rw [hin i]]
    have hcomb : ∀ i : Fin n,
        (if (i : ℕ) ≤ k then (if n - 1 - l ≤ (i : ℕ) then (1 : ℝ) else 0) else 0)
          = if n - 1 - l ≤ (i : ℕ) ∧ (i : ℕ) ≤ k then (1 : ℝ) else 0 := by
      intro i
      by_cases h1' : (i : ℕ) ≤ k
      · by_cases h2' : n - 1 - l ≤ (i : ℕ)
        · rw [ite_eq_left h1', ite_eq_left h2',
            ite_eq_left (⟨h2', h1'⟩ : n - 1 - l ≤ (i : ℕ) ∧ (i : ℕ) ≤ k)]
        · rw [ite_eq_left h1', ite_eq_right h2', ite_eq_right fun h => h2' h.1]
      · rw [ite_eq_right h1', ite_eq_right fun h => h1' h.2]
    rw [Finset.sum_congr rfl fun i _ => hcomb i,
      Fin.sum_univ_eq_sum_range fun v =>
        if n - 1 - l ≤ v ∧ v ≤ k then (1 : ℝ) else 0,
      Finset.sum_boole]
    have hfilter : (Finset.range n).filter (fun v => n - 1 - l ≤ v ∧ v ≤ k)
        = Finset.Icc (n - 1 - l) (min k (n - 1)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, le_min_iff]
      omega
    rw [hfilter, Nat.card_Icc]
    congr 1
    omega
  rw [hanti]
  by_cases hz : k + 1 ≤ n - 1 - l
  · have h0 : (k + 1 - (n - 1 - l) : ℕ) = 0 := by omega
    rw [h0]
    exact_mod_cast ovl_nonneg hq k l
  · have hval : ((k + 1 - (n - 1 - l) : ℕ) : ℝ)
        = ((k : ℝ) + 1) + (((l : ℝ) + 1) - n) := by
      have : (k + 1 - (n - 1 - l) : ℕ) = k + 1 + (l + 1) - n := by omega
      rw [this]
      push_cast [show n ≤ k + 1 + (l + 1) by omega]
      ring
    rw [hval]
    exact ovl_ge hq hrow hcol hk hl

/-- A positive same-history coupling of the two uniform marginals. -/
def IsCoupling (p : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ p i j) ∧ (∀ i, ∑ j, p i j = (n : ℝ)⁻¹)
    ∧ ∀ j, ∑ i, p i j = (n : ℝ)⁻¹

/-- The product mean of a coupling. -/
def cmean (p : Fin n → Fin n → ℝ) (a b : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, p i j * (a i * b j)

/-- The comonotone endpoint `U_{F,G} = ∫ F↓G↓` on the uniform carrier. -/
noncomputable def upperInt (a b : Fin n → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ i, a i * b i

/-- The countermonotone endpoint `L_{F,G} = ∫ F↓G↑` on the uniform carrier. -/
noncomputable def lowerInt (a b : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, a i * b (Fin.rev i)

/-- Couplings rescale to doubly stochastic weights. -/
theorem coupling_scaled {p : Fin n → Fin n → ℝ} (hn : 0 < n)
    (hp : IsCoupling p) :
    (∀ i j, 0 ≤ (n : ℝ) * p i j) ∧ (∀ i, ∑ j, (n : ℝ) * p i j = 1)
      ∧ ∀ j, ∑ i, (n : ℝ) * p i j = 1 := by
  have hne : (n : ℝ) ≠ 0 := by positivity
  refine ⟨fun i j => mul_nonneg (by positivity) (hp.1 i j), fun i => ?_,
    fun j => ?_⟩
  · rw [← Finset.mul_sum, hp.2.1 i, mul_inv_cancel₀ hne]
  · rw [← Finset.mul_sum, hp.2.2 j, mul_inv_cancel₀ hne]

/-- The product mean through the rescaled weight. -/
theorem cmean_scaled {p : Fin n → Fin n → ℝ} (hn : 0 < n) (a b : Fin n → ℝ) :
    cmean p a b = (n : ℝ)⁻¹ * ∑ i, ∑ j, ((n : ℝ) * p i j) * (a i * b j) := by
  have hne : (n : ℝ) ≠ 0 := by positivity
  unfold cmean
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- **(STG.11, upper bound)** Every positive same-history coupling has product
mean at most the comonotone endpoint. -/
theorem cmean_le_upper {p : Fin n → Fin n → ℝ} (hn : 0 < n) (hp : IsCoupling p)
    {a b : Fin n → ℝ} (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i)
    (hb : Antitone b) (hb0 : ∀ i, 0 ≤ b i) :
    cmean p a b ≤ upperInt a b := by
  obtain ⟨hq, hrow, hcol⟩ := coupling_scaled hn hp
  rw [cmean_scaled hn a b]
  unfold upperInt
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pairing_le_comonotone hq hrow hcol ha ha0 hb hb0

/-- **(STG.11, lower bound)** Every positive same-history coupling has product
mean at least the countermonotone endpoint. -/
theorem lower_le_cmean {p : Fin n → Fin n → ℝ} (hn : 0 < n) (hp : IsCoupling p)
    {a b : Fin n → ℝ} (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i)
    (hb : Antitone b) (hb0 : ∀ i, 0 ≤ b i) :
    lowerInt a b ≤ cmean p a b := by
  obtain ⟨hq, hrow, hcol⟩ := coupling_scaled hn hp
  rw [cmean_scaled hn a b]
  unfold lowerInt
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact countermonotone_le_pairing hq hrow hcol ha ha0 hb hb0

/-- **(STG.11, comonotone attainment)** The comonotone coupling is a positive
same-history coupling attaining the upper endpoint. -/
theorem comonotone_coupling_attains (hn : 0 < n) (a b : Fin n → ℝ) :
    IsCoupling (fun i j : Fin n => (n : ℝ)⁻¹ * diagW i j)
      ∧ cmean (fun i j : Fin n => (n : ℝ)⁻¹ * diagW i j) a b = upperInt a b := by
  have hd0 : ∀ i j, (0 : ℝ) ≤ diagW (n := n) i j := fun i j => by
    unfold diagW
    split_ifs
    · norm_num
    · exact le_rfl
  refine ⟨⟨fun i j => mul_nonneg (by positivity) (hd0 i j), fun i => ?_,
    fun j => ?_⟩, ?_⟩
  · rw [← Finset.mul_sum, diagW_row, mul_one]
  · rw [← Finset.mul_sum, diagW_col, mul_one]
  · unfold cmean upperInt
    rw [← diagW_pairing a b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **(STG.11, countermonotone attainment)** The countermonotone coupling is a
positive same-history coupling attaining the lower endpoint. -/
theorem countermonotone_coupling_attains (hn : 0 < n) (a b : Fin n → ℝ) :
    IsCoupling (fun i j : Fin n => (n : ℝ)⁻¹ * antidiagW i j)
      ∧ cmean (fun i j : Fin n => (n : ℝ)⁻¹ * antidiagW i j) a b = lowerInt a b := by
  have hd0 : ∀ i j, (0 : ℝ) ≤ antidiagW (n := n) i j := fun i j => by
    unfold antidiagW
    split_ifs
    · norm_num
    · exact le_rfl
  refine ⟨⟨fun i j => mul_nonneg (by positivity) (hd0 i j), fun i => ?_,
    fun j => ?_⟩, ?_⟩
  · rw [← Finset.mul_sum, antidiagW_row, mul_one]
  · rw [← Finset.mul_sum, antidiagW_col, mul_one]
  · unfold cmean lowerInt
    rw [← antidiagW_pairing a b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **(sharpness)** Every value in the closed interval is the product mean of
some positive same-history coupling: convex mixing of the two extremes. -/
theorem intermediate_attained (hn : 0 < n) {a b : Fin n → ℝ}
    {z : ℝ} (hz1 : lowerInt a b ≤ z) (hz2 : z ≤ upperInt a b) :
    ∃ p : Fin n → Fin n → ℝ, IsCoupling p ∧ cmean p a b = z := by
  obtain ⟨hcl, hvl⟩ := countermonotone_coupling_attains hn a b
  obtain ⟨hcu, hvu⟩ := comonotone_coupling_attains hn a b
  by_cases hLU : upperInt a b = lowerInt a b
  · refine ⟨_, hcl, ?_⟩
    rw [hvl]
    linarith [hz1, hz2, hLU.le, hLU.ge]
  · have hlt : lowerInt a b < upperInt a b :=
      lt_of_le_of_ne (le_trans hz1 hz2) (Ne.symm hLU)
    set t : ℝ := (z - lowerInt a b) / (upperInt a b - lowerInt a b) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one (by linarith)]
      linarith
    refine ⟨fun i j : Fin n => (1 - t) * ((n : ℝ)⁻¹ * antidiagW i j)
      + t * ((n : ℝ)⁻¹ * diagW i j), ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩,
      ?_⟩
    · have h1 := antidiagW_nonneg i j
      have h2 := diagW_nonneg i j
      have hn0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      exact add_nonneg
        (mul_nonneg (by linarith) (mul_nonneg hn0 h1))
        (mul_nonneg ht0 (mul_nonneg hn0 h2))
    · calc ∑ j, ((1 - t) * ((n : ℝ)⁻¹ * antidiagW i j)
            + t * ((n : ℝ)⁻¹ * diagW i j))
          = ((1 - t) * (n : ℝ)⁻¹) * (∑ j, antidiagW i j)
            + (t * (n : ℝ)⁻¹) * ∑ j, diagW i j := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = (n : ℝ)⁻¹ := by rw [antidiagW_row, diagW_row]; ring
    · calc ∑ i, ((1 - t) * ((n : ℝ)⁻¹ * antidiagW i j)
            + t * ((n : ℝ)⁻¹ * diagW i j))
          = ((1 - t) * (n : ℝ)⁻¹) * (∑ i, antidiagW i j)
            + (t * (n : ℝ)⁻¹) * ∑ i, diagW i j := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = (n : ℝ)⁻¹ := by rw [antidiagW_col, diagW_col]; ring
    · unfold cmean at hvl hvu ⊢
      have hexp : ∀ i j, ((1 - t) * ((n : ℝ)⁻¹ * antidiagW i j)
            + t * ((n : ℝ)⁻¹ * diagW i j)) * (a i * b j)
          = (1 - t) * ((n : ℝ)⁻¹ * antidiagW i j * (a i * b j))
            + t * ((n : ℝ)⁻¹ * diagW i j * (a i * b j)) := fun i j => by ring
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        hexp i j]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib,
        Finset.sum_add_distrib]
      rw [show (∑ i, ∑ j, (1 - t) * ((n : ℝ)⁻¹ * antidiagW i j * (a i * b j)))
          = (1 - t) * ∑ i, ∑ j, (n : ℝ)⁻¹ * antidiagW i j * (a i * b j) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]]
      rw [show (∑ i, ∑ j, t * ((n : ℝ)⁻¹ * diagW i j * (a i * b j)))
          = t * ∑ i, ∑ j, (n : ℝ)⁻¹ * diagW i j * (a i * b j) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]]
      rw [show (∑ i, ∑ j, (n : ℝ)⁻¹ * antidiagW i j * (a i * b j))
          = lowerInt a b from by rw [← hvl]]
      rw [show (∑ i, ∑ j, (n : ℝ)⁻¹ * diagW i j * (a i * b j))
          = upperInt a b from by rw [← hvu]]
      rw [ht]
      field_simp
      ring

/-- The exact no-common-history residual (STG.12). -/
noncomputable def coupResidual (a b : Fin n → ℝ) (z : ℝ) : ℝ :=
  max (lowerInt a b - z) 0 + max (z - upperInt a b) 0

/-- **(STG.12)** The residual vanishes exactly when some positive same-history
coupling realizes the claimed product mean. -/
theorem coupResidual_eq_zero_iff (hn : 0 < n) {a b : Fin n → ℝ}
    (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i) (hb : Antitone b)
    (hb0 : ∀ i, 0 ≤ b i) (z : ℝ) :
    coupResidual a b z = 0
      ↔ ∃ p : Fin n → Fin n → ℝ, IsCoupling p ∧ cmean p a b = z := by
  unfold coupResidual
  constructor
  · intro h
    have h1 : max (lowerInt a b - z) 0 = 0 ∧ max (z - upperInt a b) 0 = 0 := by
      constructor <;> [skip; skip] <;>
        (first
          | exact le_antisymm (by
              have := le_max_right (z - upperInt a b) 0
              have := le_max_right (lowerInt a b - z) 0
              linarith [le_max_right (lowerInt a b - z) 0,
                le_max_right (z - upperInt a b) 0]) (le_max_right _ _))
    obtain ⟨hl, hu⟩ := h1
    have hz1 : lowerInt a b ≤ z := by
      have := max_eq_right_iff.mp hl
      linarith [sub_nonpos.mp (max_eq_right_iff.mp hl)]
    have hz2 : z ≤ upperInt a b := by
      linarith [sub_nonpos.mp (max_eq_right_iff.mp hu)]
    exact intermediate_attained hn hz1 hz2
  · rintro ⟨p, hp, hmean⟩
    have h1 : lowerInt a b ≤ z := hmean ▸ lower_le_cmean hn hp ha ha0 hb hb0
    have h2 : z ≤ upperInt a b := hmean ▸ cmean_le_upper hn hp ha ha0 hb hb0
    rw [max_eq_right (by linarith), max_eq_right (by linarith), add_zero]

end ProdInterval

end ProdIntervalSection

/-! ### `thm:GT-projective-head-replay` — Source action and positive replay

Rendering: the final-irreducible response map (ML.13) is
`𝓛 = Q_irr 𝓡 = (1-Π_H)𝓡`, acting pointwise on the finite weighted carrier;
`C = 𝓛𝓛ᴴ` is its (weight-independent) block Gram and `q = 𝓛𝒟` its action on
the martingale increment.  The weighted Hilbert–Schmidt norm is
`∑_x w x · ‖H x‖²_HS`.  `minNorm_isLeast` is the exact finite Moore–Penrose
min-norm identity behind (ML.14); `replay_action_isLeast` states the boxed
(ML.14) for the actual increments: `d^bi = Tr(qᴴ C† q)` is the attained
minimum of the weighted HS action over all `H` with `𝓛H = q`.  (ML.15) is
`replay_action_nonneg`, `replay_action_le_trace`, the summed form
`replay_action_sum_le`, and `replay_action_of_irr_zero` (`G^irr = 0 ⟹
d^bi = 0`).  The estimator clauses (ML.16–ML.18b) follow in the next two
sections. -/

section HeadReplaySection

namespace HeadReplay

open MgtFilt ProjHead

variable {Yt S E : Type*} [Fintype Yt] [Fintype S] [Fintype E] [DecidableEq Yt]

/-- The squared Hilbert–Schmidt (Frobenius) norm of a complex matrix. -/
noncomputable def frobSq {m p : Type*} [Fintype m] [Fintype p]
    (A : Matrix m p ℂ) : ℝ := (Matrix.trace (Aᴴ * A)).re

/-- The real Hilbert–Schmidt pairing of two complex matrices. -/
noncomputable def frobInner {m p : Type*} [Fintype m] [Fintype p]
    (A B : Matrix m p ℂ) : ℝ := (Matrix.trace (Aᴴ * B)).re

/-- The squared HS norm as a sum of squared entry norms. -/
theorem frobSq_eq_sum {m p : Type*} [Fintype m] [Fintype p] (A : Matrix m p ℂ) :
    frobSq A = ∑ i, ∑ j, ‖A j i‖ ^ 2 := by
  unfold frobSq
  rw [Matrix.trace]
  rw [show (∑ i, (Aᴴ * A).diag i) = ∑ i, ((∑ j, ((‖A j i‖ : ℝ) : ℂ) ^ 2 : ℂ))
      from Finset.sum_congr rfl fun i _ => ?_]
  · rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (((‖A j i‖ : ℝ) : ℂ)) ^ 2 = ((‖A j i‖ ^ 2 : ℝ) : ℂ) from by
      push_cast; ring, Complex.ofReal_re]
  · rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']

/-- The squared HS norm is nonnegative. -/
theorem frobSq_nonneg {m p : Type*} [Fintype m] [Fintype p] (A : Matrix m p ℂ) :
    0 ≤ frobSq A := by
  rw [frobSq_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The HS pairing is symmetric. -/
theorem frobInner_symm {m p : Type*} [Fintype m] [Fintype p]
    (A B : Matrix m p ℂ) : frobInner B A = frobInner A B := by
  unfold frobInner
  rw [show Bᴴ * A = (Aᴴ * B)ᴴ from by
    rw [conjTranspose_mul, conjTranspose_conjTranspose],
    Matrix.trace_conjTranspose]
  exact Complex.conj_re _

/-- HS expansion of a sum. -/
theorem frobSq_add {m p : Type*} [Fintype m] [Fintype p] (A B : Matrix m p ℂ) :
    frobSq (A + B) = frobSq A + frobSq B + 2 * frobInner A B := by
  unfold frobSq frobInner
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
  simp only [Complex.add_re]
  have hsymm : (Matrix.trace (Bᴴ * A)).re = (Matrix.trace (Aᴴ * B)).re :=
    frobInner_symm A B
  linarith [hsymm]

/-- The trace of a PSD matrix has nonnegative real part. -/
theorem psd_trace_re_nonneg {m : Type*} [Fintype m] {A : Matrix m m ℂ}
    (hA : A.PosSemidef) : 0 ≤ (Matrix.trace A).re := by
  have h := hA.trace_nonneg
  have h2 := (Complex.le_def.mp h).1
  rwa [Complex.zero_re] at h2

/-- The pseudoinverse (min-norm) solution `H_* = 𝓛ᴴ C† 𝓛D₀` of the
final-response equation. -/
noncomputable def minNormSol (Lm : Matrix Yt S ℂ) (D0 : Matrix S E ℂ) :
    Matrix S E ℂ :=
  Lmᴴ * pinv (Matrix.posSemidef_self_mul_conjTranspose Lm).1 * (Lm * D0)

/-- The support of the row Gram absorbs on the left of `𝓛`. -/
theorem supportProj_row_gram_mul (Lm : Matrix Yt S ℂ) :
    supportProj (Matrix.posSemidef_self_mul_conjTranspose Lm).1 * Lm = Lm := by
  have h2 : supportProj (posSemidef_conjTranspose_mul_self Lmᴴ).1
      = supportProj (Matrix.posSemidef_self_mul_conjTranspose Lm).1 :=
    mgt_supportProj_congr (by rw [conjTranspose_conjTranspose]) _ _
  have h1 := supportProj_gram_mul Lmᴴ
  rw [h2] at h1
  rwa [conjTranspose_conjTranspose] at h1

omit [Fintype E] in
/-- The min-norm solution is feasible: `𝓛 H_* = 𝓛 D₀`. -/
theorem minNormSol_feasible (Lm : Matrix Yt S ℂ) (D0 : Matrix S E ℂ) :
    Lm * minNormSol Lm D0 = Lm * D0 := by
  unfold minNormSol
  set hC := (Matrix.posSemidef_self_mul_conjTranspose Lm).1 with hhC
  calc Lm * (Lmᴴ * pinv hC * (Lm * D0))
      = Lm * Lmᴴ * pinv hC * (Lm * D0) := by simp only [Matrix.mul_assoc]
    _ = supportProj hC * (Lm * D0) := by rw [mul_pinv_eq_supportProj]
    _ = supportProj hC * Lm * D0 := by rw [Matrix.mul_assoc]
    _ = Lm * D0 := by rw [supportProj_row_gram_mul]

/-- The HS action of the min-norm solution is exactly `Tr(qᴴ C† q)`. -/
theorem minNormSol_frobSq (Lm : Matrix Yt S ℂ) (D0 : Matrix S E ℂ) :
    frobSq (minNormSol Lm D0)
      = (Matrix.trace ((Lm * D0)ᴴ
          * pinv (Matrix.posSemidef_self_mul_conjTranspose Lm).1
          * (Lm * D0))).re := by
  unfold frobSq minNormSol
  set hC := (Matrix.posSemidef_self_mul_conjTranspose Lm).1 with hhC
  congr 2
  calc (Lmᴴ * pinv hC * (Lm * D0))ᴴ * (Lmᴴ * pinv hC * (Lm * D0))
      = (Lm * D0)ᴴ * (pinv hC)ᴴ * Lmᴴᴴ * (Lmᴴ * pinv hC * (Lm * D0)) := by
        rw [conjTranspose_mul (Lmᴴ * pinv hC) (Lm * D0),
          conjTranspose_mul Lmᴴ (pinv hC)]
        simp only [Matrix.mul_assoc]
    _ = (Lm * D0)ᴴ * (pinv hC * (Lm * Lmᴴ) * pinv hC) * (Lm * D0) := by
        rw [(pinv_isHermitian hC).eq, conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc]
    _ = (Lm * D0)ᴴ * pinv hC * (Lm * D0) := by
        rw [pinv_mul_self_mul_pinv]

/-- **(ML.14, optimality)** Every feasible `H` has HS action at least
`Tr(qᴴ C† q)`. -/
theorem minNorm_le (Lm : Matrix Yt S ℂ) (D0 Hm : Matrix S E ℂ)
    (hfeas : Lm * Hm = Lm * D0) :
    (Matrix.trace ((Lm * D0)ᴴ
        * pinv (Matrix.posSemidef_self_mul_conjTranspose Lm).1
        * (Lm * D0))).re ≤ frobSq Hm := by
  set hC := (Matrix.posSemidef_self_mul_conjTranspose Lm).1 with hhC
  have hcross : frobInner (minNormSol Lm D0) (Hm - minNormSol Lm D0) = 0 := by
    unfold frobInner
    have hLdiff : Lm * (Hm - minNormSol Lm D0) = 0 := by
      rw [Matrix.mul_sub, hfeas, minNormSol_feasible, sub_self]
    calc (Matrix.trace ((minNormSol Lm D0)ᴴ * (Hm - minNormSol Lm D0))).re
        = (Matrix.trace ((Lm * D0)ᴴ * (pinv hC)ᴴ
            * (Lm * (Hm - minNormSol Lm D0)))).re := by
          rw [show (minNormSol Lm D0)ᴴ
              = (Lm * D0)ᴴ * ((pinv hC)ᴴ * Lmᴴᴴ) from by
            unfold minNormSol
            rw [conjTranspose_mul (Lmᴴ * pinv hC) (Lm * D0),
              conjTranspose_mul Lmᴴ (pinv hC)]]
          rw [conjTranspose_conjTranspose]
          congr 2
          simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [hLdiff, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  calc (Matrix.trace ((Lm * D0)ᴴ * pinv hC * (Lm * D0))).re
      = frobSq (minNormSol Lm D0) := (minNormSol_frobSq Lm D0).symm
    _ ≤ frobSq (minNormSol Lm D0) + frobSq (Hm - minNormSol Lm D0) := by
        linarith [frobSq_nonneg (Hm - minNormSol Lm D0)]
    _ = frobSq Hm := by
        have h := frobSq_add (minNormSol Lm D0) (Hm - minNormSol Lm D0)
        rw [hcross, show minNormSol Lm D0 + (Hm - minNormSol Lm D0) = Hm from by
          abel] at h
        linarith [h]

/-- **(ML.14, single event)** The exact finite Moore–Penrose min-norm
identity: `Tr(qᴴ C† q)` is the least HS action of any solution of
`𝓛H = 𝓛D₀`. -/
theorem minNorm_isLeast (Lm : Matrix Yt S ℂ) (D0 : Matrix S E ℂ) :
    IsLeast {r : ℝ | ∃ Hm : Matrix S E ℂ, Lm * Hm = Lm * D0 ∧ r = frobSq Hm}
      ((Matrix.trace ((Lm * D0)ᴴ
        * pinv (Matrix.posSemidef_self_mul_conjTranspose Lm).1
        * (Lm * D0))).re) := by
  constructor
  · exact ⟨minNormSol Lm D0, minNormSol_feasible Lm D0,
      (minNormSol_frobSq Lm D0).symm⟩
  · rintro r ⟨Hm, hfeas, rfl⟩
    exact minNorm_le Lm D0 Hm hfeas

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The source-minimal action of the final irreducible response (ML.14):
`d^bi = ∑_x w x · Tr(q(x)ᴴ C† q(x))` with `q(x) = 𝓛 D(x)`. -/
noncomputable def replayAction (w : Ω → ℝ) (Lm : Matrix Yt S ℂ)
    (D : Ω → Matrix S E ℂ) : ℝ :=
  ∑ x, w x * (Matrix.trace ((Lm * D x)ᴴ
    * pinv (Matrix.posSemidef_self_mul_conjTranspose Lm).1 * (Lm * D x))).re

omit [Fintype ι] [DecidableEq ι] in
/-- **(ML.14, weighted)** The replay action is the attained minimum of the
weighted HS action over all eventwise solutions of `𝓛H = 𝓛D`. -/
theorem replayAction_isLeast {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    (Lm : Matrix Yt S ℂ) (D : Ω → Matrix S E ℂ) :
    IsLeast {r : ℝ | ∃ Hf : Ω → Matrix S E ℂ,
        (∀ x, Lm * Hf x = Lm * D x) ∧ r = ∑ x, w x * frobSq (Hf x)}
      (replayAction w Lm D) := by
  constructor
  · refine ⟨fun x => minNormSol Lm (D x), fun x => minNormSol_feasible Lm (D x),
      ?_⟩
    unfold replayAction
    refine (Finset.sum_congr rfl fun x _ => ?_).symm
    rw [minNormSol_frobSq]
  · rintro r ⟨Hf, hfeas, rfl⟩
    unfold replayAction
    refine Finset.sum_le_sum fun x _ => ?_
    exact mul_le_mul_of_nonneg_left (minNorm_le Lm (D x) (Hf x) (hfeas x)) (hw x)

omit [Fintype ι] in
/-- **(ML.14, boxed)** The manuscript instance: `𝓛 = Q_irr𝓡` and `𝒟_ℓ` the
projective martingale increment of the common filtration. -/
theorem replay_action_isLeast {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    (f : ℕ → Ω → ι) (V : Ω → Matrix S E ℂ) (ℓ : ℕ)
    (R : Matrix Yt S ℂ) (P : ℕ → Matrix Yt Yt ℂ) (H : ℕ) :
    IsLeast {r : ℝ | ∃ Hf : Ω → Matrix S E ℂ,
        (∀ x, ((1 : Matrix Yt Yt ℂ) - P H) * R * Hf x
          = ((1 : Matrix Yt Yt ℂ) - P H) * R * dinc w f V ℓ x)
        ∧ r = ∑ x, w x * frobSq (Hf x)}
      (replayAction w (((1 : Matrix Yt Yt ℂ) - P H) * R) (dinc w f V ℓ)) :=
  replayAction_isLeast hw (((1 : Matrix Yt Yt ℂ) - P H) * R) (dinc w f V ℓ)

omit [Fintype ι] [DecidableEq ι] in
/-- **(ML.15, positivity)** `0 ≤ d^bi`. -/
theorem replayAction_nonneg {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    (Lm : Matrix Yt S ℂ) (D : Ω → Matrix S E ℂ) :
    0 ≤ replayAction w Lm D := by
  unfold replayAction
  refine Finset.sum_nonneg fun x _ => mul_nonneg (hw x) ?_
  refine psd_trace_re_nonneg ?_
  have h := (pinv_posSemidef
    (Matrix.posSemidef_self_mul_conjTranspose Lm).1).conjTranspose_mul_mul_same
    (Lm * D x)
  exact h

omit [Fintype ι] [DecidableEq ι] in
/-- **(ML.15, trace bound)** `d^bi ≤ Tr G_ℓ`, the trace of the increment
Gram. -/
theorem replayAction_le_trace {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    (Lm : Matrix Yt S ℂ) (D : Ω → Matrix S E ℂ) :
    replayAction w Lm D
      ≤ (Matrix.trace (promoExpect w fun x => (D x)ᴴ * D x)).re := by
  have hterm : ∀ x, (Matrix.trace ((Lm * D x)ᴴ
      * pinv (Matrix.posSemidef_self_mul_conjTranspose Lm).1 * (Lm * D x))).re
      ≤ frobSq (D x) :=
    fun x => minNorm_le Lm (D x) (D x) rfl
  unfold replayAction
  have hrhs : (Matrix.trace (promoExpect w fun x => (D x)ᴴ * D x)).re
      = ∑ x, w x * frobSq (D x) := by
    unfold promoExpect frobSq
    rw [Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    beta_reduce
    rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  rw [hrhs]
  exact Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left (hterm x) (hw x)

omit [Fintype ι] [DecidableEq ι] in
/-- **(ML.15, level sum)** `∑_ℓ d_ℓ^bi ≤ ∑_ℓ Tr G_ℓ`. -/
theorem replayAction_sum_le {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    (Lm : Matrix Yt S ℂ) (D : ℕ → Ω → Matrix S E ℂ) (L : ℕ) :
    ∑ ℓ ∈ Finset.range (L + 1), replayAction w Lm (D ℓ)
      ≤ ∑ ℓ ∈ Finset.range (L + 1),
          (Matrix.trace (promoExpect w fun x => (D ℓ x)ᴴ * D ℓ x)).re :=
  Finset.sum_le_sum fun ℓ _ => replayAction_le_trace hw Lm (D ℓ)

omit [Fintype ι] [DecidableEq ι] in
/-- **(ML.15, degenerate branch)** `G_ℓ^irr = 0` forces `d_ℓ^bi = 0`. -/
theorem replayAction_of_irr_zero {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x)
    (Lm : Matrix Yt S ℂ) (D : Ω → Matrix S E ℂ)
    (h0 : promoExpect w (fun x => (Lm * D x)ᴴ * (Lm * D x)) = 0) :
    replayAction w Lm D = 0 := by
  have hzero := mgt_promoExpect_eq_zero hw
    (fun x => posSemidef_conjTranspose_mul_self (Lm * D x)) h0
  unfold replayAction
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hwx : w x = 0
  · rw [hwx, zero_mul]
  · have hLD : Lm * D x = 0 := conjTranspose_mul_self_eq_zero.mp (hzero x hwx)
    rw [hLD, conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul,
      Matrix.trace_zero, Complex.zero_re, mul_zero]

/-- The real-bilinear Hilbert–Schmidt pairing as a bundled bilinear map. -/
noncomputable def frobForm {m p : Type*} [Fintype m] [Fintype p] :
    Matrix m p ℂ →ₗ[ℝ] Matrix m p ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ frobInner
    (fun A A' B => by
      unfold frobInner
      rw [conjTranspose_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re])
    (fun c A B => by
      unfold frobInner
      rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.trace_smul,
        Complex.smul_re, smul_eq_mul])
    (fun A B B' => by
      unfold frobInner
      rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re])
    (fun c A B => by
      unfold frobInner
      rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul])

/-- The HS pairing of a matrix with itself is its squared HS norm. -/
theorem frobForm_self {m p : Type*} [Fintype m] [Fintype p] (A : Matrix m p ℂ) :
    frobForm A A = frobSq A := rfl

end HeadReplay

end HeadReplaySection

/-! ### Shared machinery: finite product laws for independent level samples

The independent level samples of (ML.16)–(ML.18b) are drawn from a finite
product law: one independent finite weighted carrier per draw coordinate.
`MgtProd.pw` is the product weight, `MgtProd.marg1` the one-coordinate
marginalization, and `MgtProd.marg2` the two-coordinate factorization against
a real-bilinear pairing — the exact finite renderings of independence used by
the unbiasedness and mean-square-error clauses. -/

section MgtProdSection

namespace MgtProd

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {Ωf : I → Type*} [∀ i, Fintype (Ωf i)]

/-- The product weight of independent draws. -/
def pw (w : ∀ i, Ωf i → ℝ) (ξ : ∀ i, Ωf i) : ℝ := ∏ i, w i (ξ i)

/-- The product of probability weights has total mass one. -/
theorem sum_pw (w : ∀ i, Ωf i → ℝ) (hw1 : ∀ i, ∑ x, w i x = 1) :
    ∑ ξ : ∀ i, Ωf i, pw w ξ = 1 := by
  unfold pw
  calc ∑ ξ : ∀ i, Ωf i, ∏ i, w i (ξ i) = ∏ i, ∑ x, w i x :=
        (Fintype.prod_sum fun i x => w i x).symm
    _ = ∏ _i : I, (1 : ℝ) := Finset.prod_congr rfl fun i _ => hw1 i
    _ = 1 := Finset.prod_const_one

omit [DecidableEq I] [(i : I) → Fintype (Ωf i)] in
/-- The product weight is nonnegative for nonnegative factors. -/
theorem pw_nonneg {w : ∀ i, Ωf i → ℝ} (hw : ∀ i x, 0 ≤ w i x)
    (ξ : ∀ i, Ωf i) : 0 ≤ pw w ξ :=
  Finset.prod_nonneg fun i _ => hw i (ξ i)

omit [(i : I) → Fintype (Ωf i)] in
/-- Splitting the product weight at one coordinate. -/
theorem pw_splitAt (w : ∀ i, Ωf i → ℝ) (i₀ : I) (x : Ωf i₀)
    (η : ∀ j : {j // j ≠ i₀}, Ωf j) :
    pw w ((Equiv.piSplitAt i₀ Ωf).symm (x, η))
      = w i₀ x * ∏ j : {j // j ≠ i₀}, w j (η j) := by
  unfold pw
  rw [Fintype.prod_eq_mul_prod_compl i₀]
  congr 1
  · congr 1
    rw [Equiv.piSplitAt_symm_apply, dite_eq_left rfl]
  · rw [Finset.prod_subtype (p := fun j => j ≠ i₀) ({i₀}ᶜ : Finset I)
      (fun j => by simp only [Finset.mem_compl, Finset.mem_singleton, ne_eq])
      fun j => w j ((Equiv.piSplitAt i₀ Ωf).symm (x, η) j)]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    rw [Equiv.piSplitAt_symm_apply, dite_eq_right j.2]

omit [Fintype I] [(i : I) → Fintype (Ωf i)] in
/-- Evaluation of the split configuration at the split coordinate. -/
theorem splitAt_self (i₀ : I) (x : Ωf i₀) (η : ∀ j : {j // j ≠ i₀}, Ωf j) :
    (Equiv.piSplitAt i₀ Ωf).symm (x, η) i₀ = x := by
  rw [Equiv.piSplitAt_symm_apply, dite_eq_left rfl]

omit [Fintype I] [(i : I) → Fintype (Ωf i)] in
/-- Evaluation of the split configuration away from the split coordinate. -/
theorem splitAt_ne {i₀ b : I} (hb : b ≠ i₀) (x : Ωf i₀)
    (η : ∀ j : {j // j ≠ i₀}, Ωf j) :
    (Equiv.piSplitAt i₀ Ωf).symm (x, η) b = η ⟨b, hb⟩ := by
  rw [Equiv.piSplitAt_symm_apply, dite_eq_right hb]

/-- **One-coordinate marginalization** of the product law. -/
theorem marg1 {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (w : ∀ i, Ωf i → ℝ) (hw1 : ∀ i, ∑ x, w i x = 1) (i₀ : I) (g : Ωf i₀ → M) :
    ∑ ξ : ∀ i, Ωf i, pw w ξ • g (ξ i₀) = ∑ x : Ωf i₀, w i₀ x • g x := by
  rw [← Equiv.sum_comp (Equiv.piSplitAt i₀ Ωf).symm
    (fun ξ => pw w ξ • g (ξ i₀)), Fintype.sum_prod_type]
  calc ∑ x, ∑ η : ∀ j : {j // j ≠ i₀}, Ωf j,
        pw w ((Equiv.piSplitAt i₀ Ωf).symm (x, η))
          • g ((Equiv.piSplitAt i₀ Ωf).symm (x, η) i₀)
      = ∑ x, ∑ η : ∀ j : {j // j ≠ i₀}, Ωf j,
          (w i₀ x * ∏ j : {j // j ≠ i₀}, w j (η j)) • g x :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun η _ => by
          rw [pw_splitAt, splitAt_self]
    _ = ∑ x, (w i₀ x * ∑ η : ∀ j : {j // j ≠ i₀}, Ωf j,
          ∏ j : {j // j ≠ i₀}, w j (η j)) • g x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_smul, ← Finset.mul_sum]
    _ = ∑ x, w i₀ x • g x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have hs : (∑ η : ∀ j : {j // j ≠ i₀}, Ωf j,
            ∏ j : {j // j ≠ i₀}, w j (η j)) = 1 :=
          sum_pw (fun j : {j // j ≠ i₀} => w j) fun j => hw1 j
        rw [hs, mul_one]

/-- **Two-coordinate factorization**: against a real-bilinear pairing, the
product expectation of two distinct-coordinate writers factorizes. -/
theorem marg2 {M N : Type*} [AddCommMonoid M] [Module ℝ M] [AddCommMonoid N]
    [Module ℝ N] (w : ∀ i, Ωf i → ℝ) (hw1 : ∀ i, ∑ x, w i x = 1)
    {a b : I} (hab : b ≠ a) (g : Ωf a → M) (h : Ωf b → N)
    (Φ : M →ₗ[ℝ] N →ₗ[ℝ] ℝ) :
    ∑ ξ : ∀ i, Ωf i, pw w ξ • Φ (g (ξ a)) (h (ξ b))
      = Φ (∑ x, w a x • g x) (∑ y, w b y • h y) := by
  rw [← Equiv.sum_comp (Equiv.piSplitAt a Ωf).symm
    (fun ξ => pw w ξ • Φ (g (ξ a)) (h (ξ b))), Fintype.sum_prod_type]
  calc ∑ x, ∑ η : ∀ j : {j // j ≠ a}, Ωf j,
        pw w ((Equiv.piSplitAt a Ωf).symm (x, η))
          • Φ (g ((Equiv.piSplitAt a Ωf).symm (x, η) a))
              (h ((Equiv.piSplitAt a Ωf).symm (x, η) b))
      = ∑ x, ∑ η : ∀ j : {j // j ≠ a}, Ωf j,
          w a x • ((∏ j : {j // j ≠ a}, w j (η j))
            • Φ (g x) (h (η ⟨b, hab⟩))) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun η _ => by
          rw [pw_splitAt, splitAt_self, splitAt_ne hab, mul_smul]
    _ = ∑ x, w a x • Φ (g x) (∑ y, w b y • h y) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.smul_sum]
        congr 1
        have hm1 : (∑ η : ∀ j : {j // j ≠ a}, Ωf j,
            (∏ j : {j // j ≠ a}, w j (η j)) • Φ (g x) (h (η ⟨b, hab⟩)))
            = ∑ y, w b y • Φ (g x) (h y) :=
          marg1 (Ωf := fun j : {j // j ≠ a} => Ωf j)
            (fun j => w j) (fun j => hw1 j) ⟨b, hab⟩ fun y => Φ (g x) (h y)
        rw [hm1, map_sum]
        exact Finset.sum_congr rfl fun y _ =>
          (map_smul (Φ (g x)) (w b y) (h y)).symm
    _ = Φ (∑ x, w a x • g x) (∑ y, w b y • h y) := by
        rw [show (∑ x, w a x • Φ (g x) (∑ y, w b y • h y))
            = ∑ x, Φ (w a x • g x) (∑ y, w b y • h y) from
          Finset.sum_congr rfl fun x _ => by
            rw [map_smul, LinearMap.smul_apply]]
        rw [← LinearMap.sum_apply, ← map_sum]

end MgtProd

end MgtProdSection

/-! ### `thm:GT-projective-head-replay` — Estimator, allocation, drawing law

Rendering (ML.16)–(ML.18b): the independent level samples are one finite
weighted carrier per level; `hpPacket` is the block-positive packet (ML.16)
as a direct-sum family (head blocks `0..H`, the irreducible block `H+1`, the
response-null block `H+2`), `hpMean` its level expectation `G_ℓ^HP`, and
`hpEst` the replay estimator (ML.17) on the product law of all
`∑_ℓ n_ℓ` independent draws.  `hpEst_posSemidef` and `hpEst_unbiased` are
positivity and exact unbiasedness; `hpEst_mse` is the mean-square-error bound
`≤ ∑_ℓ v_ℓ/n_ℓ` in the frozen direct-sum (Hilbert–Schmidt) metric.
`allocation_lower` and `allocation_optimal` are the sharp continuous
allocation (ML.18).  `oneEst_*` render the canonical single-level
implementation (ML.18a): positivity, exact unbiasedness for the whole summed
target, and the work-normalized second-moment bound, with
`drawing_law_bound`/`drawing_law_optimal` the boxed (ML.18b). -/

section HeadReplayEstSection

namespace HeadReplayEst

open ProjHead HeadReplay MgtProd

variable {Yt S E : Type*} [Fintype Yt] [Fintype S] [Fintype E] [DecidableEq Yt]
variable [DecidableEq S] {L : ℕ} {Ωl : Fin (L + 1) → Type*} [∀ ℓ, Fintype (Ωl ℓ)]

/-- The block-positive packet `A^HP` (ML.16) of one eventwise source factor:
head blocks `0,…,H`, the final-irreducible block `H+1`, and the response-null
block `H+2`, as a direct-sum family. -/
noncomputable def hpPacket (R : Matrix Yt S ℂ) (P : ℕ → Matrix Yt Yt ℂ)
    (H : ℕ) (Zm : Matrix S E ℂ) : Fin (H + 3) → Matrix E E ℂ := fun b =>
  if (b : ℕ) ≤ H then
    (headQ P (b : ℕ) * R * Zm)ᴴ * (headQ P (b : ℕ) * R * Zm)
  else if (b : ℕ) = H + 1 then
    (((1 : Matrix Yt Yt ℂ) - P H) * R * Zm)ᴴ
      * (((1 : Matrix Yt Yt ℂ) - P H) * R * Zm)
  else Zmᴴ * ((1 : Matrix S S ℂ) - Rᴴ * R) * Zm

/-- Every block of the packet is PSD (ML.16). -/
theorem hpPacket_posSemidef (R : Matrix Yt S ℂ) (P : ℕ → Matrix Yt Yt ℂ)
    (H : ℕ) (hR : ((1 : Matrix S S ℂ) - Rᴴ * R).PosSemidef)
    (Zm : Matrix S E ℂ) (b : Fin (H + 3)) :
    (hpPacket R P H Zm b).PosSemidef := by
  unfold hpPacket
  split_ifs with h1 h2
  · exact posSemidef_conjTranspose_mul_self _
  · exact posSemidef_conjTranspose_mul_self _
  · exact hR.conjTranspose_mul_mul_same Zm

/-- The level expectation `G_ℓ^HP` of the packet. -/
noncomputable def hpMean (wl : ∀ ℓ, Ωl ℓ → ℝ) (Z : ∀ ℓ, Ωl ℓ → Matrix S E ℂ)
    (R : Matrix Yt S ℂ) (P : ℕ → Matrix Yt Yt ℂ) (H : ℕ) (ℓ : Fin (L + 1)) :
    Fin (H + 3) → Matrix E E ℂ := fun b =>
  ∑ x, wl ℓ x • hpPacket R P H (Z ℓ x) b

/-- The replay estimator `Ĝ^HP` (ML.17) on the product of all independent
draws. -/
noncomputable def hpEst (nn : Fin (L + 1) → ℕ) (Z : ∀ ℓ, Ωl ℓ → Matrix S E ℂ)
    (R : Matrix Yt S ℂ) (P : ℕ → Matrix Yt Yt ℂ) (H : ℕ)
    (ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1) :
    Fin (H + 3) → Matrix E E ℂ := fun b =>
  ∑ ℓ, ((nn ℓ : ℝ))⁻¹ • ∑ j : Fin (nn ℓ), hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b

omit [(ℓ : Fin (L + 1)) → Fintype (Ωl ℓ)] in
/-- **(ML.17, positivity)** Every block of the estimator is PSD. -/
theorem hpEst_posSemidef (nn : Fin (L + 1) → ℕ)
    (Z : ∀ ℓ, Ωl ℓ → Matrix S E ℂ) (R : Matrix Yt S ℂ)
    (P : ℕ → Matrix Yt Yt ℂ) (H : ℕ)
    (hR : ((1 : Matrix S S ℂ) - Rᴴ * R).PosSemidef)
    (ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1) (b : Fin (H + 3)) :
    (hpEst nn Z R P H ξ b).PosSemidef := by
  unfold hpEst
  refine posSemidef_sum Finset.univ fun ℓ _ => ?_
  refine mgt_smul_posSemidef (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
  exact posSemidef_sum Finset.univ fun j _ =>
    hpPacket_posSemidef R P H hR (Z ℓ (ξ ⟨ℓ, j⟩)) b

omit [Fintype E] in
/-- **(ML.17, unbiasedness)** The replay estimator is exactly unbiased for the
summed level packets under the independent product law. -/
theorem hpEst_unbiased (nn : Fin (L + 1) → ℕ) {wl : ∀ ℓ, Ωl ℓ → ℝ}
    (hw1 : ∀ ℓ, ∑ x, wl ℓ x = 1) (hnn : ∀ ℓ, 0 < nn ℓ)
    (Z : ∀ ℓ, Ωl ℓ → Matrix S E ℂ) (R : Matrix Yt S ℂ)
    (P : ℕ → Matrix Yt Yt ℂ) (H : ℕ) (b : Fin (H + 3)) :
    ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
        pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ • hpEst nn Z R P H ξ b
      = ∑ ℓ, hpMean wl Z R P H ℓ b := by
  unfold hpEst
  calc ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
        pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
          • ∑ ℓ, ((nn ℓ : ℝ))⁻¹
            • ∑ j : Fin (nn ℓ), hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b
      = ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1, ∑ ℓ,
          pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
            • (((nn ℓ : ℝ))⁻¹
              • ∑ j : Fin (nn ℓ), hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b) :=
        Finset.sum_congr rfl fun ξ _ => Finset.smul_sum
    _ = ∑ ℓ, ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
          pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
            • (((nn ℓ : ℝ))⁻¹
              • ∑ j : Fin (nn ℓ), hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b) :=
        Finset.sum_comm
    _ = ∑ ℓ, ((nn ℓ : ℝ))⁻¹
          • ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
            ∑ j : Fin (nn ℓ),
              pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
                • hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [show (∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
              pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
                • (((nn ℓ : ℝ))⁻¹
                  • ∑ j : Fin (nn ℓ), hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b))
            = ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
              ((nn ℓ : ℝ))⁻¹
                • (pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
                  • ∑ j : Fin (nn ℓ), hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b) from
          Finset.sum_congr rfl fun ξ _ => smul_comm _ _ _, ← Finset.smul_sum]
        refine congrArg _ (Finset.sum_congr rfl fun ξ _ => Finset.smul_sum)
    _ = ∑ ℓ, ((nn ℓ : ℝ))⁻¹ • ∑ j : Fin (nn ℓ),
          ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
            pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
              • hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b :=
        Finset.sum_congr rfl fun ℓ _ => congrArg _ Finset.sum_comm
    _ = ∑ ℓ, ((nn ℓ : ℝ))⁻¹ • ∑ _j : Fin (nn ℓ),
          ∑ x, wl ℓ x • hpPacket R P H (Z ℓ x) b := by
        refine Finset.sum_congr rfl fun ℓ _ => congrArg _
          (Finset.sum_congr rfl fun j _ => ?_)
        exact marg1 (Ωf := fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => Ωl p.1)
          (fun p => wl p.1) (fun p => hw1 p.1) ⟨ℓ, j⟩
          fun x => hpPacket R P H (Z ℓ x) b
    _ = ∑ ℓ, hpMean wl Z R P H ℓ b := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul ℝ (nn ℓ), smul_smul,
          inv_mul_cancel₀ (by exact_mod_cast (hnn ℓ).ne' : (nn ℓ : ℝ) ≠ 0),
          one_smul]
        rfl

/-- The frozen direct-sum (Hilbert–Schmidt) metric on packets. -/
noncomputable def hpNormSq {H : ℕ} (X : Fin (H + 3) → Matrix E E ℂ) : ℝ :=
  ∑ b, frobSq (X b)

/-- HS scaling of a real multiple. -/
theorem frobSq_smul {m q : Type*} [Fintype m] [Fintype q] (c : ℝ)
    (A : Matrix m q ℂ) : frobSq (c • A) = c ^ 2 * frobSq A := by
  rw [frobSq_eq_sum, frobSq_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- HS scaling of the direct-sum metric. -/
theorem hpNormSq_smul {H : ℕ} (c : ℝ) (X : Fin (H + 3) → Matrix E E ℂ) :
    hpNormSq (fun b => c • X b) = c ^ 2 * hpNormSq X := by
  unfold hpNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  beta_reduce
  exact frobSq_smul c (X b)

/-- **(ML.17, mean-square error)** Under per-level variance bounds `v_ℓ` in
the frozen direct-sum metric, the estimator's mean-square error is at most
`∑_ℓ v_ℓ/n_ℓ`. -/
theorem hpEst_mse (nn : Fin (L + 1) → ℕ) {wl : ∀ ℓ, Ωl ℓ → ℝ}
    (hw1 : ∀ ℓ, ∑ x, wl ℓ x = 1) (hnn : ∀ ℓ, 0 < nn ℓ)
    (Z : ∀ ℓ, Ωl ℓ → Matrix S E ℂ) (R : Matrix Yt S ℂ)
    (P : ℕ → Matrix Yt Yt ℂ) (H : ℕ) (v : Fin (L + 1) → ℝ)
    (hvar : ∀ ℓ, ∑ x, wl ℓ x * hpNormSq
      (fun b => hpPacket R P H (Z ℓ x) b - hpMean wl Z R P H ℓ b) ≤ v ℓ) :
    ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
        pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
          * hpNormSq (fun b => hpEst nn Z R P H ξ b
            - ∑ ℓ, hpMean wl Z R P H ℓ b)
      ≤ ∑ ℓ, v ℓ / nn ℓ := by
  classical
  -- centered expectation vanishes coordinatewise
  have hcent : ∀ (p : Σ ℓ : Fin (L + 1), Fin (nn ℓ)) (b : Fin (H + 3)),
      (∑ x : Ωl p.1, wl p.1 x
        • (hpPacket R P H (Z p.1 x) b - hpMean wl Z R P H p.1 b)) = 0 := by
    intro p b
    rw [show (∑ x : Ωl p.1, wl p.1 x
        • (hpPacket R P H (Z p.1 x) b - hpMean wl Z R P H p.1 b))
        = (∑ x : Ωl p.1, wl p.1 x • hpPacket R P H (Z p.1 x) b)
          - (∑ x : Ωl p.1, wl p.1 x) • hpMean wl Z R P H p.1 b from by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => smul_sub _ _ _]
    rw [hw1 p.1, one_smul, show (∑ x : Ωl p.1, wl p.1 x
        • hpPacket R P H (Z p.1 x) b) = hpMean wl Z R P H p.1 b from rfl,
      sub_self]
  -- decomposition of the deviation into centered independent draws
  have hdecomp : ∀ (ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1)
      (b : Fin (H + 3)),
      hpEst nn Z R P H ξ b - ∑ ℓ, hpMean wl Z R P H ℓ b
        = ∑ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), ((nn p.1 : ℝ))⁻¹
            • (hpPacket R P H (Z p.1 (ξ p)) b - hpMean wl Z R P H p.1 b) := by
    intro ξ b
    rw [Fintype.sum_sigma]
    unfold hpEst
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    have hgoal : ((nn ℓ : ℝ))⁻¹
          • (∑ j : Fin (nn ℓ), hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b)
        - hpMean wl Z R P H ℓ b
        = ∑ j : Fin (nn ℓ), ((nn ℓ : ℝ))⁻¹
            • (hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b - hpMean wl Z R P H ℓ b) := by
      rw [← Finset.smul_sum,
        show (∑ j : Fin (nn ℓ),
            (hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b - hpMean wl Z R P H ℓ b))
          = (∑ j : Fin (nn ℓ), hpPacket R P H (Z ℓ (ξ ⟨ℓ, j⟩)) b)
            - (nn ℓ : ℕ) • hpMean wl Z R P H ℓ b from by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin],
        smul_sub, ← Nat.cast_smul_eq_nsmul ℝ (nn ℓ), smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast (hnn ℓ).ne' : (nn ℓ : ℝ) ≠ 0),
        one_smul]
    exact hgoal
  -- bilinear expansion of the squared metric of the decomposed deviation
  have hexpand : ∀ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
      hpNormSq (fun b => hpEst nn Z R P H ξ b - ∑ ℓ, hpMean wl Z R P H ℓ b)
        = ∑ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
            ∑ q : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
              (((nn p.1 : ℝ))⁻¹ * ((nn q.1 : ℝ))⁻¹)
                * ∑ b, frobForm
                    (hpPacket R P H (Z p.1 (ξ p)) b - hpMean wl Z R P H p.1 b)
                    (hpPacket R P H (Z q.1 (ξ q)) b
                      - hpMean wl Z R P H q.1 b) := by
    intro ξ
    unfold hpNormSq
    calc ∑ b, frobSq (hpEst nn Z R P H ξ b - ∑ ℓ, hpMean wl Z R P H ℓ b)
        = ∑ b, ∑ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
            ∑ q : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
              (((nn p.1 : ℝ))⁻¹ * ((nn q.1 : ℝ))⁻¹)
                * frobForm
                    (hpPacket R P H (Z p.1 (ξ p)) b - hpMean wl Z R P H p.1 b)
                    (hpPacket R P H (Z q.1 (ξ q)) b
                      - hpMean wl Z R P H q.1 b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hdecomp ξ b, ← frobForm_self]
          set Yp : (Σ ℓ : Fin (L + 1), Fin (nn ℓ)) → Matrix E E ℂ :=
            fun p => ((nn p.1 : ℝ))⁻¹ • (hpPacket R P H (Z p.1 (ξ p)) b
              - hpMean wl Z R P H p.1 b) with hYp
          calc frobForm (∑ p, Yp p) (∑ q, Yp q)
              = ∑ p, frobForm (Yp p) (∑ q, Yp q) := by
                rw [map_sum frobForm Yp Finset.univ, LinearMap.sum_apply]
            _ = ∑ p, ∑ q, frobForm (Yp p) (Yp q) :=
                Finset.sum_congr rfl fun p _ => map_sum _ _ _
            _ = ∑ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
                  ∑ q : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
                    (((nn p.1 : ℝ))⁻¹ * ((nn q.1 : ℝ))⁻¹)
                      * frobForm
                          (hpPacket R P H (Z p.1 (ξ p)) b
                            - hpMean wl Z R P H p.1 b)
                          (hpPacket R P H (Z q.1 (ξ q)) b
                            - hpMean wl Z R P H q.1 b) := by
                refine Finset.sum_congr rfl fun p _ =>
                  Finset.sum_congr rfl fun q _ => ?_
                rw [hYp]
                beta_reduce
                rw [show frobForm (((nn p.1 : ℝ))⁻¹
                      • (hpPacket R P H (Z p.1 (ξ p)) b
                        - hpMean wl Z R P H p.1 b))
                    = ((nn p.1 : ℝ))⁻¹ • frobForm
                        (hpPacket R P H (Z p.1 (ξ p)) b
                          - hpMean wl Z R P H p.1 b) from
                  map_smul frobForm _ _, LinearMap.smul_apply, map_smul,
                  smul_eq_mul, smul_eq_mul]
                ring
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.mul_sum]
  -- expectation of the expansion
  have hswap : ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
      pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
        * hpNormSq (fun b => hpEst nn Z R P H ξ b
          - ∑ ℓ, hpMean wl Z R P H ℓ b)
      = ∑ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
          ∑ q : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
            (((nn p.1 : ℝ))⁻¹ * ((nn q.1 : ℝ))⁻¹)
              * ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
                pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
                  * ∑ b, frobForm
                      (hpPacket R P H (Z p.1 (ξ p)) b
                        - hpMean wl Z R P H p.1 b)
                      (hpPacket R P H (Z q.1 (ξ q)) b
                        - hpMean wl Z R P H q.1 b) := by
    calc ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
        pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
          * hpNormSq (fun b => hpEst nn Z R P H ξ b
            - ∑ ℓ, hpMean wl Z R P H ℓ b)
        = ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
            ∑ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
              ∑ q : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
                pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
                  * ((((nn p.1 : ℝ))⁻¹ * ((nn q.1 : ℝ))⁻¹)
                    * ∑ b, frobForm
                        (hpPacket R P H (Z p.1 (ξ p)) b
                          - hpMean wl Z R P H p.1 b)
                        (hpPacket R P H (Z q.1 (ξ q)) b
                          - hpMean wl Z R P H q.1 b)) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          rw [hexpand ξ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ξ _ => ?_
          ring
  rw [hswap]
  -- the off-diagonal expectations vanish by independence
  have hoff : ∀ p q : Σ ℓ : Fin (L + 1), Fin (nn ℓ), q ≠ p →
      (∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
        pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
          * ∑ b, frobForm
              (hpPacket R P H (Z p.1 (ξ p)) b - hpMean wl Z R P H p.1 b)
              (hpPacket R P H (Z q.1 (ξ q)) b - hpMean wl Z R P H q.1 b)) = 0 := by
    intro p q hqp
    calc ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
        pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
          * ∑ b, frobForm
              (hpPacket R P H (Z p.1 (ξ p)) b - hpMean wl Z R P H p.1 b)
              (hpPacket R P H (Z q.1 (ξ q)) b - hpMean wl Z R P H q.1 b)
        = ∑ b, ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
            pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
              • frobForm
                (hpPacket R P H (Z p.1 (ξ p)) b - hpMean wl Z R P H p.1 b)
                (hpPacket R P H (Z q.1 (ξ q)) b - hpMean wl Z R P H q.1 b) := by
          rw [Finset.sum_comm]
          refine (Finset.sum_congr rfl fun ξ _ => ?_).symm
          rw [← Finset.smul_sum, smul_eq_mul]
      _ = ∑ b : Fin (H + 3), (0 : ℝ) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [marg2 (Ωf := fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => Ωl p.1)
            (fun p => wl p.1) (fun p => hw1 p.1) hqp
            (fun x => hpPacket R P H (Z p.1 x) b - hpMean wl Z R P H p.1 b)
            (fun y => hpPacket R P H (Z q.1 y) b - hpMean wl Z R P H q.1 b)
            frobForm, hcent p b, hcent q b, map_zero]
      _ = 0 := by rw [Finset.sum_const, smul_zero]
  -- the diagonal expectations are the level variances
  have hdiag : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
      (∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
        pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
          * ∑ b, frobForm
              (hpPacket R P H (Z p.1 (ξ p)) b - hpMean wl Z R P H p.1 b)
              (hpPacket R P H (Z p.1 (ξ p)) b - hpMean wl Z R P H p.1 b))
        ≤ v p.1 := by
    intro p
    have hm := marg1 (M := ℝ)
      (Ωf := fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => Ωl p.1)
      (fun p => wl p.1) (fun p => hw1 p.1) p
      fun x => ∑ b, frobForm
        (hpPacket R P H (Z p.1 x) b - hpMean wl Z R P H p.1 b)
        (hpPacket R P H (Z p.1 x) b - hpMean wl Z R P H p.1 b)
    simp only [smul_eq_mul] at hm
    rw [hm]
    calc ∑ x : Ωl p.1, wl p.1 x * ∑ b, frobForm
          (hpPacket R P H (Z p.1 x) b - hpMean wl Z R P H p.1 b)
          (hpPacket R P H (Z p.1 x) b - hpMean wl Z R P H p.1 b)
        = ∑ x : Ωl p.1, wl p.1 x * hpNormSq
            (fun b => hpPacket R P H (Z p.1 x) b - hpMean wl Z R P H p.1 b) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          congr 1
      _ ≤ v p.1 := hvar p.1
  -- assemble
  calc ∑ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
      ∑ q : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
        (((nn p.1 : ℝ))⁻¹ * ((nn q.1 : ℝ))⁻¹)
          * ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
            pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
              * ∑ b, frobForm
                  (hpPacket R P H (Z p.1 (ξ p)) b - hpMean wl Z R P H p.1 b)
                  (hpPacket R P H (Z q.1 (ξ q)) b - hpMean wl Z R P H q.1 b)
      = ∑ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
          (((nn p.1 : ℝ))⁻¹ * ((nn p.1 : ℝ))⁻¹)
            * ∑ ξ : ∀ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ), Ωl p.1,
              pw (fun p : Σ ℓ : Fin (L + 1), Fin (nn ℓ) => wl p.1) ξ
                * ∑ b, frobForm
                    (hpPacket R P H (Z p.1 (ξ p)) b - hpMean wl Z R P H p.1 b)
                    (hpPacket R P H (Z p.1 (ξ p)) b
                      - hpMean wl Z R P H p.1 b) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        refine Finset.sum_eq_single_of_mem p hp fun q _ hq => ?_
        rw [hoff p q hq, mul_zero]
    _ ≤ ∑ p : Σ ℓ : Fin (L + 1), Fin (nn ℓ),
          (((nn p.1 : ℝ))⁻¹ * ((nn p.1 : ℝ))⁻¹) * v p.1 := by
        refine Finset.sum_le_sum fun p _ => ?_
        refine mul_le_mul_of_nonneg_left (hdiag p) ?_
        have := inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) (nn p.1))
        positivity
    _ = ∑ ℓ, v ℓ / nn ℓ := by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        have hgoal2 : (∑ _j : Fin (nn ℓ),
            ((nn ℓ : ℝ))⁻¹ * ((nn ℓ : ℝ))⁻¹ * v ℓ) = v ℓ / nn ℓ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          have hne : (nn ℓ : ℝ) ≠ 0 := by exact_mod_cast (hnn ℓ).ne'
          field_simp
        exact hgoal2

/-- **(ML.18, lower bound)** Under the work constraint `∑ c_ℓ n_ℓ = C`, every
positive continuous allocation has total variance proxy at least
`(∑ √(v_k c_k))²/C`. -/
theorem allocation_lower (v c : Fin (L + 1) → ℝ) (hv : ∀ ℓ, 0 ≤ v ℓ)
    (hc : ∀ ℓ, 0 < c ℓ) {C : ℝ} (hC : 0 < C) (nr : Fin (L + 1) → ℝ)
    (hnr : ∀ ℓ, 0 < nr ℓ) (hcon : ∑ ℓ, c ℓ * nr ℓ = C) :
    (∑ ℓ, Real.sqrt (v ℓ * c ℓ)) ^ 2 / C ≤ ∑ ℓ, v ℓ / nr ℓ := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun ℓ => Real.sqrt (v ℓ * c ℓ)) (f := fun ℓ => v ℓ / nr ℓ)
    (g := fun ℓ => c ℓ * nr ℓ)
    (fun ℓ _ => div_nonneg (hv ℓ) (hnr ℓ).le)
    (fun ℓ _ => mul_nonneg (hc ℓ).le (hnr ℓ).le)
    (fun ℓ _ => by
      rw [Real.sq_sqrt (mul_nonneg (hv ℓ) (hc ℓ).le)]
      refine le_of_eq ?_
      have h := (hnr ℓ).ne'
      field_simp)
  rw [hcon] at hcs
  rw [div_le_iff₀ hC]
  linarith [hcs]

/-- **(ML.18, sharp allocation)** The continuous allocation
`n_ℓ^* = C√(v_ℓ/c_ℓ)/∑√(v_k c_k)` is positive, meets the work constraint, and
attains `𝒱^*(C) = (∑ √(v_k c_k))²/C`. -/
theorem allocation_optimal (v c : Fin (L + 1) → ℝ) (hv : ∀ ℓ, 0 < v ℓ)
    (hc : ∀ ℓ, 0 < c ℓ) {C : ℝ} (hC : 0 < C) :
    (∀ ℓ, 0 < C * Real.sqrt (v ℓ / c ℓ) / ∑ k, Real.sqrt (v k * c k)) ∧
    (∑ ℓ, c ℓ * (C * Real.sqrt (v ℓ / c ℓ) / ∑ k, Real.sqrt (v k * c k)) = C) ∧
    (∑ ℓ, v ℓ / (C * Real.sqrt (v ℓ / c ℓ) / ∑ k, Real.sqrt (v k * c k))
      = (∑ ℓ, Real.sqrt (v ℓ * c ℓ)) ^ 2 / C) := by
  have hT : 0 < ∑ k, Real.sqrt (v k * c k) :=
    Finset.sum_pos (fun k _ => Real.sqrt_pos.mpr (mul_pos (hv k) (hc k)))
      Finset.univ_nonempty
  have hkey : ∀ ℓ, c ℓ * Real.sqrt (v ℓ / c ℓ) = Real.sqrt (v ℓ * c ℓ) := by
    intro ℓ
    rw [show c ℓ * Real.sqrt (v ℓ / c ℓ)
        = Real.sqrt ((c ℓ) ^ 2) * Real.sqrt (v ℓ / c ℓ) from by
      rw [Real.sqrt_sq (hc ℓ).le], ← Real.sqrt_mul (sq_nonneg (c ℓ))]
    congr 1
    field_simp
  have hkey2 : ∀ ℓ, v ℓ / Real.sqrt (v ℓ / c ℓ) = Real.sqrt (v ℓ * c ℓ) := by
    intro ℓ
    have hs : Real.sqrt (v ℓ / c ℓ) ≠ 0 :=
      (Real.sqrt_pos.mpr (div_pos (hv ℓ) (hc ℓ))).ne'
    rw [div_eq_iff hs, show Real.sqrt (v ℓ * c ℓ) * Real.sqrt (v ℓ / c ℓ)
        = Real.sqrt (v ℓ * c ℓ * (v ℓ / c ℓ)) from
      (Real.sqrt_mul (mul_nonneg (hv ℓ).le (hc ℓ).le) _).symm]
    rw [show v ℓ * c ℓ * (v ℓ / c ℓ) = (v ℓ) ^ 2 from by
        field_simp
        rw [mul_div_assoc, div_self (hc ℓ).ne', mul_one],
      Real.sqrt_sq (hv ℓ).le]
  refine ⟨fun ℓ => ?_, ?_, ?_⟩
  · exact div_pos (mul_pos hC (Real.sqrt_pos.mpr (div_pos (hv ℓ) (hc ℓ)))) hT
  · calc ∑ ℓ, c ℓ * (C * Real.sqrt (v ℓ / c ℓ) / ∑ k, Real.sqrt (v k * c k))
        = ∑ ℓ, C / (∑ k, Real.sqrt (v k * c k))
            * (c ℓ * Real.sqrt (v ℓ / c ℓ)) :=
          Finset.sum_congr rfl fun ℓ _ => by ring
      _ = C / (∑ k, Real.sqrt (v k * c k)) * ∑ ℓ, Real.sqrt (v ℓ * c ℓ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ℓ _ => by rw [hkey ℓ]
      _ = C := by field_simp
  · calc ∑ ℓ, v ℓ / (C * Real.sqrt (v ℓ / c ℓ) / ∑ k, Real.sqrt (v k * c k))
        = ∑ ℓ, (∑ k, Real.sqrt (v k * c k)) / C
            * (v ℓ / Real.sqrt (v ℓ / c ℓ)) := by
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          have hs : Real.sqrt (v ℓ / c ℓ) ≠ 0 :=
            (Real.sqrt_pos.mpr (div_pos (hv ℓ) (hc ℓ))).ne'
          field_simp
      _ = (∑ k, Real.sqrt (v k * c k)) / C * ∑ ℓ, Real.sqrt (v ℓ * c ℓ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ℓ _ => by rw [hkey2 ℓ]
      _ = (∑ ℓ, Real.sqrt (v ℓ * c ℓ)) ^ 2 / C := by
          field_simp

/-- The canonical single-level implementation `Ĝ_one^HP` (ML.18a): draw a
level with probability `p_ℓ`, then one independent level sample. -/
noncomputable def oneEst (pr : Fin (L + 1) → ℝ)
    (Z : ∀ ℓ, Ωl ℓ → Matrix S E ℂ) (R : Matrix Yt S ℂ)
    (P : ℕ → Matrix Yt Yt ℂ) (H : ℕ) (s : Σ ℓ, Ωl ℓ) :
    Fin (H + 3) → Matrix E E ℂ := fun b =>
  (pr s.1)⁻¹ • hpPacket R P H (Z s.1 s.2) b

omit [(ℓ : Fin (L + 1)) → Fintype (Ωl ℓ)] in
/-- **(ML.18a, positivity)** Every block of the single-level estimator is
PSD. -/
theorem oneEst_posSemidef (pr : Fin (L + 1) → ℝ) (hpr : ∀ ℓ, 0 ≤ pr ℓ)
    (Z : ∀ ℓ, Ωl ℓ → Matrix S E ℂ) (R : Matrix Yt S ℂ)
    (P : ℕ → Matrix Yt Yt ℂ) (H : ℕ)
    (hR : ((1 : Matrix S S ℂ) - Rᴴ * R).PosSemidef) (s : Σ ℓ, Ωl ℓ)
    (b : Fin (H + 3)) : (oneEst pr Z R P H s b).PosSemidef := by
  unfold oneEst
  exact mgt_smul_posSemidef (inv_nonneg.mpr (hpr s.1))
    (hpPacket_posSemidef R P H hR (Z s.1 s.2) b)

omit [Fintype E] in
/-- **(ML.18a, unbiasedness)** The single-level estimator is exactly unbiased
for the whole summed target `∑_ℓ G_ℓ^HP` under the joint drawing law. -/
theorem oneEst_unbiased (pr : Fin (L + 1) → ℝ) (hpr : ∀ ℓ, 0 < pr ℓ)
    (wl : ∀ ℓ, Ωl ℓ → ℝ) (Z : ∀ ℓ, Ωl ℓ → Matrix S E ℂ)
    (R : Matrix Yt S ℂ) (P : ℕ → Matrix Yt Yt ℂ) (H : ℕ) (b : Fin (H + 3)) :
    ∑ s : Σ ℓ, Ωl ℓ, (pr s.1 * wl s.1 s.2) • oneEst pr Z R P H s b
      = ∑ ℓ, hpMean wl Z R P H ℓ b := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold oneEst
  rw [smul_smul, show pr ℓ * wl ℓ x * (pr ℓ)⁻¹ = wl ℓ x from by
    have h := (hpr ℓ).ne'
    field_simp]

/-- **(ML.18a/b, second moment)** Under per-level second-moment bounds `m_ℓ`,
the work-normalized second moment of the single-level estimator is at most
`∑_ℓ m_ℓ/p_ℓ`. -/
theorem oneEst_secondMoment (pr : Fin (L + 1) → ℝ) (hpr : ∀ ℓ, 0 < pr ℓ)
    (wl : ∀ ℓ, Ωl ℓ → ℝ) (Z : ∀ ℓ, Ωl ℓ → Matrix S E ℂ)
    (R : Matrix Yt S ℂ) (P : ℕ → Matrix Yt Yt ℂ) (H : ℕ)
    (m : Fin (L + 1) → ℝ)
    (hm : ∀ ℓ, ∑ x, wl ℓ x * hpNormSq (hpPacket R P H (Z ℓ x)) ≤ m ℓ) :
    ∑ s : Σ ℓ, Ωl ℓ, (pr s.1 * wl s.1 s.2) * hpNormSq (oneEst pr Z R P H s)
      ≤ ∑ ℓ, m ℓ / pr ℓ := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  calc ∑ x : Ωl ℓ, (pr ℓ * wl ℓ x)
        * hpNormSq (oneEst pr Z R P H ⟨ℓ, x⟩)
      = ∑ x : Ωl ℓ, (pr ℓ)⁻¹
          * (wl ℓ x * hpNormSq (hpPacket R P H (Z ℓ x))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [show hpNormSq (oneEst pr Z R P H ⟨ℓ, x⟩)
            = ((pr ℓ)⁻¹) ^ 2 * hpNormSq (hpPacket R P H (Z ℓ x)) from
          hpNormSq_smul _ _]
        have hne : pr ℓ ≠ 0 := (hpr ℓ).ne'
        field_simp
    _ = (pr ℓ)⁻¹ * ∑ x : Ωl ℓ, wl ℓ x * hpNormSq (hpPacket R P H (Z ℓ x)) := by
        rw [Finset.mul_sum]
    _ ≤ (pr ℓ)⁻¹ * m ℓ := by
        exact mul_le_mul_of_nonneg_left (hm ℓ) (inv_nonneg.mpr (hpr ℓ).le)
    _ = m ℓ / pr ℓ := by rw [div_eq_mul_inv, mul_comm]

/-- **(ML.18b, bound)** For every positive drawing law, the work-normalized
second-moment product dominates `(∑ √(m_ℓ c_ℓ))²`. -/
theorem drawing_law_bound (m c : Fin (L + 1) → ℝ) (hm : ∀ ℓ, 0 ≤ m ℓ)
    (hc : ∀ ℓ, 0 < c ℓ) (pr : Fin (L + 1) → ℝ) (hpr : ∀ ℓ, 0 < pr ℓ) :
    (∑ ℓ, Real.sqrt (m ℓ * c ℓ)) ^ 2
      ≤ (∑ ℓ, m ℓ / pr ℓ) * ∑ ℓ, pr ℓ * c ℓ := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun ℓ => Real.sqrt (m ℓ * c ℓ)) (f := fun ℓ => m ℓ / pr ℓ)
    (g := fun ℓ => pr ℓ * c ℓ)
    (fun ℓ _ => div_nonneg (hm ℓ) (hpr ℓ).le)
    (fun ℓ _ => mul_nonneg (hpr ℓ).le (hc ℓ).le)
    (fun ℓ _ => by
      rw [Real.sq_sqrt (mul_nonneg (hm ℓ) (hc ℓ).le)]
      refine le_of_eq ?_
      have h := (hpr ℓ).ne'
      field_simp)

/-- **(ML.18b, sharp drawing law)** `p_ℓ^* = √(m_ℓ/c_ℓ)/∑√(m_k/c_k)` is a
positive probability law attaining `(∑ √(m_ℓ c_ℓ))²`. -/
theorem drawing_law_optimal (m c : Fin (L + 1) → ℝ) (hm : ∀ ℓ, 0 < m ℓ)
    (hc : ∀ ℓ, 0 < c ℓ) :
    (∀ ℓ, 0 < Real.sqrt (m ℓ / c ℓ) / ∑ k, Real.sqrt (m k / c k)) ∧
    (∑ ℓ, Real.sqrt (m ℓ / c ℓ) / ∑ k, Real.sqrt (m k / c k) = 1) ∧
    ((∑ ℓ, m ℓ / (Real.sqrt (m ℓ / c ℓ) / ∑ k, Real.sqrt (m k / c k)))
        * ∑ ℓ, (Real.sqrt (m ℓ / c ℓ) / ∑ k, Real.sqrt (m k / c k)) * c ℓ
      = (∑ ℓ, Real.sqrt (m ℓ * c ℓ)) ^ 2) := by
  have hT : 0 < ∑ k, Real.sqrt (m k / c k) :=
    Finset.sum_pos (fun k _ => Real.sqrt_pos.mpr (div_pos (hm k) (hc k)))
      Finset.univ_nonempty
  have hkey : ∀ ℓ, m ℓ / Real.sqrt (m ℓ / c ℓ) = Real.sqrt (m ℓ * c ℓ) := by
    intro ℓ
    have hs : Real.sqrt (m ℓ / c ℓ) ≠ 0 :=
      (Real.sqrt_pos.mpr (div_pos (hm ℓ) (hc ℓ))).ne'
    rw [div_eq_iff hs, show Real.sqrt (m ℓ * c ℓ) * Real.sqrt (m ℓ / c ℓ)
        = Real.sqrt (m ℓ * c ℓ * (m ℓ / c ℓ)) from
      (Real.sqrt_mul (mul_nonneg (hm ℓ).le (hc ℓ).le) _).symm]
    rw [show m ℓ * c ℓ * (m ℓ / c ℓ) = (m ℓ) ^ 2 from by
        field_simp
        rw [mul_div_assoc, div_self (hc ℓ).ne', mul_one],
      Real.sqrt_sq (hm ℓ).le]
  have hkey2 : ∀ ℓ, Real.sqrt (m ℓ / c ℓ) * c ℓ = Real.sqrt (m ℓ * c ℓ) := by
    intro ℓ
    rw [show Real.sqrt (m ℓ / c ℓ) * c ℓ
        = Real.sqrt (m ℓ / c ℓ) * Real.sqrt ((c ℓ) ^ 2) from by
      rw [Real.sqrt_sq (hc ℓ).le],
      ← Real.sqrt_mul (div_pos (hm ℓ) (hc ℓ)).le]
    congr 1
    field_simp
  refine ⟨fun ℓ => ?_, ?_, ?_⟩
  · exact div_pos (Real.sqrt_pos.mpr (div_pos (hm ℓ) (hc ℓ))) hT
  · rw [← Finset.sum_div]
    field_simp
  · calc (∑ ℓ, m ℓ / (Real.sqrt (m ℓ / c ℓ) / ∑ k, Real.sqrt (m k / c k)))
          * ∑ ℓ, (Real.sqrt (m ℓ / c ℓ) / ∑ k, Real.sqrt (m k / c k)) * c ℓ
        = ((∑ k, Real.sqrt (m k / c k)) * ∑ ℓ, Real.sqrt (m ℓ * c ℓ))
            * ((∑ k, Real.sqrt (m k / c k))⁻¹ * ∑ ℓ, Real.sqrt (m ℓ * c ℓ)) := by
          congr 1
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            have hs : Real.sqrt (m ℓ / c ℓ) ≠ 0 :=
              (Real.sqrt_pos.mpr (div_pos (hm ℓ) (hc ℓ))).ne'
            rw [← hkey ℓ]
            field_simp
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            rw [← hkey2 ℓ]
            field_simp
      _ = (∑ ℓ, Real.sqrt (m ℓ * c ℓ)) ^ 2 := by
          field_simp

end HeadReplayEst

end HeadReplayEstSection

/-! ### `thm:GT-physical-stage-alternative` — Stage-attribution alternative

Rendering: the record is the exhaustive first-match protocol over the defined
certificates of the stage framework; each outcome's licensed content is a
proved theorem of the framework layers (the gauge and defect layers of
`EasyExact00`, the record tower and audit layers above).  The applicability of
an outcome is determined by which packet layers are supplied, so the protocol
is rendered by one first-match alternative per packet shape, with the
substantive payload carried inside each branch:

* `stage_attribution_alternative` — outcomes (S1)/(S3): over a supplied
  intermediate-law layer, either the **first** stage-occurrence certificate
  (STG.6) fails — retained with its minimality and an explicit pointwise
  separator, which no later factorization or normalization can erase — or
  every proposed stage occurs, and then the intermediate laws are exactly the
  staged transports of the base law, and the terminal discrepancy of (STG.8)
  collapses, so (STG.8)–(STG.9) control every staged route.
* `endpoint_gauge_only` — outcome (S2): with only the endpoint product
  occurring, any two positive factor lists differ by the multiplicative
  coboundary gauge (STG.3–STG.4): factor-specific prices remain in the
  multiplicative-gauge fibre.
* `record_attribution_alternative` — outcomes (S4)/(S5): over a supplied
  nested physical record, either the record residual (STG.21) vanishes and
  the packet is the unique canonical martingale factorization of the terminal
  likelihood (every stage is `P_j L`), or the residual is nonzero and the
  first failing clause — the terminal defect or the least failing
  backward-conditional stage — is an explicit pointwise witness.
* `cofinal_transport_attribution` — outcome (S6): summable transport defects
  give one unique route-independent stage-law limit.

The closing sentence is rendered by the minimality clause of (S1): the first
failing certificate is part of the retained outcome regardless of the later
stages of the packet. -/

section StageAlternativeSection

namespace StageAlternative

open MgtFilt RecordTower RecordAudit

/-- A stage-occurrence certificate with no pointwise separator vanishes. -/
theorem stageTV_eq_zero_of_forall {σ : Type*} [Fintype σ] {a μ : ℕ → σ → ℝ}
    {j : ℕ} (h : ∀ x, μ (j + 1) x = a j x * μ j x) :
    stageTV (fun x => stageOcc a μ j x) = 0 := by
  unfold stageTV
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [abs_eq_zero]
  change stageOcc a μ j x = 0
  unfold stageOcc
  rw [h x, sub_self]

/-- **(S1)/(S3) first-match alternative** over the intermediate-law layer:
either the first failing stage-occurrence certificate is retained (with
minimality and a pointwise separator), or every proposed stage occurs and the
staged route is exactly controlled. -/
theorem stage_attribution_alternative {σ : Type*} [Fintype σ]
    (a μ : ℕ → σ → ℝ) (r : ℕ) :
    (∃ j, j < r ∧ stageTV (fun x => stageOcc a μ j x) ≠ 0
      ∧ (∀ i, i < j → stageTV (fun x => stageOcc a μ i x) = 0)
      ∧ ∃ x, μ (j + 1) x ≠ a j x * μ j x) ∨
    ((∀ j, j < r → ∀ x, μ (j + 1) x = a j x * μ j x)
      ∧ (∀ j, j ≤ r → ∀ x, μ j x = stageWindow a 0 j x * μ 0 x)
      ∧ ∀ x, μ r x - (∏ j ∈ Finset.range r, a j x) * μ 0 x = 0) := by
  classical
  by_cases hall : ∀ j, j < r → stageTV (fun x => stageOcc a μ j x) = 0
  · right
    have hocc : ∀ j, j < r → ∀ x, μ (j + 1) x = a j x * μ j x := by
      intro j hj x
      have h := hall j hj
      unfold stageTV at h
      have hx := (Finset.sum_eq_zero_iff_of_nonneg
        fun y (_ : y ∈ Finset.univ) => abs_nonneg _).mp h x (Finset.mem_univ x)
      have h0 := abs_eq_zero.mp hx
      unfold stageOcc at h0
      linarith
    refine ⟨hocc, ?_, ?_⟩
    · intro j hj x
      induction j with
      | zero =>
        unfold stageWindow
        rw [Finset.Ico_self, Finset.prod_empty, one_mul]
      | succ j ih =>
        rw [hocc j (by omega) x, ih (by omega)]
        unfold stageWindow
        rw [show Finset.Ico 0 (j + 1) = Finset.range (j + 1) from
          (Finset.range_eq_Ico (j + 1)).symm,
          show Finset.Ico 0 j = Finset.range j from
          (Finset.range_eq_Ico j).symm, Finset.prod_range_succ]
        ring
    · intro x
      rw [stage_defect_telescope]
      refine Finset.sum_eq_zero fun j hj => ?_
      have h := hocc j (Finset.mem_range.mp hj) x
      unfold stageOcc
      rw [show μ (j + 1) x - a j x * μ j x = 0 from by linarith, mul_zero]
  · left
    have hex : ∃ j, j < r ∧ stageTV (fun x => stageOcc a μ j x) ≠ 0 := by
      by_contra hcon
      refine hall fun j hj => ?_
      by_contra hne
      exact hcon ⟨j, hj, hne⟩
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun i hi => ?_, ?_⟩
    · by_contra hne
      have hir : i < r := lt_trans hi (Nat.find_spec hex).1
      exact absurd ⟨hir, hne⟩ (Nat.find_min hex hi)
    · by_contra hcon
      push Not at hcon
      exact (Nat.find_spec hex).2 (stageTV_eq_zero_of_forall hcon)

/-- **(S2)** With only the endpoint product occurring, two positive factor
lists of one terminal density differ exactly by the multiplicative coboundary
gauge: normalized ends, positive interior, and the boxed relation (STG.4).
Factor-specific prices therefore remain in the gauge fibre. -/
theorem endpoint_gauge_only {σ : Type*} {a b : ℕ → σ → ℝ} {r : ℕ}
    (ha : ∀ i, i < r → ∀ x, 0 < a i x) (hb : ∀ i, i < r → ∀ x, 0 < b i x)
    (hW : ∀ x, stageProd b r x = stageProd a r x) :
    (∀ x, stageGauge a b 0 x = 1) ∧ (∀ x, stageGauge a b r x = 1)
    ∧ (∀ j, j ≤ r → ∀ x, 0 < stageGauge a b j x)
    ∧ ∀ j, j < r → ∀ x,
        b j x = a j x * stageGauge a b (j + 1) x / stageGauge a b j x :=
  ⟨fun x => stageGauge_zero a b x, fun x => stageGauge_last ha hW x,
    fun _ hj x => stageGauge_pos ha hb hj x,
    fun _ hj x => stageGauge_step ha hb hj x⟩

/-- **(S4)/(S5) first-match alternative** over the record layer: either the
record residual (STG.21) vanishes and the packet is the unique canonical
martingale factorization (every proposed stage is the canonical `P_j L`), or
the residual is nonzero and the first failing clause is an explicit pointwise
witness — the terminal defect, or else the least failing
backward-conditional stage with all earlier stages consistent. -/
theorem record_attribution_alternative {Ω : Type*} [Fintype Ω] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) {L : Ω → ℝ} {r : ℕ}
    (hLr : DetOn (f r) L) (A : ℕ → Ω → ℝ) :
    (facResidual w f L A r = 0
      ∧ ∀ j, j ≤ r → ∀ x, A j x = towerL w f L j x) ∨
    (facResidual w f L A r ≠ 0
      ∧ ((∃ x, A r x ≠ L x) ∨
          ∃ j, j < r ∧ (∃ x, A j x ≠ cexp w (f j) (A (j + 1)) x)
            ∧ ∀ i, i < j → ∀ x, A i x = cexp w (f i) (A (i + 1)) x)) := by
  classical
  by_cases h0 : facResidual w f L A r = 0
  · left
    refine ⟨h0, ?_⟩
    have hclauses := (facResidual_eq_zero_iff hw f L A r).mp h0
    exact (audit_martingale_iff_canonical hw hchain hLr A).mp
      ⟨hclauses.1, fun j hj x => hclauses.2 j hj x⟩
  · right
    refine ⟨h0, ?_⟩
    by_cases hterm : ∀ x, A r x = L x
    · right
      have hex : ∃ j, j < r ∧ ∃ x, A j x ≠ cexp w (f j) (A (j + 1)) x := by
        by_contra hcon
        push Not at hcon
        refine h0 ((facResidual_eq_zero_iff hw f L A r).mpr
          ⟨hterm, fun j hj x => hcon j hj x⟩)
      refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
        fun i hi x => ?_⟩
      by_contra hne
      have hir : i < r := lt_trans hi (Nat.find_spec hex).1
      exact absurd ⟨hir, x, hne⟩ (Nat.find_min hex hi)
    · left
      by_contra hcon
      push Not at hcon
      exact hterm fun x => hcon x

/-- **(S6)** Summable cofinal transport defects give one unique
route-independent stage-law limit. -/
theorem cofinal_transport_attribution {Ω : Type*} [Fintype Ω] {w : Ω → ℝ}
    (hw : ∀ x, 0 < w x) {Ln : ℕ → Ω → ℝ} {d : ℕ → ℝ} (hd : Summable d)
    (hdef : ∀ n, wnorm w (fun x => Ln (n + 1) x - Ln n x) ≤ d n) :
    ∃ Linf : Ω → ℝ,
      Tendsto (fun n => wnorm w (fun x => Ln n x - Linf x)) atTop (𝓝 0)
      ∧ ∀ Linf' : Ω → ℝ,
          Tendsto (fun n => wnorm w (fun x => Ln n x - Linf' x)) atTop (𝓝 0)
          → Linf' = Linf := by
  obtain ⟨Linf, hLinf⟩ := summable_defect_limit hw hd hdef
  exact ⟨Linf, hLinf, fun Linf' h' => wnorm_limit_unique hw h' hLinf⟩

/-- **(first-match composition)** Over a packet carrying both the
intermediate-law layer and the record layer, the outcomes compose in
first-match order: either the first occurrence certificate fails and is
retained, or the staged route is exactly controlled and the record layer then
decides between the canonical factorization and the first record witness. -/
theorem physical_stage_alternative {σ : Type*} [Fintype σ] {Ω : Type*}
    [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a μ : ℕ → σ → ℝ) (r : ℕ) {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    {f : ℕ → Ω → ι} (hchain : Chain f) {L : Ω → ℝ} {rr : ℕ}
    (hLr : DetOn (f rr) L) (A : ℕ → Ω → ℝ) :
    (∃ j, j < r ∧ stageTV (fun x => stageOcc a μ j x) ≠ 0
      ∧ (∀ i, i < j → stageTV (fun x => stageOcc a μ i x) = 0)
      ∧ ∃ x, μ (j + 1) x ≠ a j x * μ j x) ∨
    ((∀ j, j ≤ r → ∀ x, μ j x = stageWindow a 0 j x * μ 0 x)
      ∧ ((facResidual w f L A rr = 0
            ∧ ∀ j, j ≤ rr → ∀ x, A j x = towerL w f L j x) ∨
          (facResidual w f L A rr ≠ 0
            ∧ ((∃ x, A rr x ≠ L x) ∨
                ∃ j, j < rr ∧ (∃ x, A j x ≠ cexp w (f j) (A (j + 1)) x)
                  ∧ ∀ i, i < j → ∀ x,
                      A i x = cexp w (f i) (A (i + 1)) x)))) := by
  rcases stage_attribution_alternative a μ r with h1 | h3
  · exact Or.inl h1
  · exact Or.inr ⟨h3.2.1, record_attribution_alternative hw hchain hLr A⟩

end StageAlternative

end StageAlternativeSection

end NCG
