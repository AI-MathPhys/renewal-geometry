/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EasyExact03

/-!
# Easy exact records, batch 04 (Gran-Tensor manuscript, YM cluster)

Exact formalizations of the following manuscript records:

* `cth:YM-rare-common-factor` — a rare common binary record with
  conditional independence and unshorted maximal correlation one.
* `thm:YM-law-incidence` — transported null and canonical law incidence
  (YL.1–YL.5).
* `cor:YM-partition-curvature-transport` — target-native adjacent-cutoff
  transport (YPC.16), the adjacent Hessian bound, the summable-defect
  Cauchy property, and the normalized-row independence witness.
* `lem:YM-exact-form-isometry` — the exact-form Witten isometry (YSI.1)
  on a finite Hodge card.
* `thm:YM-source-comparison-return-Pythagoras` — comparison/return
  Pythagoras (YSI.4–YSI.5) and the return-matrix identification.
* `cor:YM-Ward-assembly-before-source-short` — Ward cancellation is
  assembled before source shorting (YSI.14–YSI.15).
* `thm:YM-source-current-incidence` — the same-history source/current
  Gram, its ancestry residual, the follower criterion, and the exact
  rank-minimality clause (YSCI.1–YSCI.4).
* `cth:YM-source-current-marginals` — identical marginals with different
  mixed blocks (YSCI.5).
* `cth:YM-geometric-not-source-reserve` — geometric reserve one with
  vanishing source-normalized reserve (YS.23).
* `cth:YM-identity-metric-artifact` — diffusive identity collapse of the
  Maxwell head at the lowest axial momentum (YS.24).
* `lem:YM-Wilson-separator` — the canonical Wilson separator (S1)–(S4)
  and the exact action split (WBM.3).

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset
open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank
open scoped ComplexOrder

-- decidability/fintype instances enter only through the dot-product calculus in proofs
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace NCG

/-! ### `cth:YM-rare-common-factor` — Rare common data cannot be discarded

Rendering: the half-slab law is the explicit finite law of the manuscript
proof — `C ~ Bernoulli(p)` and, conditionally on `C`, independent fair
noises `U, V`; the boundaries are `X₀ = (C,U)` and `X_{1/2} = (C,V)`.
The carrier is `Bool × Bool × Bool` with the product weights.  Maximal
correlation one is rendered by both halves of the equality: every pair of
boundary observables with second moment at most one has correlation at
most one, and the centred normalized record `((C-p)/√(p(1-p)))` is a pair
of boundary observables that is centred, has unit second moment, and has
correlation exactly one. -/

section RareCommon

namespace YMRareCommon

/-- The half-slab law: `C ~ Bernoulli(p)` and independent fair noises,
`w(c,u,v) = P(C=c)/4`. -/
noncomputable def slabLaw (p : ℝ) : Bool × Bool × Bool → ℝ :=
  fun w => (if w.1 then p else 1 - p) * (1 / 4)

/-- The first boundary `X₀ = (C, U)`. -/
def bnd0 (w : Bool × Bool × Bool) : Bool × Bool := (w.1, w.2.1)

/-- The second boundary `X_{1/2} = (C, V)`. -/
def bnd1 (w : Bool × Bool × Bool) : Bool × Bool := (w.1, w.2.2)

/-- Expectation of an observable under the half-slab law. -/
noncomputable def expect (p : ℝ) (φ : Bool × Bool × Bool → ℝ) : ℝ :=
  ∑ w : Bool × Bool × Bool, slabLaw p w * φ w

/-- The half-slab law is strictly positive. -/
theorem slabLaw_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (w : Bool × Bool × Bool) :
    0 < slabLaw p w := by
  unfold slabLaw
  cases w.1 <;> simp <;> linarith

/-- The half-slab law is a probability law. -/
theorem slabLaw_sum (p : ℝ) : ∑ w : Bool × Bool × Bool, slabLaw p w = 1 := by
  simp [slabLaw, Fintype.sum_prod_type]
  ring

/-- The common binary record has probability `p`. -/
theorem record_probability (p : ℝ) :
    ∑ u : Bool, ∑ v : Bool, slabLaw p (true, u, v) = p := by
  simp [slabLaw]
  ring

/-- Marginal of the record. -/
noncomputable def margC (p : ℝ) (c : Bool) : ℝ :=
  ∑ u : Bool, ∑ v : Bool, slabLaw p (c, u, v)

/-- Marginal of the first boundary. -/
noncomputable def margCU (p : ℝ) (cu : Bool × Bool) : ℝ :=
  ∑ v : Bool, slabLaw p (cu.1, cu.2, v)

/-- Marginal of the second boundary. -/
noncomputable def margCV (p : ℝ) (cv : Bool × Bool) : ℝ :=
  ∑ u : Bool, slabLaw p (cv.1, u, cv.2)

/-- **Conditional independence of the two boundaries given the record**:
`P(X₀=(c,u), X_{1/2}=(c,v)) · P(C=c) = P(X₀=(c,u)) · P(X_{1/2}=(c,v))`. -/
theorem boundaries_condIndep (p : ℝ) (c u v : Bool) :
    slabLaw p (c, u, v) * margC p c = margCU p (c, u) * margCV p (c, v) := by
  cases c <;> simp [slabLaw, margC, margCU, margCV] <;> ring

/-- **Maximal correlation is at most one**: any two boundary observables
with second moment at most one have correlation at most one. -/
theorem correlation_le_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f g : Bool × Bool → ℝ)
    (hf : expect p (fun w => f (bnd0 w) ^ 2) ≤ 1)
    (hg : expect p (fun w => g (bnd1 w) ^ 2) ≤ 1) :
    expect p (fun w => f (bnd0 w) * g (bnd1 w)) ≤ 1 := by
  have hkey : ∀ w : Bool × Bool × Bool,
      slabLaw p w * (f (bnd0 w) - g (bnd1 w)) ^ 2
        = slabLaw p w * f (bnd0 w) ^ 2
          - 2 * (slabLaw p w * (f (bnd0 w) * g (bnd1 w)))
          + slabLaw p w * g (bnd1 w) ^ 2 := fun w => by ring
  have hnn : 0 ≤ ∑ w : Bool × Bool × Bool,
      slabLaw p w * (f (bnd0 w) - g (bnd1 w)) ^ 2 :=
    Finset.sum_nonneg fun w _ =>
      mul_nonneg (slabLaw_pos hp hp1 w).le (sq_nonneg _)
  have hsplit : ∑ w : Bool × Bool × Bool,
      slabLaw p w * (f (bnd0 w) - g (bnd1 w)) ^ 2
        = expect p (fun w => f (bnd0 w) ^ 2)
          - 2 * expect p (fun w => f (bnd0 w) * g (bnd1 w))
          + expect p (fun w => g (bnd1 w) ^ 2) := by
    unfold expect
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => hkey w
  rw [hsplit] at hnn
  linarith

/-- The centred normalized record, read on either boundary. -/
noncomputable def recordWriter (p : ℝ) : Bool × Bool → ℝ :=
  fun cu => (if cu.1 then 1 - p else -p) / Real.sqrt (p * (1 - p))

/-- The normalized record is centred on the first boundary. -/
theorem recordWriter_centered {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    expect p (fun w => recordWriter p (bnd0 w)) = 0 := by
  have hs : Real.sqrt (p * (1 - p)) ≠ 0 :=
    (Real.sqrt_pos.mpr (by nlinarith)).ne'
  simp [expect, recordWriter, slabLaw, bnd0, Fintype.sum_prod_type]
  field_simp
  ring

/-- The normalized record has unit second moment. -/
theorem recordWriter_unit {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    expect p (fun w => recordWriter p (bnd0 w) ^ 2) = 1 := by
  have hpos : (0 : ℝ) < p * (1 - p) := by nlinarith
  have hs : Real.sqrt (p * (1 - p)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq : Real.sqrt (p * (1 - p)) ^ 2 = p * (1 - p) := Real.sq_sqrt hpos.le
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  simp [expect, recordWriter, slabLaw, bnd0, Fintype.sum_prod_type, div_pow]
  simp only [hsq]
  field_simp [h1p, hp.ne']
  ring

/-- **The unshorted maximal correlation is one**: the normalized record is
readable from both boundaries and has correlation exactly one. -/
theorem recordWriter_correlation_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    expect p (fun w => recordWriter p (bnd0 w) * recordWriter p (bnd1 w)) = 1 := by
  have hpoint : ∀ w : Bool × Bool × Bool,
      recordWriter p (bnd0 w) * recordWriter p (bnd1 w)
        = recordWriter p (bnd0 w) ^ 2 := by
    intro w
    unfold recordWriter bnd0 bnd1
    ring
  calc expect p (fun w => recordWriter p (bnd0 w) * recordWriter p (bnd1 w))
      = expect p (fun w => recordWriter p (bnd0 w) ^ 2) := by
        unfold expect
        refine Finset.sum_congr rfl fun w _ => ?_
        beta_reduce
        rw [hpoint w]
    _ = 1 := recordWriter_unit hp hp1

end YMRareCommon

end RareCommon

/-! ### `thm:YM-law-incidence` — Transported null and canonical law incidence

Rendering: the coarse trace law `ν` and the natural coarse Wilson law `μ`
are strictly positive probability weights on a finite carrier `k`;
`L²(ν)` is the function space `k → ℝ` with the weighted pairing
`⟨f,g⟩_ν = ∑ ν·f·g`; `r = μ/ν`, `h = √r`, and `U`, `M_h`, `P_h`,
`𝓒_h = P_h M_h` are the displayed linear maps.  YL.1 is the exact kernel
identity for the conjugated operator; the "need not be orthogonal" clause
is an explicit two-point witness; the adjoint `𝓒_h^* = M_h P_h` is
certified by the pairing identity, and YL.4 is stated as the operator
identity `𝓒_h^*𝓒_h = M_r − |r⟩⟨r|_ν` together with the `μ`-variance norm
identity (proved for every `f`; the manuscript states it for `f ⊥ 𝟙`).
YL.5 is the two-sided bound on the `ν`-centred space. -/

section LawIncidence

namespace YMLawIncidence

variable {k : Type*} [Fintype k]

/-- The weighted `L²(ν)` pairing `⟨f,g⟩_ν = ∑ ν·f·g`. -/
def wInner (ν f g : k → ℝ) : ℝ := ∑ x, ν x * (f x * g x)

/-- The mean `ρ(f) = ∑ ρ·f` of an observable under a weight. -/
def wMean (ρ f : k → ℝ) : ℝ := ∑ x, ρ x * f x

/-- Multiplication operator `M_φ f = φ·f`. -/
def mulOp (φ : k → ℝ) : (k → ℝ) →ₗ[ℝ] (k → ℝ) where
  toFun f := φ * f
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by
    funext x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The `ν`-rank-one map `f ↦ ⟨φ,f⟩_ν φ`. -/
def rankOne (ν φ : k → ℝ) : (k → ℝ) →ₗ[ℝ] (k → ℝ) where
  toFun f := wInner ν φ f • φ
  map_add' f g := by
    unfold wInner
    rw [← add_smul]
    congr 1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by simp [mul_add]
  map_smul' c f := by
    unfold wInner
    simp only [RingHom.id_apply, smul_smul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- The `ν`-orthogonal projection `P_φ = I − |φ⟩⟨φ|_ν` away from `φ`. -/
def coProj (ν φ : k → ℝ) : (k → ℝ) →ₗ[ℝ] (k → ℝ) :=
  LinearMap.id - rankOne ν φ

/-- The density `r = dμ/dν`. -/
noncomputable def dens (ν μ : k → ℝ) : k → ℝ := fun x => μ x / ν x

/-- The half-density `h = √r`. -/
noncomputable def halfDens (ν μ : k → ℝ) : k → ℝ := fun x => Real.sqrt (μ x / ν x)

/-- The multiplication unitary `U f = h f : L²(μ) → L²(ν)` conjugating the
coarse operator, `Ã = U A U⁻¹`. -/
noncomputable def transported (ν μ : k → ℝ) (A : (k → ℝ) →ₗ[ℝ] (k → ℝ)) :
    (k → ℝ) →ₗ[ℝ] (k → ℝ) :=
  mulOp (halfDens ν μ) ∘ₗ A ∘ₗ mulOp fun x => (halfDens ν μ x)⁻¹

/-- The canonical incidence operator `𝓒_h = P_h M_h` (YL.2). -/
noncomputable def lawFollower (ν μ : k → ℝ) : (k → ℝ) →ₗ[ℝ] (k → ℝ) :=
  coProj ν (halfDens ν μ) ∘ₗ mulOp (halfDens ν μ)

/-- The adjoint candidate `𝓒_h^* = M_h P_h`. -/
noncomputable def lawFollowerStar (ν μ : k → ℝ) : (k → ℝ) →ₗ[ℝ] (k → ℝ) :=
  mulOp (halfDens ν μ) ∘ₗ coProj ν (halfDens ν μ)

/-- Unfolding `𝓒_h f = h f − ⟨h, h f⟩_ν h`. -/
theorem lawFollower_def (ν μ : k → ℝ) (f : k → ℝ) :
    lawFollower ν μ f
      = halfDens ν μ * f - wInner ν (halfDens ν μ) (halfDens ν μ * f) • halfDens ν μ :=
  rfl

/-- Unfolding `𝓒_h^* g = h (g − ⟨h, g⟩_ν h)`. -/
theorem lawFollowerStar_def (ν μ : k → ℝ) (g : k → ℝ) :
    lawFollowerStar ν μ g
      = halfDens ν μ * (g - wInner ν (halfDens ν μ) g • halfDens ν μ) :=
  rfl

/-- The weighted pairing is symmetric. -/
theorem wInner_symm (ν f g : k → ℝ) : wInner ν f g = wInner ν g f :=
  Finset.sum_congr rfl fun x _ => by ring

/-- The weighted pairing is additive in the left slot. -/
theorem wInner_sub_left (ν f g w : k → ℝ) :
    wInner ν (f - g) w = wInner ν f w - wInner ν g w := by
  unfold wInner
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.sub_apply]
  ring

/-- The weighted pairing scales in the left slot. -/
theorem wInner_smul_left (ν : k → ℝ) (c : ℝ) (f w : k → ℝ) :
    wInner ν (c • f) w = c * wInner ν f w := by
  unfold wInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The weighted pairing is additive in the right slot. -/
theorem wInner_sub_right (ν w f g : k → ℝ) :
    wInner ν w (f - g) = wInner ν w f - wInner ν w g := by
  rw [wInner_symm, wInner_sub_left, wInner_symm ν f w, wInner_symm ν g w]

/-- The weighted pairing scales in the right slot. -/
theorem wInner_smul_right (ν : k → ℝ) (c : ℝ) (w f : k → ℝ) :
    wInner ν w (c • f) = c * wInner ν w f := by
  rw [wInner_symm, wInner_smul_left, wInner_symm ν f w]

/-- A multiplication factor moves across the weighted pairing. -/
theorem wInner_mul_shift (ν φ f g : k → ℝ) :
    wInner ν (φ * f) g = wInner ν f (φ * g) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.mul_apply]
  ring

variable {ν μ : k → ℝ}

omit [Fintype k] in
/-- The half-density is strictly positive. -/
theorem halfDens_pos (hν : ∀ x, 0 < ν x) (hμ : ∀ x, 0 < μ x) (x : k) :
    0 < halfDens ν μ x :=
  Real.sqrt_pos.mpr (div_pos (hμ x) (hν x))

omit [Fintype k] in
/-- `ν · h² = μ` pointwise. -/
theorem nu_mul_halfDens_sq (hν : ∀ x, 0 < ν x) (hμ : ∀ x, 0 < μ x) (x : k) :
    ν x * (halfDens ν μ x * halfDens ν μ x) = μ x := by
  unfold halfDens
  rw [Real.mul_self_sqrt (div_nonneg (hμ x).le (hν x).le)]
  field_simp [(hν x).ne']

/-- `⟨h, h·f⟩_ν = μ(f)`: the half-density intertwines the two means. -/
theorem wInner_halfDens_mul (hν : ∀ x, 0 < ν x) (hμ : ∀ x, 0 < μ x) (f : k → ℝ) :
    wInner ν (halfDens ν μ) (halfDens ν μ * f) = wMean μ f := by
  unfold wInner wMean
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := nu_mul_halfDens_sq (μ := μ) hν hμ x
  simp only [Pi.mul_apply]
  linear_combination f x * h

omit [Fintype k] in
/-- **(YL.1)** `Ker Ã_c = Span{h}`: unitary transport of the physical
null direction. -/
theorem transported_kernel (hν : ∀ x, 0 < ν x) (hμ : ∀ x, 0 < μ x)
    (A : (k → ℝ) →ₗ[ℝ] (k → ℝ))
    (hker : LinearMap.ker A = Submodule.span ℝ {(fun _ => 1 : k → ℝ)}) :
    LinearMap.ker (transported ν μ A) = Submodule.span ℝ {halfDens ν μ} := by
  have hpos := halfDens_pos (μ := μ) hν hμ
  ext f
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hf
    have hAz : A ((fun x => (halfDens ν μ x)⁻¹) * f) = 0 := by
      have hf' : halfDens ν μ * A ((fun x => (halfDens ν μ x)⁻¹) * f) = 0 := hf
      funext x
      have := congrFun hf' x
      simp only [Pi.mul_apply, Pi.zero_apply] at this ⊢
      exact (mul_eq_zero.mp this).resolve_left (hpos x).ne'
    have hmem : ((fun x => (halfDens ν μ x)⁻¹) * f)
        ∈ Submodule.span ℝ {(fun _ => 1 : k → ℝ)} := by
      rw [← hker]; exact hAz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨c, funext fun x => ?_⟩
    have hcx : c = (halfDens ν μ x)⁻¹ * f x := by
      have := congrFun hc x
      simpa using this
    have hx := (hpos x).ne'
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hcx]
    field_simp
  · rintro ⟨c, rfl⟩
    have hone : A (fun _ => 1) = 0 := by
      rw [← LinearMap.mem_ker, hker]
      exact Submodule.mem_span_singleton_self _
    unfold transported
    simp only [LinearMap.coe_comp, Function.comp_apply]
    have hcanc : (mulOp fun x => (halfDens ν μ x)⁻¹) (c • halfDens ν μ)
        = c • (fun _ => 1 : k → ℝ) := by
      funext x
      simp only [mulOp, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply, Pi.smul_apply,
        smul_eq_mul]
      field_simp [(hpos x).ne']
    rw [hcanc, map_smul, hone, smul_zero, map_zero]

/-- **(YL.3, first identity)** `𝓒_h f = h (f − μ(f)𝟙)`. -/
theorem lawFollower_apply (hν : ∀ x, 0 < ν x) (hμ : ∀ x, 0 < μ x) (f : k → ℝ) :
    lawFollower ν μ f = halfDens ν μ * (f - wMean μ f • fun _ => 1) := by
  rw [lawFollower_def, wInner_halfDens_mul hν hμ]
  funext x
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  ring

/-- A trace-centred observable **need not** be orthogonal to `h`: the
explicit two-point witness (`ν` uniform, `μ = (1/4, 3/4)`, `W = 𝟙_{x=0}`). -/
theorem centered_not_orthogonal_witness :
    ∃ (ν μ W : Fin 2 → ℝ), (∀ x, 0 < ν x) ∧ (∀ x, 0 < μ x) ∧
      (∑ x, ν x = 1) ∧ (∑ x, μ x = 1) ∧
      wInner ν (W - wMean ν W • fun _ => 1) (halfDens ν μ) ≠ 0 := by
  refine ⟨![1/2, 1/2], ![1/4, 3/4], ![1, 0], ?_, ?_, ?_, ?_, ?_⟩
  · intro x; fin_cases x <;> norm_num
  · intro x; fin_cases x <;> norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h3 : (1:ℝ) < Real.sqrt 3 := by
      have : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      simpa using this
    unfold wInner wMean halfDens
    simp only [Fin.sum_univ_two]
    norm_num
    intro hcon
    have h32 : Real.sqrt 3 / Real.sqrt 2 = (Real.sqrt 2)⁻¹ * Real.sqrt 3 := by ring
    nlinarith [hcon, h2, h3, mul_pos (inv_pos.mpr h2) (lt_trans one_pos h3)]

/-- The transported centred observable is orthogonal to `h`:
`U Z_μ = h(W − μ(W)𝟙) ⊥_ν h`. -/
theorem transported_centered_orthogonal (hν : ∀ x, 0 < ν x) (hμ : ∀ x, 0 < μ x)
    (hμ1 : ∑ x, μ x = 1) (W : k → ℝ) :
    wInner ν (halfDens ν μ * (W - wMean μ W • fun _ => 1)) (halfDens ν μ) = 0 := by
  unfold wInner
  have hpt : ∀ x, ν x * ((halfDens ν μ * (W - wMean μ W • (fun _ => 1 : k → ℝ))) x
      * halfDens ν μ x) = μ x * W x - wMean μ W * μ x := by
    intro x
    have h := nu_mul_halfDens_sq (μ := μ) hν hμ x
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    linear_combination (W x - wMean μ W) * h
  rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsum : ∑ x, μ x * W x = wMean μ W := rfl
  rw [hsum, hμ1, mul_one, sub_self]

/-- **(YL.3, second identity)** `𝓒_h Z_ν = U Z_μ`: the canonical operator
carries the trace-centred observable to the transported `μ`-centred one. -/
theorem lawFollower_centered (hν : ∀ x, 0 < ν x) (hμ : ∀ x, 0 < μ x)
    (hμ1 : ∑ x, μ x = 1) (W : k → ℝ) :
    lawFollower ν μ (W - wMean ν W • fun _ => 1)
      = halfDens ν μ * (W - wMean μ W • fun _ => 1) := by
  rw [lawFollower_apply hν hμ]
  have hpt : ∀ x, μ x * (W - wMean ν W • (fun _ => 1 : k → ℝ)) x
      = μ x * W x - wMean ν W * μ x := by
    intro x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    ring
  have hmean : wMean μ (W - wMean ν W • (fun _ => 1 : k → ℝ))
      = wMean μ W - wMean ν W := by
    have h1 : wMean μ (W - wMean ν W • (fun _ => 1 : k → ℝ))
        = ∑ x, (μ x * W x - wMean ν W * μ x) :=
      Finset.sum_congr rfl fun x _ => hpt x
    rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, hμ1, mul_one]
    rfl
  rw [hmean]
  funext x
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  ring

/-- The adjoint certificate: `⟨𝓒_h f, g⟩_ν = ⟨f, M_h P_h g⟩_ν`, so
`𝓒_h^* = M_h P_h` with respect to the `ν`-pairing. -/
theorem lawFollower_adjoint (f g : k → ℝ) :
    wInner ν (lawFollower ν μ f) g = wInner ν f (lawFollowerStar ν μ g) := by
  rw [lawFollower_def, lawFollowerStar_def]
  set h := halfDens ν μ
  have hexp : h * (g - wInner ν h g • h) = h * g - wInner ν h g • (h * h) := by
    funext x
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hR2 : wInner ν f (h * h) = wInner ν h (h * f) := by
    rw [wInner_symm ν f (h * h), wInner_mul_shift]
  rw [hexp, wInner_sub_left, wInner_smul_left, wInner_sub_right, wInner_smul_right,
    wInner_mul_shift, hR2]
  ring

/-- **(YL.4, operator identity)** `𝓒_h^*𝓒_h = M_r − |r⟩⟨r|_ν`. -/
theorem lawFollower_gram (hν : ∀ x, 0 < ν x) (hμ : ∀ x, 0 < μ x)
    (hμ1 : ∑ x, μ x = 1) (f : k → ℝ) :
    lawFollowerStar ν μ (lawFollower ν μ f)
      = dens ν μ * f - wInner ν (dens ν μ) f • dens ν μ := by
  rw [lawFollower_apply hν hμ, lawFollowerStar_def]
  set h := halfDens ν μ with hh
  set Z : k → ℝ := h * (f - wMean μ f • fun _ => 1) with hZ
  have hZinner : wInner ν h Z = 0 := by
    rw [hZ, wInner_symm]
    have := transported_centered_orthogonal (ν := ν) (μ := μ) hν hμ hμ1 f
    exact this
  rw [hZinner, zero_smul, sub_zero]
  have hmean : wInner ν (dens ν μ) f = wMean μ f := by
    unfold wInner wMean dens
    refine Finset.sum_congr rfl fun x _ => ?_
    field_simp [(hν x).ne']
  rw [hmean]
  funext x
  have hsq : h x * h x = dens ν μ x := by
    rw [hh]
    unfold halfDens dens
    exact Real.mul_self_sqrt (div_nonneg (hμ x).le (hν x).le)
  rw [hZ]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  linear_combination (f x - wMean μ f) * hsq

/-- **(YL.4, norm identity)** `‖𝓒_h f‖²_ν = Var_μ(f)`; proved for every
`f` (the manuscript states it on `f ⊥ 𝟙`). -/
theorem lawFollower_norm (hν : ∀ x, 0 < ν x) (hμ : ∀ x, 0 < μ x) (f : k → ℝ) :
    wInner ν (lawFollower ν μ f) (lawFollower ν μ f)
      = ∑ x, μ x * (f x - wMean μ f) ^ 2 := by
  rw [lawFollower_apply hν hμ]
  unfold wInner
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := nu_mul_halfDens_sq (μ := μ) hν hμ x
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  linear_combination (f x - wMean μ f) ^ 2 * h

/-- **(YL.5)** With `0 < m ≤ r ≤ M`, the incidence Gram is two-sided
bounded on the `ν`-centred space: `m‖f‖² ≤ ‖𝓒_h f‖² ≤ M‖f‖²`. -/
theorem lawFollower_two_sided (hν : ∀ x, 0 < ν x) (hμ : ∀ x, 0 < μ x)
    (hν1 : ∑ x, ν x = 1) (hμ1 : ∑ x, μ x = 1) {m M : ℝ} (hm : 0 < m)
    (hlo : ∀ x, m ≤ dens ν μ x) (hhi : ∀ x, dens ν μ x ≤ M)
    (f : k → ℝ) (hf : wInner ν (fun _ => 1) f = 0) :
    m * wInner ν f f ≤ wInner ν (lawFollower ν μ f) (lawFollower ν μ f)
      ∧ wInner ν (lawFollower ν μ f) (lawFollower ν μ f) ≤ M * wInner ν f f := by
  rw [lawFollower_norm hν hμ]
  set a := wMean μ f with hadef
  have hcent : ∑ x, ν x * f x = 0 := by
    unfold wInner at hf
    calc ∑ x, ν x * f x = ∑ x, ν x * ((fun _ => 1 : k → ℝ) x * f x) := by
          refine Finset.sum_congr rfl fun x _ => by ring
      _ = 0 := hf
  have hmu_dens : ∀ x, μ x = ν x * dens ν μ x := by
    intro x
    unfold dens
    field_simp [(hν x).ne']
  constructor
  · -- lower bound: ∑ μ (f−a)² ≥ m ∑ ν (f−a)² = m(‖f‖²_ν + a²) ≥ m ‖f‖²_ν
    have step1 : ∀ x, m * (ν x * (f x - a) ^ 2) ≤ μ x * (f x - a) ^ 2 := by
      intro x
      rw [hmu_dens x]
      have := mul_le_mul_of_nonneg_right (hlo x)
        (mul_nonneg (hν x).le (sq_nonneg (f x - a)))
      nlinarith [this, (hν x).le, sq_nonneg (f x - a), hlo x]
    have hsum1 : m * ∑ x, ν x * (f x - a) ^ 2 ≤ ∑ x, μ x * (f x - a) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => step1 x
    have hnuexp : ∑ x, ν x * (f x - a) ^ 2 = wInner ν f f + a ^ 2 := by
      have hexp : ∀ x, ν x * (f x - a) ^ 2
          = ν x * (f x * f x) - 2 * a * (ν x * f x) + a ^ 2 * ν x := by
        intro x; ring
      rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hcent, hν1]
      unfold wInner
      ring
    have hquad : m * wInner ν f f ≤ m * (wInner ν f f + a ^ 2) := by nlinarith [sq_nonneg a]
    calc m * wInner ν f f ≤ m * (wInner ν f f + a ^ 2) := hquad
      _ = m * ∑ x, ν x * (f x - a) ^ 2 := by rw [hnuexp]
      _ ≤ ∑ x, μ x * (f x - a) ^ 2 := hsum1
  · -- upper bound: Var_μ(f) ≤ ∑ μ f² = ∑ ν r f² ≤ M ‖f‖²_ν
    have hvar_le : ∑ x, μ x * (f x - a) ^ 2 ≤ ∑ x, μ x * (f x * f x) := by
      have hexp : ∑ x, μ x * (f x - a) ^ 2
          = (∑ x, μ x * (f x * f x)) - 2 * a * (∑ x, μ x * f x) + a ^ 2 * ∑ x, μ x := by
        have hpt : ∀ x, μ x * (f x - a) ^ 2
            = μ x * (f x * f x) - 2 * a * (μ x * f x) + a ^ 2 * μ x := by
          intro x; ring
        rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hma : ∑ x, μ x * f x = a := rfl
      rw [hexp, hma, hμ1]
      nlinarith [sq_nonneg a]
    have hstep : ∀ x, μ x * (f x * f x) ≤ M * (ν x * (f x * f x)) := by
      intro x
      rw [hmu_dens x]
      have := mul_le_mul_of_nonneg_right (hhi x)
        (mul_nonneg (hν x).le (mul_self_nonneg (f x)))
      nlinarith [this, (hν x).le, mul_self_nonneg (f x)]
    calc ∑ x, μ x * (f x - a) ^ 2 ≤ ∑ x, μ x * (f x * f x) := hvar_le
      _ ≤ M * ∑ x, ν x * (f x * f x) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun x _ => hstep x
      _ = M * wInner ν f f := rfl

end YMLawIncidence

end LawIncidence


/-! ### `cor:YM-partition-curvature-transport` — Adjacent-cutoff transport

Rendering: a selected card at cutoff `r` is a finite positive fibre
weight `m_r` together with the three displaced action values
`F_{r,±ε}, F_{r,0}`; `Z`, `𝓡` and `Q^full` are the displayed partition
quantities of (YPC.5)/(YPC.9).  YPC.16 is the exact adjacent log-ratio
identity; the "direct adjacent bound" clause adds the two
central-difference radii and the same-carrier topological defect; the
Cauchy clause is proved from summability of the adjacent scalar defects;
the final independence clause is an explicit one-point witness with equal
normalized rows at all three displacements and different displayed
ratios. -/

section PartitionTransport

namespace YMPartitionTransport

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The partition value `Z = ∑ m·e^{-F}` of a displaced card. -/
noncomputable def partitionZ (m F : Ω → ℝ) : ℝ := ∑ z, m z * Real.exp (-F z)

/-- The assembled two-replica ratio `𝓡 = Z(ε)Z(-ε)/Z(0)²` (YPC.9). -/
noncomputable def replicaRatio (m Fp F0 Fm : Ω → ℝ) : ℝ :=
  partitionZ m Fp * partitionZ m Fm / partitionZ m F0 ^ 2

/-- The full secant curvature `Q^full = -ε⁻² log 𝓡` (YPC.9). -/
noncomputable def secantQ (ε : ℝ) (m Fp F0 Fm : Ω → ℝ) : ℝ :=
  -(ε ^ 2)⁻¹ * Real.log (replicaRatio m Fp F0 Fm)

/-- The normalized fibre row `m·e^{-F}/Z`. -/
noncomputable def normalizedRow (m F : Ω → ℝ) : Ω → ℝ :=
  fun z => m z * Real.exp (-F z) / partitionZ m F

/-- Positive weights give a positive partition value. -/
theorem partitionZ_pos {m : Ω → ℝ} (hm : ∀ z, 0 < m z) (F : Ω → ℝ) :
    0 < partitionZ m F :=
  Finset.sum_pos (fun z _ => mul_pos (hm z) (Real.exp_pos _)) Finset.univ_nonempty

/-- The two-replica ratio of a positive card is positive. -/
theorem replicaRatio_pos {m : Ω → ℝ} (hm : ∀ z, 0 < m z) (Fp F0 Fm : Ω → ℝ) :
    0 < replicaRatio m Fp F0 Fm :=
  div_pos (mul_pos (partitionZ_pos hm Fp) (partitionZ_pos hm Fm))
    (pow_pos (partitionZ_pos hm F0) 2)

/-- **(YPC.16)** Target-native adjacent-cutoff transport: for adjacent
selected cards at one common displacement,
`Q_{r+1}^full − Q_r^full = −ε⁻² log(𝓡_{r+1}/𝓡_r)`. -/
theorem adjacent_transport (ε : ℝ) {ms : ℕ → Ω → ℝ} (hm : ∀ r z, 0 < ms r z)
    (Fps F0s Fms : ℕ → Ω → ℝ) (r : ℕ) :
    secantQ ε (ms (r + 1)) (Fps (r + 1)) (F0s (r + 1)) (Fms (r + 1))
      - secantQ ε (ms r) (Fps r) (F0s r) (Fms r)
      = -(ε ^ 2)⁻¹ * Real.log
          (replicaRatio (ms (r + 1)) (Fps (r + 1)) (F0s (r + 1)) (Fms (r + 1))
            / replicaRatio (ms r) (Fps r) (F0s r) (Fms r)) := by
  unfold secantQ
  rw [Real.log_div (replicaRatio_pos (hm (r + 1)) _ _ _).ne'
    (replicaRatio_pos (hm r) _ _ _).ne']
  ring

/-- **Direct adjacent bound for the local Hessian**: the exact log-ratio
plus the two central-difference radii plus the same-carrier topological
defect bound the adjacent difference of the local coefficient
`h_r = H_r^full − t_r`. -/
theorem adjacent_local_hessian_bound (Q H t : ℕ → ℝ) (ρ : ℕ → ℝ) (r : ℕ)
    (hr : |Q r - H r| ≤ ρ r) (hr1 : |Q (r + 1) - H (r + 1)| ≤ ρ (r + 1)) :
    |(H (r + 1) - t (r + 1)) - (H r - t r)|
      ≤ |Q (r + 1) - Q r| + ρ r + ρ (r + 1) + |t (r + 1) - t r| := by
  rw [abs_le] at hr hr1
  refine abs_le.mpr ⟨?_, ?_⟩ <;>
    nlinarith [le_abs_self (Q (r + 1) - Q r), neg_abs_le (Q (r + 1) - Q r),
      le_abs_self (t (r + 1) - t r), neg_abs_le (t (r + 1) - t r),
      hr.1, hr.2, hr1.1, hr1.2]

/-- **Summability of the scalar defects makes the transported local
coefficient Cauchy** — without any convergence of the complete boundary
instrument. -/
theorem transported_coefficient_cauchy (h δ : ℕ → ℝ)
    (hb : ∀ r, |h (r + 1) - h r| ≤ δ r) (hδ : Summable δ) : CauchySeq h := by
  refine cauchySeq_of_dist_le_of_summable δ (fun n => ?_) hδ
  rw [Real.dist_eq, abs_sub_comm]
  exact hb n

/-- **Exact transport of every normalized score row does not imply
(YPC.16)**: two one-point cards with identical normalized rows at all
three displacements and different secant curvatures. -/
theorem normalized_rows_insufficient {ε : ℝ} (hε : ε ≠ 0) :
    ∃ (m Fp F0 Fm Fp' F0' Fm' : Fin 1 → ℝ), (∀ z, 0 < m z) ∧
      normalizedRow m Fp = normalizedRow m Fp' ∧
      normalizedRow m F0 = normalizedRow m F0' ∧
      normalizedRow m Fm = normalizedRow m Fm' ∧
      secantQ ε m Fp F0 Fm ≠ secantQ ε m Fp' F0' Fm' := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => 1, fun _ => 0, fun _ => 0, fun _ => one_pos, ?_, rfl, rfl, ?_⟩
  · -- one-point normalized rows are identically one
    funext z
    unfold normalizedRow partitionZ
    simp
  · have hZ : ∀ c : ℝ,
        partitionZ (Ω := Fin 1) (fun _ => (1:ℝ)) (fun _ => c) = Real.exp (-c) := by
      intro c
      unfold partitionZ
      simp
    have h1 : secantQ (Ω := Fin 1) ε (fun _ => (1:ℝ))
        (fun _ => 0) (fun _ => 0) (fun _ => 0) = 0 := by
      unfold secantQ replicaRatio
      rw [hZ]
      simp
    have h2 : secantQ (Ω := Fin 1) ε (fun _ => (1:ℝ))
        (fun _ => 1) (fun _ => 0) (fun _ => 0) = (ε ^ 2)⁻¹ := by
      unfold secantQ replicaRatio
      rw [hZ, hZ]
      simp only [neg_zero, Real.exp_zero, one_pow, div_one, mul_one]
      rw [Real.log_exp]
      ring
    rw [h1, h2]
    have : (ε ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hε)
    exact fun hcon => this hcon.symm

end YMPartitionTransport

end PartitionTransport

/-! ### Shared spectral and quadratic-form helpers for the YM incidence records

Inverse-square-root calculus for positive-definite complex matrices on
top of the repo `spectralFunction`/`psdInvSqrt` machinery, together with
the dot-product Cauchy–Schwarz inequality and congruence-form transport
used by the YSI and YSCI sections below. -/

section SharedInvSqrt

namespace YMEasy04

variable {a b : Type*} [Fintype a] [Fintype b]

/-- Dot-product Cauchy–Schwarz: `|⟨u,v⟩|² ≤ ⟨u,u⟩⟨v,v⟩`. -/
theorem dot_cauchy_schwarz (u v : a → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (star u ⬝ᵥ u).re * (star v ⬝ᵥ v).re := by
  have hre : ∀ w : a → ℂ, (star w ⬝ᵥ w).re = ∑ i, ‖w i‖ ^ 2 := by
    intro w
    rw [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hb : ‖star u ⬝ᵥ v‖ ≤ ∑ i, ‖u i‖ * ‖v i‖ := by
    rw [dotProduct]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Pi.star_apply, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖u i‖) (fun i => ‖v i‖)
  have hnn : (0:ℝ) ≤ ∑ i, ‖u i‖ * ‖v i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [hre, hre]
  calc ‖star u ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖u i‖ * ‖v i‖) ^ 2 := by
        nlinarith [hb, norm_nonneg (star u ⬝ᵥ v)]
    _ ≤ (∑ i, ‖u i‖ ^ 2) * (∑ i, ‖v i‖ ^ 2) := hcs

/-- The self-pairing of a nonzero vector has positive real part. -/
theorem dot_self_re_pos {u : a → ℂ} (hu : u ≠ 0) : 0 < (star u ⬝ᵥ u).re := by
  have hre : (star u ⬝ᵥ u).re = ∑ i, ‖u i‖ ^ 2 := by
    rw [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  rw [hre]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ i, ?_⟩
  have : (0:ℝ) < ‖u i‖ := norm_pos_iff.mpr (by simpa using hi)
  positivity

/-- A positive real is positive as a complex number. -/
theorem zero_lt_ofReal {r : ℝ} (hr : 0 < r) : (0 : ℂ) < (r : ℂ) := by
  rw [Complex.lt_def]
  constructor
  · simpa using hr
  · simp

/-- Bilinear congruence transport of a sandwiched form. -/
theorem conj_form_bilin (M : Matrix a b ℂ) (N : Matrix a a ℂ) (u v : b → ℂ) :
    star (M *ᵥ u) ⬝ᵥ (N *ᵥ (M *ᵥ v)) = star u ⬝ᵥ ((Mᴴ * N * M) *ᵥ v) := by
  rw [star_mulVec, dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]

/-- Gram transport: `⟨Mu, Mv⟩ = ⟨u, M^*M v⟩`. -/
theorem gram_form (M : Matrix a b ℂ) (u v : b → ℂ) :
    star (M *ᵥ u) ⬝ᵥ (M *ᵥ v) = star u ⬝ᵥ ((Mᴴ * M) *ᵥ v) := by
  rw [star_mulVec, dotProduct_mulVec, dotProduct_mulVec, Matrix.vecMul_vecMul]

variable [DecidableEq a] [DecidableEq b]

omit [Fintype b] [DecidableEq a] [DecidableEq b] in
/-- Hermitian sandwich of a Gram: `(Wd)^*(Wd) = d^*(WW)d` for `W^* = W`. -/
theorem sandwich_gram {W : Matrix a a ℂ} (hW : Wᴴ = W) (D : Matrix a b ℂ) :
    (W * D)ᴴ * (W * D) = Dᴴ * (W * W) * D := by
  rw [conjTranspose_mul, hW]
  simp only [Matrix.mul_assoc]

/-- `M^{-1/2} M^{-1/2} = M⁻¹` for positive-definite `M`. -/
theorem psdInvSqrt_mul_self {M : Matrix a a ℂ} (hM : M.PosDef) :
    psdInvSqrt hM.1 * psdInvSqrt hM.1 = M⁻¹ := by
  rw [posDef_inv_eq_spectral hM]
  unfold psdInvSqrt
  rw [spectralFunction_mul]
  refine spectralFunction_congr hM.1 fun i => ?_
  rw [← mul_inv, Real.mul_self_sqrt (hM.1.posDef_iff_eigenvalues_pos.mp hM i).le]

/-- The inverse square root is Hermitian. -/
theorem psdInvSqrt_isHermitian {M : Matrix a a ℂ} (hM : M.IsHermitian) :
    (psdInvSqrt hM).IsHermitian :=
  SourceAction.spectralFunction_isHermitian hM _

/-- `M^{-1/2} M M^{-1/2} = 1` for positive-definite `M`. -/
theorem psdInvSqrt_conj_cancel {M : Matrix a a ℂ} (hM : M.PosDef) :
    psdInvSqrt hM.1 * M * psdInvSqrt hM.1 = 1 := by
  have h1 : psdInvSqrt hM.1 * psdSqrt hM.1 = 1 := psdInvSqrt_mul_psdSqrt hM
  have h2 : psdSqrt hM.1 * psdInvSqrt hM.1 = 1 := psdSqrt_mul_psdInvSqrt hM
  have key : psdInvSqrt hM.1 * (psdSqrt hM.1 * psdSqrt hM.1) * psdInvSqrt hM.1 = 1 := by
    calc psdInvSqrt hM.1 * (psdSqrt hM.1 * psdSqrt hM.1) * psdInvSqrt hM.1
        = (psdInvSqrt hM.1 * psdSqrt hM.1) * (psdSqrt hM.1 * psdInvSqrt hM.1) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, h2, Matrix.mul_one]
  calc psdInvSqrt hM.1 * M * psdInvSqrt hM.1
      = psdInvSqrt hM.1 * (psdSqrt hM.1 * psdSqrt hM.1) * psdInvSqrt hM.1 := by
        rw [psdSqrt_mul_self hM.posSemidef]
    _ = 1 := key

/-- The sandwich `M^{-1/2} L M^{-1/2}` of a positive-definite `L` is
positive definite. -/
theorem posDef_conj_invSqrt {M L : Matrix a a ℂ} (hM : M.PosDef) (hL : L.PosDef) :
    (psdInvSqrt hM.1 * L * psdInvSqrt hM.1).PosDef := by
  have hWH : (psdInvSqrt hM.1)ᴴ = psdInvSqrt hM.1 := (psdInvSqrt_isHermitian hM.1).eq
  have hherm : (psdInvSqrt hM.1 * L * psdInvSqrt hM.1).IsHermitian := by
    change (psdInvSqrt hM.1 * L * psdInvSqrt hM.1)ᴴ = _
    rw [conjTranspose_mul, conjTranspose_mul, hWH, hL.1.eq]
    simp only [Matrix.mul_assoc]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun x hx => ?_
  have hform : star x ⬝ᵥ ((psdInvSqrt hM.1 * L * psdInvSqrt hM.1) *ᵥ x)
      = star (psdInvSqrt hM.1 *ᵥ x) ⬝ᵥ (L *ᵥ (psdInvSqrt hM.1 *ᵥ x)) := by
    rw [conj_form_bilin, hWH]
  have hWx : psdInvSqrt hM.1 *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    have hone : x = (psdSqrt hM.1 * psdInvSqrt hM.1) *ᵥ x := by
      rw [psdSqrt_mul_psdInvSqrt hM, one_mulVec]
    rw [hone, ← Matrix.mulVec_mulVec, h0, mulVec_zero]
  rw [hform]
  exact hL.dotProduct_mulVec_pos hWx

/-- Contraction transfer: `TT^* ≺ 1` implies `T^*T ≺ 1`. -/
theorem contraction_transfer {T : Matrix a b ℂ}
    (h : ((1 : Matrix a a ℂ) - T * Tᴴ).PosDef) :
    ((1 : Matrix b b ℂ) - Tᴴ * T).PosDef := by
  have hherm : ((1 : Matrix b b ℂ) - Tᴴ * T).IsHermitian := by
    change ((1 : Matrix b b ℂ) - Tᴴ * T)ᴴ = _
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
      conjTranspose_conjTranspose]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun x hx => ?_
  have hreal := hermitian_form_ofReal hherm x
  have hsplit : (star x ⬝ᵥ (((1 : Matrix b b ℂ) - Tᴴ * T) *ᵥ x)).re
      = (star x ⬝ᵥ x).re - (star (T *ᵥ x) ⬝ᵥ (T *ᵥ x)).re := by
    rw [sub_mulVec, dotProduct_sub, one_mulVec, gram_form, Complex.sub_re]
  set u := T *ᵥ x with hu
  have hpos : 0 < (star x ⬝ᵥ x).re - (star u ⬝ᵥ u).re := by
    by_cases hu0 : u = 0
    · rw [hu0]
      simpa using dot_self_re_pos hx
    · -- the reflected contraction bound and Cauchy–Schwarz force `‖u‖ < ‖x‖`
      have hcontr := h.dotProduct_mulVec_pos hu0
      have hcre : 0 < (star u ⬝ᵥ u).re - (star (Tᴴ *ᵥ u) ⬝ᵥ (Tᴴ *ᵥ u)).re := by
        have hs : (star u ⬝ᵥ (((1 : Matrix a a ℂ) - T * Tᴴ) *ᵥ u)).re
            = (star u ⬝ᵥ u).re - (star (Tᴴ *ᵥ u) ⬝ᵥ (Tᴴ *ᵥ u)).re := by
          have hgram : star u ⬝ᵥ ((T * Tᴴ) *ᵥ u)
              = star (Tᴴ *ᵥ u) ⬝ᵥ (Tᴴ *ᵥ u) := by
            rw [gram_form, conjTranspose_conjTranspose]
          rw [sub_mulVec, dotProduct_sub, one_mulVec, hgram, Complex.sub_re]
        rw [← hs]
        exact (Complex.lt_def.mp hcontr).1
      have hshift : star u ⬝ᵥ u = star x ⬝ᵥ (Tᴴ *ᵥ u) := by
        rw [hu, gram_form, Matrix.mulVec_mulVec]
      have hle : (star u ⬝ᵥ u).re ≤ ‖star x ⬝ᵥ (Tᴴ *ᵥ u)‖ := by
        rw [hshift]
        exact Complex.re_le_norm _
      have hcs := dot_cauchy_schwarz x (Tᴴ *ᵥ u)
      have hxpos := dot_self_re_pos hx
      have hupos := dot_self_re_pos hu0
      nlinarith [hle, hcs, hcre, hxpos, hupos,
        norm_nonneg (star x ⬝ᵥ (Tᴴ *ᵥ u))]
  rw [hreal]
  rw [hsplit] at hreal ⊢
  exact zero_lt_ofReal hpos

end YMEasy04

end SharedInvSqrt

/-! ### `lem:YM-exact-form-isometry`, `thm:YM-source-comparison-return-Pythagoras`,
`cor:YM-Ward-assembly-before-source-short`

Rendering: one finite reduced-fibre Wilson card is a finite Hodge complex
in orthonormal coordinates — `d : ℂⁿ → ℂᵉ` the differential restricted to
the centred scalar space `𝓗₀` (injective there: `d^*d ≻ 0`), `d₂` the
two-form differential with `d₂ d = 0`, and the one-form operator
`L₁ = d d^* + d₂^* d₂`, positive definite on the finite card.  The
weighted de Rham identity `L₁ d = d L₀` is then derived, not assumed.
The YMRR split `L₁ = 𝓐_η − 𝓥_η 𝓥_η^*` is given by the manuscript card
data `A ≻ 0`, `V`; `𝓚_η = V^* A⁻¹ V`, and `I − 𝓚_η ≻ 0` is derived by
the Schur/contraction argument.  The lifts (YSI.2)–(YSI.3) use the
spectral inverse square roots.  For the Ward corollary, the coarse gauge
structure is rendered by its finite mechanism: the gauge flow generator
`G` is skew-adjoint on the card (Haar/law invariance), gauge-direction
scores are orbit derivatives of transported writers (`𝓕 d₀^c = G W`),
and gauge invariance of the occurring source is `G m = 0`; YSI.14 then
follows by differentiating along the orbit exactly as in the manuscript
proof, and YSI.15 is exact scalar algebra with `a + b = 1`. -/

section SourceIncidence

namespace YMSourceIncidence

open YMEasy04

variable {n e c w q x : Type*} [Fintype n] [Fintype e] [Fintype c] [Fintype w]
  [Fintype q] [Fintype x] [DecidableEq n] [DecidableEq e] [DecidableEq w]

variable (d : Matrix e n ℂ) (d2 : Matrix c e ℂ)

/-- The one-form Hodge operator `L₁ = d₀ d₀^* + d₁^* d₁` of the card. -/
def oneFormLap : Matrix e e ℂ := d * dᴴ + d2ᴴ * d2

omit [DecidableEq n] [DecidableEq e] in
/-- The weighted de Rham identity `L₁ d = d L₀` (derived from `d₂ d = 0`). -/
theorem oneFormLap_deRham (h2 : d2 * d = 0) :
    oneFormLap d d2 * d = d * (dᴴ * d) := by
  unfold oneFormLap
  rw [Matrix.add_mul, Matrix.mul_assoc d2ᴴ, h2, Matrix.mul_zero, add_zero,
    Matrix.mul_assoc]

/-- **`lem:YM-exact-form-isometry` (YSI.1, operator form)**
`d^* L₁⁻¹ d = I` on the centred scalar space. -/
theorem exact_form_isometry_op (h2 : d2 * d = 0) (hL0 : (dᴴ * d).PosDef)
    (hL1 : (oneFormLap d d2).PosDef) :
    dᴴ * (oneFormLap d d2)⁻¹ * d = 1 := by
  have hcomm : (oneFormLap d d2)⁻¹ * d = d * (dᴴ * d)⁻¹ := by
    have h1 : oneFormLap d d2 * (d * (dᴴ * d)⁻¹) = d := by
      rw [← Matrix.mul_assoc, oneFormLap_deRham d d2 h2, Matrix.mul_assoc,
        posDef_mul_inv_cancel hL0, Matrix.mul_one]
    calc (oneFormLap d d2)⁻¹ * d
        = (oneFormLap d d2)⁻¹ * (oneFormLap d d2 * (d * (dᴴ * d)⁻¹)) := by rw [h1]
      _ = d * (dᴴ * d)⁻¹ := by
          rw [← Matrix.mul_assoc, posDef_inv_mul_cancel hL1, Matrix.one_mul]
  calc dᴴ * (oneFormLap d d2)⁻¹ * d = dᴴ * ((oneFormLap d d2)⁻¹ * d) := by
        rw [Matrix.mul_assoc]
    _ = dᴴ * (d * (dᴴ * d)⁻¹) := by rw [hcomm]
    _ = dᴴ * d * (dᴴ * d)⁻¹ := by rw [Matrix.mul_assoc]
    _ = 1 := posDef_mul_inv_cancel hL0

/-- **`lem:YM-exact-form-isometry` (YSI.1)**
`⟨df, L₁⁻¹ dg⟩_ν = ⟨f, g⟩_ν` for all centred scalars `f, g`. -/
theorem exact_form_isometry (h2 : d2 * d = 0) (hL0 : (dᴴ * d).PosDef)
    (hL1 : (oneFormLap d d2).PosDef) (f g : n → ℂ) :
    star (d *ᵥ f) ⬝ᵥ ((oneFormLap d d2)⁻¹ *ᵥ (d *ᵥ g)) = star f ⬝ᵥ g := by
  rw [conj_form_bilin, exact_form_isometry_op d d2 h2 hL0 hL1, one_mulVec]

/-- **`lem:YM-exact-form-isometry` (equivalent form)**: `L₁^{-1/2} d` is an
isometry from the centred scalar space onto its exact one-form range. -/
theorem exact_form_lift_isometry (h2 : d2 * d = 0) (hL0 : (dᴴ * d).PosDef)
    (hL1 : (oneFormLap d d2).PosDef) :
    (psdInvSqrt hL1.1 * d)ᴴ * (psdInvSqrt hL1.1 * d) = 1 := by
  rw [sandwich_gram (psdInvSqrt_isHermitian hL1.1).eq, psdInvSqrt_mul_self hL1]
  exact exact_form_isometry_op d d2 h2 hL0 hL1

variable (A : Matrix e e ℂ) (V : Matrix e w ℂ)

/-- The source-cyclic return Gram `𝓚_η = 𝓥^* 𝓐⁻¹ 𝓥` (YMRR.15). -/
noncomputable def returnGram : Matrix w w ℂ := Vᴴ * A⁻¹ * V

omit [DecidableEq n] in
/-- On the finite card, `I − 𝓚_η` is positive definite: the Schur
complement `L₁ = 𝓐 − 𝓥𝓥^* ≻ 0` forces the strict contraction. -/
theorem one_sub_returnGram_posDef (hA : A.PosDef) (hL1 : (oneFormLap d d2).PosDef)
    (hAV : oneFormLap d d2 = A - V * Vᴴ) :
    ((1 : Matrix w w ℂ) - returnGram A V).PosDef := by
  have hWAH : (psdInvSqrt hA.1)ᴴ = psdInvSqrt hA.1 := (psdInvSqrt_isHermitian hA.1).eq
  have hT : returnGram A V = (psdInvSqrt hA.1 * V)ᴴ * (psdInvSqrt hA.1 * V) := by
    unfold returnGram
    rw [conjTranspose_mul, hWAH, ← psdInvSqrt_mul_self hA]
    simp only [Matrix.mul_assoc]
  have hVV : (psdInvSqrt hA.1 * V) * (psdInvSqrt hA.1 * V)ᴴ
      = psdInvSqrt hA.1 * (V * Vᴴ) * psdInvSqrt hA.1 := by
    rw [conjTranspose_mul, hWAH]
    simp only [Matrix.mul_assoc]
  have hcong : (1 : Matrix e e ℂ) - (psdInvSqrt hA.1 * V) * (psdInvSqrt hA.1 * V)ᴴ
      = psdInvSqrt hA.1 * oneFormLap d d2 * psdInvSqrt hA.1 := by
    rw [hAV, Matrix.mul_sub, Matrix.sub_mul, hVV, psdInvSqrt_conj_cancel hA]
  have hpos : ((1 : Matrix e e ℂ)
      - (psdInvSqrt hA.1 * V) * (psdInvSqrt hA.1 * V)ᴴ).PosDef := by
    rw [hcong]
    exact posDef_conj_invSqrt hA hL1
  rw [hT]
  exact contraction_transfer hpos

omit [DecidableEq n] in
/-- **Woodbury resolution of the one-form inverse**:
`L₁⁻¹ = 𝓐⁻¹ + 𝓐⁻¹𝓥 (I−𝓚)⁻¹ 𝓥^*𝓐⁻¹`. -/
theorem woodbury (hA : A.PosDef)
    (hAV : oneFormLap d d2 = A - V * Vᴴ)
    (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef) :
    (oneFormLap d d2)⁻¹
      = A⁻¹ + A⁻¹ * V * (1 - returnGram A V)⁻¹ * Vᴴ * A⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [hAV]
  have hAinv : A⁻¹ * A = 1 := posDef_inv_mul_cancel hA
  have hIKinv : (1 - returnGram A V)⁻¹ * (1 - returnGram A V) = 1 :=
    posDef_inv_mul_cancel hIK
  have hstep1 : Vᴴ * A⁻¹ * (A - V * Vᴴ) = (1 - returnGram A V) * Vᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul]
    congr 1
    · rw [Matrix.mul_assoc, hAinv, Matrix.mul_one]
    · unfold returnGram
      simp only [Matrix.mul_assoc]
  have hstep2 : (1 - returnGram A V)⁻¹ * (Vᴴ * A⁻¹ * (A - V * Vᴴ)) = Vᴴ := by
    rw [hstep1, ← Matrix.mul_assoc, hIKinv, Matrix.one_mul]
  calc (A⁻¹ + A⁻¹ * V * (1 - returnGram A V)⁻¹ * Vᴴ * A⁻¹) * (A - V * Vᴴ)
      = A⁻¹ * (A - V * Vᴴ)
        + A⁻¹ * (V * ((1 - returnGram A V)⁻¹ * (Vᴴ * A⁻¹ * (A - V * Vᴴ)))) := by
        rw [Matrix.add_mul]
        congr 1
        simp only [Matrix.mul_assoc]
    _ = (1 - A⁻¹ * (V * Vᴴ)) + A⁻¹ * (V * Vᴴ) := by
        rw [hstep2, Matrix.mul_sub, hAinv]
    _ = 1 := sub_add_cancel _ _

/-- The comparison lift `𝓤_η^A = 𝓐^{-1/2} d` (YSI.2). -/
noncomputable def liftA (hA : A.PosDef) : Matrix e n ℂ := psdInvSqrt hA.1 * d

/-- The return lift `𝓤_η^R = (I−𝓚)^{-1/2} 𝓥^* 𝓐⁻¹ d` (YSI.2). -/
noncomputable def liftR (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef) :
    Matrix w n ℂ :=
  psdInvSqrt hIK.1 * (Vᴴ * (A⁻¹ * d))

omit [Fintype n] [DecidableEq n] in
/-- The comparison-lift Gram is `d^* 𝓐⁻¹ d`. -/
theorem liftA_gram (hA : A.PosDef) :
    (liftA d A hA)ᴴ * liftA d A hA = dᴴ * A⁻¹ * d := by
  unfold liftA
  rw [sandwich_gram (psdInvSqrt_isHermitian hA.1).eq, psdInvSqrt_mul_self hA]

omit [Fintype n] [DecidableEq n] in
/-- The return-lift Gram is `d^* (𝓐⁻¹𝓥 (I−𝓚)⁻¹ 𝓥^*𝓐⁻¹) d`. -/
theorem liftR_gram (hA : A.PosDef)
    (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef) :
    (liftR d A V hIK)ᴴ * liftR d A V hIK
      = dᴴ * (A⁻¹ * V * (1 - returnGram A V)⁻¹ * Vᴴ * A⁻¹) * d := by
  unfold liftR
  rw [sandwich_gram (psdInvSqrt_isHermitian hIK.1).eq, psdInvSqrt_mul_self hIK]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    (hA.1.inv).eq]
  simp only [Matrix.mul_assoc]

/-- **`thm:YM-source-comparison-return-Pythagoras` (YSI.4, operator form)**
`(𝓤^A)^*𝓤^A + (𝓤^R)^*𝓤^R = I` on the centred scalar space. -/
theorem comparison_return_pythagoras_op (h2 : d2 * d = 0) (hL0 : (dᴴ * d).PosDef)
    (hA : A.PosDef) (hL1 : (oneFormLap d d2).PosDef)
    (hAV : oneFormLap d d2 = A - V * Vᴴ)
    (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef) :
    (liftA d A hA)ᴴ * liftA d A hA + (liftR d A V hIK)ᴴ * liftR d A V hIK = 1 := by
  rw [liftA_gram d A hA, liftR_gram d A V hA hIK]
  calc dᴴ * A⁻¹ * d + dᴴ * (A⁻¹ * V * (1 - returnGram A V)⁻¹ * Vᴴ * A⁻¹) * d
      = dᴴ * (A⁻¹ + A⁻¹ * V * (1 - returnGram A V)⁻¹ * Vᴴ * A⁻¹) * d := by
        rw [Matrix.mul_add, Matrix.add_mul]
    _ = dᴴ * (oneFormLap d d2)⁻¹ * d := by rw [← woodbury d d2 A V hA hAV hIK]
    _ = 1 := exact_form_isometry_op d d2 h2 hL0 hL1

/-- **`thm:YM-source-comparison-return-Pythagoras` (YSI.4)**: for all
centred scalars `f, g`,
`⟨f,g⟩_ν = ⟨𝓤^A f, 𝓤^A g⟩ + ⟨𝓤^R f, 𝓤^R g⟩`. -/
theorem comparison_return_pythagoras (h2 : d2 * d = 0) (hL0 : (dᴴ * d).PosDef)
    (hA : A.PosDef) (hL1 : (oneFormLap d d2).PosDef)
    (hAV : oneFormLap d d2 = A - V * Vᴴ)
    (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef) (f g : n → ℂ) :
    star (liftA d A hA *ᵥ f) ⬝ᵥ (liftA d A hA *ᵥ g)
      + star (liftR d A V hIK *ᵥ f) ⬝ᵥ (liftR d A V hIK *ᵥ g)
      = star f ⬝ᵥ g := by
  rw [gram_form, gram_form, ← dotProduct_add, ← Matrix.add_mulVec,
    comparison_return_pythagoras_op d d2 A V h2 hL0 hA hL1 hAV hIK, one_mulVec]

omit [Fintype q] in
/-- **`thm:YM-source-comparison-return-Pythagoras` (YSI.5)**: the mode-score
Gram splits as `𝓕^*𝓕 = Q_A^*Q_A + Q_R^*Q_R` with `Q_A = 𝓤^A 𝓕`,
`Q_R = 𝓤^R 𝓕` (YSI.3). -/
theorem score_gram_split (h2 : d2 * d = 0) (hL0 : (dᴴ * d).PosDef)
    (hA : A.PosDef) (hL1 : (oneFormLap d d2).PosDef)
    (hAV : oneFormLap d d2 = A - V * Vᴴ)
    (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef) (F : Matrix n q ℂ) :
    Fᴴ * F = (liftA d A hA * F)ᴴ * (liftA d A hA * F)
      + (liftR d A V hIK * F)ᴴ * (liftR d A V hIK * F) := by
  have hkey := comparison_return_pythagoras_op d d2 A V h2 hL0 hA hL1 hAV hIK
  calc Fᴴ * F = Fᴴ * (1 : Matrix n n ℂ) * F := by rw [Matrix.mul_one]
    _ = Fᴴ * ((liftA d A hA)ᴴ * liftA d A hA
        + (liftR d A V hIK)ᴴ * liftR d A V hIK) * F := by rw [hkey]
    _ = (liftA d A hA * F)ᴴ * (liftA d A hA * F)
        + (liftR d A V hIK * F)ᴴ * (liftR d A V hIK * F) := by
        rw [Matrix.mul_add, Matrix.add_mul, conjTranspose_mul, conjTranspose_mul]
        simp only [Matrix.mul_assoc]

omit [Fintype q] [DecidableEq n] in
/-- **`thm:YM-source-comparison-return-Pythagoras` (return identification)**:
`Q_R^*Q_R` is precisely the return matrix
`𝕃_η^ret(q) = 𝓑^*L₁⁻¹𝓑 − 𝓑^*𝓐⁻¹𝓑` with `𝓑 = d𝓕` (YMRR.12). -/
theorem return_matrix_identification (hA : A.PosDef)
    (hAV : oneFormLap d d2 = A - V * Vᴴ)
    (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef) (F : Matrix n q ℂ) :
    (liftR d A V hIK * F)ᴴ * (liftR d A V hIK * F)
      = (d * F)ᴴ * (oneFormLap d d2)⁻¹ * (d * F)
        - (d * F)ᴴ * A⁻¹ * (d * F) := by
  have hsub : (oneFormLap d d2)⁻¹ - A⁻¹
      = A⁻¹ * V * (1 - returnGram A V)⁻¹ * Vᴴ * A⁻¹ := by
    rw [woodbury d d2 A V hA hAV hIK]
    exact add_sub_cancel_left _ _
  calc (liftR d A V hIK * F)ᴴ * (liftR d A V hIK * F)
      = Fᴴ * ((liftR d A V hIK)ᴴ * liftR d A V hIK) * F := by
        rw [conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Fᴴ * (dᴴ * ((oneFormLap d d2)⁻¹ - A⁻¹) * d) * F := by
        rw [liftR_gram d A V hA hIK, hsub]
    _ = (d * F)ᴴ * (oneFormLap d d2)⁻¹ * (d * F) - (d * F)ᴴ * A⁻¹ * (d * F) := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul,
          conjTranspose_mul]
        simp only [Matrix.mul_assoc]

/-! #### `cor:YM-Ward-assembly-before-source-short` -/

/-- The total mixed row `y(g) = ⟨m, 𝓕 g⟩` (YSI.7). -/
def rowY (F : Matrix n q ℂ) (m : n → ℂ) (g : q → ℂ) : ℂ := star m ⬝ᵥ (F *ᵥ g)

/-- The comparison-arm mixed row `x_A(g) = ⟨s_A, Q_A g⟩` (YSI.7). -/
noncomputable def rowXA (hA : A.PosDef) (F : Matrix n q ℂ) (m : n → ℂ)
    (g : q → ℂ) : ℂ :=
  star (liftA d A hA *ᵥ m) ⬝ᵥ (liftA d A hA *ᵥ (F *ᵥ g))

/-- The return-arm mixed row `x_R(g) = ⟨s_R, Q_R g⟩` (YSI.7). -/
noncomputable def rowXR (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef)
    (F : Matrix n q ℂ) (m : n → ℂ) (g : q → ℂ) : ℂ :=
  star (liftR d A V hIK *ᵥ m) ⬝ᵥ (liftR d A V hIK *ᵥ (F *ᵥ g))

/-- The comparison arm energy `a = ‖s_A‖²` (YSI.6). -/
noncomputable def armA (hA : A.PosDef) (m : n → ℂ) : ℝ :=
  (star (liftA d A hA *ᵥ m) ⬝ᵥ (liftA d A hA *ᵥ m)).re

/-- The return arm energy `b = ‖s_R‖²` (YSI.6). -/
noncomputable def armR (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef)
    (m : n → ℂ) : ℝ :=
  (star (liftR d A V hIK *ᵥ m) ⬝ᵥ (liftR d A V hIK *ᵥ m)).re

/-- The comparison score energy `C_A[g] = ‖Q_A g‖²`. -/
noncomputable def energyA (hA : A.PosDef) (F : Matrix n q ℂ) (g : q → ℂ) : ℝ :=
  (star (liftA d A hA *ᵥ (F *ᵥ g)) ⬝ᵥ (liftA d A hA *ᵥ (F *ᵥ g))).re

/-- The return score energy `C_R[g] = ‖Q_R g‖²`. -/
noncomputable def energyR (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef)
    (F : Matrix n q ℂ) (g : q → ℂ) : ℝ :=
  (star (liftR d A V hIK *ᵥ (F *ᵥ g)) ⬝ᵥ (liftR d A V hIK *ᵥ (F *ᵥ g))).re

/-- The route dispersion `Δ_route = |√(b/a)x_A − √(a/b)x_R|²` (YSI.13). -/
noncomputable def routeDispersion (a b : ℝ) (xA xR : ℂ) : ℝ :=
  Complex.normSq ((Real.sqrt (b / a) : ℂ) * xA - (Real.sqrt (a / b) : ℂ) * xR)

/-- The source-shorted residual quadratic form
`𝕀_∂^{sc|src}[g] = C_A[g] + C_R[g] − |y(g)|²` (YSI.11). -/
noncomputable def scResidual (hA : A.PosDef)
    (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef)
    (F : Matrix n q ℂ) (m : n → ℂ) (g : q → ℂ) : ℝ :=
  energyA d A hA F g + energyR d A V hIK F g - Complex.normSq (rowY F m g)

/-- **(YSI.8)** The mixed rows assemble: `x_A(g) + x_R(g) = y(g)` for every
score direction (the Pythagoras identity polarized at `(m, 𝓕g)`). -/
theorem arm_row_assembly (h2 : d2 * d = 0) (hL0 : (dᴴ * d).PosDef)
    (hA : A.PosDef) (hL1 : (oneFormLap d d2).PosDef)
    (hAV : oneFormLap d d2 = A - V * Vᴴ)
    (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef)
    (F : Matrix n q ℂ) (m : n → ℂ) (g : q → ℂ) :
    rowXA d A hA F m g + rowXR d A V hIK F m g = rowY F m g :=
  comparison_return_pythagoras d d2 A V h2 hL0 hA hL1 hAV hIK m (F *ᵥ g)

/-- **(YSI.6)** The arm energies of a unit occurring source add to one:
`a + b = 1`. -/
theorem arm_energy_sum (h2 : d2 * d = 0) (hL0 : (dᴴ * d).PosDef)
    (hA : A.PosDef) (hL1 : (oneFormLap d d2).PosDef)
    (hAV : oneFormLap d d2 = A - V * Vᴴ)
    (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef)
    (m : n → ℂ) (hm : star m ⬝ᵥ m = 1) :
    armA d A hA m + armR d A V hIK m = 1 := by
  have hpyth := comparison_return_pythagoras d d2 A V h2 hL0 hA hL1 hAV hIK m m
  rw [hm] at hpyth
  have := congrArg Complex.re hpyth
  rw [Complex.add_re] at this
  simpa [armA, armR] using this

omit [DecidableEq n] in
/-- **(YSI.14, first half)** A gauge-invariant occurring source has zero
total row along every coarse gauge direction: `y(d₀^c ξ) = 0`. -/
theorem ward_row_zero (F : Matrix n q ℂ) (m : n → ℂ) (G : Matrix n n ℂ)
    (W : Matrix n x ℂ) (d0c : Matrix q x ℂ) (hGskew : Gᴴ = -G)
    (hgauge : F * d0c = G * W) (hminv : G *ᵥ m = 0) (ξ : x → ℂ) :
    rowY F m (d0c *ᵥ ξ) = 0 := by
  unfold rowY
  rw [Matrix.mulVec_mulVec, hgauge, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
  have hstar : star m ᵥ* G = star (Gᴴ *ᵥ m) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  rw [hstar, hGskew, Matrix.neg_mulVec, hminv, neg_zero, star_zero,
    zero_dotProduct]

/-- **(YSI.14, second half)** Along a coarse gauge direction the two arm
rows cancel exactly: `x_A(g) + x_R(g) = 0`. -/
theorem ward_arm_cancellation (h2 : d2 * d = 0) (hL0 : (dᴴ * d).PosDef)
    (hA : A.PosDef) (hL1 : (oneFormLap d d2).PosDef)
    (hAV : oneFormLap d d2 = A - V * Vᴴ)
    (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef)
    (F : Matrix n q ℂ) (m : n → ℂ) (G : Matrix n n ℂ)
    (W : Matrix n x ℂ) (d0c : Matrix q x ℂ) (hGskew : Gᴴ = -G)
    (hgauge : F * d0c = G * W) (hminv : G *ᵥ m = 0) (ξ : x → ℂ) :
    rowXA d A hA F m (d0c *ᵥ ξ) + rowXR d A V hIK F m (d0c *ᵥ ξ) = 0 := by
  rw [arm_row_assembly d d2 A V h2 hL0 hA hL1 hAV hIK,
    ward_row_zero F m G W d0c hGskew hgauge hminv]

/-- **(YSI.15, first identity, scalar form)** With `a, b > 0`, `a + b = 1`
and cancelling rows `x_A + x_R = 0`, the route dispersion is
`Δ_route = |x_A|²/a + |x_R|²/b`. -/
theorem route_dispersion_of_cancelling {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) {xA xR : ℂ} (hsum : xA + xR = 0) :
    routeDispersion a b xA xR
      = Complex.normSq xA / a + Complex.normSq xR / b := by
  have hxR : xR = -xA := by linear_combination hsum
  subst hxR
  unfold routeDispersion
  rw [mul_neg, sub_neg_eq_add, ← add_mul, Complex.normSq_mul, Complex.normSq_neg]
  have hcoe : ((Real.sqrt (b / a) : ℂ) + (Real.sqrt (a / b) : ℂ))
      = ((Real.sqrt (b / a) + Real.sqrt (a / b) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcoe, Complex.normSq_ofReal]
  have hsq : (Real.sqrt (b / a) + Real.sqrt (a / b))
      * (Real.sqrt (b / a) + Real.sqrt (a / b)) = 1 / a + 1 / b := by
    have h1 : Real.sqrt (b / a) * Real.sqrt (b / a) = b / a :=
      Real.mul_self_sqrt (by positivity)
    have h2 : Real.sqrt (a / b) * Real.sqrt (a / b) = a / b :=
      Real.mul_self_sqrt (by positivity)
    have h3 : Real.sqrt (b / a) * Real.sqrt (a / b) = 1 := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show b / a * (a / b) = 1 by field_simp]
      exact Real.sqrt_one
    have hexp : (Real.sqrt (b / a) + Real.sqrt (a / b))
        * (Real.sqrt (b / a) + Real.sqrt (a / b))
        = Real.sqrt (b / a) * Real.sqrt (b / a)
          + 2 * (Real.sqrt (b / a) * Real.sqrt (a / b))
          + Real.sqrt (a / b) * Real.sqrt (a / b) := by ring
    rw [hexp, h1, h2, h3]
    field_simp
    linear_combination (a + b) * hab
  rw [hsq]
  ring

omit [DecidableEq n] in
/-- **(YSI.15, second identity)** Along a coarse gauge direction the
source-shorted residual is the assembled arm energy:
`𝕀_∂^{sc|src}[g] = C_A[g] + C_R[g]`. -/
theorem ward_assembled_residual (hA : A.PosDef)
    (hIK : ((1 : Matrix w w ℂ) - returnGram A V).PosDef)
    (F : Matrix n q ℂ) (m : n → ℂ) (G : Matrix n n ℂ)
    (W : Matrix n x ℂ) (d0c : Matrix q x ℂ) (hGskew : Gᴴ = -G)
    (hgauge : F * d0c = G * W) (hminv : G *ᵥ m = 0) (ξ : x → ℂ) :
    scResidual d A V hA hIK F m (d0c *ᵥ ξ)
      = energyA d A hA F (d0c *ᵥ ξ) + energyR d A V hIK F (d0c *ᵥ ξ) := by
  unfold scResidual
  rw [ward_row_zero F m G W d0c hGskew hgauge hminv, Complex.normSq_zero, sub_zero]

/-- **Separate shorting subtracts the positive route dispersion**: shorting
the two arms separately (YSI.10) and adding differs from the assembled
short by exactly `Δ_route ≥ 0`; an arm-by-arm short would therefore
create an artificial follower from a cancellation carried by one source. -/
theorem separate_short_gap {a b CA CR : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) {xA xR y : ℂ} (hsum : xA + xR = y) (hy : y = 0) :
    (CA + CR - Complex.normSq y)
        - ((CA - Complex.normSq xA / a) + (CR - Complex.normSq xR / b))
      = routeDispersion a b xA xR
      ∧ 0 ≤ routeDispersion a b xA xR := by
  subst hy
  rw [route_dispersion_of_cancelling ha hb hab hsum]
  constructor
  · rw [Complex.normSq_zero]
    ring
  · exact add_nonneg (div_nonneg (Complex.normSq_nonneg _) ha.le)
      (div_nonneg (Complex.normSq_nonneg _) hb.le)

end YMSourceIncidence

end SourceIncidence

/-! ### `thm:YM-source-current-incidence` and `cth:YM-source-current-marginals`

Rendering: the supported curvature-source coefficient space, occurring
space, and reduced current fibre are finite-dimensional in orthonormal
coordinates; the half-score synthesis is `S` with `ℂ^src = S^*S ≻ 0`
(YSCI.1); the routed minimum Witten current is `𝓙 = 𝓡 Q` with
`Q = L₁^{-1/2} 𝓑 (ℂ^src)^{-1/2}` (YSCI.2) for a declared route `𝓡`.
The same-history Gram, ancestry residual, positivity, and vanishing
criterion are (YSCI.3)–(YSCI.4).  The rank clause is rendered exactly:
the residual rank is the least `r` such that the routed current factors
through the normalized source range plus `r` additional response-source
directions.  The countertheorem is the manuscript's explicit
`E = ℝ, 𝓗 = ℝ²` witness (YSCI.5). -/

section SourceCurrent

namespace YMSourceCurrent

open YMEasy04

variable {p u z : Type*} [Fintype p] [DecidableEq p] [Fintype u] [DecidableEq u]
  [Fintype z] [DecidableEq z]

/-- The source-normalized isometry `𝓢̃ = 𝓢 (ℂ^src)^{-1/2}` (YSCI.1). -/
noncomputable def srcNormalized (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef) :
    Matrix u p ℂ :=
  S * psdInvSqrt hC.1

/-- The current synthesis `Q = L₁^{-1/2} 𝓑 (ℂ^src)^{-1/2}` (YSCI.2). -/
noncomputable def currentSynth (L1 : Matrix z z ℂ) (hL1 : L1.PosDef)
    (B : Matrix z p ℂ) {S : Matrix u p ℂ} (hC : (Sᴴ * S).PosDef) : Matrix z p ℂ :=
  psdInvSqrt hL1.1 * B * psdInvSqrt hC.1

/-- The routed current `𝓙 = 𝓡 Q` through a declared source-faithful route. -/
noncomputable def routedCurrent (R : Matrix u z ℂ) (L1 : Matrix z z ℂ)
    (hL1 : L1.PosDef) (B : Matrix z p ℂ) {S : Matrix u p ℂ}
    (hC : (Sᴴ * S).PosDef) : Matrix u p ℂ :=
  R * currentSynth L1 hL1 B hC

/-- The normalized source range projection `P = 𝓢̃ 𝓢̃^*`. -/
noncomputable def srcProj (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef) :
    Matrix u u ℂ :=
  srcNormalized S hC * (srcNormalized S hC)ᴴ

/-- The ancestry residual `𝕀^{cur|src} = K − X^*X` (YSCI.4). -/
noncomputable def ancestryResidual (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef)
    (J : Matrix u p ℂ) : Matrix p p ℂ :=
  Jᴴ * J - ((srcNormalized S hC)ᴴ * J)ᴴ * ((srcNormalized S hC)ᴴ * J)

omit [DecidableEq u] in
/-- **(YSCI.1)** The normalized source is an isometry: `𝓢̃^*𝓢̃ = I`. -/
theorem srcNormalized_isometry (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef) :
    (srcNormalized S hC)ᴴ * srcNormalized S hC = 1 := by
  unfold srcNormalized
  calc (S * psdInvSqrt hC.1)ᴴ * (S * psdInvSqrt hC.1)
      = psdInvSqrt hC.1 * (Sᴴ * S) * psdInvSqrt hC.1 := by
        rw [conjTranspose_mul, (psdInvSqrt_isHermitian hC.1).eq]
        simp only [Matrix.mul_assoc]
    _ = 1 := psdInvSqrt_conj_cancel hC

/-- The two-column synthesis `(𝓢̃, 𝓙)` of the same-history pair. -/
noncomputable def pairSynth (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef)
    (J : Matrix u p ℂ) : Matrix u (p ⊕ p) ℂ :=
  Matrix.of fun i s => Sum.elim (fun j => srcNormalized S hC i j) (fun j => J i j) s

omit [DecidableEq u] in
/-- The same-history Gram is the Gram of the pair `(𝓢̃, 𝓙)`. -/
theorem pairSynth_gram (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef)
    (J : Matrix u p ℂ) :
    (pairSynth S hC J)ᴴ * pairSynth S hC J
      = Matrix.fromBlocks ((srcNormalized S hC)ᴴ * srcNormalized S hC)
          ((srcNormalized S hC)ᴴ * J) (Jᴴ * srcNormalized S hC) (Jᴴ * J) := by
  ext s t
  rcases s with j | j <;> rcases t with j' | j' <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, pairSynth]

omit [DecidableEq u] in
/-- **(YSCI.3)** The same-history Gram
`𝔾 = [[I, X],[X^*, K]]` is positive semidefinite. -/
theorem same_history_gram_posSemidef (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef)
    (J : Matrix u p ℂ) :
    (Matrix.fromBlocks 1 ((srcNormalized S hC)ᴴ * J)
      (((srcNormalized S hC)ᴴ * J)ᴴ) (Jᴴ * J)).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (pairSynth S hC J)
  rw [pairSynth_gram, srcNormalized_isometry] at h
  have hX : Jᴴ * srcNormalized S hC = ((srcNormalized S hC)ᴴ * J)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rwa [hX] at h

omit [DecidableEq u] in
/-- The source projection is Hermitian and idempotent. -/
theorem srcProj_projection (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef) :
    (srcProj S hC)ᴴ = srcProj S hC ∧ srcProj S hC * srcProj S hC = srcProj S hC := by
  constructor
  · unfold srcProj
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  · unfold srcProj
    calc srcNormalized S hC * (srcNormalized S hC)ᴴ
          * (srcNormalized S hC * (srcNormalized S hC)ᴴ)
        = srcNormalized S hC
          * ((srcNormalized S hC)ᴴ * srcNormalized S hC) * (srcNormalized S hC)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = srcNormalized S hC * (srcNormalized S hC)ᴴ := by
          rw [srcNormalized_isometry, Matrix.mul_one]

/-- The complement of the source projection is idempotent. -/
theorem srcProj_complement_idem (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef) :
    (1 - srcProj S hC) * (1 - srcProj S hC) = 1 - srcProj S hC := by
  obtain ⟨_, hPP⟩ := srcProj_projection S hC
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP]
  abel

/-- The residual compression factors through the complement:
`𝓙^*(I−P)𝓙 = ((I−P)𝓙)^*((I−P)𝓙)`. -/
theorem complement_compression (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef)
    (J : Matrix u p ℂ) :
    Jᴴ * (1 - srcProj S hC) * J
      = ((1 - srcProj S hC) * J)ᴴ * ((1 - srcProj S hC) * J) := by
  obtain ⟨hPh, _⟩ := srcProj_projection S hC
  rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPh]
  conv_rhs => rw [← Matrix.mul_assoc, Matrix.mul_assoc Jᴴ,
    srcProj_complement_idem S hC]

/-- **(YSCI.4, identity)** The ancestry residual is the compression of the
routed current by the complement of the source range:
`K − X^*X = 𝓙^*(I − P)𝓙`. -/
theorem ancestryResidual_eq (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef)
    (J : Matrix u p ℂ) :
    ancestryResidual S hC J = Jᴴ * (1 - srcProj S hC) * J := by
  unfold ancestryResidual srcProj
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  congr 1
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- **(YSCI.4, positivity)** The ancestry residual is positive
semidefinite. -/
theorem ancestryResidual_posSemidef (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef)
    (J : Matrix u p ℂ) : (ancestryResidual S hC J).PosSemidef := by
  rw [ancestryResidual_eq, complement_compression]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **(YSCI.4, vanishing)** The residual vanishes exactly when the routed
current is a deterministic follower of the occurring reflected source:
`𝕀^{cur|src} = 0 ↔ 𝓙 = 𝓢̃ X`. -/
theorem ancestryResidual_eq_zero_iff (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef)
    (J : Matrix u p ℂ) :
    ancestryResidual S hC J = 0
      ↔ J = srcNormalized S hC * ((srcNormalized S hC)ᴴ * J) := by
  rw [ancestryResidual_eq, complement_compression,
    Matrix.conjTranspose_mul_self_eq_zero]
  constructor
  · intro h0
    have hJ : J - srcProj S hC * J = 0 := by
      rwa [Matrix.sub_mul, Matrix.one_mul] at h0
    have hJ' : J = srcProj S hC * J := sub_eq_zero.mp hJ
    conv_lhs => rw [hJ']
    unfold srcProj
    simp only [Matrix.mul_assoc]
  · intro hJ
    rw [Matrix.sub_mul, Matrix.one_mul]
    have hfix : srcProj S hC * J = J := by
      conv_rhs => rw [hJ]
      unfold srcProj
      simp only [Matrix.mul_assoc]
    rw [hfix, sub_self]

omit [Fintype u] [DecidableEq u] in
/-- Rank factorization: any matrix factors through `Fin rank` columns. -/
theorem rank_factorization (N : Matrix u p ℂ) :
    ∃ (T : Matrix u (Fin N.rank) ℂ) (Y : Matrix (Fin N.rank) p ℂ), N = T * Y := by
  have bas : Module.Basis (Fin N.rank) ℂ (LinearMap.range N.mulVecLin) :=
    Module.finBasis ℂ (LinearMap.range N.mulVecLin)
  have hmem : ∀ k : p, N *ᵥ Pi.single k 1 ∈ LinearMap.range N.mulVecLin :=
    fun k => ⟨Pi.single k 1, by rw [Matrix.mulVecLin_apply]⟩
  refine ⟨Matrix.of fun i j => (bas j : u → ℂ) i,
    Matrix.of fun j k => bas.repr ⟨N *ᵥ Pi.single k 1, hmem k⟩ j, ?_⟩
  ext i k
  have hrepr := bas.sum_repr ⟨N *ᵥ Pi.single k 1, hmem k⟩
  have hval := congrFun (congrArg Subtype.val hrepr) i
  simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at hval
  have hcol : (N *ᵥ Pi.single k 1) i = N i k := by
    simp [Matrix.mulVec_single]
  rw [Matrix.mul_apply]
  rw [← hcol, ← hval]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  ring

/-- **(YSCI.4, rank minimality)** The residual rank is the least number of
additional response-source directions: the minimum `r` such that the
routed current factors as `𝓙 = 𝓢̃ X' + T Y` with `r` extra columns. -/
theorem ancestryResidual_rank_least (S : Matrix u p ℂ) (hC : (Sᴴ * S).PosDef)
    (J : Matrix u p ℂ) :
    IsLeast {r : ℕ | ∃ (T : Matrix u (Fin r) ℂ) (Y : Matrix (Fin r) p ℂ)
        (X' : Matrix p p ℂ), J = srcNormalized S hC * X' + T * Y}
      (ancestryResidual S hC J).rank := by
  obtain ⟨hPh, hPP⟩ := srcProj_projection S hC
  set N : Matrix u p ℂ := (1 - srcProj S hC) * J with hN
  have hfact : ancestryResidual S hC J = Nᴴ * N := by
    rw [ancestryResidual_eq, complement_compression, hN]
  have hrank : (ancestryResidual S hC J).rank = N.rank := by
    rw [hfact, Matrix.rank_conjTranspose_mul_self]
  have hkill : (1 - srcProj S hC) * srcNormalized S hC = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    unfold srcProj
    rw [Matrix.mul_assoc, srcNormalized_isometry, Matrix.mul_one, sub_self]
  constructor
  · -- the residual rank is attained: rank-factor the complement compression
    rw [hrank]
    obtain ⟨T, Y, hTY⟩ := rank_factorization N
    refine ⟨T, Y, (srcNormalized S hC)ᴴ * J, ?_⟩
    rw [← hTY, hN, Matrix.sub_mul, Matrix.one_mul]
    unfold srcProj
    simp only [Matrix.mul_assoc]
    abel
  · -- no factorization can use fewer directions
    rintro r ⟨T, Y, X', hJ⟩
    rw [hrank]
    have hN' : N = (1 - srcProj S hC) * (T * Y) := by
      rw [hN, hJ, Matrix.mul_add, ← Matrix.mul_assoc, hkill, Matrix.zero_mul,
        zero_add]
    calc N.rank = ((1 - srcProj S hC) * (T * Y)).rank := by rw [hN']
      _ ≤ (T * Y).rank := Matrix.rank_mul_le_right _ _
      _ ≤ T.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin r) := Matrix.rank_le_card_width T
      _ = r := Fintype.card_fin r

end YMSourceCurrent

/-! ### `cth:YM-source-current-marginals` — Marginals do not determine incidence

The manuscript's explicit witness: `E = ℝ`, `𝓗 = ℝ²`, `𝓢(1) = e₁`, with
the two current cards `𝓙₀(1) = e₁` and `𝓙₁(1) = e₂` (YSCI.5).  Both
cards have identical source and current marginals `I = K = 1`, but the
mixed blocks and ancestry residuals differ. -/

namespace YMSourceCurrentMarginals

/-- The witness source synthesis `𝓢(1) = e₁`. -/
def witS : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The first current card `𝓙₀(1) = e₁`. -/
def witJ0 : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The second current card `𝓙₁(1) = e₂`. -/
def witJ1 : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The source marginal is `I = 1`, so `𝓢` is already normalized. -/
theorem wit_source_marginal : witSᵀ * witS = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [witS, Matrix.mul_apply, Fin.sum_univ_two]

/-- **(YSCI.5, marginals)** The two current cards have identical current
marginals `K₀ = K₁ = 1`. -/
theorem wit_current_marginals : witJ0ᵀ * witJ0 = 1 ∧ witJ1ᵀ * witJ1 = 1 := by
  constructor <;>
  · ext i j
    fin_cases i
    fin_cases j
    simp [witJ0, witJ1, Matrix.mul_apply, Fin.sum_univ_two]

/-- **(YSCI.5, mixed blocks)** `X₀ = 1` and `X₁ = 0`: the mixed
same-history blocks differ. -/
theorem wit_mixed_blocks : witSᵀ * witJ0 = 1 ∧ witSᵀ * witJ1 = 0 := by
  constructor <;>
  · ext i j
    fin_cases i
    fin_cases j
    simp [witS, witJ0, witJ1, Matrix.mul_apply, Fin.sum_univ_two]

/-- **(YSCI.5, residuals)** `𝕀₀^{cur|src} = 0` while `𝕀₁^{cur|src} = 1`:
separate outward intervals for the marginals cannot replace the mixed
same-history block. -/
theorem wit_residuals :
    witJ0ᵀ * witJ0 - (witSᵀ * witJ0)ᵀ * (witSᵀ * witJ0) = 0
      ∧ witJ1ᵀ * witJ1 - (witSᵀ * witJ1)ᵀ * (witSᵀ * witJ1) = 1 := by
  constructor <;>
  · ext i j
    fin_cases i
    fin_cases j
    simp [witS, witJ0, witJ1, Matrix.mul_apply, Fin.sum_univ_two]

/-- The witness conclusion: identical marginals, different incidence. -/
theorem marginals_do_not_determine_incidence :
    witSᵀ * witS = 1 ∧ witJ0ᵀ * witJ0 = witJ1ᵀ * witJ1
      ∧ witJ0ᵀ * witJ0 - (witSᵀ * witJ0)ᵀ * (witSᵀ * witJ0)
        ≠ witJ1ᵀ * witJ1 - (witSᵀ * witJ1)ᵀ * (witSᵀ * witJ1) := by
  refine ⟨wit_source_marginal, ?_, ?_⟩
  · rw [wit_current_marginals.1, wit_current_marginals.2]
  · rw [wit_residuals.1, wit_residuals.2]
    intro hcon
    have := congrFun (congrFun hcon 0) 0
    simp at this

end YMSourceCurrentMarginals

end SourceCurrent

/-! ### `cth:YM-geometric-not-source-reserve` — Geometric vs source reserve

Rendering: on one curvature fibre (any nonempty finite carrier) take
`ℚ_n = I` and `ℂ_n = nI` (YS.23).  The geometric reserve
`λ_min(ℚ_n) = 1` and the source-normalized reserve
`λ_min(ℂ_n^{-1/2} ℚ_n ℂ_n^{-1/2}) = n⁻¹ → 0` are rendered as attained
`IsGreatest` Loewner floors; the normalized-reserve matrix is computed
for every positive-semidefinite square root `W` of `ℂ_n⁻¹` (and such a
root is exhibited). -/

section GeometricReserve

namespace YMSourceReserve

open YMEasy04

variable {k : Type*} [Fintype k] [DecidableEq k] [Nonempty k]

omit [DecidableEq k] [Nonempty k] in
/-- The self-pairing has nonnegative real part. -/
theorem dot_self_re_nonneg (x : k → ℂ) : 0 ≤ (star x ⬝ᵥ x).re := by
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

omit [Nonempty k] in
/-- A nonnegative real multiple of the identity is PSD. -/
theorem smul_one_posSemidef {cs : ℝ} (hc : 0 ≤ cs) :
    ((cs : ℂ) • (1 : Matrix k k ℂ)).PosSemidef := by
  have hherm : ((cs : ℂ) • (1 : Matrix k k ℂ)).IsHermitian := by
    change ((cs : ℂ) • (1 : Matrix k k ℂ))ᴴ = _
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  rw [smul_mulVec, one_mulVec, dotProduct_smul]
  have hx : star x ⬝ᵥ x = ((star x ⬝ᵥ x).re : ℂ) := by
    have h := hermitian_form_ofReal (Matrix.isHermitian_one (n := k) (α := ℂ)) x
    rwa [one_mulVec] at h
  rw [hx, smul_eq_mul, ← Complex.ofReal_mul]
  rw [Complex.le_def]
  constructor
  · simpa using mul_nonneg hc (dot_self_re_nonneg x)
  · simp

/-- A real multiple of the identity is PSD exactly for nonnegative
multipliers. -/
theorem smul_one_posSemidef_iff (cs : ℝ) :
    ((cs : ℂ) • (1 : Matrix k k ℂ)).PosSemidef ↔ 0 ≤ cs := by
  constructor
  · intro h
    have hx := h.dotProduct_mulVec_nonneg (Pi.single (Classical.arbitrary k) 1)
    rw [smul_mulVec, one_mulVec, dotProduct_smul] at hx
    have hdot : star (Pi.single (Classical.arbitrary k) (1:ℂ))
        ⬝ᵥ Pi.single (Classical.arbitrary k) 1 = 1 := by
      rw [dotProduct_single]
      simp
    rw [hdot, smul_eq_mul, mul_one] at hx
    exact (Complex.le_def.mp hx).1
  · exact smul_one_posSemidef

/-- The least Rayleigh floor of `c·I` is exactly `c`: the scalar
eigenvalue as an attained `IsGreatest`. -/
theorem scalar_lambda_min (cs : ℝ) :
    IsGreatest {δ : ℝ | ((cs : ℂ) • (1 : Matrix k k ℂ)
      - (δ : ℂ) • 1).PosSemidef} cs := by
  have hkey : ∀ δ : ℝ, (cs : ℂ) • (1 : Matrix k k ℂ) - (δ : ℂ) • 1
      = ((cs - δ : ℝ) : ℂ) • 1 := by
    intro δ
    push_cast
    rw [sub_smul]
  constructor
  · change ((cs : ℂ) • (1 : Matrix k k ℂ) - (cs : ℂ) • 1).PosSemidef
    rw [hkey, sub_self]
    simpa using smul_one_posSemidef (k := k) (le_refl 0)
  · intro δ hδ
    have h : (((cs - δ : ℝ) : ℂ) • (1 : Matrix k k ℂ)).PosSemidef := by
      rw [← hkey δ]
      exact hδ
    have := (smul_one_posSemidef_iff (cs - δ)).mp h
    linarith

/-- **(YS.23, geometric reserve)** The geometric reserve of `ℚ_n = I` is
one, uniformly in the cutoff. -/
theorem geometric_reserve_one :
    IsGreatest {δ : ℝ | ((1 : Matrix k k ℂ) - (δ : ℂ) • 1).PosSemidef} 1 := by
  have h := scalar_lambda_min (k := k) 1
  simpa using h

omit [Nonempty k] in
/-- The inverse of `ℂ_n = nI`. -/
theorem scaled_identity_inv (n : ℕ) (hn : 1 ≤ n) :
    (((n : ℝ) : ℂ) • (1 : Matrix k k ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) • 1 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    ← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity : ((n:ℝ)) ≠ 0)]
  simp

omit [Nonempty k] in
/-- **(YS.23, normalized reserve matrix)** For every square root `W` of
`ℂ_n⁻¹`, the source-normalized head is `W ℚ_n W = n⁻¹ I`. -/
theorem source_normalized_head (n : ℕ) (hn : 1 ≤ n) (W : Matrix k k ℂ)
    (hW : W * W = (((n : ℝ) : ℂ) • (1 : Matrix k k ℂ))⁻¹) :
    W * (1 : Matrix k k ℂ) * W = (((n : ℝ)⁻¹ : ℝ) : ℂ) • 1 := by
  rw [Matrix.mul_one, hW, scaled_identity_inv n hn]

omit [Nonempty k] in
/-- A PSD square root of `ℂ_n⁻¹` exists: `W = (√n)⁻¹ I`. -/
theorem invSqrt_witness (n : ℕ) (hn : 1 ≤ n) :
    ∃ W : Matrix k k ℂ, W.PosSemidef
      ∧ W * W = (((n : ℝ) : ℂ) • (1 : Matrix k k ℂ))⁻¹ := by
  refine ⟨(((Real.sqrt n)⁻¹ : ℝ) : ℂ) • 1, smul_one_posSemidef (by positivity), ?_⟩
  rw [scaled_identity_inv n hn, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    smul_smul, ← Complex.ofReal_mul,
    ← mul_inv, Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ (n:ℝ))]

/-- **(YS.23, collapse)** `λ_min(ℂ_n^{-1/2}ℚ_nℂ_n^{-1/2}) = n⁻¹`. -/
theorem normalized_reserve_eq (n : ℕ) :
    IsGreatest {δ : ℝ | ((((n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix k k ℂ)
      - (δ : ℂ) • 1).PosSemidef} (n : ℝ)⁻¹ :=
  scalar_lambda_min (k := k) ((n : ℝ)⁻¹)

/-- **(YS.23, limit)** The source-normalized reserve `n⁻¹` tends to zero:
a cutoff-uniform curvature sign does not supply a cutoff-uniform
source-normalized reserve. -/
theorem reserve_collapse :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds 0) := by
  simpa [one_div] using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)

end YMSourceReserve

end GeometricReserve

/-! ### `cth:YM-identity-metric-artifact` — Diffusive identity collapse

Rendering: the Bloch fibre of the Maxwell head at momentum `k` on the
scalar colour component (the `⊗ I_𝔤` factor acts as the identity): the
curl `d₁(k)` is the displayed pair matrix, the two-form pairing carries
the antisymmetry factor `1/2`, so `d₁^*d₁ = ω·1 − δδ^*` (YS.7 on
one-forms) and the curvature representative
`ω⁻² d₁ (d₁^*d₁) d₁^*` acts as the identity on the exact curvature range
(YS.16).  At the lowest axial momentum `k = (2π/M,0,0)` the restriction
of `d₁^*d₁` to the transverse fibre `𝓣_k = Ker d₀(k)^*` has least
eigenvalue exactly `ω(k) = 4 sin²(π/M) → 0` (YS.24). -/

section MaxwellHead

namespace YMMaxwellHead

/-- The Bloch curl `d₁(k) : A ↦ (δ_i A_j − δ_j A_i)` (YS.4). -/
def curlMatrix (δ : Fin 3 → ℂ) : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  Matrix.of fun ij l =>
    δ ij.1 * (if l = ij.2 then 1 else 0) - δ ij.2 * (if l = ij.1 then 1 else 0)

/-- The gauge-invariant Maxwell head `d₁^*d₁ = ω·1 − δδ^*` on one-forms. -/
noncomputable def maxwellHead (δ : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (star δ ⬝ᵥ δ) • 1 - Matrix.vecMulVec δ (star δ)

/-- The curl Gram with the antisymmetric two-form pairing:
`d₁ᴴ d₁ = 2(ω·1 − δδ^*)`, i.e. `d₁^*d₁ = ω·1 − δδ^*` in the halved
two-form metric. -/
theorem curl_gram (δ : Fin 3 → ℂ) :
    (curlMatrix δ)ᴴ * curlMatrix δ = (2 : ℂ) • maxwellHead δ := by
  ext l m
  fin_cases l <;> fin_cases m <;>
    · simp [curlMatrix, maxwellHead, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.vecMulVec_apply,
        dotProduct]
      ring

/-- The curl annihilates the gradient direction: `d₁ δ = 0`
(the complex identity `d₁ d₀ = 0` on the Bloch fibre, YS.6). -/
theorem curl_kills_gradient (δ : Fin 3 → ℂ) : curlMatrix δ *ᵥ δ = 0 := by
  have key : ∀ (av : ℂ) (t : Fin 3),
      (∑ x, (av * if x = t then 1 else 0) * δ x) = av * δ t := by
    intro av t
    have hcongr : ∀ x ∈ Finset.univ, (av * if x = t then 1 else 0) * δ x
        = if x = t then av * δ x else 0 := by
      intro x _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hcongr,
      Finset.sum_ite_eq' Finset.univ t fun x => av * δ x]
    simp
  funext ij
  simp only [curlMatrix, Matrix.mulVec, Matrix.of_apply, dotProduct, sub_mul,
    Finset.sum_sub_distrib, Pi.zero_apply]
  rw [key, key]
  ring

/-- The curl annihilates the rank-one gradient block. -/
theorem curl_mul_vecMulVec (δ : Fin 3 → ℂ) :
    curlMatrix δ * Matrix.vecMulVec δ (star δ) = 0 := by
  ext ij m
  have hz := congrFun (curl_kills_gradient δ) ij
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hz
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  calc ∑ l, curlMatrix δ ij l * (δ l * star δ m)
      = (∑ l, curlMatrix δ ij l * δ l) * star δ m := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = 0 := by rw [hz, zero_mul]

/-- The curl intertwines the Maxwell head with the scalar `ω`:
`d₁ (ω·1 − δδ^*) = ω d₁`. -/
theorem curl_mul_maxwellHead (δ : Fin 3 → ℂ) :
    curlMatrix δ * maxwellHead δ = (star δ ⬝ᵥ δ) • curlMatrix δ := by
  unfold maxwellHead
  rw [Matrix.mul_sub, curl_mul_vecMulVec, sub_zero, Matrix.mul_smul,
    Matrix.mul_one]

/-- Rank-one action on a vector: `(δδ^*) A = ⟨δ, A⟩ δ`. -/
theorem vecMulVec_mulVec (δ A : Fin 3 → ℂ) :
    Matrix.vecMulVec δ (star δ) *ᵥ A = (star δ ⬝ᵥ A) • δ := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- On the transverse fibre `𝓣_k = Ker d₀^*` the Maxwell head acts as
the diffusive scalar: `(ω·1 − δδ^*) A = ω A` for `⟨δ, A⟩ = 0`. -/
theorem maxwellHead_transverse (δ A : Fin 3 → ℂ) (hA : star δ ⬝ᵥ A = 0) :
    maxwellHead δ *ᵥ A = (star δ ⬝ᵥ δ) • A := by
  unfold maxwellHead
  rw [Matrix.sub_mulVec, vecMulVec_mulVec, hA, zero_smul, sub_zero, smul_mulVec,
    one_mulVec]

/-- The curvature representative `ω⁻² d₁ (d₁^*d₁) d₁^*` (YS.16), with the
halved two-form pairing giving `d₁^* = (1/2)d₁ᴴ`. -/
noncomputable def curvatureRep (δ : Fin 3 → ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  ((star δ ⬝ᵥ δ) ^ 2)⁻¹
    • (curlMatrix δ * maxwellHead δ * ((1 / 2 : ℂ) • (curlMatrix δ)ᴴ))

/-- **The curvature representative is exactly the identity** on the exact
curvature range `𝓩_k = Ran d₁`: `ℚ (d₁ A) = d₁ A` — unit curvature
reserve at every cutoff. -/
theorem curvatureRep_identity (δ : Fin 3 → ℂ) (hω : star δ ⬝ᵥ δ ≠ 0)
    (A : Fin 3 → ℂ) :
    curvatureRep δ *ᵥ (curlMatrix δ *ᵥ A) = curlMatrix δ *ᵥ A := by
  have hDH : curlMatrix δ * maxwellHead δ * ((1 / 2 : ℂ) • (curlMatrix δ)ᴴ)
      = ((star δ ⬝ᵥ δ) * (1 / 2)) • (curlMatrix δ * (curlMatrix δ)ᴴ) := by
    rw [curl_mul_maxwellHead, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hDDD' : curlMatrix δ * (curlMatrix δ)ᴴ * curlMatrix δ
      = (2 * (star δ ⬝ᵥ δ)) • curlMatrix δ := by
    rw [Matrix.mul_assoc, curl_gram, Matrix.mul_smul, curl_mul_maxwellHead,
      smul_smul]
  have hDDD : (curlMatrix δ * (curlMatrix δ)ᴴ) *ᵥ (curlMatrix δ *ᵥ A)
      = (2 * (star δ ⬝ᵥ δ)) • (curlMatrix δ *ᵥ A) := by
    rw [Matrix.mulVec_mulVec, hDDD', smul_mulVec]
  unfold curvatureRep
  rw [hDH, smul_mulVec, smul_mulVec, hDDD, smul_smul, smul_smul]
  have hs : ((star δ ⬝ᵥ δ) ^ 2)⁻¹ * ((star δ ⬝ᵥ δ) * (1 / 2))
      * (2 * (star δ ⬝ᵥ δ)) = 1 := by
    field_simp
  rw [hs, one_smul]

/-- The lowest axial Bloch multiplier `δ(2π/M,0,0)`. -/
noncomputable def axialDelta (M : ℕ) : Fin 3 → ℂ :=
  ![Complex.exp ((2 * Real.pi / M : ℝ) * Complex.I) - 1, 0, 0]

/-- The axial diffusive factor: `ω(2π/M,0,0) = 4 sin²(π/M)`. -/
theorem axial_omega (M : ℕ) :
    star (axialDelta M) ⬝ᵥ axialDelta M
      = ((4 * Real.sin (Real.pi / M) ^ 2 : ℝ) : ℂ) := by
  set θ : ℝ := 2 * Real.pi / M with hθ
  have hval : star (axialDelta M) ⬝ᵥ axialDelta M
      = ((Complex.normSq (Complex.exp ((θ : ℝ) * Complex.I) - 1) : ℝ) : ℂ) := by
    unfold axialDelta
    rw [dotProduct, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.star_apply]
    rw [← hθ]
    simp [Complex.normSq_eq_conj_mul_self]
  rw [hval]
  congr 1
  have hre : (Complex.exp ((θ : ℝ) * Complex.I)).re = Real.cos θ :=
    Complex.exp_ofReal_mul_I_re θ
  have him : (Complex.exp ((θ : ℝ) * Complex.I)).im = Real.sin θ :=
    Complex.exp_ofReal_mul_I_im θ
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hre, him]
  have hθ2 : θ = 2 * (Real.pi / M) := by rw [hθ]; ring
  have hcos : Real.cos θ = Real.cos (Real.pi / M) ^ 2 - Real.sin (Real.pi / M) ^ 2 := by
    rw [hθ2, Real.cos_two_mul']
  have hpy := Real.sin_sq_add_cos_sq (Real.pi / M)
  have hpyθ := Real.sin_sq_add_cos_sq θ
  simp only [Complex.one_re, Complex.one_im]
  nlinarith [hcos, hpy, hpyθ]

/-- The second axial component vanishes. -/
theorem axialDelta_one (M : ℕ) : axialDelta M 1 = 0 := rfl

/-- **(YS.24)** At the lowest axial momentum the restriction of the
Maxwell head to the transverse fibre has least eigenvalue exactly
`4 sin²(π/M)` — the diffusive factor `ω(k)`, not a colour gap. -/
theorem maxwell_lowest_axial (M : ℕ) :
    IsLeast {μ : ℝ | ∃ A : Fin 3 → ℂ, A ≠ 0 ∧ star (axialDelta M) ⬝ᵥ A = 0
        ∧ maxwellHead (axialDelta M) *ᵥ A = ((μ : ℝ) : ℂ) • A}
      (4 * Real.sin (Real.pi / M) ^ 2) := by
  constructor
  · refine ⟨Pi.single 1 1, ?_, ?_, ?_⟩
    · intro hcon
      have := congrFun hcon 1
      simp at this
    · rw [dotProduct_single]
      simp [axialDelta_one]
    · rw [maxwellHead_transverse _ _ (by rw [dotProduct_single]; simp [axialDelta_one]),
        axial_omega]
  · rintro μ ⟨A, hA0, hAt, hAe⟩
    have heig := maxwellHead_transverse (axialDelta M) A hAt
    rw [axial_omega] at heig
    rw [heig] at hAe
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hA0
    have hcoord := congrFun hAe i
    simp only [Pi.smul_apply, smul_eq_mul] at hcoord
    have hAi : A i ≠ 0 := by simpa using hi
    have hval : ((4 * Real.sin (Real.pi / M) ^ 2 : ℝ) : ℂ) = ((μ : ℝ) : ℂ) :=
      mul_right_cancel₀ hAi hcoord
    have := Complex.ofReal_inj.mp hval
    linarith

/-- **(YS.24, collapse)** The identity floor `4 sin²(π/M)` vanishes as
`M → ∞`: the sequence has unit curvature reserve but no uniform
identity-metric floor. -/
theorem diffusive_collapse :
    Filter.Tendsto (fun M : ℕ => 4 * Real.sin (Real.pi / M) ^ 2)
      Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun M : ℕ => Real.pi / M) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat Real.pi
  have h2 : Filter.Tendsto (fun M : ℕ => Real.sin (Real.pi / M))
      Filter.atTop (nhds 0) := by
    have hcomp := (Real.continuous_sin.tendsto 0).comp h1
    rw [Real.sin_zero] at hcomp
    exact Filter.Tendsto.congr (fun M => rfl) hcomp
  have h3 := (h2.pow 2).const_mul (4 : ℝ)
  simpa using h3

end YMMaxwellHead

end MaxwellHead

/-! ### `lem:YM-Wilson-separator` — Canonical Wilson separator

Rendering: a finite periodic lattice card is a finite link set `E`, a
finite plaquette set `P` with boundary-link map `bd : P → Finset E`
(nonempty boundaries, every link on some plaquette), and a source
contour carrier `X ⊆ E`.  The plaquette collar (WBM.1) is generated
iteratively — `𝓟₀` the plaquettes incident with `X`, `𝓟_{R+1}` the
plaquettes incident with a radius-`R` collar link — which is the
plaquette-distance collar; `Σ_{N,R}` is the displayed separating shell
(WBM.2), and the Wilson action is any sum of plaquette-local terms.
(S1)–(S3) are the displayed set inclusions and (S4) is the exact split
(WBM.3) with the two locality clauses. -/

section WilsonSeparator

namespace YMWilsonSeparator

variable {E P : Type*} [Fintype E] [Fintype P] [DecidableEq E] [DecidableEq P]

variable (bd : P → Finset E) (X : Finset E)

/-- The links of a plaquette family. -/
def collarLinks (s : Finset P) : Finset E := s.biUnion bd

/-- The plaquette collar `𝓟_{N,R}^□` (WBM.1), generated iteratively. -/
def collar : ℕ → Finset P
  | 0 => Finset.univ.filter fun pq => (bd pq ∩ X).Nonempty
  | R + 1 => Finset.univ.filter fun pq =>
      (bd pq ∩ collarLinks bd (collar R)).Nonempty

/-- The separating link shell `Σ_{N,R}` (WBM.2). -/
def shell (R : ℕ) : Finset E :=
  (collarLinks bd (collar bd X R)).filter fun e =>
    ∃ pq, pq ∉ collar bd X R ∧ e ∈ bd pq

/-- The interior links `𝓘_{N,R} = 𝓛_{N,R} \ Σ_{N,R}`. -/
def interior (R : ℕ) : Finset E := collarLinks bd (collar bd X R) \ shell bd X R

/-- The exterior links `𝓞_{N,R} = 𝓔_N \ 𝓛_{N,R}`. -/
def exterior (R : ℕ) : Finset E := (collarLinks bd (collar bd X R))ᶜ

omit [Fintype E] [DecidableEq P] in
/-- Collar membership at successor radius. -/
theorem mem_collar_succ {pq : P} {R : ℕ} :
    pq ∈ collar bd X (R + 1)
      ↔ (bd pq ∩ collarLinks bd (collar bd X R)).Nonempty := by
  simp only [collar, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype E] [DecidableEq P] in
/-- The collar is monotone in the radius. -/
theorem collar_mono (hbd : ∀ pq, (bd pq).Nonempty) (R : ℕ) :
    collar bd X R ⊆ collar bd X (R + 1) := by
  intro pq hp
  rw [mem_collar_succ]
  obtain ⟨e, he⟩ := hbd pq
  exact ⟨e, Finset.mem_inter.mpr ⟨he, Finset.mem_biUnion.mpr ⟨pq, hp, he⟩⟩⟩

omit [Fintype E] [DecidableEq P] in
/-- The radius-zero collar sits in every collar. -/
theorem collar_zero_subset (hbd : ∀ pq, (bd pq).Nonempty) (R : ℕ) :
    collar bd X 0 ⊆ collar bd X R := by
  induction R with
  | zero => exact Finset.Subset.refl _
  | succ R ih => exact ih.trans (collar_mono bd X hbd R)

omit [Fintype E] in
/-- **(S1)** The source contour lies in the interior:
`X_N^□ ⊆ 𝓘_{N,R}`. -/
theorem source_subset_interior (hbd : ∀ pq, (bd pq).Nonempty)
    (hcov : ∀ e : E, ∃ pq, e ∈ bd pq) (R : ℕ) : X ⊆ interior bd X R := by
  intro e he
  obtain ⟨pq, hpq⟩ := hcov e
  have hp0 : pq ∈ collar bd X 0 := by
    simp only [collar, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, Finset.mem_inter.mpr ⟨hpq, he⟩⟩
  have hpR : pq ∈ collar bd X R := collar_zero_subset bd X hbd R hp0
  rw [interior, Finset.mem_sdiff]
  constructor
  · exact Finset.mem_biUnion.mpr ⟨pq, hpR, hpq⟩
  · intro hcon
    rw [shell, Finset.mem_filter] at hcon
    obtain ⟨-, q, hq, heq⟩ := hcon
    have hq0 : q ∈ collar bd X 0 := by
      simp only [collar, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, Finset.mem_inter.mpr ⟨heq, he⟩⟩
    exact hq (collar_zero_subset bd X hbd R hq0)

/-- **(S2)** No plaquette contains both an interior and an exterior
link. -/
theorem no_mixed_plaquette (R : ℕ) (pq : P) :
    ¬((bd pq ∩ interior bd X R).Nonempty ∧ (bd pq ∩ exterior bd X R).Nonempty) := by
  rintro ⟨⟨e1, he1⟩, ⟨e2, he2⟩⟩
  rw [Finset.mem_inter] at he1 he2
  by_cases hp : pq ∈ collar bd X R
  · have : e2 ∈ collarLinks bd (collar bd X R) :=
      Finset.mem_biUnion.mpr ⟨pq, hp, he2.1⟩
    have hcon := he2.2
    rw [exterior, Finset.mem_compl] at hcon
    exact hcon this
  · have hin := he1.2
    rw [interior, Finset.mem_sdiff] at hin
    refine hin.2 ?_
    rw [shell, Finset.mem_filter]
    exact ⟨hin.1, pq, hp, he1.1⟩

/-- **(S3)** The next shell lies in the current exterior:
`Σ_{N,R+1} ⊆ 𝓞_{N,R}`. -/
theorem shell_nesting (R : ℕ) : shell bd X (R + 1) ⊆ exterior bd X R := by
  intro e he
  rw [shell, Finset.mem_filter] at he
  obtain ⟨-, q, hq, heq⟩ := he
  rw [exterior, Finset.mem_compl]
  intro hcon
  refine hq ?_
  rw [mem_collar_succ]
  exact ⟨e, Finset.mem_inter.mpr ⟨heq, hcon⟩⟩

variable {G : Type*} (act : P → (E → G) → ℝ)

/-- The Wilson action `A_N = ∑_p a_p`. -/
noncomputable def wilsonAction (σ : E → G) : ℝ := ∑ pq, act pq σ

/-- The interior action `A_{N,R}^in` (plaquettes in the collar). -/
noncomputable def actionIn (R : ℕ) (σ : E → G) : ℝ :=
  ∑ pq ∈ collar bd X R, act pq σ

/-- The exterior action `A_{N,R}^out` (plaquettes off the collar). -/
noncomputable def actionOut (R : ℕ) (σ : E → G) : ℝ :=
  ∑ pq ∈ (collar bd X R)ᶜ, act pq σ

omit [Fintype E] in
/-- **(S4, split)** The exact decomposition
`A_N = A_{N,R}^in + A_{N,R}^out` (WBM.3). -/
theorem action_split (R : ℕ) (σ : E → G) :
    wilsonAction act σ = actionIn bd X act R σ + actionOut bd X act R σ :=
  (Finset.sum_add_sum_compl (collar bd X R) _).symm

omit [Fintype E] in
/-- **(S4, interior locality)** The interior action depends only on
interior and shell links. -/
theorem actionIn_local
    (hloc : ∀ pq σ τ, (∀ e ∈ bd pq, σ e = τ e) → act pq σ = act pq τ)
    (R : ℕ) (σ τ : E → G)
    (hagree : ∀ e ∈ interior bd X R ∪ shell bd X R, σ e = τ e) :
    actionIn bd X act R σ = actionIn bd X act R τ := by
  refine Finset.sum_congr rfl fun pq hp => hloc pq σ τ fun e he => ?_
  refine hagree e ?_
  have hlink : e ∈ collarLinks bd (collar bd X R) := Finset.mem_biUnion.mpr ⟨pq, hp, he⟩
  rw [interior, Finset.mem_union, Finset.mem_sdiff]
  by_cases hs : e ∈ shell bd X R
  · exact Or.inr hs
  · exact Or.inl ⟨hlink, hs⟩

/-- **(S4, exterior locality)** The exterior action depends only on shell
and exterior links. -/
theorem actionOut_local
    (hloc : ∀ pq σ τ, (∀ e ∈ bd pq, σ e = τ e) → act pq σ = act pq τ)
    (R : ℕ) (σ τ : E → G)
    (hagree : ∀ e ∈ shell bd X R ∪ exterior bd X R, σ e = τ e) :
    actionOut bd X act R σ = actionOut bd X act R τ := by
  refine Finset.sum_congr rfl fun pq hp => hloc pq σ τ fun e he => ?_
  rw [Finset.mem_compl] at hp
  refine hagree e ?_
  rw [Finset.mem_union]
  by_cases hl : e ∈ collarLinks bd (collar bd X R)
  · refine Or.inl ?_
    rw [shell, Finset.mem_filter]
    exact ⟨hl, pq, hp, he⟩
  · refine Or.inr ?_
    rw [exterior, Finset.mem_compl]
    exact hl

end YMWilsonSeparator

end WilsonSeparator

end NCG
