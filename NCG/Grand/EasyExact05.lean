/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EasyExact04

/-!
# Easy exact records, batch 05 (Gran-Tensor manuscript, final YM cluster)

Exact formalizations of the following manuscript records:

* `prop:YM-boundary-replica-acquisition` — the three scalar replica
  queries (WBM.12) reconstruct the complete boundary Gram, and the
  source short is evaluated from the queries without pointwise message
  reconstruction.
* `cor:YM-native-descendant-collapse` — the conditional Pythagoras
  collapse (YNC.6), record contractivity (YNC.7), and the rescaling
  cost `b_N² p_N(β_N) ≥ v_*/3030750000`.
* `cth:YM-cutoff-radial-independent` — the explicit finite product
  model with prescribed cutoff residual and radial ratio.
* `cor:YM-radial-four-leaf` — the positive four-leaf radial reads
  (YMBR.14) and the Creutz ratio identity (YMBR.15).
* `cor:YM-seventeen-loss` — the strict finite-card source–geometry
  incompatibility (YMBL.14)–(YMBL.15).
* `lem:YM-rational-face-certificate` — the rational optimum-face
  complementary-slackness certificate.
* `cth:YM-kernel-collapse-soft-direction` — absolute kernel collapse
  with surviving normalized soft direction (YMFG.25).

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset Filter
open scoped Topology

namespace NCG

/-! ### Shared machinery: conditional expectation on a finite weighted carrier

The records of this batch condition finite writers on finite records.
`FiberCondExp.condMean μ q f t` is the `μ`-average of `f` over the fiber
`{q = t}` and `FiberCondExp.condExp μ q f` is the associated conditional
expectation; for strictly positive weights it is the `μ`-orthogonal
projection onto record-measurable functions, giving the exact Pythagoras
and contraction identities used by the records below. -/

section FiberCondExpSection

namespace FiberCondExp

variable {Ω : Type*} [Fintype Ω] {T : Type*} [DecidableEq T]

/-- Weighted mean `∑ μ·f`. -/
def wmean (μ f : Ω → ℝ) : ℝ := ∑ x, μ x * f x

/-- Weighted squared `L²` norm `∑ μ·f²`. -/
def wsq (μ f : Ω → ℝ) : ℝ := ∑ x, μ x * f x ^ 2

/-- The centred writer `f - ∑ μ·f`. -/
def centered (μ f : Ω → ℝ) : Ω → ℝ := fun x => f x - wmean μ f

/-- Weighted variance: the squared norm of the centred writer. -/
def wvar (μ f : Ω → ℝ) : ℝ := wsq μ (centered μ f)

/-- The squared norm is nonnegative for nonnegative weights. -/
theorem wsq_nonneg {μ : Ω → ℝ} (hμ : ∀ x, 0 ≤ μ x) (f : Ω → ℝ) : 0 ≤ wsq μ f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (sq_nonneg _)

/-- The variance is nonnegative for nonnegative weights. -/
theorem wvar_nonneg {μ : Ω → ℝ} (hμ : ∀ x, 0 ≤ μ x) (f : Ω → ℝ) : 0 ≤ wvar μ f :=
  wsq_nonneg hμ _

/-- Variance of a deterministic rescaling: `Var(b·f) = b²·Var(f)`. -/
theorem wvar_const_mul (μ f : Ω → ℝ) (b : ℝ) :
    wvar μ (fun x => b * f x) = b ^ 2 * wvar μ f := by
  unfold wvar wsq centered wmean
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hm : ∑ y, μ y * (b * f y) = b * ∑ y, μ y * f y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hm]
  ring

/-- Conditional fiber mean of `f` given the record value `t`. -/
noncomputable def condMean (μ : Ω → ℝ) (q : Ω → T) (f : Ω → ℝ) (t : T) : ℝ :=
  (∑ x ∈ Finset.univ.filter fun x => q x = t, μ x * f x)
    / ∑ x ∈ Finset.univ.filter fun x => q x = t, μ x

/-- Conditional expectation of `f` given the record `q`. -/
noncomputable def condExp (μ : Ω → ℝ) (q : Ω → T) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => condMean μ q f (q x)

/-- The conditional mean times the fiber mass recovers the fiber integral. -/
theorem condMean_mul_mass {μ : Ω → ℝ} (hμ : ∀ x, 0 < μ x) (q : Ω → T) (f : Ω → ℝ)
    (t : T) :
    condMean μ q f t * ∑ x ∈ Finset.univ.filter fun x => q x = t, μ x
      = ∑ x ∈ Finset.univ.filter fun x => q x = t, μ x * f x := by
  rcases (Finset.univ.filter fun x => q x = t).eq_empty_or_nonempty with h | h
  · rw [h, Finset.sum_empty, Finset.sum_empty, mul_zero]
  · have hW : 0 < ∑ x ∈ Finset.univ.filter fun x => q x = t, μ x :=
      Finset.sum_pos (fun x _ => hμ x) h
    unfold condMean
    exact div_mul_cancel₀ _ hW.ne'

/-- Each fiber integral of `f - condMean` vanishes. -/
theorem fiber_cancel {μ : Ω → ℝ} (hμ : ∀ x, 0 < μ x) (q : Ω → T) (f : Ω → ℝ)
    (t : T) :
    ∑ x ∈ Finset.univ.filter fun x => q x = t, μ x * (f x - condMean μ q f t) = 0 := by
  have hsplit : ∑ x ∈ Finset.univ.filter fun x => q x = t, μ x * (f x - condMean μ q f t)
      = (∑ x ∈ Finset.univ.filter fun x => q x = t, μ x * f x)
        - condMean μ q f t * ∑ x ∈ Finset.univ.filter fun x => q x = t, μ x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsplit, condMean_mul_mass hμ q f t, sub_self]

/-- **Orthogonality**: the conditional residual is orthogonal to every
record-measurable writer. -/
theorem orth {μ : Ω → ℝ} [Finite T] (hμ : ∀ x, 0 < μ x) (q : Ω → T) (f : Ω → ℝ)
    (g : T → ℝ) :
    ∑ x, μ x * ((f x - condExp μ q f x) * g (q x)) = 0 := by
  have := Fintype.ofFinite T
  rw [← Finset.sum_fiberwise Finset.univ q
    fun x => μ x * ((f x - condExp μ q f x) * g (q x))]
  refine Finset.sum_eq_zero fun t _ => ?_
  have hcongr : ∀ x ∈ Finset.univ.filter fun x => q x = t,
      μ x * ((f x - condExp μ q f x) * g (q x))
        = μ x * (f x - condMean μ q f t) * g t := by
    intro x hx
    have hqx : q x = t := (Finset.mem_filter.mp hx).2
    simp only [condExp, hqx]
    ring
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul, ← Finset.sum_congr rfl
    (fun x _ => rfl), fiber_cancel hμ q f t, zero_mul]

/-- **Conditional Pythagoras**: `‖f‖² = ‖E[f|q]‖² + ‖f - E[f|q]‖²`. -/
theorem pythagoras {μ : Ω → ℝ} [Finite T] (hμ : ∀ x, 0 < μ x) (q : Ω → T) (f : Ω → ℝ) :
    wsq μ f = wsq μ (condExp μ q f) + wsq μ (fun x => f x - condExp μ q f x) := by
  have hcross : ∑ x, μ x * ((f x - condExp μ q f x) * condExp μ q f x) = 0 :=
    orth hμ q f (condMean μ q f)
  have hpt : ∀ x, μ x * f x ^ 2
      = μ x * condExp μ q f x ^ 2 + μ x * (f x - condExp μ q f x) ^ 2
        + 2 * (μ x * ((f x - condExp μ q f x) * condExp μ q f x)) := fun x => by ring
  unfold wsq
  rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hcross, mul_zero, add_zero]

/-- **Conditional contraction**: `‖E[f|q]‖² ≤ ‖f‖²`. -/
theorem condExp_contraction {μ : Ω → ℝ} [Finite T] (hμ : ∀ x, 0 < μ x) (q : Ω → T)
    (f : Ω → ℝ) :
    wsq μ (condExp μ q f) ≤ wsq μ f := by
  have h := pythagoras hμ q f
  have h2 : 0 ≤ wsq μ (fun x => f x - condExp μ q f x) :=
    wsq_nonneg (fun x => (hμ x).le) _
  linarith

end FiberCondExp

end FiberCondExpSection

/-! ### `prop:YM-boundary-replica-acquisition` — Three-query boundary-glued acquisition

Rendering: the Markov-blanket sampling of the manuscript — one shell
value `s`, two conditionally independent interiors `u₁, u₂` and two
conditionally independent exteriors `o₁, o₂` — is the finite replica law
`m(s)·κin(s,u₁)·κin(s,u₂)·κout(s,o₁)·κout(s,o₂)` on
`S × In × In × Out × Out`, with `m` the shell law and `κin`, `κout` the
two conditional kernels.  The writers `Y` and `A` may depend on the
shell and their own coordinate.  The boundary Gram entries
`I = ‖U‖²`, `C = ⟨U,V⟩`, `S = ‖V‖²` are defined through the conditional
messages `U(s) = E[Y|s]`, `V(s) = E[A|s]` exactly as in (WBM.8)–(WBM.9),
and the three theorems `replica_query_*` prove that the three raw
replica queries of (WBM.12) — expectations of products of the raw
writers, with no conditional message appearing on the left-hand side —
equal them.  `short_evaluated_from_queries` renders the final clause:
the source short `S - C²/I` (the Schur residual of (WBM.11)) is
evaluated directly from the three scalar queries and equals the squared
norm of the residual message, so the conditional messages never need to
be reconstructed pointwise. -/

section ReplicaAcquisition

namespace YMReplicaAcquisition

variable {S In Out : Type*} [Fintype S] [Fintype In] [Fintype Out]

/-- The five-coordinate boundary-glued replica law: one shell value, two
conditionally independent interiors, two conditionally independent
exteriors. -/
def repLaw (m : S → ℝ) (κi : S → In → ℝ) (κo : S → Out → ℝ) :
    S × In × In × Out × Out → ℝ :=
  fun w => m w.1 * κi w.1 w.2.1 * κi w.1 w.2.2.1 * κo w.1 w.2.2.2.1 * κo w.1 w.2.2.2.2

/-- Expectation of a replica observable under the boundary-glued law,
in iterated-sum form. -/
def repE (m : S → ℝ) (κi : S → In → ℝ) (κo : S → Out → ℝ)
    (φ : S → In → In → Out → Out → ℝ) : ℝ :=
  ∑ s, ∑ u₁, ∑ u₂, ∑ o₁, ∑ o₂,
    m s * κi s u₁ * κi s u₂ * κo s o₁ * κo s o₂ * φ s u₁ u₂ o₁ o₂

/-- The iterated-sum expectation is the expectation under the replica law
on the five-fold product carrier. -/
theorem repE_eq_sum_repLaw (m : S → ℝ) (κi : S → In → ℝ) (κo : S → Out → ℝ)
    (φ : S → In → In → Out → Out → ℝ) :
    repE m κi κo φ
      = ∑ w : S × In × In × Out × Out,
          repLaw m κi κo w * φ w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 := by
  simp only [repE, repLaw, Fintype.sum_prod_type]

omit [Fintype S] [Fintype In] [Fintype Out] in
/-- The replica law is nonnegative for nonnegative data. -/
theorem repLaw_nonneg {m : S → ℝ} {κi : S → In → ℝ} {κo : S → Out → ℝ}
    (hm : ∀ s, 0 ≤ m s) (hκi : ∀ s u, 0 ≤ κi s u) (hκo : ∀ s o, 0 ≤ κo s o)
    (w : S × In × In × Out × Out) : 0 ≤ repLaw m κi κo w := by
  unfold repLaw
  have h1 := hm w.1
  have h2 := hκi w.1 w.2.1
  have h3 := hκi w.1 w.2.2.1
  have h4 := hκo w.1 w.2.2.2.1
  have h5 := hκo w.1 w.2.2.2.2
  positivity

/-- The conditional interior message `U(s) = E[Y | s]`. -/
def msgU (κi : S → In → ℝ) (Y : S → In → ℝ) (s : S) : ℝ := ∑ u, κi s u * Y s u

/-- The conditional exterior message `V(s) = E[A | s]`. -/
def msgV (κo : S → Out → ℝ) (A : S → Out → ℝ) (s : S) : ℝ := ∑ o, κo s o * A s o

/-- The source Gram entry `I = ‖U‖²` of (WBM.9). -/
def gramI (m : S → ℝ) (κi : S → In → ℝ) (Y : S → In → ℝ) : ℝ :=
  ∑ s, m s * msgU κi Y s ^ 2

/-- The cross Gram entry `C = ⟨U,V⟩` of (WBM.9). -/
def gramC (m : S → ℝ) (κi : S → In → ℝ) (κo : S → Out → ℝ)
    (Y : S → In → ℝ) (A : S → Out → ℝ) : ℝ :=
  ∑ s, m s * (msgU κi Y s * msgV κo A s)

/-- The score Gram entry `S = ‖V‖²` of (WBM.9). -/
def gramS (m : S → ℝ) (κo : S → Out → ℝ) (A : S → Out → ℝ) : ℝ :=
  ∑ s, m s * msgV κo A s ^ 2

/-- Averaging a probability kernel against a constant. -/
theorem sum_weight_mul {α : Type*} [Fintype α] {κ : α → ℝ} (hκ : ∑ a, κ a = 1)
    (c : ℝ) : ∑ a, κ a * c = c := by
  rw [← Finset.sum_mul, hκ, one_mul]

/-- Master factorization: the replica expectation of a product observable
factors through the shell into products of conditional one-leaf means. -/
theorem repE_factor {m : S → ℝ} {κi : S → In → ℝ} {κo : S → Out → ℝ}
    (f₁ f₂ : S → In → ℝ) (g₁ g₂ : S → Out → ℝ) :
    repE m κi κo (fun s u₁ u₂ o₁ o₂ => f₁ s u₁ * f₂ s u₂ * (g₁ s o₁ * g₂ s o₂))
      = ∑ s, m s * ((∑ u, κi s u * f₁ s u) * (∑ u, κi s u * f₂ s u)
          * ((∑ o, κo s o * g₁ s o) * (∑ o, κo s o * g₂ s o))) := by
  unfold repE
  refine Finset.sum_congr rfl fun s _ => ?_
  have h1 : ∀ (u₁ u₂ : In) (o₁ : Out),
      ∑ o₂, m s * κi s u₁ * κi s u₂ * κo s o₁ * κo s o₂
          * (f₁ s u₁ * f₂ s u₂ * (g₁ s o₁ * g₂ s o₂))
        = (∑ o₂, κo s o₂ * g₂ s o₂)
            * (m s * κi s u₁ * κi s u₂ * κo s o₁
              * (f₁ s u₁ * f₂ s u₂ * g₁ s o₁)) := by
    intro u₁ u₂ o₁
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun o₂ _ => by ring
  have h2 : ∀ (u₁ u₂ : In),
      ∑ o₁, (∑ o₂, κo s o₂ * g₂ s o₂)
          * (m s * κi s u₁ * κi s u₂ * κo s o₁ * (f₁ s u₁ * f₂ s u₂ * g₁ s o₁))
        = (∑ o₁, κo s o₁ * g₁ s o₁) * ((∑ o₂, κo s o₂ * g₂ s o₂)
            * (m s * κi s u₁ * κi s u₂ * (f₁ s u₁ * f₂ s u₂))) := by
    intro u₁ u₂
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun o₁ _ => by ring
  have h3 : ∀ u₁ : In,
      ∑ u₂, (∑ o₁, κo s o₁ * g₁ s o₁) * ((∑ o₂, κo s o₂ * g₂ s o₂)
          * (m s * κi s u₁ * κi s u₂ * (f₁ s u₁ * f₂ s u₂)))
        = (∑ u₂, κi s u₂ * f₂ s u₂) * ((∑ o₁, κo s o₁ * g₁ s o₁)
            * ((∑ o₂, κo s o₂ * g₂ s o₂) * (m s * κi s u₁ * f₁ s u₁))) := by
    intro u₁
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun u₂ _ => by ring
  have h4 : ∑ u₁, (∑ u₂, κi s u₂ * f₂ s u₂) * ((∑ o₁, κo s o₁ * g₁ s o₁)
        * ((∑ o₂, κo s o₂ * g₂ s o₂) * (m s * κi s u₁ * f₁ s u₁)))
      = (∑ u₁, κi s u₁ * f₁ s u₁) * ((∑ u₂, κi s u₂ * f₂ s u₂)
          * ((∑ o₁, κo s o₁ * g₁ s o₁) * ((∑ o₂, κo s o₂ * g₂ s o₂) * m s))) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun u₁ _ => by ring
  calc ∑ u₁, ∑ u₂, ∑ o₁, ∑ o₂,
        m s * κi s u₁ * κi s u₂ * κo s o₁ * κo s o₂
          * (f₁ s u₁ * f₂ s u₂ * (g₁ s o₁ * g₂ s o₂))
      = ∑ u₁, ∑ u₂, ∑ o₁, (∑ o₂, κo s o₂ * g₂ s o₂)
          * (m s * κi s u₁ * κi s u₂ * κo s o₁
            * (f₁ s u₁ * f₂ s u₂ * g₁ s o₁)) := by
        refine Finset.sum_congr rfl fun u₁ _ => ?_
        exact Finset.sum_congr rfl fun u₂ _ =>
          Finset.sum_congr rfl fun o₁ _ => h1 u₁ u₂ o₁
    _ = ∑ u₁, ∑ u₂, (∑ o₁, κo s o₁ * g₁ s o₁) * ((∑ o₂, κo s o₂ * g₂ s o₂)
          * (m s * κi s u₁ * κi s u₂ * (f₁ s u₁ * f₂ s u₂))) := by
        refine Finset.sum_congr rfl fun u₁ _ => ?_
        exact Finset.sum_congr rfl fun u₂ _ => h2 u₁ u₂
    _ = ∑ u₁, (∑ u₂, κi s u₂ * f₂ s u₂) * ((∑ o₁, κo s o₁ * g₁ s o₁)
          * ((∑ o₂, κo s o₂ * g₂ s o₂) * (m s * κi s u₁ * f₁ s u₁))) := by
        exact Finset.sum_congr rfl fun u₁ _ => h3 u₁
    _ = (∑ u₁, κi s u₁ * f₁ s u₁) * ((∑ u₂, κi s u₂ * f₂ s u₂)
          * ((∑ o₁, κo s o₁ * g₁ s o₁) * ((∑ o₂, κo s o₂ * g₂ s o₂) * m s))) := h4
    _ = m s * ((∑ u, κi s u * f₁ s u) * (∑ u, κi s u * f₂ s u)
          * ((∑ o, κo s o * g₁ s o) * (∑ o, κo s o * g₂ s o))) := by ring

/-- The replica law is a probability law when the shell law and the two
conditional kernels are normalized. -/
theorem repLaw_sum {m : S → ℝ} {κi : S → In → ℝ} {κo : S → Out → ℝ}
    (hm : ∑ s, m s = 1) (hκi : ∀ s, ∑ u, κi s u = 1) (hκo : ∀ s, ∑ o, κo s o = 1) :
    ∑ w : S × In × In × Out × Out, repLaw m κi κo w = 1 := by
  have h2 : repE m κi κo (fun _ _ _ _ _ => (1 : ℝ)) = 1 := by
    have h3 := repE_factor (m := m) (κi := κi) (κo := κo)
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
    have h4 : repE m κi κo (fun s u₁ u₂ o₁ o₂ => (1 : ℝ) * 1 * (1 * 1))
        = repE m κi κo fun _ _ _ _ _ => (1 : ℝ) := by norm_num
    rw [← h4, h3]
    have h5 : ∀ s, m s * ((∑ u, κi s u * (1 : ℝ)) * (∑ u, κi s u * (1 : ℝ))
        * ((∑ o, κo s o * (1 : ℝ)) * (∑ o, κo s o * (1 : ℝ)))) = m s := by
      intro s
      simp only [mul_one, hκi s, hκo s]
    rw [Finset.sum_congr rfl fun s _ => h5 s, hm]
  rw [← h2, repE_eq_sum_repLaw]
  exact Finset.sum_congr rfl fun w _ => by simp

/-- **First replica query (WBM.12)**: the two-interior product acquires
the source Gram entry, `E[Y(u₁)Y(u₂)] = I`. -/
theorem replica_query_interior {m : S → ℝ} {κi : S → In → ℝ} {κo : S → Out → ℝ}
    (hκo : ∀ s, ∑ o, κo s o = 1) (Y : S → In → ℝ) :
    repE m κi κo (fun s u₁ u₂ _ _ => Y s u₁ * Y s u₂) = gramI m κi Y := by
  have h : repE m κi κo (fun s u₁ u₂ o₁ o₂ => Y s u₁ * Y s u₂ * ((1 : ℝ) * 1))
      = repE m κi κo fun s u₁ u₂ _ _ => Y s u₁ * Y s u₂ := by norm_num
  rw [← h, repE_factor Y Y (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))]
  unfold gramI msgU
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [mul_one, hκo s]
  ring

/-- **Second replica query (WBM.12)**: the mixed interior–exterior product
acquires the cross Gram entry, `E[Y(u₁)A(o₁)] = C`. -/
theorem replica_query_cross {m : S → ℝ} {κi : S → In → ℝ} {κo : S → Out → ℝ}
    (hκi : ∀ s, ∑ u, κi s u = 1) (hκo : ∀ s, ∑ o, κo s o = 1)
    (Y : S → In → ℝ) (A : S → Out → ℝ) :
    repE m κi κo (fun s u₁ _ o₁ _ => Y s u₁ * A s o₁) = gramC m κi κo Y A := by
  have h : repE m κi κo (fun s u₁ u₂ o₁ o₂ => Y s u₁ * 1 * (A s o₁ * 1))
      = repE m κi κo fun s u₁ _ o₁ _ => Y s u₁ * A s o₁ := by norm_num
  rw [← h, repE_factor Y (fun _ _ => (1 : ℝ)) A (fun _ _ => (1 : ℝ))]
  unfold gramC msgU msgV
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [mul_one, hκi s, hκo s]

/-- **Third replica query (WBM.12)**: the two-exterior product acquires
the score Gram entry, `E[A(o₁)A(o₂)] = S`. -/
theorem replica_query_exterior {m : S → ℝ} {κi : S → In → ℝ} {κo : S → Out → ℝ}
    (hκi : ∀ s, ∑ u, κi s u = 1) (A : S → Out → ℝ) :
    repE m κi κo (fun s _ _ o₁ o₂ => A s o₁ * A s o₂) = gramS m κo A := by
  have h : repE m κi κo (fun s u₁ u₂ o₁ o₂ => (1 : ℝ) * 1 * (A s o₁ * A s o₂))
      = repE m κi κo fun s _ _ o₁ o₂ => A s o₁ * A s o₂ := by norm_num
  rw [← h, repE_factor (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) A A]
  unfold gramS msgV
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [mul_one, hκi s]
  ring

/-- **Three-query boundary-glued acquisition (WBM.12)**: the three scalar
replica queries reconstruct the complete boundary Gram
`(I, C; C, S)`. -/
theorem boundary_gram_reconstruction {m : S → ℝ} {κi : S → In → ℝ}
    {κo : S → Out → ℝ} (hκi : ∀ s, ∑ u, κi s u = 1) (hκo : ∀ s, ∑ o, κo s o = 1)
    (Y : S → In → ℝ) (A : S → Out → ℝ) :
    repE m κi κo (fun s u₁ u₂ _ _ => Y s u₁ * Y s u₂) = gramI m κi Y
    ∧ repE m κi κo (fun s u₁ _ o₁ _ => Y s u₁ * A s o₁) = gramC m κi κo Y A
    ∧ repE m κi κo (fun s _ _ o₁ o₂ => A s o₁ * A s o₂) = gramS m κo A :=
  ⟨replica_query_interior hκo Y, replica_query_cross hκi hκo Y A,
    replica_query_exterior hκi A⟩

/-- **The source short is evaluated from the three scalar queries**: the
Schur residual `S - C²/I` equals the squared norm of the residual
message `V - (C/I)·U`, so the conditional messages need not be
reconstructed pointwise. -/
theorem short_evaluated_from_queries {m : S → ℝ} {κi : S → In → ℝ}
    {κo : S → Out → ℝ} (Y : S → In → ℝ) (A : S → Out → ℝ)
    (hI : gramI m κi Y ≠ 0) :
    gramS m κo A - gramC m κi κo Y A ^ 2 / gramI m κi Y
      = ∑ s, m s * (msgV κo A s
          - gramC m κi κo Y A / gramI m κi Y * msgU κi Y s) ^ 2 := by
  have hpt : ∀ s, m s * (msgV κo A s
        - gramC m κi κo Y A / gramI m κi Y * msgU κi Y s) ^ 2
      = m s * msgV κo A s ^ 2
        - 2 * (gramC m κi κo Y A / gramI m κi Y) * (m s * (msgU κi Y s * msgV κo A s))
        + (gramC m κi κo Y A / gramI m κi Y) ^ 2 * (m s * msgU κi Y s ^ 2) :=
    fun s => by ring
  rw [Finset.sum_congr rfl fun s _ => hpt s, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ s, m s * msgV κo A s ^ 2 = gramS m κo A := rfl
  have h2 : ∑ s, m s * (msgU κi Y s * msgV κo A s) = gramC m κi κo Y A := rfl
  have h3 : ∑ s, m s * msgU κi Y s ^ 2 = gramI m κi Y := rfl
  rw [h1, h2, h3]
  field_simp
  ring

end YMReplicaAcquisition

end ReplicaAcquisition

/-! ### `cor:YM-native-descendant-collapse` — Every unrescaled native descendant collapses

Rendering: each cutoff `N` carries a finite configuration carrier
`Ω N` with a strictly positive probability weight `μ N`, the native fan
writer `f N`, and finite records `Q N` (the centre record `𝒬_N`) and
`A N` (an arbitrary, possibly cutoff-dependent record `𝒜_N`).  The
variance bound of `thm:YM-complete-native-collapse` (YNC.4),
`Var(f_N) ≤ 3030750000·p_N(β_N)`, and the escaping-sequence collapse
`p_N(β_N) → 0` enter as hypotheses, since that theorem is a separate
manuscript record.  `descendant_pythagoras_collapse` is (YNC.6): the
exact Pythagoras identity `‖F_N‖² = ‖M_N‖² + ‖ξ_N‖²` for
`F_N = f_N - E f_N`, `M_N = E[F_N|𝒬_N]`, `ξ_N = F_N - M_N`, together
with the convergence of all three squared norms to zero.
`record_contraction` is (YNC.7) for every record family, and
`rescaling_cost` is the final clause: any deterministic rescaling with
variance floor `v_* > 0` forces `b_N²·p_N(β_N) ≥ v_*/3030750000`. -/

section DescendantCollapse

namespace YMDescendantCollapse

open FiberCondExp

/-- **(YNC.6), Pythagoras and collapse**: on every escaping periodic
Wilson sequence the centred native fan satisfies the exact conditional
Pythagoras identity, and the total, message, and residual stocks all
collapse. -/
theorem descendant_pythagoras_collapse
    (Ω : ℕ → Type*) [∀ N, Fintype (Ω N)]
    (T : ℕ → Type*) [∀ N, Finite (T N)] [∀ N, DecidableEq (T N)]
    (μ : ∀ N, Ω N → ℝ) (hμ : ∀ N x, 0 < μ N x)
    (f : ∀ N, Ω N → ℝ) (Q : ∀ N, Ω N → T N) (p : ℕ → ℝ)
    (hvar : ∀ N, wvar (μ N) (f N) ≤ 3030750000 * p N)
    (hp : Tendsto p atTop (𝓝 0)) :
    (∀ N, wsq (μ N) (centered (μ N) (f N))
        = wsq (μ N) (condExp (μ N) (Q N) (centered (μ N) (f N)))
          + wsq (μ N) (fun x => centered (μ N) (f N) x
              - condExp (μ N) (Q N) (centered (μ N) (f N)) x))
    ∧ Tendsto (fun N => wsq (μ N) (centered (μ N) (f N))) atTop (𝓝 0)
    ∧ Tendsto (fun N => wsq (μ N) (condExp (μ N) (Q N) (centered (μ N) (f N))))
        atTop (𝓝 0)
    ∧ Tendsto (fun N => wsq (μ N) (fun x => centered (μ N) (f N) x
        - condExp (μ N) (Q N) (centered (μ N) (f N)) x)) atTop (𝓝 0) := by
  have hpy : ∀ N, wsq (μ N) (centered (μ N) (f N))
      = wsq (μ N) (condExp (μ N) (Q N) (centered (μ N) (f N)))
        + wsq (μ N) (fun x => centered (μ N) (f N) x
            - condExp (μ N) (Q N) (centered (μ N) (f N)) x) :=
    fun N => pythagoras (hμ N) (Q N) _
  have hlim : Tendsto (fun N => 3030750000 * p N) atTop (𝓝 0) := by
    simpa using hp.const_mul (3030750000 : ℝ)
  have hF0 : Tendsto (fun N => wsq (μ N) (centered (μ N) (f N))) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => wsq_nonneg (fun x => (hμ N x).le) _)
      (fun N => ?_) hlim
    exact hvar N
  have hM0 : Tendsto (fun N => wsq (μ N)
      (condExp (μ N) (Q N) (centered (μ N) (f N)))) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => wsq_nonneg (fun x => (hμ N x).le) _)
      (fun N => condExp_contraction (hμ N) (Q N) _) hF0
  have hxi0 : Tendsto (fun N => wsq (μ N) (fun x => centered (μ N) (f N) x
      - condExp (μ N) (Q N) (centered (μ N) (f N)) x)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => wsq_nonneg (fun x => (hμ N x).le) _)
      (fun N => ?_) hF0
    have h := hpy N
    have h2 : 0 ≤ wsq (μ N) (condExp (μ N) (Q N) (centered (μ N) (f N))) :=
      wsq_nonneg (fun x => (hμ N x).le) _
    linarith
  exact ⟨hpy, hF0, hM0, hxi0⟩

/-- **(YNC.7), record contraction**: for every possibly cutoff-dependent
record family the conditional descendant stock is dominated by the
variance and collapses; no unrescaled conditional descendant of the
fixed native fan has a positive absolute limiting stock. -/
theorem record_contraction
    (Ω : ℕ → Type*) [∀ N, Fintype (Ω N)]
    (T : ℕ → Type*) [∀ N, Finite (T N)] [∀ N, DecidableEq (T N)]
    (μ : ∀ N, Ω N → ℝ) (hμ : ∀ N x, 0 < μ N x)
    (f : ∀ N, Ω N → ℝ) (A : ∀ N, Ω N → T N) (p : ℕ → ℝ)
    (hvar : ∀ N, wvar (μ N) (f N) ≤ 3030750000 * p N)
    (hp : Tendsto p atTop (𝓝 0)) :
    (∀ N, wsq (μ N) (condExp (μ N) (A N) (centered (μ N) (f N)))
        ≤ wvar (μ N) (f N))
    ∧ Tendsto (fun N => wsq (μ N) (condExp (μ N) (A N) (centered (μ N) (f N))))
        atTop (𝓝 0) := by
  have hbound : ∀ N, wsq (μ N) (condExp (μ N) (A N) (centered (μ N) (f N)))
      ≤ wvar (μ N) (f N) := fun N => condExp_contraction (hμ N) (A N) _
  refine ⟨hbound, ?_⟩
  have hlim : Tendsto (fun N => 3030750000 * p N) atTop (𝓝 0) := by
    simpa using hp.const_mul (3030750000 : ℝ)
  refine squeeze_zero (fun N => wsq_nonneg (fun x => (hμ N x).le) _)
    (fun N => (hbound N).trans (hvar N)) hlim

/-- **Rescaling cost**: a deterministic rescaling `b_N` with variance
floor `Var(b_N f_N) ≥ v_* > 0` necessarily pays
`b_N² p_N(β_N) ≥ v_*/3030750000`, and in particular `b_N² p_N > 0`. -/
theorem rescaling_cost
    (Ω : ℕ → Type*) [∀ N, Fintype (Ω N)]
    (μ : ∀ N, Ω N → ℝ) (f : ∀ N, Ω N → ℝ) (p : ℕ → ℝ)
    (hvar : ∀ N, wvar (μ N) (f N) ≤ 3030750000 * p N)
    (b : ℕ → ℝ) (v : ℝ) (hv : 0 < v)
    (hvb : ∀ N, v ≤ wvar (μ N) (fun x => b N * f N x)) :
    ∀ N, 0 < b N ^ 2 * p N ∧ v / 3030750000 ≤ b N ^ 2 * p N := by
  intro N
  have h1 : wvar (μ N) (fun x => b N * f N x) = b N ^ 2 * wvar (μ N) (f N) :=
    wvar_const_mul (μ N) (f N) (b N)
  have h2 : v ≤ b N ^ 2 * (3030750000 * p N) := by
    calc v ≤ wvar (μ N) (fun x => b N * f N x) := hvb N
      _ = b N ^ 2 * wvar (μ N) (f N) := h1
      _ ≤ b N ^ 2 * (3030750000 * p N) :=
          mul_le_mul_of_nonneg_left (hvar N) (sq_nonneg _)
  have h3 : b N ^ 2 * (3030750000 * p N) = b N ^ 2 * p N * 3030750000 := by ring
  have h4 : v / 3030750000 ≤ b N ^ 2 * p N := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3030750000)]
    linarith
  refine ⟨lt_of_lt_of_le ?_ h4, h4⟩
  positivity

end YMDescendantCollapse

end DescendantCollapse

/-! ### `cth:YM-cutoff-radial-independent` — Cutoff and radial coefficients are independent

Rendering: the fully constructed finite witness of the manuscript proof.
The carrier is the product `(Bool × Bool) × (Bool × Bool)`: the cutoff
factor carries the independent fair Rademacher spins `(G, X)` under the
uniform weight `1/4`, and the radial factor carries a fair Rademacher
`U` and an independent `±1` writer `E` with mean `q_rad` (weight
`(1±q)/4`).  The cutoff writer is `F = √(1-R_cut)·G + √R_cut·X`; both
`F` and `G` are centred with unit variance and the normalized Schur
residual `1 - ⟨F,G⟩²/(‖F‖²‖G‖²)` is exactly `R_cut`.  The radial source
is the inner message `s·U` with entrance stock `s²`; the outer record is
`V = U·E`, and the conditional expectation `E[s·U | V] = s·q_rad·V` is
proved both through the generic fiber construction and through the
orthogonality characterization, giving outer stock `s²q_rad²` and
one-step norm ratio `q_rad`.  The law is a product, so every joint
expectation of a cutoff writer times a radial writer factorizes: the two
cards are independent, and since `R_cut, q_rad` range over all of
`[0,1]`, no residual value bounds the radial coefficient and the radial
coefficient does not determine cutoff visibility. -/

section CutoffRadialIndependent

namespace YMCutoffRadial

/-- The `±1` reading of a Boolean spin. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The cutoff factor: the uniform law on the fair Rademacher pair `(G,X)`. -/
noncomputable def cutFactor : Bool × Bool → ℝ := fun _ => 1 / 4

/-- The radial factor: a fair Rademacher `U` and an independent `±1`
writer `E` of mean `q`. -/
noncomputable def radFactor (q : ℝ) : Bool × Bool → ℝ :=
  fun p => 1 / 2 * (if p.2 then (1 + q) / 2 else (1 - q) / 2)

/-- The full finite product probability model. -/
noncomputable def fullLaw (q : ℝ) : (Bool × Bool) × Bool × Bool → ℝ :=
  fun w => cutFactor w.1 * radFactor q w.2

/-- Expectation under the cutoff factor. -/
noncomputable def cutE (φ : Bool × Bool → ℝ) : ℝ := ∑ p, cutFactor p * φ p

/-- Expectation under the radial factor. -/
noncomputable def radE (q : ℝ) (ψ : Bool × Bool → ℝ) : ℝ := ∑ p, radFactor q p * ψ p

/-- Expectation under the full product law. -/
noncomputable def fullE (q : ℝ) (Φ : (Bool × Bool) × Bool × Bool → ℝ) : ℝ :=
  ∑ w, fullLaw q w * Φ w

/-- The cutoff writer `F = √(1-R)·G + √R·X`. -/
noncomputable def Fwr (R : ℝ) : Bool × Bool → ℝ :=
  fun p => Real.sqrt (1 - R) * sgn p.1 + Real.sqrt R * sgn p.2

/-- The old-record writer `G`. -/
def Gwr : Bool × Bool → ℝ := fun p => sgn p.1

/-- The inner radial spin `U`. -/
def radU : Bool × Bool → ℝ := fun p => sgn p.1

/-- The outer radial record writer `V = U·E`. -/
def radV : Bool × Bool → ℝ := fun p => sgn p.1 * sgn p.2

/-- The Boolean record read of `V`. -/
def vRec : Bool × Bool → Bool := fun p => p.1 == p.2

/-- The full law is nonnegative for `0 ≤ q ≤ 1`. -/
theorem fullLaw_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (w : (Bool × Bool) × Bool × Bool) : 0 ≤ fullLaw q w := by
  obtain ⟨p, u, e⟩ := w
  unfold fullLaw cutFactor radFactor
  cases e <;> simp <;> nlinarith

/-- The full law is a probability law. -/
theorem fullLaw_sum (q : ℝ) : ∑ w, fullLaw q w = 1 := by
  simp [fullLaw, cutFactor, radFactor, Fintype.sum_prod_type]
  ring

/-- **Product independence**: every joint expectation of a cutoff writer
times a radial writer factorizes. -/
theorem product_factorization (q : ℝ) (φ ψ : Bool × Bool → ℝ) :
    fullE q (fun w => φ w.1 * ψ w.2) = cutE φ * radE q ψ := by
  unfold fullE fullLaw cutE radE
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => by ring

/-- The cutoff writer `G` is centred. -/
theorem cutE_G : cutE Gwr = 0 := by
  simp [cutE, Gwr, cutFactor, sgn, Fintype.sum_prod_type]

/-- The cutoff writer `G` has unit variance. -/
theorem cutE_G_sq : cutE (fun p => Gwr p ^ 2) = 1 := by
  simp [cutE, Gwr, cutFactor, sgn]

/-- The cutoff writer `F` is centred. -/
theorem cutE_F (R : ℝ) : cutE (Fwr R) = 0 := by
  simp [cutE, Fwr, cutFactor, sgn, Fintype.sum_prod_type]
  ring

/-- The cutoff writer `F` has unit variance for `0 ≤ R ≤ 1`. -/
theorem cutE_F_sq {R : ℝ} (h0 : 0 ≤ R) (h1 : R ≤ 1) :
    cutE (fun p => Fwr R p ^ 2) = 1 := by
  have ha : Real.sqrt (1 - R) ^ 2 = 1 - R := Real.sq_sqrt (by linarith)
  have hb : Real.sqrt R ^ 2 = R := Real.sq_sqrt h0
  simp [cutE, Fwr, cutFactor, sgn, Fintype.sum_prod_type]
  nlinarith [ha, hb]

/-- The cutoff cross moment is `⟨F,G⟩ = √(1-R)`. -/
theorem cutE_FG (R : ℝ) : cutE (fun p => Fwr R p * Gwr p) = Real.sqrt (1 - R) := by
  simp [cutE, Fwr, Gwr, cutFactor, sgn, Fintype.sum_prod_type]
  ring

/-- **The normalized Schur residual of the cutoff pair is exactly
`R_cut`**. -/
theorem cutoff_residual {R : ℝ} (h0 : 0 ≤ R) (h1 : R ≤ 1) :
    1 - cutE (fun p => Fwr R p * Gwr p) ^ 2
        / (cutE (fun p => Fwr R p ^ 2) * cutE (fun p => Gwr p ^ 2)) = R := by
  rw [cutE_FG, cutE_F_sq h0 h1, cutE_G_sq,
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - R)]
  norm_num

/-- The radial factor is a probability law. -/
theorem radFactor_sum (q : ℝ) : ∑ p, radFactor q p = 1 := by
  simp [radFactor, Fintype.sum_prod_type]
  ring

/-- **Entrance stock**: the inner radial message `s·U` has stock `s²`. -/
theorem radial_entrance_stock (q s : ℝ) :
    radE q (fun p => (s * radU p) ^ 2) = s ^ 2 := by
  simp [radE, radFactor, radU, sgn, Fintype.sum_prod_type]
  ring

/-- **The conditional message**: the generic fiber conditional mean of
`s·U` given the record `V` is `s·q·(±1)`. -/
theorem radial_condMean (q s : ℝ) :
    FiberCondExp.condMean (radFactor q) vRec (fun p => s * radU p)
      = fun v => s * q * sgn v := by
  funext v
  unfold FiberCondExp.condMean
  rw [Finset.sum_filter, Finset.sum_filter]
  cases v <;>
    · simp [Fintype.sum_prod_type, vRec, radU, sgn, radFactor]
      ring_nf

/-- `sgn` of the record read is the record writer `V`. -/
theorem sgn_vRec (p : Bool × Bool) : sgn (vRec p) = radV p := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> simp [sgn, vRec, radV]

/-- **`E[s·U | V] = s·q·V`** as a pointwise conditional expectation. -/
theorem radial_condExp (q s : ℝ) :
    FiberCondExp.condExp (radFactor q) vRec (fun p => s * radU p)
      = fun p => s * q * radV p := by
  funext p
  have h := congrFun (radial_condMean q s) (vRec p)
  unfold FiberCondExp.condExp
  rw [h, sgn_vRec]

/-- **Orthogonality characterization**: the residual `s·U - s·q·V` is
orthogonal to every record-measurable writer, for every `q`. -/
theorem radial_orthogonality (q s : ℝ) (h : Bool → ℝ) :
    radE q (fun p => (s * radU p - s * q * radV p) * h (vRec p)) = 0 := by
  simp [radE, radFactor, radU, radV, vRec, sgn, Fintype.sum_prod_type]
  ring

/-- **Outer stock**: the conditional radial message has stock `s²q²`. -/
theorem radial_outer_stock (q s : ℝ) :
    radE q (fun p => (s * q * radV p) ^ 2) = s ^ 2 * q ^ 2 := by
  simp [radE, radFactor, radV, sgn, Fintype.sum_prod_type]
  ring

/-- **One-step norm ratio**: the outer/inner radial norm ratio is
exactly `q_rad`. -/
theorem radial_step_ratio {q s : ℝ} (hs : 0 < s) (hq0 : 0 ≤ q) :
    Real.sqrt (s ^ 2 * q ^ 2) / Real.sqrt (s ^ 2) = q := by
  rw [show s ^ 2 * q ^ 2 = (s * q) ^ 2 by ring,
    Real.sqrt_sq (mul_nonneg hs.le hq0), Real.sqrt_sq hs.le]
  exact mul_div_cancel_left₀ q hs.ne'

/-- **Cutoff and radial coefficients are independent**: for every
`R_cut, q_rad ∈ [0,1]` and source scale `s > 0`, the explicit finite
product model realizes residual `R_cut`, entrance stock `s²`, and
one-step norm ratio `q_rad`, with the two cards independent.  Hence no
old/fine residual value bounds the radial coefficient and the radial
coefficient does not determine cutoff visibility. -/
theorem cutoff_radial_independent (R q s : ℝ) (h0R : 0 ≤ R) (h1R : R ≤ 1)
    (h0q : 0 ≤ q) (h1q : q ≤ 1) (hs : 0 < s) :
    (∀ w, 0 ≤ fullLaw q w) ∧ (∑ w, fullLaw q w = 1)
    ∧ (∀ φ ψ, fullE q (fun w => φ w.1 * ψ w.2) = cutE φ * radE q ψ)
    ∧ cutE (Fwr R) = 0 ∧ cutE (fun p => Fwr R p ^ 2) = 1
    ∧ cutE Gwr = 0 ∧ cutE (fun p => Gwr p ^ 2) = 1
    ∧ 1 - cutE (fun p => Fwr R p * Gwr p) ^ 2
        / (cutE (fun p => Fwr R p ^ 2) * cutE (fun p => Gwr p ^ 2)) = R
    ∧ radE q (fun p => (s * radU p) ^ 2) = s ^ 2
    ∧ FiberCondExp.condExp (radFactor q) vRec (fun p => s * radU p)
        = (fun p => s * q * radV p)
    ∧ radE q (fun p => (s * q * radV p) ^ 2) = s ^ 2 * q ^ 2
    ∧ Real.sqrt (s ^ 2 * q ^ 2) / Real.sqrt (s ^ 2) = q :=
  ⟨fullLaw_nonneg h0q h1q, fullLaw_sum q, product_factorization q,
    cutE_F R, cutE_F_sq h0R h1R, cutE_G, cutE_G_sq, cutoff_residual h0R h1R,
    radial_entrance_stock q s, radial_condExp q s, radial_outer_stock q s,
    radial_step_ratio hs h0q⟩

end YMCutoffRadial

end CutoffRadialIndependent

/-! ### `cor:YM-radial-four-leaf` — Positive four-leaf radial acquisition

Rendering: the two consecutive separating shells and the selected source
form the finite Markov chain `S2 → S1 → In` (outer shell `R+1`, inner
shell `R`, interior), with outer shell law `m2` and conditional kernels
`κ` (inner shell given outer shell) and `κi` (interior given inner
shell).  The conditional four-leaf replica tree samples one outer shell
value, one inner spine `t` with two conditionally independent interior
leaves `u₁, u₂`, and two independent side branches `(t₁,w₁), (t₂,w₂)`
through their own inner shells.  The positive reads are
`A⁻ = U_{N,R}(t)² ≥ 0` and `A⁺ = U_{N,R+1}(r)² ≥ 0` (squares of the
shell messages), the replica identities (YMBR.14) are
`read_minus_expectation`, `read_plus_expectation`, and
`read_diff_expectation` with `E D ≥ 0` from the conditional
Cauchy–Schwarz contraction, and the Creutz ratio identity (YMBR.15) is
`creutz_ratio` under `I_{N,R} > 0` with the absorbing-zero norm-ratio
`qStep = ‖U_{R+1}‖/‖U_R‖`.  The independence clause is
`radial_card_product_independent` and `cutoff_card_factorization`: under
the product with any independent cutoff card the radial reads are
unchanged and joint expectations factorize.  The final sentence on the
finite Haar-endpoint coefficients `A₁,A₂,A₃` is a scope remark about
`thm:YM-outer-replica-card` and is not a mathematical claim of this
record. -/

section RadialFourLeaf

namespace YMRadialFourLeaf

variable {S2 S1 In : Type*} [Fintype S2] [Fintype S1] [Fintype In]

/-- The inner shell message `U_{N,R}(t) = E[Y | t]`. -/
def msg1 (κi : S1 → In → ℝ) (Y : S1 → In → ℝ) (t : S1) : ℝ := ∑ u, κi t u * Y t u

/-- The outer shell message `U_{N,R+1}(r) = E[U_{N,R} | r]`. -/
def msg2 (κ : S2 → S1 → ℝ) (κi : S1 → In → ℝ) (Y : S1 → In → ℝ) (r : S2) : ℝ :=
  ∑ t, κ r t * msg1 κi Y t

/-- The inner stock `I_{N,R} = ‖U_{N,R}‖²`. -/
def stockI (m2 : S2 → ℝ) (κ : S2 → S1 → ℝ) (κi : S1 → In → ℝ)
    (Y : S1 → In → ℝ) : ℝ :=
  ∑ r, ∑ t, m2 r * κ r t * msg1 κi Y t ^ 2

/-- The outer stock `I_{N,R+1} = ‖U_{N,R+1}‖²`. -/
def stockO (m2 : S2 → ℝ) (κ : S2 → S1 → ℝ) (κi : S1 → In → ℝ)
    (Y : S1 → In → ℝ) : ℝ :=
  ∑ r, m2 r * msg2 κ κi Y r ^ 2

/-- The positive inner read `A⁻ = U_{N,R}(t)²`. -/
def readMinus (κi : S1 → In → ℝ) (Y : S1 → In → ℝ) (t : S1) : ℝ := msg1 κi Y t ^ 2

/-- The positive outer read `A⁺ = U_{N,R+1}(r)²`. -/
def readPlus (κ : S2 → S1 → ℝ) (κi : S1 → In → ℝ) (Y : S1 → In → ℝ) (r : S2) : ℝ :=
  msg2 κ κi Y r ^ 2

/-- The difference read `D = A⁻ - A⁺` on the tree spine. -/
def readD (κ : S2 → S1 → ℝ) (κi : S1 → In → ℝ) (Y : S1 → In → ℝ)
    (r : S2) (t : S1) : ℝ :=
  readMinus κi Y t - readPlus κ κi Y r

/-- The four-leaf conditional replica tree expectation: one outer shell
value `r`, a central spine `t` with two interior leaves `u₁, u₂`, and
two independent side branches `(t₁,w₁)`, `(t₂,w₂)`. -/
def treeE (m2 : S2 → ℝ) (κ : S2 → S1 → ℝ) (κi : S1 → In → ℝ)
    (φ : S2 → S1 → In → In → S1 → In → S1 → In → ℝ) : ℝ :=
  ∑ r, ∑ t, ∑ u₁, ∑ u₂, ∑ t₁, ∑ w₁, ∑ t₂, ∑ w₂,
    m2 r * (κ r t * κi t u₁ * κi t u₂) * (κ r t₁ * κi t₁ w₁) * (κ r t₂ * κi t₂ w₂)
      * φ r t u₁ u₂ t₁ w₁ t₂ w₂

omit [Fintype S2] in
/-- The positive reads are nonnegative. -/
theorem reads_nonneg (κ : S2 → S1 → ℝ) (κi : S1 → In → ℝ) (Y : S1 → In → ℝ)
    (r : S2) (t : S1) :
    0 ≤ readMinus κi Y t ∧ 0 ≤ readPlus κ κi Y r :=
  ⟨sq_nonneg _, sq_nonneg _⟩

section Collapse

variable {m2 : S2 → ℝ} {κ : S2 → S1 → ℝ} {κi : S1 → In → ℝ}

omit [Fintype S2] in
/-- Averaging one side branch against a constant. -/
theorem branch_collapse (hκ : ∀ r, ∑ t, κ r t = 1) (hκi : ∀ t, ∑ u, κi t u = 1)
    (r : S2) (c : ℝ) :
    ∑ t', ∑ w', κ r t' * κi t' w' * c = c := by
  have h1 : ∀ t', ∑ w', κ r t' * κi t' w' * c = κ r t' * c := by
    intro t'
    calc ∑ w', κ r t' * κi t' w' * c
        = ∑ w', κi t' w' * (κ r t' * c) :=
          Finset.sum_congr rfl fun w' _ => by ring
      _ = κ r t' * c := by rw [← Finset.sum_mul, hκi t', one_mul]
  rw [Finset.sum_congr rfl fun t' _ => h1 t', ← Finset.sum_mul, hκ r, one_mul]

omit [Fintype S2] in
/-- Averaging both side branches against a constant. -/
theorem double_branch_collapse (hκ : ∀ r, ∑ t, κ r t = 1)
    (hκi : ∀ t, ∑ u, κi t u = 1) (r : S2) (c : ℝ) :
    ∑ t₁, ∑ w₁, ∑ t₂, ∑ w₂,
      (κ r t₁ * κi t₁ w₁) * (κ r t₂ * κi t₂ w₂) * c = c := by
  have h : ∀ (t₁ : S1) (w₁ : In),
      ∑ t₂, ∑ w₂, (κ r t₁ * κi t₁ w₁) * (κ r t₂ * κi t₂ w₂) * c
        = κ r t₁ * κi t₁ w₁ * c := by
    intro t₁ w₁
    calc ∑ t₂, ∑ w₂, (κ r t₁ * κi t₁ w₁) * (κ r t₂ * κi t₂ w₂) * c
        = ∑ t₂, ∑ w₂, κ r t₂ * κi t₂ w₂ * (κ r t₁ * κi t₁ w₁ * c) := by
          exact Finset.sum_congr rfl fun t₂ _ =>
            Finset.sum_congr rfl fun w₂ _ => by ring
      _ = κ r t₁ * κi t₁ w₁ * c := branch_collapse hκ hκi r _
  calc ∑ t₁, ∑ w₁, ∑ t₂, ∑ w₂, (κ r t₁ * κi t₁ w₁) * (κ r t₂ * κi t₂ w₂) * c
      = ∑ t₁, ∑ w₁, κ r t₁ * κi t₁ w₁ * c :=
        Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun w₁ _ => h t₁ w₁
    _ = c := branch_collapse hκ hκi r c

omit [Fintype S2] in
/-- Averaging the spine against a constant. -/
theorem spine_collapse (hκ : ∀ r, ∑ t, κ r t = 1) (hκi : ∀ t, ∑ u, κi t u = 1)
    (r : S2) (c : ℝ) :
    ∑ t, ∑ u₁, ∑ u₂, κ r t * κi t u₁ * κi t u₂ * c = c := by
  have h1 : ∀ (t : S1) (u₁ : In),
      ∑ u₂, κ r t * κi t u₁ * κi t u₂ * c = κ r t * κi t u₁ * c := by
    intro t u₁
    calc ∑ u₂, κ r t * κi t u₁ * κi t u₂ * c
        = ∑ u₂, κi t u₂ * (κ r t * κi t u₁ * c) :=
          Finset.sum_congr rfl fun u₂ _ => by ring
      _ = κ r t * κi t u₁ * c := by rw [← Finset.sum_mul, hκi t, one_mul]
  have h2 : ∀ t : S1, ∑ u₁, κ r t * κi t u₁ * c = κ r t * c := by
    intro t
    calc ∑ u₁, κ r t * κi t u₁ * c
        = ∑ u₁, κi t u₁ * (κ r t * c) :=
          Finset.sum_congr rfl fun u₁ _ => by ring
      _ = κ r t * c := by rw [← Finset.sum_mul, hκi t, one_mul]
  calc ∑ t, ∑ u₁, ∑ u₂, κ r t * κi t u₁ * κi t u₂ * c
      = ∑ t, ∑ u₁, κ r t * κi t u₁ * c :=
        Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u₁ _ => h1 t u₁
    _ = ∑ t, κ r t * c := Finset.sum_congr rfl fun t _ => h2 t
    _ = c := by rw [← Finset.sum_mul, hκ r, one_mul]

omit [Fintype S2] in
/-- One side branch reads the outer message. -/
theorem branch_message (Y : S1 → In → ℝ) (r : S2) :
    ∑ t', ∑ w', κ r t' * κi t' w' * Y t' w' = msg2 κ κi Y r := by
  unfold msg2 msg1
  refine Finset.sum_congr rfl fun t' _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w' _ => by ring

omit [Fintype S2] in
/-- Both side branches read the squared outer message, with a constant
spectator factor. -/
theorem double_branch_product (Y : S1 → In → ℝ) (r : S2) (c : ℝ) :
    ∑ t₁, ∑ w₁, ∑ t₂, ∑ w₂,
      (κ r t₁ * κi t₁ w₁ * Y t₁ w₁) * (κ r t₂ * κi t₂ w₂ * Y t₂ w₂) * c
      = msg2 κ κi Y r ^ 2 * c := by
  have hA : ∀ (t₁ : S1) (w₁ : In),
      ∑ t₂, ∑ w₂, (κ r t₁ * κi t₁ w₁ * Y t₁ w₁) * (κ r t₂ * κi t₂ w₂ * Y t₂ w₂) * c
        = κ r t₁ * κi t₁ w₁ * Y t₁ w₁ * (msg2 κ κi Y r * c) := by
    intro t₁ w₁
    calc ∑ t₂, ∑ w₂, (κ r t₁ * κi t₁ w₁ * Y t₁ w₁) * (κ r t₂ * κi t₂ w₂ * Y t₂ w₂) * c
        = ∑ t₂, ∑ w₂, κ r t₂ * κi t₂ w₂ * Y t₂ w₂
            * (κ r t₁ * κi t₁ w₁ * Y t₁ w₁ * c) := by
          exact Finset.sum_congr rfl fun t₂ _ =>
            Finset.sum_congr rfl fun w₂ _ => by ring
      _ = ∑ t₂, (∑ w₂, κ r t₂ * κi t₂ w₂ * Y t₂ w₂)
            * (κ r t₁ * κi t₁ w₁ * Y t₁ w₁ * c) := by
          refine Finset.sum_congr rfl fun t₂ _ => ?_
          rw [Finset.sum_mul]
      _ = (∑ t₂, ∑ w₂, κ r t₂ * κi t₂ w₂ * Y t₂ w₂)
            * (κ r t₁ * κi t₁ w₁ * Y t₁ w₁ * c) := by
          rw [Finset.sum_mul]
      _ = κ r t₁ * κi t₁ w₁ * Y t₁ w₁ * (msg2 κ κi Y r * c) := by
          rw [branch_message Y r]; ring
  calc ∑ t₁, ∑ w₁, ∑ t₂, ∑ w₂,
        (κ r t₁ * κi t₁ w₁ * Y t₁ w₁) * (κ r t₂ * κi t₂ w₂ * Y t₂ w₂) * c
      = ∑ t₁, ∑ w₁, κ r t₁ * κi t₁ w₁ * Y t₁ w₁ * (msg2 κ κi Y r * c) :=
        Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun w₁ _ => hA t₁ w₁
    _ = ∑ t₁, (∑ w₁, κ r t₁ * κi t₁ w₁ * Y t₁ w₁) * (msg2 κ κi Y r * c) := by
        refine Finset.sum_congr rfl fun t₁ _ => ?_
        rw [Finset.sum_mul]
    _ = (∑ t₁, ∑ w₁, κ r t₁ * κi t₁ w₁ * Y t₁ w₁) * (msg2 κ κi Y r * c) := by
        rw [Finset.sum_mul]
    _ = msg2 κ κi Y r ^ 2 * c := by rw [branch_message Y r]; ring

/-- **(YMBR.14), inner read**: `E[A⁻] = E[Y(u₁)Y(u₂)] = I_{N,R}`. -/
theorem read_minus_expectation (hκ : ∀ r, ∑ t, κ r t = 1)
    (hκi : ∀ t, ∑ u, κi t u = 1) (Y : S1 → In → ℝ) :
    treeE m2 κ κi (fun _ t u₁ u₂ _ _ _ _ => Y t u₁ * Y t u₂)
      = stockI m2 κ κi Y := by
  unfold treeE stockI
  refine Finset.sum_congr rfl fun r _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  have hu : ∀ (u₁ u₂ : In),
      ∑ t₁, ∑ w₁, ∑ t₂, ∑ w₂,
        m2 r * (κ r t * κi t u₁ * κi t u₂) * (κ r t₁ * κi t₁ w₁)
          * (κ r t₂ * κi t₂ w₂) * (Y t u₁ * Y t u₂)
        = m2 r * (κ r t * κi t u₁ * κi t u₂) * (Y t u₁ * Y t u₂) := by
    intro u₁ u₂
    calc ∑ t₁, ∑ w₁, ∑ t₂, ∑ w₂,
          m2 r * (κ r t * κi t u₁ * κi t u₂) * (κ r t₁ * κi t₁ w₁)
            * (κ r t₂ * κi t₂ w₂) * (Y t u₁ * Y t u₂)
        = ∑ t₁, ∑ w₁, ∑ t₂, ∑ w₂,
            (κ r t₁ * κi t₁ w₁) * (κ r t₂ * κi t₂ w₂)
              * (m2 r * (κ r t * κi t u₁ * κi t u₂) * (Y t u₁ * Y t u₂)) := by
          exact Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun w₁ _ =>
            Finset.sum_congr rfl fun t₂ _ => Finset.sum_congr rfl fun w₂ _ => by ring
      _ = m2 r * (κ r t * κi t u₁ * κi t u₂) * (Y t u₁ * Y t u₂) :=
          double_branch_collapse hκ hκi r _
  rw [Finset.sum_congr rfl fun u₁ _ => Finset.sum_congr rfl fun u₂ _ => hu u₁ u₂]
  conv_rhs => rw [sq]
  unfold msg1
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u₁ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u₂ _ => by ring

/-- **(YMBR.14), outer read**: `E[A⁺] = E[Y(w₁)Y(w₂)] = I_{N,R+1}`. -/
theorem read_plus_expectation (hκ : ∀ r, ∑ t, κ r t = 1)
    (hκi : ∀ t, ∑ u, κi t u = 1) (Y : S1 → In → ℝ) :
    treeE m2 κ κi (fun _ _ _ _ t₁ w₁ t₂ w₂ => Y t₁ w₁ * Y t₂ w₂)
      = stockO m2 κ κi Y := by
  unfold treeE stockO
  refine Finset.sum_congr rfl fun r _ => ?_
  have hspine : ∀ (t : S1) (u₁ u₂ : In),
      ∑ t₁, ∑ w₁, ∑ t₂, ∑ w₂,
        m2 r * (κ r t * κi t u₁ * κi t u₂) * (κ r t₁ * κi t₁ w₁)
          * (κ r t₂ * κi t₂ w₂) * (Y t₁ w₁ * Y t₂ w₂)
        = κ r t * κi t u₁ * κi t u₂ * (m2 r * msg2 κ κi Y r ^ 2) := by
    intro t u₁ u₂
    calc ∑ t₁, ∑ w₁, ∑ t₂, ∑ w₂,
          m2 r * (κ r t * κi t u₁ * κi t u₂) * (κ r t₁ * κi t₁ w₁)
            * (κ r t₂ * κi t₂ w₂) * (Y t₁ w₁ * Y t₂ w₂)
        = ∑ t₁, ∑ w₁, ∑ t₂, ∑ w₂,
            (κ r t₁ * κi t₁ w₁ * Y t₁ w₁) * (κ r t₂ * κi t₂ w₂ * Y t₂ w₂)
              * (m2 r * (κ r t * κi t u₁ * κi t u₂)) := by
          exact Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun w₁ _ =>
            Finset.sum_congr rfl fun t₂ _ => Finset.sum_congr rfl fun w₂ _ => by ring
      _ = msg2 κ κi Y r ^ 2 * (m2 r * (κ r t * κi t u₁ * κi t u₂)) :=
          double_branch_product Y r _
      _ = κ r t * κi t u₁ * κi t u₂ * (m2 r * msg2 κ κi Y r ^ 2) := by ring
  rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u₁ _ =>
    Finset.sum_congr rfl fun u₂ _ => hspine t u₁ u₂]
  exact spine_collapse hκ hκi r _

/-- The tree expectation is linear in differences of observables. -/
theorem treeE_sub (φ ψ : S2 → S1 → In → In → S1 → In → S1 → In → ℝ) :
    treeE m2 κ κi (fun r t u₁ u₂ t₁ w₁ t₂ w₂ =>
        φ r t u₁ u₂ t₁ w₁ t₂ w₂ - ψ r t u₁ u₂ t₁ w₁ t₂ w₂)
      = treeE m2 κ κi φ - treeE m2 κ κi ψ := by
  unfold treeE
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **(YMBR.14), difference read**: `E[D] = I_{N,R} - I_{N,R+1}`. -/
theorem read_diff_expectation (hκ : ∀ r, ∑ t, κ r t = 1)
    (hκi : ∀ t, ∑ u, κi t u = 1) (Y : S1 → In → ℝ) :
    treeE m2 κ κi (fun _ t u₁ u₂ t₁ w₁ t₂ w₂ =>
        Y t u₁ * Y t u₂ - Y t₁ w₁ * Y t₂ w₂)
      = stockI m2 κ κi Y - stockO m2 κ κi Y := by
  have h := treeE_sub (m2 := m2) (κ := κ) (κi := κi)
    (fun _ t u₁ u₂ _ _ _ _ => Y t u₁ * Y t u₂)
    (fun _ _ _ _ t₁ w₁ t₂ w₂ => Y t₁ w₁ * Y t₂ w₂)
  rw [read_minus_expectation hκ hκi Y, read_plus_expectation hκ hκi Y] at h
  simpa using h

/-- The inner stock is nonnegative. -/
theorem stockI_nonneg (hm2 : ∀ r, 0 ≤ m2 r) (hκnn : ∀ r t, 0 ≤ κ r t)
    (Y : S1 → In → ℝ) : 0 ≤ stockI m2 κ κi Y :=
  Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun t _ =>
    mul_nonneg (mul_nonneg (hm2 r) (hκnn r t)) (sq_nonneg _)

/-- The outer stock is nonnegative. -/
theorem stockO_nonneg (hm2 : ∀ r, 0 ≤ m2 r) (Y : S1 → In → ℝ) :
    0 ≤ stockO m2 κ κi Y :=
  Finset.sum_nonneg fun r _ => mul_nonneg (hm2 r) (sq_nonneg _)

/-- **Outward information loss**: `I_{N,R+1} ≤ I_{N,R}` by the
conditional Cauchy–Schwarz contraction, so `E[D] ≥ 0`. -/
theorem stock_antitone (hm2 : ∀ r, 0 ≤ m2 r) (hκnn : ∀ r t, 0 ≤ κ r t)
    (hκ : ∀ r, ∑ t, κ r t = 1) (Y : S1 → In → ℝ) :
    stockO m2 κ κi Y ≤ stockI m2 κ κi Y := by
  unfold stockO stockI
  refine Finset.sum_le_sum fun r _ => ?_
  have hcs : msg2 κ κi Y r ^ 2 ≤ ∑ t, κ r t * msg1 κi Y t ^ 2 := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun t => κ r t * msg1 κi Y t) (f := κ r)
      (g := fun t => κ r t * msg1 κi Y t ^ 2)
      (fun t _ => hκnn r t)
      (fun t _ => mul_nonneg (hκnn r t) (sq_nonneg _))
      (fun t _ => le_of_eq (by ring))
    rw [hκ r, one_mul] at h
    exact h
  calc m2 r * msg2 κ κi Y r ^ 2
      ≤ m2 r * ∑ t, κ r t * msg1 κi Y t ^ 2 :=
        mul_le_mul_of_nonneg_left hcs (hm2 r)
    _ = ∑ t, m2 r * κ r t * msg1 κi Y t ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring

/-- **(YMBR.14), bundled**: the four-leaf replica tree gives positive
reads acquiring `I_{N,R}`, `I_{N,R+1}`, and their nonnegative
difference. -/
theorem four_leaf_reads (hm2 : ∀ r, 0 ≤ m2 r) (hκnn : ∀ r t, 0 ≤ κ r t)
    (hκ : ∀ r, ∑ t, κ r t = 1) (hκi : ∀ t, ∑ u, κi t u = 1) (Y : S1 → In → ℝ) :
    treeE m2 κ κi (fun _ t u₁ u₂ _ _ _ _ => Y t u₁ * Y t u₂) = stockI m2 κ κi Y
    ∧ treeE m2 κ κi (fun _ _ _ _ t₁ w₁ t₂ w₂ => Y t₁ w₁ * Y t₂ w₂)
        = stockO m2 κ κi Y
    ∧ treeE m2 κ κi (fun _ t u₁ u₂ t₁ w₁ t₂ w₂ =>
        Y t u₁ * Y t u₂ - Y t₁ w₁ * Y t₂ w₂)
        = stockI m2 κ κi Y - stockO m2 κ κi Y
    ∧ 0 ≤ stockI m2 κ κi Y - stockO m2 κ κi Y :=
  ⟨read_minus_expectation hκ hκi Y, read_plus_expectation hκ hκi Y,
    read_diff_expectation hκ hκi Y,
    sub_nonneg.mpr (stock_antitone hm2 hκnn hκ Y)⟩

/-- The absorbing-zero one-step norm ratio `q_{N,R} = ‖U_{R+1}‖/‖U_R‖`. -/
noncomputable def qStep (m2 : S2 → ℝ) (κ : S2 → S1 → ℝ) (κi : S1 → In → ℝ)
    (Y : S1 → In → ℝ) : ℝ :=
  Real.sqrt (stockO m2 κ κi Y) / Real.sqrt (stockI m2 κ κi Y)

/-- **(YMBR.15), the Creutz ratio identity**: whenever `I_{N,R} > 0`,
`q² = I_{N,R+1}/I_{N,R} = 1 - E[D]/E[A⁻]`. -/
theorem creutz_ratio (hm2 : ∀ r, 0 ≤ m2 r) (Y : S1 → In → ℝ)
    (hI : 0 < stockI m2 κ κi Y) :
    qStep m2 κ κi Y ^ 2 = stockO m2 κ κi Y / stockI m2 κ κi Y
    ∧ stockO m2 κ κi Y / stockI m2 κ κi Y
        = 1 - (stockI m2 κ κi Y - stockO m2 κ κi Y) / stockI m2 κ κi Y := by
  constructor
  · unfold qStep
    rw [div_pow, Real.sq_sqrt (stockO_nonneg hm2 Y), Real.sq_sqrt hI.le]
  · field_simp
    ring

end Collapse

section ProductIndependence

variable {m2 : S2 → ℝ} {κ : S2 → S1 → ℝ} {κi : S1 → In → ℝ}

/-- Expectation under the product of an independent cutoff card `mw`
and the four-leaf tree law. -/
def jointE {W : Type*} [Fintype W] (mw : W → ℝ) (m2 : S2 → ℝ) (κ : S2 → S1 → ℝ)
    (κi : S1 → In → ℝ)
    (Φ : W → S2 → S1 → In → In → S1 → In → S1 → In → ℝ) : ℝ :=
  ∑ ω, mw ω * treeE m2 κ κi (Φ ω)

/-- The tree expectation is homogeneous. -/
theorem treeE_const_mul (c : ℝ) (φ : S2 → S1 → In → In → S1 → In → S1 → In → ℝ) :
    treeE m2 κ κi (fun r t u₁ u₂ t₁ w₁ t₂ w₂ => c * φ r t u₁ u₂ t₁ w₁ t₂ w₂)
      = c * treeE m2 κ κi φ := by
  unfold treeE
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ =>
    Finset.sum_congr rfl fun u₁ _ => Finset.sum_congr rfl fun u₂ _ =>
    Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun w₁ _ =>
    Finset.sum_congr rfl fun t₂ _ => Finset.sum_congr rfl fun w₂ _ => by ring

/-- **Cutoff–radial factorization**: joint expectations of a cutoff
writer times a radial four-leaf observable factorize. -/
theorem cutoff_card_factorization {W : Type*} [Fintype W] (mw : W → ℝ)
    (ψ : W → ℝ) (φ : S2 → S1 → In → In → S1 → In → S1 → In → ℝ) :
    jointE mw m2 κ κi (fun ω r t u₁ u₂ t₁ w₁ t₂ w₂ =>
        ψ ω * φ r t u₁ u₂ t₁ w₁ t₂ w₂)
      = (∑ ω, mw ω * ψ ω) * treeE m2 κ κi φ := by
  unfold jointE
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [treeE_const_mul]
  ring

/-- **The radial card is independent of the outer cutoff card**: under
the product with any independent cutoff card, every radial four-leaf
expectation — hence the reads, stocks, and Creutz ratio — is
unchanged. -/
theorem radial_card_product_independent {W : Type*} [Fintype W] (mw : W → ℝ)
    (hmw : ∑ ω, mw ω = 1) (φ : S2 → S1 → In → In → S1 → In → S1 → In → ℝ) :
    jointE mw m2 κ κi (fun _ r t u₁ u₂ t₁ w₁ t₂ w₂ =>
        φ r t u₁ u₂ t₁ w₁ t₂ w₂)
      = treeE m2 κ κi φ := by
  unfold jointE
  rw [← Finset.sum_mul, hmw, one_mul]

end ProductIndependence

end YMRadialFourLeaf

end RadialFourLeaf

/-! ### `cor:YM-seventeen-loss` — Strict finite-card source–geometry incompatibility

Rendering: the seventeen-sector stock of
`thm:YM-seventeen-leading-sectors` (YMBL.12) enters as hypotheses, since
that theorem is a separate manuscript record: `P₄` (the planar-ribbon
line projection) and `P♯` (the sixteen-line nonplanar projection) are
symmetric idempotent real matrices with orthogonal ranges
(`P₄P♯ = 0`), `‖P₁₇φ‖² = 17·B₄` for `P₁₇ = P₄ + P♯`, and
`‖P♯φ‖² = 16·B₄`, with `B₄ = 18⁻⁹⁷` and `φ` the assembled leading
source coefficient `φ₃₂,₁⁽⁴⁸⁾`.  The conclusions are exactly
(YMBL.14)–(YMBL.15): `A₁ = ‖φ‖² ≥ 17B₄`, `‖(I-P₄)φ‖² ≥ 16B₄`,
`0 < ϑ₃₂ = B₄/A₁ ≤ 1/17`, and `1 - ϑ₃₂ ≥ 16/17`, together with the
planar-line contribution `‖P₄φ‖² = B₄` used in the manuscript proof. -/

section SeventeenLoss

namespace YMSeventeenLoss

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- Squared Euclidean norm of a real vector. -/
def sqN (v : k → ℝ) : ℝ := v ⬝ᵥ v

/-- The exact seventeen-sector unit `B₄ = 18⁻⁹⁷`. -/
noncomputable def B4 : ℝ := (18 : ℝ) ^ (-97 : ℤ)

/-- `B₄ > 0`. -/
theorem B4_pos : 0 < B4 := zpow_pos (by norm_num) _

omit [DecidableEq k] in
/-- Squared norms are nonnegative. -/
theorem sqN_nonneg (v : k → ℝ) : 0 ≤ sqN v :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

omit [DecidableEq k] in
/-- Moving a matrix across the real dot product transposes it. -/
theorem mulVec_dot (M : Matrix k k ℝ) (u v : k → ℝ) :
    (M *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Mᵀ *ᵥ v) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq k] in
/-- For a symmetric idempotent, `‖Pφ‖² = ⟨φ, Pφ⟩`. -/
theorem proj_sqN {P : Matrix k k ℝ} (hs : Pᵀ = P) (hi : P * P = P) (x : k → ℝ) :
    sqN (P *ᵥ x) = x ⬝ᵥ (P *ᵥ x) := by
  unfold sqN
  rw [mulVec_dot, hs, Matrix.mulVec_mulVec, hi]

omit [DecidableEq k] in
/-- Pythagoras for a symmetric idempotent. -/
theorem proj_pythagoras {P : Matrix k k ℝ} (hs : Pᵀ = P) (hi : P * P = P)
    (x : k → ℝ) :
    sqN x = sqN (P *ᵥ x) + sqN (fun i => x i - (P *ᵥ x) i) := by
  have h1 : sqN (P *ᵥ x) = x ⬝ᵥ (P *ᵥ x) := proj_sqN hs hi x
  have hcomm : (P *ᵥ x) ⬝ᵥ x = x ⬝ᵥ (P *ᵥ x) := dotProduct_comm _ _
  have hexp : sqN (fun i => x i - (P *ᵥ x) i)
      = sqN x - (P *ᵥ x) ⬝ᵥ x - x ⬝ᵥ (P *ᵥ x) + sqN (P *ᵥ x) := by
    unfold sqN
    simp only [dotProduct]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, hcomm, h1]
  ring

omit [DecidableEq k] in
/-- Contraction for a symmetric idempotent: `‖Pφ‖² ≤ ‖φ‖²`. -/
theorem proj_contraction {P : Matrix k k ℝ} (hs : Pᵀ = P) (hi : P * P = P)
    (x : k → ℝ) : sqN (P *ᵥ x) ≤ sqN x := by
  have h := proj_pythagoras hs hi x
  have h2 := sqN_nonneg fun i => x i - (P *ᵥ x) i
  linarith

/-- **Strict finite-card source–geometry incompatibility
(YMBL.14)–(YMBL.15)**: the exact seventeen-sector stock forces
`A₁ ≥ 17B₄`, the planar contribution `‖P₄φ‖² = B₄`,
`‖(I-P₄)φ‖² ≥ 16B₄`, and hence `0 < ϑ₃₂ ≤ 1/17` and
`1 - ϑ₃₂ ≥ 16/17`: at least sixteen seventeenths of the certified
leading shell-one stock lies outside the planar line. -/
theorem seventeen_loss (P4 Ps : Matrix k k ℝ) (φ : k → ℝ)
    (h4s : P4ᵀ = P4) (h4i : P4 * P4 = P4)
    (hss : Psᵀ = Ps) (hsi : Ps * Ps = Ps)
    (horth : P4 * Ps = 0)
    (h17 : sqN ((P4 + Ps) *ᵥ φ) = 17 * B4)
    (hsh : sqN (Ps *ᵥ φ) = 16 * B4) :
    17 * B4 ≤ sqN φ
    ∧ sqN (P4 *ᵥ φ) = B4
    ∧ 16 * B4 ≤ sqN ((1 - P4) *ᵥ φ)
    ∧ 0 < B4 / sqN φ ∧ B4 / sqN φ ≤ 1 / 17
    ∧ 16 / 17 ≤ 1 - B4 / sqN φ := by
  have horth' : Ps * P4 = 0 := by
    have h := congrArg Matrix.transpose horth
    rw [Matrix.transpose_mul, h4s, hss, Matrix.transpose_zero] at h
    exact h
  have h17s : (P4 + Ps)ᵀ = P4 + Ps := by rw [Matrix.transpose_add, h4s, hss]
  have h17i : (P4 + Ps) * (P4 + Ps) = P4 + Ps := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h4i, hsi, horth, horth']
    simp
  have hA1 : 17 * B4 ≤ sqN φ := by
    have h := proj_contraction h17s h17i φ
    rw [h17] at h
    exact h
  have hcross : (P4 *ᵥ φ) ⬝ᵥ (Ps *ᵥ φ) = 0 := by
    rw [mulVec_dot, h4s, Matrix.mulVec_mulVec, horth, Matrix.zero_mulVec,
      dotProduct_zero]
  have hsplit : sqN ((P4 + Ps) *ᵥ φ) = sqN (P4 *ᵥ φ) + sqN (Ps *ᵥ φ) := by
    have hadd : (P4 + Ps) *ᵥ φ = fun i => (P4 *ᵥ φ) i + (Ps *ᵥ φ) i := by
      rw [Matrix.add_mulVec]
      rfl
    rw [hadd]
    unfold sqN
    have hexp : ∑ i, ((P4 *ᵥ φ) i + (Ps *ᵥ φ) i) * ((P4 *ᵥ φ) i + (Ps *ᵥ φ) i)
        = ∑ i, ((P4 *ᵥ φ) i * (P4 *ᵥ φ) i + (Ps *ᵥ φ) i * (Ps *ᵥ φ) i
          + 2 * ((P4 *ᵥ φ) i * (Ps *ᵥ φ) i)) :=
      Finset.sum_congr rfl fun i _ => by ring
    calc ∑ i, ((P4 *ᵥ φ) i + (Ps *ᵥ φ) i) * ((P4 *ᵥ φ) i + (Ps *ᵥ φ) i)
        = ∑ i, ((P4 *ᵥ φ) i * (P4 *ᵥ φ) i + (Ps *ᵥ φ) i * (Ps *ᵥ φ) i
            + 2 * ((P4 *ᵥ φ) i * (Ps *ᵥ φ) i)) := hexp
      _ = (P4 *ᵥ φ) ⬝ᵥ (P4 *ᵥ φ) + (Ps *ᵥ φ) ⬝ᵥ (Ps *ᵥ φ)
            + 2 * ((P4 *ᵥ φ) ⬝ᵥ (Ps *ᵥ φ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          rfl
      _ = (P4 *ᵥ φ) ⬝ᵥ (P4 *ᵥ φ) + (Ps *ᵥ φ) ⬝ᵥ (Ps *ᵥ φ) := by
          rw [hcross, mul_zero, add_zero]
  have hP4 : sqN (P4 *ᵥ φ) = B4 := by
    rw [h17, hsh] at hsplit
    linarith
  have hcompl : 16 * B4 ≤ sqN ((1 - P4) *ᵥ φ) := by
    have hPs1 : Ps * (1 - P4) = Ps := by
      rw [Matrix.mul_sub, Matrix.mul_one, horth', sub_zero]
    have hcontr := proj_contraction hss hsi ((1 - P4) *ᵥ φ)
    rw [Matrix.mulVec_mulVec, hPs1, hsh] at hcontr
    exact hcontr
  have hA1pos : 0 < sqN φ :=
    lt_of_lt_of_le (by have := B4_pos; linarith) hA1
  have hθpos : 0 < B4 / sqN φ := div_pos B4_pos hA1pos
  have hθle : B4 / sqN φ ≤ 1 / 17 := by
    rw [div_le_div_iff₀ hA1pos (by norm_num : (0 : ℝ) < 17)]
    linarith
  exact ⟨hA1, hP4, hcompl, hθpos, hθle, by linarith⟩

end YMSeventeenLoss

end SeventeenLoss

/-! ### `lem:YM-rational-face-certificate` — Rational optimum-face certificate

Rendering: the rational linear system is `A *ᵥ x = b`, `x ≥ 0` over `ℚ`
with finite row and column types.  The first dual certificate is a
vector `y` with `Aᵀy ≤ c` and `bᵀy = L`, together with a feasible `x₀`
attaining `cᵀx₀ = L`; the lemma proves weak duality, that `L` is the
optimum value, and complementary slackness: every minimizer is
supported on the zero-reduced-cost columns.  The "further rational dual
on the affine face" is a pair `(y', t)` with `Aᵀy' + t·c ≤ d` and
`bᵀy' + t·L = M` (a dual certificate for the face
`{Ax = b, x ≥ 0, cᵀx = L}`), which gives `dᵀx ≥ M` there; combined with
the hypothesis `dᵀx ≤ M` on the face, `dᵀx = M` throughout the optimum
face.  The final proof remark on clearing denominators is a proof
device, not a stated claim. -/

section RationalFaceCertificate

namespace YMRationalFace

variable {ι γ : Type*} [Fintype ι] [Fintype γ]

/-- Feasibility for the rational system `Ax = b`, `x ≥ 0`. -/
def Feasible (A : Matrix ι γ ℚ) (b : ι → ℚ) (x : γ → ℚ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b

/-- Minimality of `cᵀx` over the feasible set. -/
def IsMinimizer (A : Matrix ι γ ℚ) (b : ι → ℚ) (c x : γ → ℚ) : Prop :=
  Feasible A b x ∧ ∀ x', Feasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'

/-- The reduced-cost identity: `cᵀx - yᵀb = ∑ⱼ (c - Aᵀy)ⱼ xⱼ` on the
affine constraint set. -/
theorem reduced_cost_identity (A : Matrix ι γ ℚ) (b : ι → ℚ) (c y : _)
    (x : γ → ℚ) (hx : A *ᵥ x = b) :
    c ⬝ᵥ x - y ⬝ᵥ b = ∑ j, (c j - (y ᵥ* A) j) * x j := by
  rw [← hx, Matrix.dotProduct_mulVec]
  simp only [dotProduct, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Weak duality**: the dual certificate bounds every feasible value
from below by `L = bᵀy`. -/
theorem dual_lower_bound {A : Matrix ι γ ℚ} {b : ι → ℚ} {c y : _} {L : ℚ}
    (hdual : ∀ j, (y ᵥ* A) j ≤ c j) (hL : y ⬝ᵥ b = L)
    (x : γ → ℚ) (hx : Feasible A b x) : L ≤ c ⬝ᵥ x := by
  have h := reduced_cost_identity A b c y x hx.2
  have hnn : 0 ≤ ∑ j, (c j - (y ᵥ* A) j) * x j :=
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hdual j)) (hx.1 j)
  rw [hL] at h
  linarith

/-- **The optimum value is `L`** when some feasible point attains it. -/
theorem optimum_value {A : Matrix ι γ ℚ} {b : ι → ℚ} {c y x0 : _} {L : ℚ}
    (hdual : ∀ j, (y ᵥ* A) j ≤ c j) (hL : y ⬝ᵥ b = L)
    (hx0 : Feasible A b x0) (hx0L : c ⬝ᵥ x0 = L)
    {x : γ → ℚ} (hmin : IsMinimizer A b c x) : c ⬝ᵥ x = L :=
  le_antisymm (hx0L ▸ hmin.2 x0 hx0) (dual_lower_bound hdual hL x hmin.1)

/-- **Complementary slackness**: every minimizer of `cᵀx` is supported
on the columns with zero reduced cost `cⱼ - (Aᵀy)ⱼ = 0`. -/
theorem optimum_support {A : Matrix ι γ ℚ} {b : ι → ℚ} {c y x0 : _} {L : ℚ}
    (hdual : ∀ j, (y ᵥ* A) j ≤ c j) (hL : y ⬝ᵥ b = L)
    (hx0 : Feasible A b x0) (hx0L : c ⬝ᵥ x0 = L)
    {x : γ → ℚ} (hmin : IsMinimizer A b c x) :
    ∀ j, x j ≠ 0 → c j = (y ᵥ* A) j := by
  have hval : c ⬝ᵥ x = L := optimum_value hdual hL hx0 hx0L hmin
  have hzero : ∑ j, (c j - (y ᵥ* A) j) * x j = 0 := by
    have h := reduced_cost_identity A b c y x hmin.1.2
    rw [hval, hL] at h
    linarith
  have hterm : ∀ j ∈ Finset.univ, (c j - (y ᵥ* A) j) * x j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hdual j)) (hmin.1.1 j)).mp hzero
  intro j hj
  have h := hterm j (Finset.mem_univ j)
  rcases mul_eq_zero.mp h with h' | h'
  · linarith [sub_eq_zero.mp h']
  · exact absurd h' hj

/-- **The face dual bound**: a rational dual `(y', t)` on the affine
face `cᵀx = L` gives `dᵀx ≥ M` on the face. -/
theorem face_dual_bound {A : Matrix ι γ ℚ} {b : ι → ℚ} {c d y' : _} {t L M : ℚ}
    (hfd : ∀ j, (y' ᵥ* A) j + t * c j ≤ d j)
    (hM : y' ⬝ᵥ b + t * L = M)
    (x : γ → ℚ) (hx : Feasible A b x) (hxL : c ⬝ᵥ x = L) : M ≤ d ⬝ᵥ x := by
  have hkey : d ⬝ᵥ x - (y' ⬝ᵥ b + t * L)
      = ∑ j, (d j - (y' ᵥ* A) j - t * c j) * x j := by
    rw [← hxL, ← hx.2, Matrix.dotProduct_mulVec]
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hnn : 0 ≤ ∑ j, (d j - (y' ᵥ* A) j - t * c j) * x j :=
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (by linarith [hfd j]) (hx.1 j)
  rw [hM] at hkey
  linarith

/-- **Equality on the optimum face**: if in addition every feasible
point of the face satisfies `dᵀx ≤ M`, then `dᵀx = M` throughout the
face, and in particular at every minimizer. -/
theorem face_dual_equality {A : Matrix ι γ ℚ} {b : ι → ℚ} {c d y y' x0 : _}
    {t L M : ℚ}
    (hdual : ∀ j, (y ᵥ* A) j ≤ c j) (hL : y ⬝ᵥ b = L)
    (hx0 : Feasible A b x0) (hx0L : c ⬝ᵥ x0 = L)
    (hfd : ∀ j, (y' ᵥ* A) j + t * c j ≤ d j)
    (hM : y' ⬝ᵥ b + t * L = M)
    (hupper : ∀ x, Feasible A b x → c ⬝ᵥ x = L → d ⬝ᵥ x ≤ M) :
    (∀ x, Feasible A b x → c ⬝ᵥ x = L → d ⬝ᵥ x = M)
    ∧ ∀ x, IsMinimizer A b c x → d ⬝ᵥ x = M := by
  have hface : ∀ x, Feasible A b x → c ⬝ᵥ x = L → d ⬝ᵥ x = M := fun x hx hxL =>
    le_antisymm (hupper x hx hxL) (face_dual_bound hfd hM x hx hxL)
  exact ⟨hface, fun x hmin =>
    hface x hmin.1 (optimum_value hdual hL hx0 hx0L hmin)⟩

end YMRationalFace

end RationalFaceCertificate

/-! ### `cth:YM-kernel-collapse-soft-direction` — Kernel collapse with a surviving soft direction

Rendering: the scalar positive kernels `F_j(t) = ε_j²·e^{-tλ_j}` for
sequences `ε_j ↓ 0`, `λ_j ↓ 0` (positive, antitone, tending to zero).
`kern_tendstoUniformlyOn` proves convergence to the zero kernel
uniformly on `[0,∞)` — in particular locally uniformly
(`kern_tendstoLocallyUniformlyOn`); for a scalar kernel the trace norm
is the absolute value.  The minimal GNS space of the zero limit is
zero: every GNS Gram form of the zero kernel vanishes
(`zero_kernel_gns`).  The boxed ratio identity (YMFG.25)
`F_j(2τ)/F_j(0) = e^{-2τλ_j} → 1` is `ratio_formula` and
`ratio_tendsto_one`.  `witness_bundle` instantiates the fully explicit
witness `ε_j = λ_j = 1/(j+1)`. -/

section KernelCollapseSoftDirection

namespace YMKernelCollapse

/-- The scalar positive kernels `F_j(t) = ε_j²·e^{-tλ_j}`. -/
noncomputable def kern (ε lam : ℕ → ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ε j ^ 2 * Real.exp (-(t * lam j))

/-- The kernels are positive. -/
theorem kern_pos {ε lam : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (j : ℕ) (t : ℝ) :
    0 < kern ε lam j t :=
  mul_pos (pow_pos (hε j) 2) (Real.exp_pos _)

/-- **Absolute kernel collapse**: the kernels converge to the zero
kernel uniformly on `[0,∞)`. -/
theorem kern_tendstoUniformlyOn {ε lam : ℕ → ℝ} (hε : ∀ j, 0 < ε j)
    (hlam : ∀ j, 0 ≤ lam j) (hε0 : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformlyOn (fun j t => kern ε lam j t) (fun _ => 0) atTop
      (Set.Ici 0) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have h2 : Tendsto (fun j => ε j ^ 2) atTop (𝓝 0) := by
    have := hε0.mul hε0
    simpa [pow_two] using this
  filter_upwards [NormedAddGroup.tendsto_nhds_zero.mp h2 δ hδ] with j hj t ht
  have hb : kern ε lam j t ≤ ε j ^ 2 := by
    unfold kern
    calc ε j ^ 2 * Real.exp (-(t * lam j)) ≤ ε j ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht (hlam j))))
            (sq_nonneg _)
      _ = ε j ^ 2 := mul_one _
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (kern_pos hε j t)]
  calc kern ε lam j t ≤ ε j ^ 2 := hb
    _ ≤ ‖ε j ^ 2‖ := le_abs_self _
    _ < δ := hj

/-- Locally uniform convergence to the zero kernel on `[0,∞)`. -/
theorem kern_tendstoLocallyUniformlyOn {ε lam : ℕ → ℝ} (hε : ∀ j, 0 < ε j)
    (hlam : ∀ j, 0 ≤ lam j) (hε0 : Tendsto ε atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn (fun j t => kern ε lam j t) (fun _ => 0) atTop
      (Set.Ici 0) :=
  (kern_tendstoUniformlyOn hε hlam hε0).tendstoLocallyUniformlyOn

/-- The GNS Gram form of a scalar kernel on a finite family of
time-translates of the entrance vector. -/
def gnsForm (F : ℝ → ℝ) {n : ℕ} (τv : Fin n → ℝ) (a : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * a j * F (τv i + τv j)

/-- **The minimal GNS space of the zero limit is zero**: every GNS Gram
form of the zero kernel vanishes identically. -/
theorem zero_kernel_gns {n : ℕ} (τv : Fin n → ℝ) (a : Fin n → ℝ) :
    gnsForm (fun _ => 0) τv a = 0 := by
  simp [gnsForm]

/-- **(YMFG.25), the ratio identity**: `F_j(2τ)/F_j(0) = e^{-2τλ_j}`. -/
theorem ratio_formula {ε lam : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (τ : ℝ) (j : ℕ) :
    kern ε lam j (2 * τ) / kern ε lam j 0 = Real.exp (-(2 * τ * lam j)) := by
  unfold kern
  rw [zero_mul, neg_zero, Real.exp_zero, mul_one, mul_comm, mul_div_assoc,
    div_self (pow_ne_zero 2 (hε j).ne'), mul_one]

/-- **(YMFG.25), survival of the normalized soft direction**: for every
`τ`, the normalized ratio `F_j(2τ)/F_j(0)` tends to one. -/
theorem ratio_tendsto_one {ε lam : ℕ → ℝ} (hε : ∀ j, 0 < ε j)
    (hlam0 : Tendsto lam atTop (𝓝 0)) (τ : ℝ) :
    Tendsto (fun j => kern ε lam j (2 * τ) / kern ε lam j 0) atTop (𝓝 1) := by
  have h1 : Tendsto (fun j => -(2 * τ * lam j)) atTop (𝓝 0) := by
    have := (hlam0.const_mul (2 * τ)).neg
    simpa using this
  have h2 : Tendsto (fun j => Real.exp (-(2 * τ * lam j))) atTop (𝓝 1) := by
    have := (Real.continuous_exp.continuousAt (x := (0 : ℝ))).tendsto.comp h1
    simpa [Function.comp_def] using this
  exact Tendsto.congr (fun j => (ratio_formula hε τ j).symm) h2

/-- The explicit witness sequence `1/(j+1)`. -/
noncomputable def witSeq : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)

/-- The witness sequence is positive. -/
theorem witSeq_pos (j : ℕ) : 0 < witSeq j := by
  unfold witSeq
  positivity

/-- The witness sequence is antitone (it decreases to zero). -/
theorem witSeq_antitone : Antitone witSeq := by
  intro a b hab
  unfold witSeq
  have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hab
    linarith
  exact one_div_le_one_div_of_le ha hab'

/-- The witness sequence tends to zero. -/
theorem witSeq_tendsto : Tendsto witSeq atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- **The fully explicit countertheorem witness**: with
`ε_j = λ_j = 1/(j+1)` (positive, decreasing to zero), the kernels
`F_j(t) = ε_j²e^{-tλ_j}` are positive, converge to the zero kernel
uniformly (hence locally uniformly) on `[0,∞)`, the zero limit has zero
GNS Gram forms, and for every `τ` the normalized ratio
`F_j(2τ)/F_j(0) = e^{-2τλ_j}` tends to one.  Absolute kernel
convergence therefore determines only the quotient by the limiting
entrance null space. -/
theorem witness_bundle :
    (∀ j t, 0 < kern witSeq witSeq j t)
    ∧ TendstoUniformlyOn (fun j t => kern witSeq witSeq j t) (fun _ => 0)
        atTop (Set.Ici 0)
    ∧ TendstoLocallyUniformlyOn (fun j t => kern witSeq witSeq j t) (fun _ => 0)
        atTop (Set.Ici 0)
    ∧ (∀ (n : ℕ) (τv a : Fin n → ℝ), gnsForm (fun _ => 0) τv a = 0)
    ∧ (∀ τ j, kern witSeq witSeq j (2 * τ) / kern witSeq witSeq j 0
        = Real.exp (-(2 * τ * witSeq j)))
    ∧ ∀ τ, Tendsto (fun j => kern witSeq witSeq j (2 * τ) / kern witSeq witSeq j 0)
        atTop (𝓝 1) :=
  ⟨fun j t => kern_pos witSeq_pos j t,
    kern_tendstoUniformlyOn witSeq_pos (fun j => (witSeq_pos j).le) witSeq_tendsto,
    kern_tendstoLocallyUniformlyOn witSeq_pos (fun j => (witSeq_pos j).le)
      witSeq_tendsto,
    fun _ τv a => zero_kernel_gns τv a,
    fun τ j => ratio_formula witSeq_pos τ j,
    fun τ => ratio_tendsto_one witSeq_pos witSeq_tendsto τ⟩

end YMKernelCollapse

end KernelCollapseSoftDirection

end NCG
