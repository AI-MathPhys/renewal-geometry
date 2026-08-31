import NCG.Grand.AnomalyFreeFieldShellGaugeQuotientExact

/-!
# Gauge-quotient control line

A nowhere-zero finite quotient section gives an explicit scalar trivialization.
In that frame a unitary line connection is a purely imaginary one-form, hence
is uniquely the flat section-parallel connection plus `i η` for a real
one-form `η`.  Finite-loop parallel transport is the exponential of its
integrated connection form.
-/

open scoped ComplexConjugate

namespace NCG
namespace GaugeQuotientControlLine

/-- Pointwise scalar-coordinate trivialization supplied by a nowhere-zero
section of a complex line. -/
theorem section_scalar_coordinate {X : Type*} (σ : X → ℂ)
    (hσ : ∀ x, σ x ≠ 0) (x : X) (v : ℂ) :
    ∃! c : ℂ, c * σ x = v := by
  refine ⟨v / σ x, ?_, ?_⟩
  · exact div_mul_cancel₀ v (hσ x)
  · intro c hc
    apply (mul_right_cancel₀ (hσ x))
    rw [hc, div_mul_cancel₀ v (hσ x)]

/-- In the section frame, the connection that declares the section parallel
has zero connection one-form. -/
def sectionParallelConnection {E : Type*} : E → ℂ := fun _ => 0

/-- A line-connection one-form is unitary exactly when its coefficients are
purely imaginary in the unit section frame. -/
def IsUnitaryConnection {E : Type*} (A : E → ℂ) : Prop :=
  ∀ e, (A e).re = 0

/-- The real one-form underlying a unitary connection. -/
def realConnectionForm {E : Type*} (A : E → ℂ) : E → ℝ :=
  fun e => (A e).im

theorem unitaryConnection_decomposition {E : Type*} (A : E → ℂ)
    (hA : IsUnitaryConnection A) :
    A = fun e => sectionParallelConnection e +
      Complex.I * (realConnectionForm A e : ℂ) := by
  funext e
  apply Complex.ext
  · simp [sectionParallelConnection, realConnectionForm, hA e]
  · simp [sectionParallelConnection, realConnectionForm]

/-- The real coefficient form in the unitary decomposition is unique. -/
theorem unitaryConnection_decomposition_unique {E : Type*} (A : E → ℂ)
    (η : E → ℝ)
    (hη : A = fun e => sectionParallelConnection e + Complex.I * (η e : ℂ)) :
    η = realConnectionForm A := by
  funext e
  have he := congrFun hη e
  have him := congrArg Complex.im he
  symm
  simpa [sectionParallelConnection, realConnectionForm] using him

/-- Exponential parallel transport along a finite ordered loop. -/
noncomputable def loopHolonomy {E : Type*} (A : E → ℂ) (γ : List E) : ℂ :=
  Complex.exp ((γ.map A).sum)

@[simp] theorem sectionParallelConnection_holonomy {E : Type*} (γ : List E) :
    loopHolonomy (sectionParallelConnection (E := E)) γ = 1 := by
  change Complex.exp ((γ.map (fun _ => (0 : ℂ))).sum) = 1
  simp

theorem unitaryConnection_loopHolonomy {E : Type*} (A : E → ℂ)
    (hA : IsUnitaryConnection A) (γ : List E) :
    loopHolonomy A γ =
      Complex.exp (Complex.I * (((γ.map (realConnectionForm A)).sum : ℝ) : ℂ)) := by
  rw [loopHolonomy]
  congr 1
  have hpoint : ∀ e, A e = Complex.I * (realConnectionForm A e : ℂ) := by
    intro e
    have he := congrFun (unitaryConnection_decomposition A hA) e
    simpa [sectionParallelConnection] using he
  induction γ with
  | nil => simp
  | cons e γ ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [hpoint e, ih]
      push_cast
      ring

/-- The anomaly-free quotient's literal unit Berezin section is nowhere zero
and therefore trivializes the control line; every unitary connection then has
the unique real-form decomposition and the advertised loop holonomy. -/
theorem gauge_quotient_control_line
    {E : Type*} (A : E → ℂ) (hA : IsUnitaryConnection A) (γ : List E) :
    (∀ x : SMGaugeCover ⧸ smGaugeHom.ker,
      AnomalyFreeFieldShellGaugeQuotient.unitBerezinSection x ≠ 0) ∧
    A = (fun e => sectionParallelConnection e +
      Complex.I * (realConnectionForm A e : ℂ)) ∧
    (∀ η : E → ℝ,
      A = (fun e => sectionParallelConnection e + Complex.I * (η e : ℂ)) →
        η = realConnectionForm A) ∧
    loopHolonomy A γ =
      Complex.exp (Complex.I * (((γ.map (realConnectionForm A)).sum : ℝ) : ℂ)) := by
  refine ⟨?_, unitaryConnection_decomposition A hA,
    unitaryConnection_decomposition_unique A,
    unitaryConnection_loopHolonomy A hA γ⟩
  intro x
  simp [AnomalyFreeFieldShellGaugeQuotient.unitBerezinSection]

end GaugeQuotientControlLine
end NCG
