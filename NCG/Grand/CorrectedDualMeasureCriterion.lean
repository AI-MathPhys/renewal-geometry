/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.SMSTGraphRegulator

/-!
# Correct dual determinant line and independent-measure criterion

This file gives the complete finite statement of
`thm:SMST-corrected-dual-measure`.

The graph connection is represented by its actual weighted finite-matrix
formula.  Entrywise conjugation reverses that formula, whereas transpose with
source--target reversal preserves it.  A real-linear graph differential
calculus then propagates the same sign table to curvature, vertical moment,
and periods.  The resulting period holonomies identify the conjugate graph
line with the dual line and the transpose graph line with the original line.

The second half separates a genuinely independent Berezin factor from a
Nambu rewriting of the same determinant: a tensor product is phase-trivial
exactly when the second line has the negative connection and inverse
holonomy.  Positive real Gaussian determinants have no complex phase.  A real
Pfaffian line has vanishing local response and curvature, but global
triviality is still exactly its `Z/2` sign-holonomy certificate.
-/

open Matrix

namespace NCG
namespace CorrectedDualMeasureCriterion

/-! ## Weighted graph connection and the conjugate/transpose sign table -/

variable {E F I X : Type*}
  [Fintype E] [Fintype F] [Fintype I]

/-- The finite graph-connection formula, including the edge/block weights
`R_E` from the manuscript.  `A` is the graph frame and `B` its tangent
variation. -/
def weightedGraphConnection (weight : I -> Real)
    (A B : X -> I -> Matrix F E Complex) : X -> Real :=
  fun x => Finset.univ.sum fun i =>
    weight i * (Matrix.trace ((A x i)ᴴ * B x i)).im

/-- Entrywise conjugation of a finite matrix family. -/
def conjugateFamily (A : X -> I -> Matrix F E Complex) :
    X -> I -> Matrix F E Complex :=
  fun x i => (A x i).map star

/-- Transpose together with source--target reversal. -/
def transposeDualFamily (A : X -> I -> Matrix F E Complex) :
    X -> I -> Matrix E F Complex :=
  fun x i => (A x i)ᵀ

/-- Conjugation reverses the weighted graph connection. -/
theorem weightedGraphConnection_conjugate (weight : I -> Real)
    (A B : X -> I -> Matrix F E Complex) :
    weightedGraphConnection weight (conjugateFamily A)
        (conjugateFamily B) =
      -weightedGraphConnection weight A B := by
  funext x
  simp only [weightedGraphConnection, conjugateFamily, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [NCG.dual_trace_conj]
  ring

/-- The Hilbert--Schmidt trace pairing is unchanged by simultaneous
transpose and source--target reversal. -/
theorem trace_conjTranspose_transpose_mul_transpose
    (A B : Matrix F E Complex) :
    Matrix.trace ((Aᵀ)ᴴ * Bᵀ) = Matrix.trace (Aᴴ * B) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- Transpose duality preserves the weighted graph connection. -/
theorem weightedGraphConnection_transposeDual (weight : I -> Real)
    (A B : X -> I -> Matrix F E Complex) :
    weightedGraphConnection weight (transposeDualFamily A)
        (transposeDualFamily B) =
      weightedGraphConnection weight A B := by
  funext x
  unfold weightedGraphConnection transposeDualFamily
  apply Finset.sum_congr rfl
  intro i hi
  rw [trace_conjTranspose_transpose_mul_transpose]

/-- The one-dimensional phase tangent `(A,B) = (1,i)` has nonzero graph
connection.  Since transpose is the identity in this scalar family, this is
the manuscript''s direct counterexample to cancellation by transpose alone. -/
theorem scalar_phase_tangent_graphConnection :
    (weightedGraphConnection
      (E := Fin 1) (F := Fin 1) (I := Fin 1) (X := Unit)
      (fun _ => (1 : Real))
      (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) Complex))
      (fun _ _ => Complex.I •
        (1 : Matrix (Fin 1) (Fin 1) Complex))) () = 1 := by
  simp [weightedGraphConnection, Matrix.trace, Matrix.diag,
    Matrix.mul_apply]

/-! ## Curvature, vertical moment, periods, and graph-line identifications -/

/-- A finite real-linear differential calculus for a graph connection.
Curvature, vertical moment, and loop period are linear observables of the
connection one-form. -/
structure GraphDifferentialCalculus
    (Tangent TwoForm Vertical Loop : Type*) where
  curvature : LinearMap (RingHom.id Real) (Tangent -> Real) (TwoForm -> Real)
  verticalMoment :
    LinearMap (RingHom.id Real) (Tangent -> Real) (Vertical -> Real)
  period : LinearMap (RingHom.id Real) (Tangent -> Real) (Loop -> Real)

/-- The complete local and global data retained from a graph connection. -/
structure GraphPhaseLine
    (Tangent TwoForm Vertical Loop : Type*) where
  connection : Tangent -> Real
  curvature : TwoForm -> Real
  verticalMoment : Vertical -> Real
  period : Loop -> Real

/-- Build the graph phase line from its connection and differential
calculus. -/
def graphPhaseLine {Tangent TwoForm Vertical Loop : Type*}
    (calculus : GraphDifferentialCalculus Tangent TwoForm Vertical Loop)
    (alpha : Tangent -> Real) :
    GraphPhaseLine Tangent TwoForm Vertical Loop where
  connection := alpha
  curvature := calculus.curvature alpha
  verticalMoment := calculus.verticalMoment alpha
  period := calculus.period alpha

/-- Dual connection, curvature, moment, and period. -/
def dualGraphPhaseLine {Tangent TwoForm Vertical Loop : Type*}
    (line : GraphPhaseLine Tangent TwoForm Vertical Loop) :
    GraphPhaseLine Tangent TwoForm Vertical Loop where
  connection := -line.connection
  curvature := -line.curvature
  verticalMoment := -line.verticalMoment
  period := -line.period

/-- Connection-preserving graph-line equivalence, including every local
observable and every protected loop period. -/
def GraphLineEquivalent {Tangent TwoForm Vertical Loop : Type*}
    (left right : GraphPhaseLine Tangent TwoForm Vertical Loop) : Prop :=
  And (forall x, left.connection x = right.connection x)
    (And (forall omega, left.curvature omega = right.curvature omega)
      (And (forall xi, left.verticalMoment xi = right.verticalMoment xi)
        (forall loop, left.period loop = right.period loop)))

/-- Linearity propagates connection negation to curvature, vertical moment,
and loop periods. -/
theorem graphPhaseLine_neg_equivalent_dual
    {Tangent TwoForm Vertical Loop : Type*}
    (calculus : GraphDifferentialCalculus Tangent TwoForm Vertical Loop)
    (alpha : Tangent -> Real) :
    GraphLineEquivalent (graphPhaseLine calculus (-alpha))
      (dualGraphPhaseLine (graphPhaseLine calculus alpha)) := by
  refine ⟨fun x => rfl, ?_, ?_, ?_⟩
  · intro omega
    simp [graphPhaseLine, dualGraphPhaseLine]
  · intro xi
    simp [graphPhaseLine, dualGraphPhaseLine]
  · intro loop
    simp [graphPhaseLine, dualGraphPhaseLine]

/-- Equal connections produce equivalent graph phase lines. -/
theorem graphPhaseLine_equivalent_of_connection_eq
    {Tangent TwoForm Vertical Loop : Type*}
    (calculus : GraphDifferentialCalculus Tangent TwoForm Vertical Loop)
    {alpha beta : Tangent -> Real} (h : alpha = beta) :
    GraphLineEquivalent (graphPhaseLine calculus alpha)
      (graphPhaseLine calculus beta) := by
  subst beta
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Full conjugation sign table: connection, curvature, vertical moment, and
period all identify the conjugate graph line with the dual graph line. -/
theorem conjugateGraphLine_equivalent_dual
    {TwoForm Vertical Loop : Type*}
    (calculus : GraphDifferentialCalculus X TwoForm Vertical Loop)
    (weight : I -> Real) (A B : X -> I -> Matrix F E Complex) :
    GraphLineEquivalent
      (graphPhaseLine calculus
        (weightedGraphConnection weight (conjugateFamily A)
          (conjugateFamily B)))
      (dualGraphPhaseLine
        (graphPhaseLine calculus (weightedGraphConnection weight A B))) := by
  rw [weightedGraphConnection_conjugate]
  exact graphPhaseLine_neg_equivalent_dual calculus _

/-- Full transpose sign table: connection, curvature, vertical moment, and
period identify the transpose-dual graph line with the original line. -/
theorem transposeDualGraphLine_equivalent_original
    {TwoForm Vertical Loop : Type*}
    (calculus : GraphDifferentialCalculus X TwoForm Vertical Loop)
    (weight : I -> Real) (A B : X -> I -> Matrix F E Complex) :
    GraphLineEquivalent
      (graphPhaseLine calculus
        (weightedGraphConnection weight (transposeDualFamily A)
          (transposeDualFamily B)))
      (graphPhaseLine calculus (weightedGraphConnection weight A B)) := by
  apply graphPhaseLine_equivalent_of_connection_eq
  exact weightedGraphConnection_transposeDual weight A B

/-- Holonomy reconstructed from a graph-line period. -/
noncomputable def graphHolonomy {Tangent TwoForm Vertical Loop : Type*}
    (line : GraphPhaseLine Tangent TwoForm Vertical Loop) (loop : Loop) :
    Complex :=
  Complex.exp ((line.period loop : Complex) * Complex.I)

/-- Negating the graph period gives inverse holonomy. -/
theorem dualGraphPhaseLine_holonomy
    {Tangent TwoForm Vertical Loop : Type*}
    (line : GraphPhaseLine Tangent TwoForm Vertical Loop) (loop : Loop) :
    graphHolonomy (dualGraphPhaseLine line) loop =
      (graphHolonomy line loop)⁻¹ := by
  rw [graphHolonomy, graphHolonomy]
  change Complex.exp ((-(line.period loop) : Real) * Complex.I) = _
  push_cast
  rw [show (-(line.period loop : Complex)) * Complex.I =
      -((line.period loop : Complex) * Complex.I) by ring,
    Complex.exp_neg]

/-! ## Independent complex measure lines -/

/-- A complex measure line is represented by its local connection and its
nonvanishing protected-loop holonomies. -/
structure ComplexMeasureLine (Tangent Loop : Type*) where
  connection : Tangent -> Real
  holonomy : Loop -> Complex
  holonomy_ne_zero : forall loop, Ne (holonomy loop) 0

/-- Tensor product of independently integrated complex measure lines. -/
def tensorMeasureLine {Tangent Loop : Type*}
    (left right : ComplexMeasureLine Tangent Loop) :
    ComplexMeasureLine Tangent Loop where
  connection := fun x => left.connection x + right.connection x
  holonomy := fun loop => left.holonomy loop * right.holonomy loop
  holonomy_ne_zero := fun loop =>
    mul_ne_zero (left.holonomy_ne_zero loop) (right.holonomy_ne_zero loop)

/-- Dual measure line: negative connection and inverse holonomy. -/
noncomputable def dualMeasureLine {Tangent Loop : Type*}
    (line : ComplexMeasureLine Tangent Loop) :
    ComplexMeasureLine Tangent Loop where
  connection := -line.connection
  holonomy := fun loop => (line.holonomy loop)⁻¹
  holonomy_ne_zero := fun loop => inv_ne_zero (line.holonomy_ne_zero loop)

/-- Vanishing local phase response and trivial protected holonomy. -/
def PhaseTrivial {Tangent Loop : Type*}
    (line : ComplexMeasureLine Tangent Loop) : Prop :=
  And (forall x, line.connection x = 0)
    (forall loop, line.holonomy loop = 1)

/-- Exact independent-measure criterion: a tensor product cancels its complex
phase precisely when the independently sourced second factor has the dual
connection and inverse holonomy. -/
theorem tensor_phaseTrivial_iff_independent_dual
    {Tangent Loop : Type*} (left right : ComplexMeasureLine Tangent Loop) :
    PhaseTrivial (tensorMeasureLine left right) <->
      And (forall x, right.connection x = -left.connection x)
        (forall loop, right.holonomy loop = (left.holonomy loop)⁻¹) := by
  constructor
  · rintro ⟨hconnection, hholonomy⟩
    constructor
    · intro x
      have hx := hconnection x
      change left.connection x + right.connection x = 0 at hx
      linarith
    · intro loop
      have hloop := hholonomy loop
      change left.holonomy loop * right.holonomy loop = 1 at hloop
      exact eq_inv_of_mul_eq_one_right hloop
  · rintro ⟨hconnection, hholonomy⟩
    constructor
    · intro x
      change left.connection x + right.connection x = 0
      rw [hconnection]
      ring
    · intro loop
      change left.holonomy loop * right.holonomy loop = 1
      rw [hholonomy]
      exact mul_inv_cancel₀ (left.holonomy_ne_zero loop)

/-- An independently integrated dual factor always cancels both local phase
response and global complex holonomy. -/
theorem independent_dual_factor_cancels
    {Tangent Loop : Type*} (line : ComplexMeasureLine Tangent Loop) :
    PhaseTrivial (tensorMeasureLine line (dualMeasureLine line)) := by
  rw [tensor_phaseTrivial_iff_independent_dual]
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- A second copy of the original line (the Nambu/transpose rewriting) cannot
cancel a nonzero local phase response. -/
theorem repeated_nambu_line_does_not_cancel
    {Tangent Loop : Type*} (line : ComplexMeasureLine Tangent Loop)
    (x : Tangent) (hresponse : Ne (line.connection x) 0) :
    Not (PhaseTrivial (tensorMeasureLine line line)) := by
  intro htrivial
  have hx := htrivial.1 x
  change line.connection x + line.connection x = 0 at hx
  apply hresponse
  linarith

/-! ## Determinants and the positive-boson clause -/

/-- An independently integrated conjugate Berezin block has determinant
`det D * conjugate(det D) = normSq(det D)`, so its complex phase cancels. -/
theorem independent_conjugate_block_determinant
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n Complex) :
    D.det * (D.map star).det = (Complex.normSq D.det : Complex) := by
  have hmap : (D.map star).det = star D.det := by
    simpa [RingHom.mapMatrix_apply] using
      ((starRingEnd Complex).map_det D).symm
  rw [hmap, Complex.star_def, Complex.normSq_eq_conj_mul_self]
  ring

/-- A complex number contributes only a positive real modulus. -/
def PositiveRealModulus (z : Complex) : Prop := z.im = 0 /\ 0 < z.re

/-- A positive bosonic Gaussian determinant has no complex phase. -/
theorem positiveBosonicGaussian_has_no_complex_phase
    {J : Type*} [Fintype J] (quadraticEigenvalue : J -> Real)
    (hpositive : forall j, 0 < quadraticEigenvalue j) :
    PositiveRealModulus
      ((Finset.univ.prod quadraticEigenvalue : Real) : Complex) := by
  constructor
  · change (0 : Real) = 0
    rfl
  · change 0 < Finset.univ.prod quadraticEigenvalue
    exact Finset.prod_pos fun j _ => hpositive j

/-! ## Real/Pfaffian measure lines -/

/-- Local data and `Z/2` sign holonomy of a genuinely real/Pfaffian measure
line.  `false` is positive transport and `true` is a sign reversal. -/
structure RealPfaffianMeasureLine
    (Tangent TwoForm Loop : Type*) where
  localPhaseResponse : Tangent -> Real
  curvature : TwoForm -> Real
  signHolonomy : Loop -> Bool

/-- A real measure line has no local complex phase response or curvature. -/
def LocallyRealPfaffian {Tangent TwoForm Loop : Type*}
    (line : RealPfaffianMeasureLine Tangent TwoForm Loop) : Prop :=
  And (forall x, line.localPhaseResponse x = 0)
    (forall omega, line.curvature omega = 0)

/-- Global triviality additionally requires positive sign around every
protected loop. -/
def GloballyTrivialRealLine {Tangent TwoForm Loop : Type*}
    (line : RealPfaffianMeasureLine Tangent TwoForm Loop) : Prop :=
  forall loop, line.signHolonomy loop = false

/-- A negative sign holonomy is a genuine global obstruction even when all
local phase response and curvature vanish. -/
theorem negative_sign_holonomy_obstructs_global_triviality
    {Tangent TwoForm Loop : Type*}
    (line : RealPfaffianMeasureLine Tangent TwoForm Loop)
    (_hlocal : LocallyRealPfaffian line) (loop : Loop)
    (hnegative : line.signHolonomy loop = true) :
    Not (GloballyTrivialRealLine line) := by
  intro hglobal
  have hpositive := hglobal loop
  rw [hnegative] at hpositive
  contradiction

/-- Once the local real/Pfaffian conditions are certified, the final and only
remaining global certificate is the `Z/2` sign holonomy. -/
theorem realPfaffian_final_certificate
    {Tangent TwoForm Loop : Type*}
    (line : RealPfaffianMeasureLine Tangent TwoForm Loop)
    (_hlocal : LocallyRealPfaffian line) :
    GloballyTrivialRealLine line <->
      forall loop, line.signHolonomy loop = false := by
  rfl

end CorrectedDualMeasureCriterion
end NCG
