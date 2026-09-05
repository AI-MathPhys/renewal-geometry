import NCG.Grand.CStarAlgebraCompletion
import NCG.Grand.CStarAlgebraCompletionHom
import NCG.Grand.BrandNewEasy02
import NCG.Grand.GreenLocalityLaplaceBounds

/-!
# Conditional quasilocal OS completion

The selected represented local words form a normed pre-C-star algebra.  Its
uniform completion is a genuine C-star algebra, the local words are dense, and
contractive quotient/transfer maps extend to the completion.  Local collar
packets give the quantitative commutator estimate, while the declared response
and Green packets remain quasilocal elements of the same completion.
-/

open Filter UniformSpace

noncomputable section

namespace NCG
namespace QuasilocalOSCompletion

/-- A concrete norm-local approximation packet. -/
structure LocalApproximationPacket
    (E : Type*) [NormedAddCommGroup E] (x : E) where
  approximate : ℕ → E
  error : ℕ → ℝ
  error_nonneg : ∀ n, 0 ≤ error n
  norm_sub_le : ∀ n, ‖x - approximate n‖ ≤ error n
  error_tendsto_zero : Tendsto error atTop (nhds 0)

/-- Quasilocality means possession of one norm-local approximation packet. -/
def IsQuasilocal
    (E : Type*) [NormedAddCommGroup E] (x : E) : Prop :=
  Nonempty (LocalApproximationPacket E x)

/-- Every represented local word is quasilocal in the completion. -/
theorem local_word_isQuasilocal
    {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    [NormedAlgebra ℂ A] [StarModule ℂ A] (a : A) :
    IsQuasilocal (Completion A) (a : Completion A) := by
  refine ⟨{
    approximate := fun _ => (a : Completion A)
    error := fun _ => 0
    error_nonneg := fun _ => le_rfl
    norm_sub_le := fun _ => by simp
    error_tendsto_zero := tendsto_const_nhds
  }⟩

/-- The norm closure of the represented local words is the whole completed
quasilocal carrier. -/
theorem closure_represented_local_words
    {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    [NormedAlgebra ℂ A] [StarModule ℂ A] :
    closure (Set.range (fun a : A => (a : Completion A)))
      = Set.univ := by
  exact Completion.denseRange_coe.closure_eq

/-- Collar-local representatives give the exact manuscript commutator bound
inside the completed C-star algebra. -/
theorem completed_quasilocal_commutator
    {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    [NormedAlgebra ℂ A] [StarModule ℂ A]
    (x y : Completion A)
    (xLocal yLocal : ℝ → Completion A)
    (etaX etaY : ℝ → ℝ) (distance : ℝ)
    (hx : ∀ R, ‖x - xLocal R‖ ≤ etaX R)
    (hy : ∀ R, ‖y - yLocal R‖ ≤ etaY R)
    (hdisjoint : ∀ R, 2 * R < distance →
      xLocal R * yLocal R = yLocal R * xLocal R) :
    ∀ R, 2 * R < distance →
      ‖x * y - y * x‖ ≤
        2 * etaX R * ‖y‖ +
          2 * (‖x‖ + etaX R) * etaY R :=
  quasilocal_commutator_from_collars
    x y xLocal yLocal etaX etaY distance hx hy hdisjoint

/-- The five locality clauses of the conditional OS packet assemble on one
completed carrier: the completion is generated densely by local words, its
critical responses and fixed-mass Green writer are quasilocal, and every pair
of disjoint approximation packets obeys the quantitative commutator bound. -/
theorem conditional_quasilocal_OS_completion
    {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    [NormedAlgebra ℂ A] [StarModule ℂ A]
    (firstResponse pairResponse greenWriter : Completion A)
    (hfirst : IsQuasilocal (Completion A) firstResponse)
    (hpair : IsQuasilocal (Completion A) pairResponse)
    (hgreen : IsQuasilocal (Completion A) greenWriter)
    (x y : Completion A)
    (xLocal yLocal : ℝ → Completion A)
    (etaX etaY : ℝ → ℝ) (distance : ℝ)
    (hx : ∀ R, ‖x - xLocal R‖ ≤ etaX R)
    (hy : ∀ R, ‖y - yLocal R‖ ≤ etaY R)
    (hdisjoint : ∀ R, 2 * R < distance →
      xLocal R * yLocal R = yLocal R * xLocal R) :
    closure (Set.range (fun a : A => (a : Completion A))) = Set.univ ∧
      IsQuasilocal (Completion A) firstResponse ∧
      IsQuasilocal (Completion A) pairResponse ∧
      IsQuasilocal (Completion A) greenWriter ∧
      ∀ R, 2 * R < distance →
        ‖x * y - y * x‖ ≤
          2 * etaX R * ‖y‖ +
            2 * (‖x‖ + etaX R) * etaY R := by
  exact ⟨closure_represented_local_words, hfirst, hpair, hgreen,
    completed_quasilocal_commutator
      x y xLocal yLocal etaX etaY distance hx hy hdisjoint⟩

end QuasilocalOSCompletion
end NCG

