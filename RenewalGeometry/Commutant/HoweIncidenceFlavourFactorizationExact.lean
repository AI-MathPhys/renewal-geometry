/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.OddChoiOccurrenceExact

/-!
# Incidence–flavour factorization of the Howe certificate
  (`cor:howe-incidence-flavour-factorization`)

Spacetime–gauge duality manuscript, `app:incidence-flavour-stability`.

Carrier `⊕_v V_v ⊗ G_v`, rendered with uniform (padded) module and generation index types as
`V × (M × G)`; factorized incidences `Y_e = E_{t(e)s(e)} ⊗ (D_e ⊗ F_e)` (`incY`), block-diagonal
multiplicity test operators `X = ∑_v E_{vv} ⊗ (1 ⊗ X_v)` (`testOp`), type-central contrasts
`X_v = z_v 1` (`zfun`), additional generators `c_j` commuting with all type-central
contrasts (the non-incidence flavour generators).  The Howe form on the test space is
`𝔾(X,X') = ∑_e (⟨[Y_e,X],[Y_e,X']⟩ + ⟨[Y_eᴴ,X],[Y_eᴴ,X']⟩) + ∑_j ⟨[c_j,X],[c_j,X']⟩`.

* `howeForm_block` — with `κ_e = ‖D_e‖²_HS`,
  `(𝒟_cen z)_e = √κ_e((z_t − z_s)F_e, (z_s − z_t)F_eᴴ)` (`dcen_apply`) and
  `(𝒟_fl X)_e = √κ_e(X_tF_e − F_eX_s, X_sF_eᴴ − F_eᴴX_t)` (`dfl`),
  `𝔾(z + X, z' + X') = ⟨𝒟_cen z,𝒟_cen z'⟩ + ⟨𝒟_cen z,𝒟_fl X'⟩ + ⟨𝒟_fl X,𝒟_cen z'⟩
  + ⟨𝒟_fl X,𝒟_fl X'⟩ + C_extra(X,X')`;
* `restrictedGram_eq_fromBlocks` — in coordinates (bases `zb` of the declared contrasts and
  `xb` of the flavour directions), the restricted Howe Gram is
  `[[A_cen, B], [Bᴴ, C_fl]]` with `A_cen = 𝒟_cenᴴ𝒟_cen`, `B = 𝒟_cenᴴ𝒟_fl`,
  `C_fl = 𝒟_flᴴ𝒟_fl + C_extra`, `C_extra ⪰ 0` (`extraGram_posSemidef`);
* `howe_factorized_schur` — if `A_cen ≻ 0`:
  `S_{fl|cen} = C_extra + 𝒟_flᴴ(I − P_cen)𝒟_fl` with `P_cen = 𝒟_cen A_cen⁻¹ 𝒟_cenᴴ` an
  orthogonal projection onto the range of `𝒟_cen` (`eq:howe-factorized-Schur`), and
  `𝔾 ≻ 0 ⟺ S_{fl|cen} ≻ 0` (rigidity = connectivity + conditional flavour rigidity);
* `edge_forced_of_posDef` — if `𝔾 ≻ 0` and a nonzero declared contrast `z` commutes with every
  incidence except `e₀`, then `Y_{e₀} ≠ 0` and `z_{t(e₀)} ≠ z_{s(e₀)}`: the edge must occur.

Rendering disclosed: module/generation spaces are padded to uniform index types (the
commutators, hence the Howe form, are unchanged by padding); the extra generators are assumed
to commute with the type-central contrasts, which is the meaning of "non-incidence flavour
commutators"; the block form is stated as an identity of sesquilinear forms and, in
coordinates, of Gram matrices.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace RenewalGeometry
namespace HoweIncidenceFlavour

open OddChoiOccurrence

/-! ## Hilbert–Schmidt inner product -/

section HSInner

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `⟨A, B⟩_HS = Tr(Aᴴ B)`. -/
def hsInner (A B : Matrix m n ℂ) : ℂ := (Aᴴ * B).trace

theorem hsInner_eq_sum (A B : Matrix m n ℂ) :
    hsInner A B = ∑ i, ∑ j, star (A i j) * B i j := by
  simp only [hsInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

theorem hsInner_add_left (A A' B : Matrix m n ℂ) :
    hsInner (A + A') B = hsInner A B + hsInner A' B := by
  simp [hsInner, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add]

theorem hsInner_add_right (A B B' : Matrix m n ℂ) :
    hsInner A (B + B') = hsInner A B + hsInner A B' := by
  simp [hsInner, Matrix.mul_add, Matrix.trace_add]

theorem hsInner_neg_neg (A B : Matrix m n ℂ) : hsInner (-A) (-B) = hsInner A B := by
  simp [hsInner]

theorem hsInner_zero_left (B : Matrix m n ℂ) : hsInner 0 B = 0 := by simp [hsInner]

theorem hsInner_zero_right (A : Matrix m n ℂ) : hsInner A 0 = 0 := by simp [hsInner]

theorem hsInner_real_smul (r : ℝ) (A B : Matrix m n ℂ) :
    hsInner ((r : ℂ) • A) ((r : ℂ) • B) = ((r ^ 2 : ℝ) : ℂ) * hsInner A B := by
  simp only [hsInner, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  push_cast; ring

theorem hsSq_conjTranspose_eq (A : Matrix m n ℂ) : hsSq Aᴴ = hsSq A := by
  simp only [hsSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

theorem hsInner_self (A : Matrix m n ℂ) : hsInner A A = (hsSq A : ℂ) := by
  rw [hsInner, Matrix.trace_mul_comm, trace_mul_conjTranspose_eq_hsSq]

end HSInner

/-! ## Factorized incidences and block-diagonal test operators -/

variable {V M G E : Type*} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]
  [Fintype G] [DecidableEq G] [Fintype E] [DecidableEq E]

/-- The factorized incidence `Y_e = E_{t(e)s(e)} ⊗ (D_e ⊗ F_e)`. -/
noncomputable def incY (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (e : E) : Matrix (V × (M × G)) (V × (M × G)) ℂ :=
  single (tgt e) (src e) (1 : ℂ) ⊗ₖ (D e ⊗ₖ F e)

/-- The block-diagonal multiplicity test operator `∑_v E_{vv} ⊗ (1 ⊗ X_v)`. -/
noncomputable def testOp (M : Type*) [Fintype M] [DecidableEq M] (W : V → Matrix G G ℂ) :
    Matrix (V × (M × G)) (V × (M × G)) ℂ :=
  ∑ v, single v v (1 : ℂ) ⊗ₖ ((1 : Matrix M M ℂ) ⊗ₖ W v)

/-- Type-central contrasts `X_v = z_v 1`. -/
noncomputable def zfun (z : V → ℂ) : V → Matrix G G ℂ := fun v => z v • 1

/-- The commutator `[c, X]`. -/
def comm {n : Type*} [Fintype n] (c X : Matrix n n ℂ) : Matrix n n ℂ := c * X - X * c

theorem comm_add {n : Type*} [Fintype n] (c X X' : Matrix n n ℂ) :
    comm c (X + X') = comm c X + comm c X' := by
  simp only [comm, Matrix.mul_add, Matrix.add_mul]; abel

theorem testOp_add (W W' : V → Matrix G G ℂ) :
    testOp M (W + W') = testOp M W + testOp M W' := by
  simp only [testOp, Pi.add_apply, Matrix.kronecker_add, ← Finset.sum_add_distrib]

theorem testOp_mul_block (a b : V) (D' : Matrix M M ℂ) (F' : Matrix G G ℂ)
    (W : V → Matrix G G ℂ) :
    testOp M W * (single a b (1 : ℂ) ⊗ₖ (D' ⊗ₖ F')) = single a b (1 : ℂ) ⊗ₖ (D' ⊗ₖ (W a * F')) := by
  rw [testOp, Finset.sum_mul, Finset.sum_eq_single a]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, single_mul_single_same, one_mul,
      Matrix.one_mul]
  · intro v _ hv
    rw [← Matrix.mul_kronecker_mul]
    simp [hv]
  · simp

theorem block_mul_testOp (a b : V) (D' : Matrix M M ℂ) (F' : Matrix G G ℂ)
    (W : V → Matrix G G ℂ) :
    (single a b (1 : ℂ) ⊗ₖ (D' ⊗ₖ F')) * testOp M W = single a b (1 : ℂ) ⊗ₖ (D' ⊗ₖ (F' * W b)) := by
  rw [testOp, Finset.mul_sum, Finset.sum_eq_single b]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, single_mul_single_same, one_mul,
      Matrix.mul_one]
  · intro v _ hv
    rw [← Matrix.mul_kronecker_mul]
    simp [Ne.symm hv]
  · simp

theorem comm_block_testOp (a b : V) (D' : Matrix M M ℂ) (F' : Matrix G G ℂ)
    (W : V → Matrix G G ℂ) :
    comm (single a b (1 : ℂ) ⊗ₖ (D' ⊗ₖ F')) (testOp M W)
      = -(single a b (1 : ℂ) ⊗ₖ (D' ⊗ₖ (W a * F' - F' * W b))) := by
  rw [comm, block_mul_testOp, testOp_mul_block]
  ext ⟨i, j, k⟩ ⟨i', j', k'⟩
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.kroneckerMap_apply]
  ring

theorem hsInner_block (a b : V) (D' : Matrix M M ℂ) (A A' : Matrix G G ℂ) :
    hsInner (single a b (1 : ℂ) ⊗ₖ (D' ⊗ₖ A)) (single a b (1 : ℂ) ⊗ₖ (D' ⊗ₖ A'))
      = (hsSq D' : ℂ) * hsInner A A' := by
  rw [hsInner, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    Matrix.trace_kronecker, Matrix.conjTranspose_single, star_one, single_mul_single_same, one_mul,
    Matrix.trace_single_eq_same, one_mul, ← hsInner_self, hsInner, hsInner]

theorem incY_conjTranspose (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (e : E) :
    (incY src tgt D F e)ᴴ = single (src e) (tgt e) (1 : ℂ) ⊗ₖ ((D e)ᴴ ⊗ₖ (F e)ᴴ) := by
  rw [incY, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_single, star_one]

/-! ## The edge maps `𝒟_cen`, `𝒟_fl` -/

/-- `𝒟(W)_e = √κ_e (W_t F_e − F_e W_s, W_s F_eᴴ − F_eᴴ W_t)`. -/
noncomputable def edgeVec (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (W : V → Matrix G G ℂ) : E → Matrix G G ℂ × Matrix G G ℂ :=
  fun e => (((Real.sqrt (hsSq (D e)) : ℝ) : ℂ) • (W (tgt e) * F e - F e * W (src e)),
    ((Real.sqrt (hsSq (D e)) : ℝ) : ℂ) • (W (src e) * (F e)ᴴ - (F e)ᴴ * W (tgt e)))

/-- `𝒟_cen z = 𝒟(z 1)`. -/
noncomputable def dcen (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (z : V → ℂ) : E → Matrix G G ℂ × Matrix G G ℂ :=
  edgeVec src tgt D F (zfun z)

/-- `𝒟_fl X = 𝒟(X)`. -/
noncomputable def dfl (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (X : V → Matrix G G ℂ) : E → Matrix G G ℂ × Matrix G G ℂ :=
  edgeVec src tgt D F X

omit [DecidableEq V] [DecidableEq M] [DecidableEq E] in
/-- `(𝒟_cen z)_e = √κ_e ((z_t − z_s) F_e, (z_s − z_t) F_eᴴ)`. -/
theorem dcen_apply (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (z : V → ℂ) (e : E) :
    dcen src tgt D F z e =
      (((Real.sqrt (hsSq (D e)) : ℝ) : ℂ) • ((z (tgt e) - z (src e)) • F e),
        ((Real.sqrt (hsSq (D e)) : ℝ) : ℂ) • ((z (src e) - z (tgt e)) • (F e)ᴴ)) := by
  simp only [dcen, edgeVec, zfun, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, sub_smul]

/-- The edge-space inner product `∑_e (⟨a_e, b_e⟩ + ⟨a'_e, b'_e⟩)`. -/
def edgeInner (a b : E → Matrix G G ℂ × Matrix G G ℂ) : ℂ :=
  ∑ e, (hsInner (a e).1 (b e).1 + hsInner (a e).2 (b e).2)

/-- The incidence part of the Howe form on test operators. -/
noncomputable def incidencePart (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (W W' : V → Matrix G G ℂ) : ℂ :=
  ∑ e, (hsInner (comm (incY src tgt D F e) (testOp M W)) (comm (incY src tgt D F e) (testOp M W'))
    + hsInner (comm (incY src tgt D F e)ᴴ (testOp M W))
        (comm (incY src tgt D F e)ᴴ (testOp M W')))

/-- The non-incidence (extra) part `C_extra`. -/
noncomputable def extraForm {J : Type*} [Fintype J]
    (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ) (W W' : V → Matrix G G ℂ) : ℂ :=
  ∑ j, hsInner (comm (c j) (testOp M W)) (comm (c j) (testOp M W'))

/-- The relative Howe form on the block-diagonal test space. -/
noncomputable def howeForm (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    {J : Type*} [Fintype J] (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (W W' : V → Matrix G G ℂ) : ℂ :=
  incidencePart src tgt D F W W' + extraForm c W W'

theorem incidencePart_eq (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (W W' : V → Matrix G G ℂ) :
    incidencePart (M := M) src tgt D F W W'
      = edgeInner (edgeVec src tgt D F W) (edgeVec src tgt D F W') := by
  unfold incidencePart edgeInner
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [incY_conjTranspose, incY, comm_block_testOp, comm_block_testOp, comm_block_testOp,
    comm_block_testOp, hsInner_neg_neg, hsInner_neg_neg, hsInner_block, hsInner_block]
  simp only [edgeVec, hsInner_real_smul]
  rw [Real.sq_sqrt (hsSq_nonneg _), hsSq_conjTranspose_eq]

/-! ## The block form of the Howe form -/

section Block

variable {J : Type*} [Fintype J]

omit [DecidableEq V] [DecidableEq M] [DecidableEq E] in
theorem edgeVec_add (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (W W' : V → Matrix G G ℂ) :
    edgeVec src tgt D F (W + W') = edgeVec src tgt D F W + edgeVec src tgt D F W' := by
  funext e
  refine Prod.ext ?_ ?_ <;>
    simp only [edgeVec, Pi.add_apply, Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add,
      smul_sub, smul_add] <;> abel

omit [DecidableEq V] [DecidableEq E] in
theorem edgeInner_add_left (a a' b : E → Matrix G G ℂ × Matrix G G ℂ) :
    edgeInner (a + a') b = edgeInner a b + edgeInner a' b := by
  simp only [edgeInner, Pi.add_apply, Prod.fst_add, Prod.snd_add, hsInner_add_left,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

omit [DecidableEq V] [DecidableEq E] in
theorem edgeInner_add_right (a b b' : E → Matrix G G ℂ × Matrix G G ℂ) :
    edgeInner a (b + b') = edgeInner a b + edgeInner a b' := by
  simp only [edgeInner, Pi.add_apply, Prod.fst_add, Prod.snd_add, hsInner_add_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

theorem extraForm_zfun_left (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (hc : ∀ j z, comm (c j) (testOp M (zfun (G := G) z)) = 0) (z : V → ℂ)
    (W : V → Matrix G G ℂ) : extraForm c (zfun z) W = 0 := by
  simp [extraForm, hc, hsInner_zero_left]

theorem extraForm_zfun_right (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (hc : ∀ j z, comm (c j) (testOp M (zfun (G := G) z)) = 0) (z : V → ℂ)
    (W : V → Matrix G G ℂ) : extraForm c W (zfun z) = 0 := by
  simp [extraForm, hc, hsInner_zero_right]

theorem extraForm_add_zfun (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (hc : ∀ j z, comm (c j) (testOp M (zfun (G := G) z)) = 0) (z z' : V → ℂ)
    (X X' : V → Matrix G G ℂ) : extraForm c (zfun z + X) (zfun z' + X') = extraForm c X X' := by
  simp only [extraForm, testOp_add, comm_add, hc, zero_add]

theorem howeForm_eq (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ) (W W' : V → Matrix G G ℂ) :
    howeForm src tgt D F c W W'
      = edgeInner (edgeVec src tgt D F W) (edgeVec src tgt D F W') + extraForm c W W' := by
  rw [howeForm, incidencePart_eq]

/-- **Block form** (operator level): for type-central contrasts `z, z'` and flavour directions
`X, X'`, `𝔾(z + X, z' + X') = ⟨𝒟_cen z,𝒟_cen z'⟩ + ⟨𝒟_cen z,𝒟_fl X'⟩ + ⟨𝒟_fl X,𝒟_cen z'⟩
+ ⟨𝒟_fl X,𝒟_fl X'⟩ + C_extra(X, X')`. -/
theorem howeForm_block (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (hc : ∀ j z, comm (c j) (testOp M (zfun (G := G) z)) = 0) (z z' : V → ℂ)
    (X X' : V → Matrix G G ℂ) :
    howeForm src tgt D F c (zfun z + X) (zfun z' + X')
      = edgeInner (dcen src tgt D F z) (dcen src tgt D F z')
        + edgeInner (dcen src tgt D F z) (dfl src tgt D F X')
        + edgeInner (dfl src tgt D F X) (dcen src tgt D F z')
        + edgeInner (dfl src tgt D F X) (dfl src tgt D F X') + extraForm c X X' := by
  rw [howeForm_eq, edgeVec_add, edgeVec_add, edgeInner_add_left, edgeInner_add_right,
    edgeInner_add_right, extraForm_add_zfun c hc]
  simp only [dcen, dfl]
  ring

end Block

/-! ## Coordinates: the restricted Gram matrix -/

section Coordinates

variable {J Zc Xf : Type*} [Fintype J] [Fintype Zc] [DecidableEq Zc] [Fintype Xf] [DecidableEq Xf]

/-- Vectorization of the edge space `E × {incidence, adjoint} × G × G`. -/
def evec (a : E → Matrix G G ℂ × Matrix G G ℂ) : E × Bool × G × G → ℂ :=
  fun k => if k.2.1 then (a k.1).2 k.2.2.1 k.2.2.2 else (a k.1).1 k.2.2.1 k.2.2.2

omit [DecidableEq V] [Fintype V] [DecidableEq E] in
theorem edgeInner_eq_dotProduct (a b : E → Matrix G G ℂ × Matrix G G ℂ) :
    edgeInner a b = star (evec a) ⬝ᵥ evec b := by
  unfold edgeInner dotProduct
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [evec, ite_true, Bool.false_eq_true, ite_false, Fintype.sum_prod_type, hsInner_eq_sum,
    Pi.star_apply]
  ring

/-- The synthesis matrix of `𝒟_cen` on a basis `zb` of the declared contrasts. -/
noncomputable def cenSynth (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (zb : Zc → V → ℂ) : Matrix (E × Bool × G × G) Zc ℂ :=
  Matrix.of fun k a => evec (dcen src tgt D F (zb a)) k

/-- The synthesis matrix of `𝒟_fl` on a basis `xb` of the flavour directions. -/
noncomputable def flSynth (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (xb : Xf → V → Matrix G G ℂ) : Matrix (E × Bool × G × G) Xf ℂ :=
  Matrix.of fun k b => evec (dfl src tgt D F (xb b)) k

/-- The stacked extra-commutator synthesis. -/
noncomputable def extraSynth (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (xb : Xf → V → Matrix G G ℂ) : Matrix (J × ((V × (M × G)) × (V × (M × G)))) Xf ℂ :=
  Matrix.of fun q b => comm (c q.1) (testOp M (xb b)) q.2.1 q.2.2

/-- `C_extra = (extra synthesis)ᴴ (extra synthesis)`. -/
noncomputable def extraGram (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (xb : Xf → V → Matrix G G ℂ) : Matrix Xf Xf ℂ :=
  (extraSynth c xb)ᴴ * extraSynth c xb

theorem extraGram_posSemidef (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (xb : Xf → V → Matrix G G ℂ) : (extraGram c xb).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

theorem extraGram_apply (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (xb : Xf → V → Matrix G G ℂ) (b b' : Xf) :
    extraGram c xb b b' = extraForm c (xb b) (xb b') := by
  simp only [extraGram, extraSynth, extraForm, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Fintype.sum_prod_type, hsInner_eq_sum]

/-- The tested elements: contrasts `z 1` for the basis `zb`, then flavour directions `xb`. -/
noncomputable def testElem (zb : Zc → V → ℂ) (xb : Xf → V → Matrix G G ℂ) :
    Zc ⊕ Xf → V → Matrix G G ℂ :=
  Sum.elim (fun a => zfun (zb a)) xb

/-- The relative Howe Gram restricted to the block-diagonal test space. -/
noncomputable def restrictedGram (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ) (zb : Zc → V → ℂ)
    (xb : Xf → V → Matrix G G ℂ) : Matrix (Zc ⊕ Xf) (Zc ⊕ Xf) ℂ :=
  Matrix.of fun a b => howeForm src tgt D F c (testElem zb xb a) (testElem zb xb b)

theorem synth_gram_apply {K ι κ : Type*} [Fintype K] (f : ι → K → ℂ) (g : κ → K → ℂ)
    (a : ι) (b : κ) :
    ((Matrix.of fun k a => f a k)ᴴ * Matrix.of fun k b => g b k) a b = star (f a) ⬝ᵥ g b := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct,
    Pi.star_apply]

/-- **Block form of the restricted Howe Gram**:
`𝔾|_test = [[𝒟_cenᴴ𝒟_cen, 𝒟_cenᴴ𝒟_fl], [𝒟_flᴴ𝒟_cen, 𝒟_flᴴ𝒟_fl + C_extra]]`. -/
theorem restrictedGram_eq_fromBlocks (src tgt : E → V) (D : E → Matrix M M ℂ)
    (F : E → Matrix G G ℂ) (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (hc : ∀ j z, comm (c j) (testOp M (zfun (G := G) z)) = 0) (zb : Zc → V → ℂ)
    (xb : Xf → V → Matrix G G ℂ) :
    restrictedGram src tgt D F c zb xb =
      fromBlocks ((cenSynth src tgt D F zb)ᴴ * cenSynth src tgt D F zb)
        ((cenSynth src tgt D F zb)ᴴ * flSynth src tgt D F xb)
        ((flSynth src tgt D F xb)ᴴ * cenSynth src tgt D F zb)
        ((flSynth src tgt D F xb)ᴴ * flSynth src tgt D F xb + extraGram c xb) := by
  ext (a | a) (b | b)
  · simp only [restrictedGram, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, testElem, Sum.elim_inl,
      howeForm_eq, extraForm_zfun_left c hc, add_zero, cenSynth, synth_gram_apply,
      edgeInner_eq_dotProduct, dcen]
  · simp only [restrictedGram, Matrix.of_apply, Matrix.fromBlocks_apply₁₂, testElem, Sum.elim_inl,
      Sum.elim_inr, howeForm_eq, extraForm_zfun_left c hc, add_zero, cenSynth, flSynth,
      synth_gram_apply, edgeInner_eq_dotProduct, dcen, dfl]
  · simp only [restrictedGram, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, testElem, Sum.elim_inl,
      Sum.elim_inr, howeForm_eq, extraForm_zfun_right c hc, add_zero, cenSynth, flSynth,
      synth_gram_apply, edgeInner_eq_dotProduct, dcen, dfl]
  · simp only [restrictedGram, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, testElem, Sum.elim_inr,
      howeForm_eq, Matrix.add_apply, extraGram_apply, flSynth, synth_gram_apply,
      edgeInner_eq_dotProduct, dfl]

end Coordinates

/-! ## The Schur complement -/

section Schur

/-- Strict positivity of a Hermitian block matrix with positive-definite corner is strict
positivity of its Schur complement. -/
theorem posDef_fromBlocks_iff {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {A : Matrix m m ℂ} (B : Matrix m n ℂ) {D : Matrix n n ℂ} (hA : A.PosDef)
    (hD : D.IsHermitian) :
    (fromBlocks A B Bᴴ D).PosDef ↔ (D - Bᴴ * A⁻¹ * B).PosDef := by
  letI : Invertible A := hA.isUnit.invertible
  have hH : (fromBlocks A B Bᴴ D).IsHermitian := Matrix.IsHermitian.fromBlocks hA.1 rfl hD
  have hAinv : (A⁻¹)ᴴ = A⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hA.1.eq]
  have hSH : (D - Bᴴ * A⁻¹ * B).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sub, hD.eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hAinv, Matrix.mul_assoc]
  have key : ∀ (x : m → ℂ) (y : n → ℂ),
      star (Sum.elim x y) ⬝ᵥ (fromBlocks A B Bᴴ D *ᵥ Sum.elim x y)
        = star (x + (A⁻¹ * B) *ᵥ y) ⬝ᵥ (A *ᵥ (x + (A⁻¹ * B) *ᵥ y))
          + star y ⬝ᵥ ((D - Bᴴ * A⁻¹ * B) *ᵥ y) := by
    intro x y
    have := Matrix.schur_complement_eq₁₁ B D x y hA.1
    simpa only [Matrix.dotProduct_mulVec] using this
  constructor
  · intro h
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hSH fun y hy => ?_
    have hne : Sum.elim (-((A⁻¹ * B) *ᵥ y)) y ≠ 0 := by
      intro h0
      apply hy
      funext i
      have := congrFun h0 (Sum.inr i)
      simpa using this
    have := h.dotProduct_mulVec_pos hne
    rw [key, neg_add_cancel, Matrix.mulVec_zero, dotProduct_zero, zero_add] at this
    exact this
  · intro hS
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun w hw => ?_
    rw [← Sum.elim_comp_inl_inr w, key]
    by_cases hy : w ∘ Sum.inr = 0
    · rw [hy, Matrix.mulVec_zero, add_zero, Matrix.mulVec_zero, dotProduct_zero, add_zero]
      refine hA.dotProduct_mulVec_pos fun hx => hw ?_
      rw [← Sum.elim_comp_inl_inr w, hx, hy]
      funext i; cases i <;> rfl
    · exact add_pos_of_nonneg_of_pos (hA.posSemidef.dotProduct_mulVec_nonneg _)
        (hS.dotProduct_mulVec_pos hy)

/-- **`eq:howe-factorized-Schur`** (matrix level).  For `A_cen = 𝒟_cenᴴ𝒟_cen ≻ 0`,
`B = 𝒟_cenᴴ𝒟_fl`, `C_fl = 𝒟_flᴴ𝒟_fl + C_extra`: the Schur complement is
`S_{fl|cen} = C_extra + 𝒟_flᴴ(I − P_cen)𝒟_fl`, `P_cen = 𝒟_cen A_cen⁻¹ 𝒟_cenᴴ` is the orthogonal
projection onto the range of `𝒟_cen`, and the block Gram is positive definite iff
`S_{fl|cen}` is. -/
theorem howe_factorized_schur {K Zc Xf : Type*} [Fintype K] [DecidableEq K] [Fintype Zc]
    [DecidableEq Zc] [Fintype Xf] [DecidableEq Xf] (Dc : Matrix K Zc ℂ) (Df : Matrix K Xf ℂ)
    (Cx : Matrix Xf Xf ℂ) (hA : (Dcᴴ * Dc).PosDef) (hCx : Cx.IsHermitian) :
    (Dfᴴ * Df + Cx) - (Dcᴴ * Df)ᴴ * (Dcᴴ * Dc)⁻¹ * (Dcᴴ * Df)
        = Cx + Dfᴴ * (1 - Dc * (Dcᴴ * Dc)⁻¹ * Dcᴴ) * Df ∧
    (Dc * (Dcᴴ * Dc)⁻¹ * Dcᴴ) * (Dc * (Dcᴴ * Dc)⁻¹ * Dcᴴ) = Dc * (Dcᴴ * Dc)⁻¹ * Dcᴴ ∧
    (Dc * (Dcᴴ * Dc)⁻¹ * Dcᴴ)ᴴ = Dc * (Dcᴴ * Dc)⁻¹ * Dcᴴ ∧
    (Dc * (Dcᴴ * Dc)⁻¹ * Dcᴴ) * Dc = Dc ∧
    ((fromBlocks (Dcᴴ * Dc) (Dcᴴ * Df) (Dfᴴ * Dc) (Dfᴴ * Df + Cx)).PosDef ↔
      (Cx + Dfᴴ * (1 - Dc * (Dcᴴ * Dc)⁻¹ * Dcᴴ) * Df).PosDef) := by
  have hdet : IsUnit (Dcᴴ * Dc).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hinv : (Dcᴴ * Dc)⁻¹ * (Dcᴴ * Dc) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hAinv : ((Dcᴴ * Dc)⁻¹)ᴴ = (Dcᴴ * Dc)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hA.1.eq]
  have hid : (Dfᴴ * Df + Cx) - (Dcᴴ * Df)ᴴ * (Dcᴴ * Dc)⁻¹ * (Dcᴴ * Df)
      = Cx + Dfᴴ * (1 - Dc * (Dcᴴ * Dc)⁻¹ * Dcᴴ) * Df := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    abel
  have hPD : (Dc * (Dcᴴ * Dc)⁻¹ * Dcᴴ) * Dc = Dc := by
    rw [Matrix.mul_assoc (Dc * (Dcᴴ * Dc)⁻¹) Dcᴴ Dc, Matrix.mul_assoc Dc, hinv, Matrix.mul_one]
  refine ⟨hid, ?_, ?_, hPD, ?_⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPD]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hAinv, Matrix.mul_assoc]
  · have hB : Dfᴴ * Dc = (Dcᴴ * Df)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have hDH : (Dfᴴ * Df + Cx).IsHermitian :=
      (Matrix.isHermitian_conjTranspose_mul_self Df).add hCx
    rw [hB, posDef_fromBlocks_iff _ hA hDH, hid]

end Schur

/-! ## Edge occurrence forced by strict positivity, and the packaged corollary -/

section Edge

variable {J Zc Xf : Type*} [Fintype J] [Fintype Zc] [DecidableEq Zc] [Fintype Xf] [DecidableEq Xf]

theorem evec_dcen_apply (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (z : V → ℂ) (k : E × Bool × G × G) :
    evec (dcen src tgt D F z) k = (z (tgt k.1) - z (src k.1)) *
      (if k.2.1 then -(((Real.sqrt (hsSq (D k.1)) : ℝ) : ℂ) * (F k.1)ᴴ k.2.2.1 k.2.2.2)
        else ((Real.sqrt (hsSq (D k.1)) : ℝ) : ℂ) * F k.1 k.2.2.1 k.2.2.2) := by
  obtain ⟨e, β, i, j⟩ := k
  cases β <;> simp only [evec, dcen_apply, Matrix.smul_apply, smul_eq_mul, Bool.false_eq_true,
    ite_false, ite_true] <;> ring

theorem evec_dcen_sum (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (zb : Zc → V → ℂ) (w : Zc → ℂ) :
    evec (dcen src tgt D F (∑ a, w a • zb a)) = cenSynth src tgt D F zb *ᵥ w := by
  funext k
  simp only [mulVec, dotProduct, cenSynth, Matrix.of_apply, evec_dcen_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **Edge occurrence forced by `𝔾_Howe ≻ 0`**: if a nonzero declared type-central contrast
`z = ∑ w_a zb_a` commutes with every incidence (and adjoint) other than `e₀` — i.e. deleting
`e₀` would create an additional type-central commutant direction — then strict positivity of
the restricted Howe Gram forces `Y_{e₀} ≠ 0` with `z_{t(e₀)} ≠ z_{s(e₀)}`. -/
theorem edge_forced_of_posDef (src tgt : E → V) (D : E → Matrix M M ℂ) (F : E → Matrix G G ℂ)
    (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (hc : ∀ j z, comm (c j) (testOp M (zfun (G := G) z)) = 0) (zb : Zc → V → ℂ)
    (xb : Xf → V → Matrix G G ℂ) (hG : (restrictedGram src tgt D F c zb xb).PosDef)
    (w : Zc → ℂ) (hw : w ≠ 0) (e₀ : E)
    (hother : ∀ e, e ≠ e₀ →
      comm (incY src tgt D F e) (testOp M (zfun (G := G) (∑ a, w a • zb a))) = 0 ∧
      comm (incY src tgt D F e)ᴴ (testOp M (zfun (G := G) (∑ a, w a • zb a))) = 0) :
    incY src tgt D F e₀ ≠ 0 ∧ (∑ a, w a • zb a) (tgt e₀) ≠ (∑ a, w a • zb a) (src e₀) := by
  set z := ∑ a, w a • zb a with hz
  have hpos : 0 < howeForm src tgt D F c (zfun (G := G) z) (zfun z) := by
    have hne : (Sum.elim w (0 : Xf → ℂ)) ≠ 0 := by
      intro h
      apply hw
      funext a
      have := congrFun h (Sum.inl a)
      simpa using this
    have h1 := hG.dotProduct_mulVec_pos hne
    rw [restrictedGram_eq_fromBlocks _ _ _ _ c hc, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, Matrix.mulVec_zero,
      Matrix.mulVec_zero, add_zero, add_zero, Function.star_sumElim, star_zero,
      sumElim_dotProduct_sumElim, zero_dotProduct, add_zero, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← evec_dcen_sum,
      ← edgeInner_eq_dotProduct] at h1
    rw [howeForm_eq, extraForm_zfun_left c hc, add_zero]
    exact h1
  rw [howeForm_eq, extraForm_zfun_left c hc, add_zero, ← incidencePart_eq, incidencePart,
    Finset.sum_eq_single e₀ (fun e _ he => by
      rw [(hother e he).1, (hother e he).2, hsInner_zero_left, add_zero])
      (by simp)] at hpos
  constructor
  · intro h0
    rw [h0, Matrix.conjTranspose_zero] at hpos
    simp [comm, hsInner] at hpos
  · intro hzeq
    have h0 : zfun (G := G) z (tgt e₀) * F e₀ - F e₀ * zfun z (src e₀) = 0 := by
      simp [zfun, hzeq]
    have h0' : zfun (G := G) z (src e₀) * (F e₀)ᴴ - (F e₀)ᴴ * zfun z (tgt e₀) = 0 := by
      simp [zfun, hzeq]
    rw [incY_conjTranspose, incY, comm_block_testOp, comm_block_testOp, h0, h0'] at hpos
    simp [hsInner] at hpos

/-- **`cor:howe-incidence-flavour-factorization`** (packaged): the block form of the Howe form
on the block-diagonal test space, its coordinate form
`𝔾|_test = [[A_cen, B], [Bᴴ, 𝒟_flᴴ𝒟_fl + C_extra]]` with `C_extra ⪰ 0`, and, when
`A_cen ≻ 0`, the Schur complement `S_{fl|cen} = C_extra + 𝒟_flᴴ(I − P_cen)𝒟_fl`
(`eq:howe-factorized-Schur`) with `𝔾|_test ≻ 0 ⟺ S_{fl|cen} ≻ 0`.  Edge occurrence:
`edge_forced_of_posDef`. -/
theorem howe_incidence_flavour_factorization (src tgt : E → V) (D : E → Matrix M M ℂ)
    (F : E → Matrix G G ℂ) (c : J → Matrix (V × (M × G)) (V × (M × G)) ℂ)
    (hc : ∀ j z, comm (c j) (testOp M (zfun (G := G) z)) = 0) (zb : Zc → V → ℂ)
    (xb : Xf → V → Matrix G G ℂ) :
    (∀ (z z' : V → ℂ) (X X' : V → Matrix G G ℂ),
      howeForm src tgt D F c (zfun z + X) (zfun z' + X')
        = edgeInner (dcen src tgt D F z) (dcen src tgt D F z')
          + edgeInner (dcen src tgt D F z) (dfl src tgt D F X')
          + edgeInner (dfl src tgt D F X) (dcen src tgt D F z')
          + edgeInner (dfl src tgt D F X) (dfl src tgt D F X') + extraForm c X X') ∧
    restrictedGram src tgt D F c zb xb =
      fromBlocks ((cenSynth src tgt D F zb)ᴴ * cenSynth src tgt D F zb)
        ((cenSynth src tgt D F zb)ᴴ * flSynth src tgt D F xb)
        ((flSynth src tgt D F xb)ᴴ * cenSynth src tgt D F zb)
        ((flSynth src tgt D F xb)ᴴ * flSynth src tgt D F xb + extraGram c xb) ∧
    (extraGram c xb).PosSemidef ∧
    (((cenSynth src tgt D F zb)ᴴ * cenSynth src tgt D F zb).PosDef →
      (flSynth src tgt D F xb)ᴴ * flSynth src tgt D F xb + extraGram c xb
          - ((cenSynth src tgt D F zb)ᴴ * flSynth src tgt D F xb)ᴴ
            * ((cenSynth src tgt D F zb)ᴴ * cenSynth src tgt D F zb)⁻¹
            * ((cenSynth src tgt D F zb)ᴴ * flSynth src tgt D F xb)
        = extraGram c xb + (flSynth src tgt D F xb)ᴴ * (1 - cenSynth src tgt D F zb
            * ((cenSynth src tgt D F zb)ᴴ * cenSynth src tgt D F zb)⁻¹
            * (cenSynth src tgt D F zb)ᴴ) * flSynth src tgt D F xb ∧
      ((restrictedGram src tgt D F c zb xb).PosDef ↔
        (extraGram c xb + (flSynth src tgt D F xb)ᴴ * (1 - cenSynth src tgt D F zb
            * ((cenSynth src tgt D F zb)ᴴ * cenSynth src tgt D F zb)⁻¹
            * (cenSynth src tgt D F zb)ᴴ) * flSynth src tgt D F xb).PosDef)) := by
  refine ⟨howeForm_block src tgt D F c hc, restrictedGram_eq_fromBlocks src tgt D F c hc zb xb,
    extraGram_posSemidef c xb, fun hA => ?_⟩
  have hS := howe_factorized_schur (cenSynth src tgt D F zb) (flSynth src tgt D F xb)
    (extraGram c xb) hA (extraGram_posSemidef c xb).1
  refine ⟨hS.1, ?_⟩
  rw [restrictedGram_eq_fromBlocks src tgt D F c hc zb xb]
  exact hS.2.2.2.2

end Edge

end HoweIncidenceFlavour
end RenewalGeometry
