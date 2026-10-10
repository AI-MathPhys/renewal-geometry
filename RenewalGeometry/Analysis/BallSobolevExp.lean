/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevNormedAlgebra

/-!
# Complexification, matrix-valued `H^s(B)` and the exponential map
  (stage D1b of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `Cx V` — **the complexification `V ⊕ iV` of a commutative normed `ℝ`-algebra** with the `ℓ¹`
  norm `‖a + ib‖ = ‖a‖ + ‖b‖`: a normed commutative ring and normed `ℝ`-algebra, complete when
  `V` is (generic);
* `evC`, `evM` — the pointwise values (`L²(B)` representatives) of `H^s(B, ℂ)` functions and of
  `H^s(B, M_m(ℂ))` matrix fields `MatSob c r s m = Matrix (Fin m) (Fin m) (Cx (SobAlg c r s))`
  (with the `ℓ^∞`-operator norm, a Banach algebra); `evM_mul` (a.e. multiplicativity), `evM_pow`;
* `evM_exp` — **the Banach-algebra exponential is the pointwise matrix exponential**:
  `evM (exp M) x = exp (evM M x)` for a.e. `x ∈ B`; hence `exp M` takes values in `G` a.e. when
  `M` takes values in `𝔤` with `exp 𝔤 ⊆ G` (`evM_exp_mem`);
* `analyticAt_exp_matSob`, `hasStrictFDerivAt_exp_matSob_zero` — the exponential of the Banach
  algebra `MatSob` is analytic, with derivative the identity at `0`.
-/

open MeasureTheory Set Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg

set_option linter.unusedSectionVars false

/-! ### The complexification of a commutative normed algebra -/

/-- The complexification `V ⊕ iV` of a commutative ring `V`. -/
@[ext] structure Cx (V : Type*) where
  /-- Real part. -/
  re : V
  /-- Imaginary part. -/
  im : V

namespace Cx

variable {V : Type*}

section Ring

variable [CommRing V]

instance : Zero (Cx V) := ⟨⟨0, 0⟩⟩
instance : One (Cx V) := ⟨⟨1, 0⟩⟩
instance : Add (Cx V) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg (Cx V) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub (Cx V) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Mul (Cx V) := ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
instance : SMul ℕ (Cx V) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩
instance : SMul ℤ (Cx V) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩

@[simp] theorem zero_re : (0 : Cx V).re = 0 := rfl
@[simp] theorem zero_im : (0 : Cx V).im = 0 := rfl
@[simp] theorem one_re : (1 : Cx V).re = 1 := rfl
@[simp] theorem one_im : (1 : Cx V).im = 0 := rfl
@[simp] theorem add_re (z w : Cx V) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : Cx V) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : Cx V) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : Cx V) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : Cx V) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : Cx V) : (z - w).im = z.im - w.im := rfl
@[simp] theorem mul_re (z w : Cx V) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : Cx V) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp] theorem nsmul_re (n : ℕ) (z : Cx V) : (n • z).re = n • z.re := rfl
@[simp] theorem nsmul_im (n : ℕ) (z : Cx V) : (n • z).im = n • z.im := rfl
@[simp] theorem zsmul_re (n : ℤ) (z : Cx V) : (n • z).re = n • z.re := rfl
@[simp] theorem zsmul_im (n : ℤ) (z : Cx V) : (n • z).im = n • z.im := rfl

/-- The underlying pair. -/
def toProd (z : Cx V) : V × V := (z.re, z.im)

theorem toProd_injective : Function.Injective (toProd (V := V)) := by
  intro z w h
  simp only [toProd, Prod.mk.injEq] at h
  exact Cx.ext h.1 h.2

instance instAddCommGroup : AddCommGroup (Cx V) :=
  Function.Injective.addCommGroup toProd toProd_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance instCommRing : CommRing (Cx V) :=
  { instAddCommGroup with
    mul := (· * ·)
    one := 1
    mul_assoc := fun a b c => by ext <;> simp <;> ring
    one_mul := fun a => by ext <;> simp
    mul_one := fun a => by ext <;> simp
    left_distrib := fun a b c => by ext <;> simp <;> ring
    right_distrib := fun a b c => by ext <;> simp <;> ring
    zero_mul := fun a => by ext <;> simp
    mul_zero := fun a => by ext <;> simp
    mul_comm := fun a b => by ext <;> simp <;> ring
    natCast := fun n => ⟨n, 0⟩
    natCast_zero := by ext <;> simp
    natCast_succ := fun n => by ext <;> simp
    intCast := fun z => ⟨z, 0⟩
    intCast_ofNat := fun n => by
      apply Cx.ext
      · show ((n : ℤ) : V) = (n : V)
        simp
      · show (0 : V) = 0
        rfl
    intCast_negSucc := fun n => by
      apply Cx.ext
      · show ((Int.negSucc n : ℤ) : V) = -(((n + 1 : ℕ) : V))
        simp
      · show (0 : V) = -0
        simp
    npow := npowRec
    npow_zero := fun _ => rfl
    npow_succ := fun _ _ => rfl }

@[simp] theorem natCast_re (n : ℕ) : (n : Cx V).re = n := rfl
@[simp] theorem natCast_im (n : ℕ) : (n : Cx V).im = 0 := rfl

end Ring

section Normed

variable [NormedCommRing V] [NormedAlgebra ℝ V]

instance : SMul ℝ (Cx V) := ⟨fun a z => ⟨a • z.re, a • z.im⟩⟩

@[simp] theorem smul_re (a : ℝ) (z : Cx V) : (a • z).re = a • z.re := rfl
@[simp] theorem smul_im (a : ℝ) (z : Cx V) : (a • z).im = a • z.im := rfl

/-- The additive map to pairs. -/
def toProdHom : Cx V →+ V × V where
  toFun := toProd
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule : Module ℝ (Cx V) :=
  Function.Injective.module ℝ toProdHom toProd_injective (fun _ _ => rfl)

/-- The `ℓ¹` norm `‖a + ib‖ = ‖a‖ + ‖b‖`. -/
def normAG : AddGroupNorm (Cx V) where
  toFun z := ‖z.re‖ + ‖z.im‖
  map_zero' := by simp
  add_le' z w := by
    show ‖z.re + w.re‖ + ‖z.im + w.im‖ ≤ ‖z.re‖ + ‖z.im‖ + (‖w.re‖ + ‖w.im‖)
    linarith [norm_add_le z.re w.re, norm_add_le z.im w.im]
  neg' z := by
    show ‖-z.re‖ + ‖-z.im‖ = ‖z.re‖ + ‖z.im‖
    simp
  eq_zero_of_map_eq_zero' z h := by
    have h' : ‖z.re‖ + ‖z.im‖ = 0 := h
    have h1 : ‖z.re‖ = 0 := by linarith [norm_nonneg z.re, norm_nonneg z.im]
    have h2 : ‖z.im‖ = 0 := by linarith [norm_nonneg z.re, norm_nonneg z.im]
    ext
    · exact norm_eq_zero.mp h1
    · exact norm_eq_zero.mp h2

instance instNormedAddCommGroup : NormedAddCommGroup (Cx V) := normAG.toNormedAddCommGroup

theorem norm_def (z : Cx V) : ‖z‖ = ‖z.re‖ + ‖z.im‖ := rfl

theorem norm_re_le (z : Cx V) : ‖z.re‖ ≤ ‖z‖ := by
  rw [norm_def]; linarith [norm_nonneg z.im]

theorem norm_im_le (z : Cx V) : ‖z.im‖ ≤ ‖z‖ := by
  rw [norm_def]; linarith [norm_nonneg z.re]

instance instAlgebra : Algebra ℝ (Cx V) :=
  Algebra.ofModule (fun a z w => by ext <;> simp [smul_sub, smul_add])
    (fun a z w => by ext <;> simp [smul_sub, smul_add])

instance instNormedSpace : NormedSpace ℝ (Cx V) where
  norm_smul_le a z := by
    rw [norm_def, norm_def]
    simp only [smul_re, smul_im, norm_smul]
    rw [mul_add]

/-- **The complexification is a normed commutative ring** (`ℓ¹` norm). -/
instance instNormedCommRing : NormedCommRing (Cx V) :=
  { instNormedAddCommGroup, instCommRing with
    norm_mul_le := fun z w => by
      rw [norm_def, norm_def, norm_def]
      simp only [mul_re, mul_im]
      have h1 := norm_sub_le (z.re * w.re) (z.im * w.im)
      have h2 := norm_add_le (z.re * w.im) (z.im * w.re)
      have h3 := norm_mul_le z.re w.re
      have h4 := norm_mul_le z.im w.im
      have h5 := norm_mul_le z.re w.im
      have h6 := norm_mul_le z.im w.re
      nlinarith [norm_nonneg z.re, norm_nonneg z.im, norm_nonneg w.re, norm_nonneg w.im] }

instance instNormedAlgebra : NormedAlgebra ℝ (Cx V) :=
  { instAlgebra with norm_smul_le := fun a z => norm_smul_le a z }

/-- **The complexification of a Banach algebra is complete.** -/
instance instCompleteSpace [CompleteSpace V] : CompleteSpace (Cx V) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hre : CauchySeq fun n => (u n).re := by
    rw [Metric.cauchySeq_iff'] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (by simpa using norm_re_le (u n - u N)) (by
      simpa [dist_eq_norm] using hN n hn)
  have him : CauchySeq fun n => (u n).im := by
    rw [Metric.cauchySeq_iff'] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (by simpa using norm_im_le (u n - u N)) (by
      simpa [dist_eq_norm] using hN n hn)
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hre
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete him
  refine ⟨⟨a, b⟩, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp ha).add (tendsto_iff_norm_sub_tendsto_zero.mp hb)
  rw [zero_add] at h1
  refine h1.congr fun n => ?_
  rw [norm_def]
  rfl

theorem tendsto_re {ι : Type*} {l : Filter ι} {u : ι → Cx V} {z : Cx V}
    (h : Tendsto u l (𝓝 z)) : Tendsto (fun i => (u i).re) l (𝓝 z.re) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  exact squeeze_zero (fun _ => norm_nonneg _) (fun i => by simpa using norm_re_le (u i - z)) h

theorem tendsto_im {ι : Type*} {l : Filter ι} {u : ι → Cx V} {z : Cx V}
    (h : Tendsto u l (𝓝 z)) : Tendsto (fun i => (u i).im) l (𝓝 z.im) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  exact squeeze_zero (fun _ => norm_nonneg _) (fun i => by simpa using norm_im_le (u i - z)) h

end Normed

end Cx

/-! ### Pointwise values of `H^s(B, ℂ)` and `H^s(B, M_m(ℂ))` -/

open scoped Matrix.Norms.Operator

/-- Entries are bounded by the `ℓ^∞`-operator norm. -/
theorem norm_entry_le_linfty {α : Type*} [SeminormedAddCommGroup α] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) α) (i j : Fin m) : ‖A i j‖ ≤ ‖A‖ := by
  have h := Matrix.linfty_opNNNorm_def A
  have h1 : ‖A i j‖₊ ≤ ∑ j', ‖A i j'‖₊ :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖₊) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j', ‖A i j'‖₊ ≤ (Finset.univ : Finset (Fin m)).sup fun i => ∑ j', ‖A i j'‖₊ :=
    Finset.le_sup (f := fun i => ∑ j', ‖A i j'‖₊) (Finset.mem_univ i)
  have : ‖A i j‖₊ ≤ ‖A‖₊ := by rw [h]; exact h1.trans h2
  exact_mod_cast this

section Eval

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {s : ℕ} [hs : Fact (3 ≤ s)]

namespace SobAlg

theorem fn_sum {ι : Type*} (t : Finset ι) (F : ι → SobAlg c r s) :
    fn (∑ i ∈ t, F i) =ᵐ[volume.restrict (euclBall c r)] fun x => ∑ i ∈ t, fn (F i) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using fn_zero (c := c) (r := r) (s := s)
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [fn_add (F a) (∑ i ∈ t, F i), ih] with x h1 h2
    rw [h1, h2, Finset.sum_insert ha]

/-- The `L²(B)` norm of the function component is controlled by the algebra norm. -/
theorem eLpNorm_fn_le (F : SobAlg c r s) :
    eLpNorm (fn F) 2 (volume.restrict (euclBall c r)) ≤
      ENNReal.ofReal ((Kal c r s)⁻¹ * ‖F‖) := by
  have h1 : eLpNorm (fn F) 2 (volume.restrict (euclBall c r)) =
      ENNReal.ofReal ‖((jet F : HsB c r s) : JetAmb c r s) (nilW s)‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    rfl
  rw [h1]
  refine ENNReal.ofReal_le_ofReal ((PiLp.norm_apply_le _ _).trans ?_)
  exact norm_jet_le F

end SobAlg

open SobAlg

/-- Pointwise values (an `L²(B)` representative) of a complex `H^s(B)` function. -/
def evC (z : Cx (SobAlg c r s)) (x : Fin 4 → ℝ) : ℂ :=
  (fn z.re x : ℂ) + (fn z.im x : ℂ) * Complex.I

theorem evC_add (z w : Cx (SobAlg c r s)) :
    evC (z + w) =ᵐ[volume.restrict (euclBall c r)] fun x => evC z x + evC w x := by
  filter_upwards [fn_add z.re w.re, fn_add z.im w.im] with x h1 h2
  simp only [evC, Cx.add_re, Cx.add_im, h1, h2]
  push_cast; ring

theorem evC_sub (z w : Cx (SobAlg c r s)) :
    evC (z - w) =ᵐ[volume.restrict (euclBall c r)] fun x => evC z x - evC w x := by
  filter_upwards [fn_sub z.re w.re, fn_sub z.im w.im] with x h1 h2
  simp only [evC, Cx.sub_re, Cx.sub_im, h1, h2]
  push_cast; ring

theorem evC_zero : evC (0 : Cx (SobAlg c r s)) =ᵐ[volume.restrict (euclBall c r)] fun _ => 0 := by
  filter_upwards [fn_zero (c := c) (r := r) (s := s)] with x h1
  simp only [evC, Cx.zero_re, Cx.zero_im, h1]
  simp

theorem evC_one : evC (1 : Cx (SobAlg c r s)) =ᵐ[volume.restrict (euclBall c r)] fun _ => 1 := by
  filter_upwards [fn_one (c := c) (r := r) (s := s), fn_zero (c := c) (r := r) (s := s)]
    with x h1 h2
  simp only [evC, Cx.one_re, Cx.one_im, h1, h2]
  simp

theorem evC_smul (a : ℝ) (z : Cx (SobAlg c r s)) :
    evC (a • z) =ᵐ[volume.restrict (euclBall c r)] fun x => (a : ℂ) * evC z x := by
  filter_upwards [fn_smul a z.re, fn_smul a z.im] with x h1 h2
  simp only [evC, Cx.smul_re, Cx.smul_im, h1, h2]
  push_cast; ring

theorem evC_mul (z w : Cx (SobAlg c r s)) :
    evC (z * w) =ᵐ[volume.restrict (euclBall c r)] fun x => evC z x * evC w x := by
  filter_upwards [fn_sub (z.re * w.re) (z.im * w.im), fn_add (z.re * w.im) (z.im * w.re),
    fn_mul z.re w.re, fn_mul z.im w.im, fn_mul z.re w.im, fn_mul z.im w.re] with x h1 h2 h3 h4 h5 h6
  simp only [evC, Cx.mul_re, Cx.mul_im, h1, h2, h3, h4, h5, h6]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem evC_sum {ι : Type*} (t : Finset ι) (z : ι → Cx (SobAlg c r s)) :
    evC (∑ i ∈ t, z i) =ᵐ[volume.restrict (euclBall c r)] fun x => ∑ i ∈ t, evC (z i) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using evC_zero (c := c) (r := r) (s := s)
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [evC_add (z a) (∑ i ∈ t, z i), ih] with x h1 h2
    rw [h1, h2, Finset.sum_insert ha]

/-- Complex `H^s(B)` functions are determined by their values. -/
theorem ext_evC {z w : Cx (SobAlg c r s)}
    (h : evC z =ᵐ[volume.restrict (euclBall c r)] evC w) : z = w := by
  have hre : fn z.re =ᵐ[volume.restrict (euclBall c r)] fn w.re := by
    filter_upwards [h] with x hx
    have := congrArg Complex.re hx
    simpa [evC] using this
  have him : fn z.im =ᵐ[volume.restrict (euclBall c r)] fn w.im := by
    filter_upwards [h] with x hx
    have := congrArg Complex.im hx
    simpa [evC] using this
  exact Cx.ext (ext_fn hre) (ext_fn him)

/-- Pointwise bound of a value by the real and imaginary components. -/
theorem norm_evC_le (z : Cx (SobAlg c r s)) (x : Fin 4 → ℝ) :
    ‖evC z x‖ ≤ |fn z.re x| + |fn z.im x| := by
  unfold evC
  refine (norm_add_le _ _).trans ?_
  simp

/-- The matrix algebra `H^s(B, M_m(ℂ))` (with the `ℓ^∞`-operator norm). -/
abbrev MatSob (c : Fin 4 → ℝ) (r : ℝ) [Fact (0 < r)] (s : ℕ) [Fact (3 ≤ s)] (m : ℕ) :=
  Matrix (Fin m) (Fin m) (Cx (SobAlg c r s))

variable {m : ℕ}

/-- Pointwise values (an `L²(B)` representative) of a matrix field. -/
def evM (M : MatSob c r s m) (x : Fin 4 → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => evC (M i j) x

theorem evM_apply (M : MatSob c r s m) (x : Fin 4 → ℝ) (i j : Fin m) :
    evM M x i j = evC (M i j) x := rfl

/-- Entrywise a.e. equality gives a.e. equality of matrices. -/
theorem ae_matrix_of_entries {f g : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ i j, (fun x => f x i j) =ᵐ[volume.restrict (euclBall c r)] fun x => g x i j) :
    f =ᵐ[volume.restrict (euclBall c r)] g := by
  have h' : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ i j, f x i j = g x i j := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact h i j
  filter_upwards [h'] with x hx
  ext i j; exact hx i j

theorem evM_add (M N : MatSob c r s m) :
    evM (M + N) =ᵐ[volume.restrict (euclBall c r)] fun x => evM M x + evM N x :=
  ae_matrix_of_entries fun i j => by
    filter_upwards [evC_add (M i j) (N i j)] with x hx
    simp [evM, hx]

theorem evM_sub (M N : MatSob c r s m) :
    evM (M - N) =ᵐ[volume.restrict (euclBall c r)] fun x => evM M x - evM N x :=
  ae_matrix_of_entries fun i j => by
    filter_upwards [evC_sub (M i j) (N i j)] with x hx
    simp [evM, hx]

theorem evM_smul (a : ℝ) (M : MatSob c r s m) :
    evM (a • M) =ᵐ[volume.restrict (euclBall c r)] fun x => (a : ℂ) • evM M x :=
  ae_matrix_of_entries fun i j => by
    filter_upwards [evC_smul a (M i j)] with x hx
    simp [evM, hx]

theorem evM_zero : evM (0 : MatSob c r s m) =ᵐ[volume.restrict (euclBall c r)] fun _ => 0 :=
  ae_matrix_of_entries fun i j => by
    filter_upwards [evC_zero (c := c) (r := r) (s := s)] with x hx
    simp [evM, hx]

theorem evM_one : evM (1 : MatSob c r s m) =ᵐ[volume.restrict (euclBall c r)] fun _ => 1 :=
  ae_matrix_of_entries fun i j => by
    by_cases hij : i = j
    · subst hij
      filter_upwards [evC_one (c := c) (r := r) (s := s)] with x hx
      simp [evM, hx]
    · filter_upwards [evC_zero (c := c) (r := r) (s := s)] with x hx
      simp [evM, hx, Matrix.one_apply_ne hij]

theorem evM_mul (M N : MatSob c r s m) :
    evM (M * N) =ᵐ[volume.restrict (euclBall c r)] fun x => evM M x * evM N x :=
  ae_matrix_of_entries fun i j => by
    have h1 := evC_sum Finset.univ (fun k => M i k * N k j)
    have h2 : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ k,
        evC (M i k * N k j) x = evC (M i k) x * evC (N k j) x := by
      rw [ae_all_iff]; exact fun k => evC_mul (M i k) (N k j)
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [evM, Matrix.mul_apply, Matrix.of_apply, hx1, hx2]

theorem evM_sum {ι : Type*} (t : Finset ι) (M : ι → MatSob c r s m) :
    evM (∑ i ∈ t, M i) =ᵐ[volume.restrict (euclBall c r)] fun x => ∑ i ∈ t, evM (M i) x :=
  ae_matrix_of_entries fun i j => by
    filter_upwards [evC_sum t (fun k => M k i j)] with x hx
    simp only [evM, Matrix.sum_apply, Matrix.of_apply, hx]

theorem evM_pow (M : MatSob c r s m) (n : ℕ) :
    evM (M ^ n) =ᵐ[volume.restrict (euclBall c r)] fun x => evM M x ^ n := by
  induction n with
  | zero => simpa using evM_one (c := c) (r := r) (s := s) (m := m)
  | succ n ih =>
    filter_upwards [evM_mul (M ^ n) M, ih] with x h1 h2
    rw [pow_succ, h1, h2, pow_succ]

/-- The matrix exponential partial sums, pointwise. -/
theorem evM_expPartial (M : MatSob c r s m) :
    ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ N : ℕ,
      evM (∑ n ∈ Finset.range N, ((n.factorial : ℝ)⁻¹) • M ^ n) x =
        ∑ n ∈ Finset.range N, ((n.factorial : ℝ)⁻¹) • evM M x ^ n := by
  rw [ae_all_iff]
  intro N
  have h1 := evM_sum (Finset.range N) (fun n => ((n.factorial : ℝ)⁻¹) • M ^ n)
  have h2 : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ n,
      evM (((n.factorial : ℝ)⁻¹) • M ^ n) x = ((n.factorial : ℝ)⁻¹ : ℂ) • evM M x ^ n := by
    rw [ae_all_iff]
    intro n
    filter_upwards [evM_smul ((n.factorial : ℝ)⁻¹) (M ^ n), evM_pow M n] with x h1 h2
    rw [h1, h2]
    simp
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hx2 n]
  ext i j
  simp [Matrix.smul_apply]

/-- The `L²` error function of a matrix field (sum of the absolute values of the components). -/
def errFn (D : MatSob c r s m) : (Fin 4 → ℝ) → ℝ :=
  ∑ i, ∑ j, ((fun x => ‖fn (D i j).re x‖) + (fun x => ‖fn (D i j).im x‖))

theorem errFn_apply (D : MatSob c r s m) (x : Fin 4 → ℝ) :
    errFn D x = ∑ i, ∑ j, (‖fn (D i j).re x‖ + ‖fn (D i j).im x‖) := by
  simp [errFn, Finset.sum_apply]

theorem aestronglyMeasurable_errFn (D : MatSob c r s m) :
    AEStronglyMeasurable (errFn D) (volume.restrict (euclBall c r)) :=
  Finset.aestronglyMeasurable_sum _ fun i _ => Finset.aestronglyMeasurable_sum _ fun j _ =>
    (memLp_fn _).aestronglyMeasurable.norm.add (memLp_fn _).aestronglyMeasurable.norm

/-- The error function is controlled by the norm of the matrix field. -/
theorem eLpNorm_errFn_le (D : MatSob c r s m) :
    eLpNorm (errFn D) 2 (volume.restrict (euclBall c r)) ≤
      ∑ _i : Fin m, ∑ _j : Fin m, (ENNReal.ofReal ((Kal c r s)⁻¹ * ‖D‖) +
        ENNReal.ofReal ((Kal c r s)⁻¹ * ‖D‖)) := by
  unfold errFn
  refine (eLpNorm_sum_le (fun i _ => Finset.aestronglyMeasurable_sum _ fun j _ =>
    (memLp_fn _).aestronglyMeasurable.norm.add (memLp_fn _).aestronglyMeasurable.norm)
    (by norm_num)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine (eLpNorm_sum_le (fun j _ =>
    (memLp_fn _).aestronglyMeasurable.norm.add (memLp_fn _).aestronglyMeasurable.norm)
    (by norm_num)).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine (eLpNorm_add_le (memLp_fn _).aestronglyMeasurable.norm
    (memLp_fn _).aestronglyMeasurable.norm (by norm_num)).trans ?_
  have hentry : ‖D i j‖ ≤ ‖D‖ := norm_entry_le_linfty D i j
  have hK : 0 ≤ (Kal c r s)⁻¹ := inv_nonneg.mpr (Kal_pos c r s).le
  refine add_le_add ?_ ?_
  · rw [eLpNorm_norm]
    refine (eLpNorm_fn_le _).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left ((Cx.norm_re_le _).trans hentry) hK
  · rw [eLpNorm_norm]
    refine (eLpNorm_fn_le _).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left ((Cx.norm_im_le _).trans hentry) hK

/-- Convergence in `H^s(B, M_m(ℂ))` gives `L²` convergence of the error functions. -/
theorem tendsto_eLpNorm_errFn {ι : Type*} {l : Filter ι} {D : ι → MatSob c r s m}
    (hD : Tendsto D l (𝓝 0)) :
    Tendsto (fun k => eLpNorm (errFn (D k) - fun _ => (0 : ℝ)) 2 (volume.restrict (euclBall c r)))
      l (𝓝 0) := by
  have h0 : Tendsto (fun k => ENNReal.ofReal ((Kal c r s)⁻¹ * ‖D k‖)) l (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have := (tendsto_zero_iff_norm_tendsto_zero.mp hD).const_mul (Kal c r s)⁻¹
    simpa using this
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun j _ => h0.add h0
  simp only [add_zero, Finset.sum_const_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
    (fun k => ?_)
  have e0 : (errFn (D k) - fun _ => (0 : ℝ)) = errFn (D k) := by funext x; simp
  rw [e0]
  exact eLpNorm_errFn_le (D k)

/-- Entries of the difference of two matrix fields are bounded by the error function. -/
theorem ae_norm_evM_sub_le (M N : MatSob c r s m) :
    ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ i j,
      ‖evM M x i j - evM N x i j‖ ≤ errFn (M - N) x := by
  have hij : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ i j,
      evC (M i j - N i j) x = evC (M i j) x - evC (N i j) x := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact evC_sub _ _
  filter_upwards [hij] with x hx i j
  rw [evM_apply, evM_apply, ← hx i j, errFn_apply]
  refine (norm_evC_le _ x).trans ?_
  have e : |fn (M i j - N i j).re x| + |fn (M i j - N i j).im x| =
      ‖fn ((M - N) i j).re x‖ + ‖fn ((M - N) i j).im x‖ := by
    simp [Real.norm_eq_abs]
  rw [e]
  refine (Finset.single_le_sum (f := fun j => ‖fn ((M - N) i j).re x‖ +
    ‖fn ((M - N) i j).im x‖) (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
  exact Finset.single_le_sum (f := fun i => ∑ j, (‖fn ((M - N) i j).re x‖ +
    ‖fn ((M - N) i j).im x‖)) (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.mem_univ i)

set_option backward.isDefEq.respectTransparency false in
/-- **A convergent sequence of matrix fields has a subsequence converging pointwise a.e.** -/
theorem exists_subseq_tendsto_evM {M : ℕ → MatSob c r s m} {L : MatSob c r s m}
    (hM : Tendsto M atTop (𝓝 L)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂(volume.restrict (euclBall c r)),
      Tendsto (fun k => evM (M (ns k)) x) atTop (𝓝 (evM L x)) := by
  have hD : Tendsto (fun k => M k - L) atTop (𝓝 0) := by
    simpa using hM.sub_const L
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
    (fun k => aestronglyMeasurable_errFn (M k - L)) aestronglyMeasurable_const
    (tendsto_eLpNorm_errFn hD)).exists_seq_tendsto_ae
  have hdiff : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ k i j,
      ‖evM (M k) x i j - evM L x i j‖ ≤ errFn (M k - L) x := by
    rw [ae_all_iff]; intro k; exact ae_norm_evM_sub_le (M k) L
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, hdiff] with x hx1 hx2
  have key : Tendsto (fun k => fun i j => evM (M (ns k)) x i j) atTop
      (𝓝 (fun i j => evM L x i j)) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    intro j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hx2 (ns k) i j) (by simpa using hx1)
  exact key

set_option backward.isDefEq.respectTransparency false in
/-- **The Banach-algebra exponential of `H^s(B, M_m(ℂ))` is the pointwise matrix exponential.** -/
theorem evM_exp (M : MatSob c r s m) :
    evM (exp M) =ᵐ[volume.restrict (euclBall c r)] fun x => exp (evM M x) := by
  set S : ℕ → MatSob c r s m := fun N => ∑ n ∈ Finset.range N, ((n.factorial : ℝ)⁻¹) • M ^ n
  have hS : Tendsto S atTop (𝓝 (exp M)) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) M).tendsto_sum_nat
  obtain ⟨ns, hns, hae⟩ := exists_subseq_tendsto_evM hS
  filter_upwards [hae, evM_expPartial M] with x hx1 hx3
  have hB : Tendsto (fun k => evM (S (ns k)) x) atTop (𝓝 (exp (evM M x))) := by
    simp only [S, hx3]
    exact ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (evM M x)).tendsto_sum_nat).comp
      hns.tendsto_atTop
  exact tendsto_nhds_unique hx1 hB

set_option backward.isDefEq.respectTransparency false in
/-- **The exponential of a `𝔤`-valued field is `G`-valued** (a.e. on the ball), when `exp 𝔤 ⊆ G`. -/
theorem evM_exp_mem {𝔤 G : Set (Matrix (Fin m) (Fin m) ℂ)} (hexp : ∀ X ∈ 𝔤, exp X ∈ G)
    {M : MatSob c r s m} (hM : ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM M x ∈ 𝔤) :
    ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (exp M) x ∈ G := by
  filter_upwards [evM_exp M, hM] with x h1 h2
  rw [h1]; exact hexp _ h2

set_option backward.isDefEq.respectTransparency false in
/-- **The exponential of `H^s(B, M_m(ℂ))` is analytic** (Banach algebra). -/
theorem analyticAt_exp_matSob (M : MatSob c r s m) : AnalyticAt ℝ exp M :=
  NormedSpace.exp_analytic M

set_option backward.isDefEq.respectTransparency false in
/-- The exponential is strictly differentiable at `0` with derivative the identity. -/
theorem hasStrictFDerivAt_exp_matSob_zero :
    HasStrictFDerivAt (exp : MatSob c r s m → MatSob c r s m)
      (1 : MatSob c r s m →L[ℝ] MatSob c r s m) 0 :=
  hasStrictFDerivAt_exp_zero

end Eval

end RenewalGeometry.BallAnalysis.BallAlg
