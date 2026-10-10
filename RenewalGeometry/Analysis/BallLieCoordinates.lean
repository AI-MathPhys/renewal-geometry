/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallMatSobCalculus
import RenewalGeometry.Algebra.MatrixExpDerivative

/-!
# Lie-algebra coordinates for `𝔤`-valued `H^s(B)` matrix fields
  (stage D1 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `LieBasis m d` — a real basis `e_a` of a matrix Lie algebra `𝔤 ⊆ M_m(ℂ)` with structure
  constants `[e_a, e_b] = Σ_c f_abc e_c` and a real-linear left inverse `κ` (coordinates);
* `cplxS` — the ring homomorphism `ℂ → Cx (H^s(B))` (constants), `constM` its matrix version;
* `embX` — `u ↦ Σ_a u_a e_a`, `𝔤`-valued fields from their coordinates (continuous linear);
* `coordL` — the pointwise coordinates `M ↦ κ ∘ M` (continuous linear), `coordL_embX`
  (`coordL ∘ embX = id`);
* `embX_mul_sub` — the bracket of two `𝔤`-valued fields in coordinates (structure constants);
* `derM_embX`, `rhoM_embX` — derivatives and restrictions act on the coordinates.
-/

open MeasureTheory Set Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

/-- **A real basis of a matrix Lie algebra** `𝔤 = span_ℝ {e_a} ⊆ M_m(ℂ)`, with structure constants
and a real-linear coordinate map `κ` (`κ e_a = δ_a`). -/
structure LieBasis (m d : ℕ) where
  /-- The basis. -/
  e : Fin d → Matrix (Fin m) (Fin m) ℂ
  /-- The coordinates (a left inverse). -/
  κ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] (Fin d → ℝ)
  κ_e : ∀ a, κ (e a) = Pi.single a 1
  /-- The structure constants. -/
  f : Fin d → Fin d → Fin d → ℝ
  bracket : ∀ a b, e a * e b - e b * e a = ∑ c, f a b c • e c

namespace LieBasis

variable {m d : ℕ} (L : LieBasis m d)

/-- The Lie algebra spanned by the basis. -/
def lieAlg : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ) := Submodule.span ℝ (Set.range L.e)

theorem κ_sum (v : Fin d → ℝ) : L.κ (∑ a, v a • L.e a) = v := by
  rw [map_sum]
  simp only [map_smul, L.κ_e]
  funext c
  simp [Finset.sum_apply, Pi.single_apply]

/-- Elements of the Lie algebra are recovered from their coordinates. -/
theorem sum_κ_of_mem {X : Matrix (Fin m) (Fin m) ℂ} (hX : X ∈ L.lieAlg) :
    ∑ a, L.κ X a • L.e a = X := by
  obtain ⟨v, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hX
  rw [L.κ_sum]

theorem sum_mem (v : Fin d → ℝ) : ∑ a, v a • L.e a ∈ L.lieAlg :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- The Lie algebra is closed under the bracket. -/
theorem bracket_mem {X Y : Matrix (Fin m) (Fin m) ℂ} (hX : X ∈ L.lieAlg) (hY : Y ∈ L.lieAlg) :
    X * Y - Y * X ∈ L.lieAlg := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hY using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [L.bracket]
      exact L.sum_mem _
    | zero => simp
    | add y z _ _ hy hz =>
      rw [mul_add, add_mul]
      convert add_mem hy hz using 1
      abel
    | smul t y _ hy =>
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
      exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add x z _ _ hx hz =>
    rw [add_mul, mul_add]
    convert add_mem hx hz using 1
    abel
  | smul t x _ hx =>
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ _ hx

/-- The real coefficients of the coordinate map on matrix units. -/
def α (c : Fin d) (i j : Fin m) : ℝ := L.κ (Matrix.single i j 1) c

/-- The real coefficients of the coordinate map on imaginary matrix units. -/
def β (c : Fin d) (i j : Fin m) : ℝ := L.κ (Matrix.single i j Complex.I) c

/-- The coordinates in terms of real and imaginary parts of the entries. -/
theorem κ_apply (X : Matrix (Fin m) (Fin m) ℂ) (c : Fin d) :
    L.κ X c = ∑ i, ∑ j, ((X i j).re * L.α c i j + (X i j).im * L.β c i j) := by
  have hX : X = ∑ i, ∑ j, ((X i j).re • Matrix.single i j (1 : ℂ) +
      (X i j).im • Matrix.single i j Complex.I) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
    congr 1
    apply Complex.ext <;> simp
  conv_lhs => rw [hX]
  simp only [map_sum, map_add, map_smul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem sum_α_β (a c : Fin d) :
    ∑ i, ∑ j, ((L.e a i j).re * L.α c i j + (L.e a i j).im * L.β c i j) =
      if a = c then 1 else 0 := by
  rw [← L.κ_apply, L.κ_e, Pi.single_apply]
  by_cases h : a = c
  · subst h; simp
  · simp [h, Ne.symm h]

end LieBasis

/-- `u ↦ u + i0` as a continuous linear map. -/
def Cx.ofReL {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] : V →L[ℝ] Cx V :=
  LinearMap.mkContinuous
    { toFun := Cx.ofRe
      map_add' := fun u v => by ext <;> simp [Cx.ofRe]
      map_smul' := fun t u => by ext <;> simp [Cx.ofRe] }
    1 fun u => by
      show ‖u‖ + ‖(0 : V)‖ ≤ 1 * ‖u‖
      simp

/-! ### Complex constants and `𝔤`-valued matrix fields -/

section Coord

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {s : ℕ} [hs : Fact (3 ≤ s)] {m d : ℕ}

/-- Complex constants as elements of the complexified Banach algebra. -/
def cplxRingHom : ℂ →+* Cx (SobAlg c r s) where
  toFun z := ⟨z.re • 1, z.im • 1⟩
  map_one' := by ext <;> simp
  map_mul' z w := by
    ext <;> simp <;> module
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp [add_smul]

theorem constM_eq (X : Matrix (Fin m) (Fin m) ℂ) :
    constM (c := c) (r := r) s X = (cplxRingHom (c := c) (r := r) (s := s)).mapMatrix X := rfl

theorem constM_mul (X Y : Matrix (Fin m) (Fin m) ℂ) :
    constM (c := c) (r := r) s (X * Y) = constM s X * constM s Y := by
  rw [constM_eq, constM_eq, constM_eq, map_mul]

theorem constM_sub (X Y : Matrix (Fin m) (Fin m) ℂ) :
    constM (c := c) (r := r) s (X - Y) = constM s X - constM s Y := by
  rw [constM_eq, constM_eq, constM_eq, map_sub]

theorem constM_smul (t : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) :
    constM (c := c) (r := r) s (t • X) = t • constM s X := by
  refine Matrix.ext fun i j => ?_
  ext <;> simp [constM, smul_smul]

theorem constM_sum {ι : Type*} (t : Finset ι) (X : ι → Matrix (Fin m) (Fin m) ℂ) :
    constM (c := c) (r := r) s (∑ i ∈ t, X i) = ∑ i ∈ t, constM s (X i) := by
  rw [constM_eq, map_sum]; rfl

/-- **`𝔤`-valued fields from their coordinates**: `u ↦ Σ_a u_a e_a`. -/
def embX (L : LieBasis m d) (u : Fin d → SobAlg c r s) : MatSob c r s m :=
  ∑ a, Cx.ofRe (u a) • constM s (L.e a)

theorem embX_apply (L : LieBasis m d) (u : Fin d → SobAlg c r s) (i j : Fin m) :
    embX L u i j = ⟨∑ a, (L.e a i j).re • u a, ∑ a, (L.e a i j).im • u a⟩ := by
  simp only [embX, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  ext
  · simp only [Cx.ofRe_mul_eq]
    rw [show (∑ a, (⟨u a * (constM s (L.e a) i j).re, u a * (constM s (L.e a) i j).im⟩ :
      Cx (SobAlg c r s))).re = ∑ a, u a * (constM s (L.e a) i j).re from by
        induction (Finset.univ : Finset (Fin d)) using Finset.induction_on <;> simp_all]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [constM, mul_comm]
  · simp only [Cx.ofRe_mul_eq]
    rw [show (∑ a, (⟨u a * (constM s (L.e a) i j).re, u a * (constM s (L.e a) i j).im⟩ :
      Cx (SobAlg c r s))).im = ∑ a, u a * (constM s (L.e a) i j).im from by
        induction (Finset.univ : Finset (Fin d)) using Finset.induction_on <;> simp_all]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [constM, mul_comm]

theorem embX_add (L : LieBasis m d) (u v : Fin d → SobAlg c r s) :
    embX L (u + v) = embX L u + embX L v := by
  simp only [embX, ← Finset.sum_add_distrib, Pi.add_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← add_smul]
  congr 1
  ext <;> simp [Cx.ofRe]

theorem embX_smul (L : LieBasis m d) (t : ℝ) (u : Fin d → SobAlg c r s) :
    embX L (t • u) = t • embX L u := by
  simp only [embX, Finset.smul_sum, Pi.smul_apply]
  refine Finset.sum_congr rfl fun a _ => Matrix.ext fun i j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Cx.ofRe_mul_eq]
  ext <;> simp [smul_mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- `embX` as a continuous linear map. -/
def embXL (L : LieBasis m d) : (Fin d → SobAlg c r s) →L[ℝ] MatSob c r s m where
  toFun := embX L
  map_add' := embX_add L
  map_smul' := embX_smul L
  cont := by
    have : Continuous fun u : Fin d → SobAlg c r s =>
        ∑ a, Cx.ofRe (u a) • constM (c := c) (r := r) s (L.e a) := by
      refine continuous_finsetSum _ fun a _ => ?_
      have h1 : Continuous fun u : Fin d → SobAlg c r s => Cx.ofRe (u a) :=
        (Cx.ofReL (V := SobAlg c r s)).continuous.comp (continuous_apply a)
      exact h1.smul continuous_const
    exact this

theorem embXL_apply (L : LieBasis m d) (u : Fin d → SobAlg c r s) : embXL L u = embX L u := rfl

/-- The pointwise coordinates of a matrix field. -/
def coordFun (L : LieBasis m d) (M : MatSob c r s m) : Fin d → SobAlg c r s :=
  fun e => ∑ i, ∑ j, (L.α e i j • (M i j).re + L.β e i j • (M i j).im)

set_option backward.isDefEq.respectTransparency false in
/-- **The coordinates** `M ↦ κ ∘ M` as a continuous linear map. -/
def coordL (L : LieBasis m d) : MatSob c r s m →L[ℝ] (Fin d → SobAlg c r s) where
  toFun := coordFun L
  map_add' M N := by
    funext e
    simp only [coordFun, Matrix.add_apply, Cx.add_re, Cx.add_im, smul_add, Pi.add_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by abel
  map_smul' t M := by
    funext e
    simp only [coordFun, Matrix.smul_apply, Cx.smul_re, Cx.smul_im, Pi.smul_apply,
      RingHom.id_apply, Finset.smul_sum, smul_add, smul_comm t]
  cont := by
    refine continuous_pi fun e => continuous_finsetSum _ fun i _ => continuous_finsetSum _
      fun j _ => ?_
    have hij : Continuous fun M : MatSob c r s m => M i j :=
      (continuous_apply j).comp (continuous_apply i)
    have hre : Continuous fun z : Cx (SobAlg c r s) => z.re :=
      continuous_iff_continuousAt.mpr fun z => tendsto_nhds_iff_seq_tendsto.mpr fun u hu =>
        Cx.tendsto_re hu
    have him : Continuous fun z : Cx (SobAlg c r s) => z.im :=
      continuous_iff_continuousAt.mpr fun z => tendsto_nhds_iff_seq_tendsto.mpr fun u hu =>
        Cx.tendsto_im hu
    exact ((hre.comp hij).const_smul (L.α e i j)).add ((him.comp hij).const_smul (L.β e i j))

theorem coordL_apply (L : LieBasis m d) (M : MatSob c r s m) (e : Fin d) :
    coordL L M e = ∑ i, ∑ j, (L.α e i j • (M i j).re + L.β e i j • (M i j).im) := rfl

/-- **Coordinates of `Σ_a u_a e_a` are `u`.** -/
theorem coordL_embX (L : LieBasis m d) (u : Fin d → SobAlg c r s) : coordL L (embX L u) = u := by
  funext e
  rw [coordL_apply]
  have key : ∀ i j, L.α e i j • (embX L u i j).re + L.β e i j • (embX L u i j).im =
      ∑ a, ((L.e a i j).re * L.α e i j + (L.e a i j).im * L.β e i j) • u a := by
    intro i j
    rw [embX_apply]
    simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, add_smul]
    refine Finset.sum_congr rfl fun a _ => by rw [mul_comm (L.α e i j), mul_comm (L.β e i j)]
  simp only [key]
  have h1 : ∀ i : Fin m, ∑ j, ∑ a, ((L.e a i j).re * L.α e i j + (L.e a i j).im * L.β e i j) •
      u a = ∑ a, ∑ j, ((L.e a i j).re * L.α e i j + (L.e a i j).im * L.β e i j) • u a :=
    fun i => Finset.sum_comm
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  simp only [← Finset.sum_smul, L.sum_α_β]
  simp

/-- The bracket of coordinate fields, via the structure constants. -/
def brk (L : LieBasis m d) (u v : Fin d → SobAlg c r s) : Fin d → SobAlg c r s :=
  fun e => ∑ a, ∑ b, L.f a b e • (u a * v b)

theorem ofRe_smul_constM_smul (x : SobAlg c r s) (t : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) :
    Cx.ofRe x • (t • constM (c := c) (r := r) s X) = Cx.ofRe (t • x) • constM s X := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Cx.ofRe_mul_eq]
  ext <;> simp [mul_smul_comm, smul_mul_assoc]

theorem embX_mul (L : LieBasis m d) (u v : Fin d → SobAlg c r s) :
    embX L u * embX L v = ∑ a, ∑ b, Cx.ofRe (u a * v b) •
      (constM (c := c) (r := r) s (L.e a) * constM s (L.e b)) := by
  simp only [embX, Finset.sum_mul_sum, smul_mul_smul_comm, Cx.ofRe_mul]

/-- **The bracket of `𝔤`-valued fields in coordinates.** -/
theorem embX_mul_sub (L : LieBasis m d) (u v : Fin d → SobAlg c r s) :
    embX L u * embX L v - embX L v * embX L u = embX L (brk L u v) := by
  rw [embX_mul, embX_mul, Finset.sum_comm (f := fun a b => Cx.ofRe (v a * u b) •
    (constM (c := c) (r := r) s (L.e a) * constM s (L.e b)))]
  simp only [← Finset.sum_sub_distrib, mul_comm (v _) (u _), ← smul_sub, ← constM_mul,
    ← constM_sub, L.bracket, constM_sum, constM_smul, Finset.smul_sum, ofRe_smul_constM_smul]
  rw [embX]
  simp only [brk]
  have hofRe : ∀ (t : Finset (Fin d)) (g : Fin d → SobAlg c r s),
      Cx.ofRe (∑ i ∈ t, g i) = ∑ i ∈ t, Cx.ofRe (g i) := fun t g => map_sum Cx.ofReL g t
  simp only [hofRe, Finset.sum_smul]
  exact (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm

/-- Derivatives act on the coordinates. -/
theorem derM_embX (L : LieBasis m d) (μ : Fin 4) (u : Fin d → SobAlg c r (s + 1)) :
    derM μ (embX L u) = embX L (fun a => derS μ (u a)) := by
  refine Matrix.ext fun i j => ?_
  rw [derM_apply, embX_apply, embX_apply]
  simp only [map_sum, map_smul]

/-- Restrictions act on the coordinates. -/
theorem rhoM_embX (L : LieBasis m d) (u : Fin d → SobAlg c r (s + 1)) :
    rhoM (embX L u) = embX L (fun a => restrS (Nat.le_succ s) (u a)) := by
  refine Matrix.ext fun i j => ?_
  rw [rhoM_apply, embX_apply, embX_apply]
  simp only [map_sum, map_smul]

/-- Pointwise values of `Σ_a u_a e_a`. -/
theorem evM_embX (L : LieBasis m d) (u : Fin d → SobAlg c r s) :
    evM (embX L u) =ᵐ[volume.restrict (euclBall c r)]
      fun x => ∑ a, ((fn (u a) x : ℝ) : ℂ) • L.e a := by
  refine ae_matrix_of_entries fun i j => ?_
  have hre : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ i j,
      fn (∑ a, (L.e a i j).re • u a) x = ∑ a, (L.e a i j).re * fn (u a) x := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    have h1 := fn_sum Finset.univ (fun a => (L.e a i j).re • u a)
    have h2 : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ a,
        fn ((L.e a i j).re • u a) x = (L.e a i j).re * fn (u a) x := by
      rw [ae_all_iff]; exact fun a => fn_smul _ _
    filter_upwards [h1, h2] with x e1 e2
    rw [e1]; exact Finset.sum_congr rfl fun a _ => e2 a
  have him : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ i j,
      fn (∑ a, (L.e a i j).im • u a) x = ∑ a, (L.e a i j).im * fn (u a) x := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    have h1 := fn_sum Finset.univ (fun a => (L.e a i j).im • u a)
    have h2 : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ a,
        fn ((L.e a i j).im • u a) x = (L.e a i j).im * fn (u a) x := by
      rw [ae_all_iff]; exact fun a => fn_smul _ _
    filter_upwards [h1, h2] with x e1 e2
    rw [e1]; exact Finset.sum_congr rfl fun a _ => e2 a
  filter_upwards [hre, him] with x e1 e2
  simp only [evM_apply, evC, embX_apply, e1 i j, e2 i j, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [← Complex.re_add_im (L.e a i j)]
  ring

/-- Pointwise values of the coordinates. -/
theorem fn_coordL (L : LieBasis m d) (M : MatSob c r s m) (e : Fin d) :
    fn (coordL L M e) =ᵐ[volume.restrict (euclBall c r)] fun x => L.κ (evM M x) e := by
  have h1 := fn_sum Finset.univ (fun i => ∑ j, (L.α e i j • (M i j).re + L.β e i j • (M i j).im))
  have h2 : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ i,
      fn (∑ j, (L.α e i j • (M i j).re + L.β e i j • (M i j).im)) x =
        ∑ j, (L.α e i j * fn (M i j).re x + L.β e i j * fn (M i j).im x) := by
    rw [ae_all_iff]; intro i
    have h3 := fn_sum Finset.univ (fun j => L.α e i j • (M i j).re + L.β e i j • (M i j).im)
    have h4 : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ j,
        fn (L.α e i j • (M i j).re + L.β e i j • (M i j).im) x =
          L.α e i j * fn (M i j).re x + L.β e i j * fn (M i j).im x := by
      rw [ae_all_iff]; intro j
      filter_upwards [fn_add (L.α e i j • (M i j).re) (L.β e i j • (M i j).im),
        fn_smul (L.α e i j) (M i j).re, fn_smul (L.β e i j) (M i j).im] with x e1 e2 e3
      rw [e1, e2, e3]
    filter_upwards [h3, h4] with x e3 e4
    rw [e3]; exact Finset.sum_congr rfl fun j _ => e4 j
  filter_upwards [h1, h2] with x e1 e2
  rw [coordL_apply, e1, L.κ_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e2 i]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [evM_apply, evC]
  simp
  ring

end Coord

/-! ### Exponentials preserve the Lie algebra -/

section LieExp

variable {m d : ℕ} (L : LieBasis m d)

/-- The projection `X ↦ Σ_a κ(X)_a e_a` onto the Lie algebra. -/
def LieBasis.projL : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun X := ∑ a, L.κ X a • L.e a
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' t X := by simp [Finset.smul_sum, smul_smul]

theorem LieBasis.closed_lieAlg : IsClosed (L.lieAlg : Set (Matrix (Fin m) (Fin m) ℂ)) :=
  L.lieAlg.closed_of_finiteDimensional

set_option backward.isDefEq.respectTransparency false in
/-- **`e^X Y e^{-X} ∈ 𝔤`** for `X, Y ∈ 𝔤`. -/
theorem LieBasis.exp_conj_mem {X Y : Matrix (Fin m) (Fin m) ℂ} (hX : X ∈ L.lieAlg)
    (hY : Y ∈ L.lieAlg) : exp X * Y * exp (-X) ∈ L.lieAlg := by
  have h := MatrixExpDerivative.exp_smul_adOp_apply X Y 1
  simp only [one_smul] at h
  rw [← h]
  set T := MatrixExpDerivative.adOp X
  have hT : ∀ k : ℕ, (T ^ k) Y ∈ L.lieAlg := by
    intro k
    induction k with
    | zero => simpa using hY
    | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, MatrixExpDerivative.adOp_apply]
      exact L.bracket_mem hX ih
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) T).mapL
    (ContinuousLinearMap.apply ℝ (Matrix (Fin m) (Fin m) ℂ) Y)
  refine L.closed_lieAlg.mem_of_tendsto hs.tendsto_sum_nat (Eventually.of_forall fun N => ?_)
  refine Submodule.sum_mem _ fun k _ => ?_
  simp only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (hT k)

theorem LieBasis.projL_mem (X : Matrix (Fin m) (Fin m) ℂ) : L.projL X ∈ L.lieAlg :=
  L.sum_mem _

theorem LieBasis.projL_of_mem {X : Matrix (Fin m) (Fin m) ℂ} (hX : X ∈ L.lieAlg) :
    L.projL X = X := L.sum_κ_of_mem hX

set_option backward.isDefEq.respectTransparency false in
/-- Interval integrals of continuous `𝔤`-valued curves are in `𝔤`. -/
theorem LieBasis.intervalIntegral_mem {w : ℝ → Matrix (Fin m) (Fin m) ℂ} (hw : Continuous w)
    (hmem : ∀ s, w s ∈ L.lieAlg) : (∫ s in (0 : ℝ)..1, w s) ∈ L.lieAlg := by
  set P : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    LinearMap.toContinuousLinearMap L.projL
  have h := P.intervalIntegral_comp_comm (hw.intervalIntegrable (μ := volume) 0 1)
  have hP : ∀ s, P (w s) = w s := fun s => L.projL_of_mem (hmem s)
  simp only [hP] at h
  rw [h]
  exact L.projL_mem _

set_option backward.isDefEq.respectTransparency false in
/-- **`D exp(X)[Y] e^{-X} ∈ 𝔤`** for `X, Y ∈ 𝔤` (Duhamel's formula and `Ad`-invariance). -/
theorem LieBasis.fderiv_exp_mul_mem {X Y : Matrix (Fin m) (Fin m) ℂ} (hX : X ∈ L.lieAlg)
    (hY : Y ∈ L.lieAlg) : fderiv ℝ exp X Y * exp (-X) ∈ L.lieAlg := by
  rw [MatrixExpDerivative.fderiv_exp_apply]
  set R : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin m) (Fin m) ℂ)).flip (exp (-X))
  have hc : Continuous fun s : ℝ => exp (s • X) * Y * exp ((1 - s) • X) :=
    ((MatrixExpDerivative.continuous_exp'.comp (continuous_id.smul continuous_const)).mul
      continuous_const).mul (MatrixExpDerivative.continuous_exp'.comp
        ((continuous_const.sub continuous_id).smul continuous_const))
  have h := R.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 1)
  have hR : ∀ Z, R Z = Z * exp (-X) := fun Z => rfl
  rw [← hR, ← h]
  have he : ∀ s : ℝ, exp (s • X) * Y * exp ((1 - s) • X) * exp (-X) =
      exp (s • X) * Y * exp (-(s • X)) := by
    intro s
    rw [mul_assoc (exp (s • X) * Y), ← MatrixExpDerivative.exp_add_of_commute'
      (((Commute.refl X).smul_left (1 - s)).neg_right)]
    congr 2
    rw [sub_smul, one_smul]; abel
  simp only [hR, he]
  refine L.intervalIntegral_mem ?_ fun s => L.exp_conj_mem (L.lieAlg.smul_mem s hX) hY
  exact ((MatrixExpDerivative.continuous_exp'.comp (continuous_id.smul continuous_const)).mul
    continuous_const).mul (MatrixExpDerivative.continuous_exp'.comp
      (continuous_id.smul continuous_const).neg)

end LieExp

end RenewalGeometry.BallAnalysis.BallAlg
