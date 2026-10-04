/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.VariableTorusDiracEstimates

/-!
# Plane-wave consistency of the variable covariant Wilson operator, and the norm-resolvent limit

Paper `predictive_spectral_geometry`, `thm:supp-compact-spin-resolvent`, clause
`eq:supp-local-norm-resolvent` (and the spectral-projection clause) for the fixed smooth
periodic coordinate extension with genuinely variable coefficients.

* `USmall`, `UBdd`: uniform smallness / boundedness of families indexed by the mesh, with a small
  calculus (sums, products with bounded factors).
* `Coeffs.uSmall_link`: exact transport links satisfy `h⁻¹ (U_j(x) - I) → Ω_j(x/m)` uniformly
  in the lattice point (for a merely continuous connection).
* `Coeffs.uSmall_covPlaneSymbol_sub`: **the local plane-wave symbol of the covariant Wilson
  operator converges uniformly to the continuum symbol**,
  `sup_x ‖covPlaneSymbol_{1/m}(x) - A_k(x/m)‖ → 0`, from the link expansion, the `C¹` Taylor
  expansion of `c^j` along `e_j`, and `e^{2πik_j/m} = 1 + 2πik_j/m + O(m⁻²)`; the Wilson term
  tends to zero on plane waves.
* `Coeffs.tendsto_covStage_planeWave`: **(A3) on plane waves**,
  `𝒥⁰_h D_h (𝒥⁰_h)^* (e^{2πik·x} v) → A_k e^{2πik·x} v = D̂_g (e^{2πik·x} v)` in `L²`, by the
  cellwise sup estimate for the piecewise-constant embedding.
* `Coeffs.wilsonDiscretization`, `Coeffs.supp_local_norm_resolvent`: **`eq:supp-local-norm-resolvent`
  and the spectral-projection clause** for the variable-coefficient periodic extension, with (A2)
  from `Coeffs.exists_uniform_garding` and (A3) from `Coeffs.tendsto_covStage_planeWave`.
* The fixed doubled convention from undoubled data: `Coeffs.doubled` (`ĉ^j = c^j ⊗ σ₁`,
  `Ω̂ = Ω ⊗ I`), `Coeffs.doubled_uniformlyElliptic` (from `c^j c^k + c^k c^j = 2 g^{jk}(y)` and
  uniformly elliptic `g`), `Coeffs.doubled_grading` (`γ̂ = I ⊗ σ₃` anticommutes with the covariant
  Wilson operator), `Coeffs.supp_local_norm_resolvent_doubled`.
* Non-vacuity: `cosDoubledCoeffs` (`(3 + 2 cos 2πx) σ₁` on `𝕋¹`, connection `i I`, exact links
  `exp(ihI)`), `cosDoubled_tendsto_norm_resolvent`, and the undoubled `cosCoeffs` example.
-/

open MeasureTheory Set Finset ComplexConjugate UnitAddTorus Filter Topology Matrix
open scoped BigOperators Real ENNReal InnerProductSpace lp

noncomputable section

namespace RenewalGeometry.VariableTorusDirac

open FlatTorusSpinAtlas CovariantWilsonGarding VariableWilsonGarding FrozenWilsonGarding
  LatticeTorusPlancherel TorusCellEmbedding

set_option linter.unusedSectionVars false

variable {d K : ℕ}

/-! ### Uniform smallness along the meshes -/

section uniform

variable {X : ℕ → Type*} {E : Type*} [SeminormedAddCommGroup E]

/-- A family `f n : X n → E` is uniformly small: `sup_x ‖f n x‖ → 0`. -/
def USmall (f : ∀ n, X n → E) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, ‖f n x‖ ≤ ε

/-- A family is eventually uniformly bounded. -/
def UBdd (f : ∀ n, X n → E) : Prop := ∃ B, ∀ᶠ n in atTop, ∀ x, ‖f n x‖ ≤ B

namespace USmall

theorem zero : USmall (X := X) (fun _ _ => (0 : E)) :=
  fun ε hε => Eventually.of_forall fun n x => by rw [norm_zero]; exact hε.le

theorem add {f g : ∀ n, X n → E} (hf : USmall f) (hg : USmall g) :
    USmall (fun n x => f n x + g n x) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε)] with n h1 h2 x
  calc ‖f n x + g n x‖ ≤ ‖f n x‖ + ‖g n x‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (h1 x) (h2 x)
    _ = ε := add_halves ε

theorem neg {f : ∀ n, X n → E} (hf : USmall f) : USmall (fun n x => -f n x) := by
  intro ε hε
  filter_upwards [hf ε hε] with n h x
  rw [norm_neg]; exact h x

theorem sub {f g : ∀ n, X n → E} (hf : USmall f) (hg : USmall g) :
    USmall (fun n x => f n x - g n x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem congr {f g : ∀ n, X n → E} (hf : USmall f) (h : ∀ n x, f n x = g n x) : USmall g := by
  intro ε hε
  filter_upwards [hf ε hε] with n hn x
  rw [← h]; exact hn x

theorem of_norm_le {F : Type*} [SeminormedAddCommGroup F] {f : ∀ n, X n → E}
    {g : ∀ n, X n → F} (hg : USmall g) (C : ℝ) (h : ∀ᶠ n in atTop, ∀ x, ‖f n x‖ ≤ C * ‖g n x‖) :
    USmall f := by
  intro ε hε
  have hC : 0 < |C| + 1 := by positivity
  filter_upwards [hg (ε / (|C| + 1)) (by positivity), h] with n h1 h2 x
  calc ‖f n x‖ ≤ C * ‖g n x‖ := h2 x
    _ ≤ |C| * ‖g n x‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
    _ ≤ (|C| + 1) * (ε / (|C| + 1)) :=
        mul_le_mul (by linarith) (h1 x) (norm_nonneg _) hC.le
    _ = ε := by field_simp

theorem of_bound {f : ∀ n, X n → E} {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, ∀ x, ‖f n x‖ ≤ b n) : USmall f := by
  intro ε hε
  filter_upwards [h, (tendsto_order.1 hb).2 ε hε] with n h1 h2 x
  exact (h1 x).trans h2.le

theorem of_tendsto {s : ℕ → E} (hs : Tendsto s atTop (𝓝 0)) : USmall (X := X) (fun n _ => s n) :=
  of_bound (b := fun n => ‖s n‖) (by simpa using hs.norm)
    (Eventually.of_forall fun n x => le_rfl)

theorem sum {ι : Type*} (s : Finset ι) {f : ι → ∀ n, X n → E}
    (h : ∀ i ∈ s, USmall (f i)) : USmall (fun n x => ∑ i ∈ s, f i n x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (X := X) (E := E))
  | insert a s ha ih =>
    refine (USmall.add (h a (mem_insert_self a s))
      (ih fun i hi => h i (mem_insert_of_mem hi))).congr fun n x => ?_
    rw [sum_insert ha]

theorem uBdd {f : ∀ n, X n → E} (hf : USmall f) : UBdd f := ⟨1, hf 1 one_pos⟩

theorem comp {Y : ℕ → Type*} {f : ∀ n, X n → E} (hf : USmall f) (φ : ∀ n, Y n → X n) :
    USmall (fun n y => f n (φ n y)) := by
  intro ε hε
  filter_upwards [hf ε hε] with n h y
  exact h _

end USmall

namespace UBdd

theorem of_bound {f : ∀ n, X n → E} (B : ℝ) (h : ∀ n x, ‖f n x‖ ≤ B) : UBdd f :=
  ⟨B, Eventually.of_forall h⟩

theorem add {f g : ∀ n, X n → E} (hf : UBdd f) (hg : UBdd g) :
    UBdd (fun n x => f n x + g n x) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨A + B, ?_⟩
  filter_upwards [hA, hB] with n h1 h2 x
  exact (norm_add_le _ _).trans (add_le_add (h1 x) (h2 x))

theorem nonneg_bound {f : ∀ n, X n → E} (hf : UBdd f) :
    ∃ B, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ x, ‖f n x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨max B 0, le_max_right _ _, hB.mono fun n h x => (h x).trans (le_max_left _ _)⟩

end UBdd

section mul

variable {R : Type*} [NonUnitalSeminormedRing R]

theorem USmall.mul_uBdd {f g : ∀ n, X n → R} (hf : USmall f) (hg : UBdd g) :
    USmall (fun n x => f n x * g n x) := by
  obtain ⟨B, hB0, hB⟩ := hg.nonneg_bound
  refine USmall.of_norm_le hf B ?_
  filter_upwards [hB] with n h x
  rw [mul_comm B]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (h x) (norm_nonneg _))

theorem UBdd.mul_uSmall {f g : ∀ n, X n → R} (hf : UBdd f) (hg : USmall g) :
    USmall (fun n x => f n x * g n x) := by
  obtain ⟨B, hB0, hB⟩ := hf.nonneg_bound
  refine USmall.of_norm_le hg B ?_
  filter_upwards [hB] with n h x
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (h x) (norm_nonneg _))

end mul

section smul

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

theorem USmall.smul_uBdd {s : ∀ n, X n → 𝕜} {f : ∀ n, X n → E} (hs : USmall s) (hf : UBdd f) :
    USmall (fun n x => s n x • f n x) := by
  obtain ⟨B, hB0, hB⟩ := hf.nonneg_bound
  refine USmall.of_norm_le hs B ?_
  filter_upwards [hB] with n h x
  rw [norm_smul, mul_comm B]
  exact mul_le_mul_of_nonneg_left (h x) (norm_nonneg _)

theorem UBdd.smul_uSmall {s : ∀ n, X n → 𝕜} {f : ∀ n, X n → E} (hs : UBdd s) (hf : USmall f) :
    USmall (fun n x => s n x • f n x) := by
  obtain ⟨B, hB0, hB⟩ := hs.nonneg_bound
  refine USmall.of_norm_le hf B ?_
  filter_upwards [hB] with n h x
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)

theorem USmall.const_smul {f : ∀ n, X n → E} (hf : USmall f) (c : 𝕜) :
    USmall (fun n x => c • f n x) :=
  (UBdd.of_bound (X := X) (f := fun _ _ => c) ‖c‖ fun _ _ => le_rfl).smul_uSmall hf

end smul

end uniform

/-! ### The phases `ω_j = e^{2πik_j/m}` -/

section phase

/-- `e^{2πik·(t e_j)} = e^{2πi k_j t}`. -/
theorem mFourier_lineVec (k : Fin d → ℤ) (j : Fin d) (t : ℝ) :
    mFourier k (lineVec j t) = Complex.exp (2 * π * Complex.I * (k j : ℂ) * (t : ℂ)) := by
  simp only [mFourier, ContinuousMap.coe_mk, lineVec]
  rw [Finset.prod_eq_single j]
  · rw [Pi.single_eq_same, fourier_coe_apply]; simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, fourier_apply, smul_zero, AddCircle.toCircle_zero, Circle.coe_one]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The mesh `h_n = 1/(n+1)`. -/
abbrev mesh (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹

theorem mesh_pos (n : ℕ) : 0 < mesh n := by unfold mesh; positivity

theorem tendsto_mesh : Tendsto mesh atTop (𝓝 0) := by
  have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine this.congr fun n => ?_
  rw [mesh, one_div]; push_cast; rfl

/-- The lattice phase `ω_j = χ_k(e_j) = e^{2πik_j/m}`. -/
theorem latticeChar_zcast_single (k : Fin d → ℤ) (j : Fin d) (n : ℕ) :
    latticeChar (zcast (n + 1) k) (Pi.single j 1) =
      Complex.exp (2 * π * Complex.I * (k j : ℂ) * ((mesh n : ℝ) : ℂ)) := by
  rw [← mFourier_shiftVec, ← mFourier_lineVec]
  rfl

/-- `h⁻¹ (e^{c h} - 1) → c` as `h = 1/(n+1) → 0`. -/
theorem tendsto_inv_mesh_mul_exp_sub_one (c : ℂ) :
    Tendsto (fun n => ((mesh n : ℝ) : ℂ)⁻¹ * (Complex.exp (c * ((mesh n : ℝ) : ℂ)) - 1))
      atTop (𝓝 c) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun n => ‖c‖ ^ 2 * mesh n) atTop (𝓝 (‖c‖ ^ 2 * 0)) :=
    tendsto_mesh.const_mul _
  rw [mul_zero] at hb
  have hsmall : ∀ᶠ n in atTop, ‖c * ((mesh n : ℝ) : ℂ)‖ ≤ 1 := by
    have : Tendsto (fun n => ‖c‖ * mesh n) atTop (𝓝 (‖c‖ * 0)) := tendsto_mesh.const_mul _
    rw [mul_zero] at this
    filter_upwards [(tendsto_order.1 this).2 1 one_pos] with n hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mesh_pos n)]
    exact hn.le
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [hsmall] with n hn
  have hm := mesh_pos n
  have hm0 : ((mesh n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have e : ((mesh n : ℝ) : ℂ)⁻¹ * (Complex.exp (c * ((mesh n : ℝ) : ℂ)) - 1) - c =
      ((mesh n : ℝ) : ℂ)⁻¹ * (Complex.exp (c * ((mesh n : ℝ) : ℂ)) - 1 - c * ((mesh n : ℝ) : ℂ)) := by
    field_simp
  rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  have h1 := Complex.norm_exp_sub_one_sub_id_le hn
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm] at h1
  calc (mesh n)⁻¹ * ‖Complex.exp (c * ((mesh n : ℝ) : ℂ)) - 1 - c * ((mesh n : ℝ) : ℂ)‖
      ≤ (mesh n)⁻¹ * (‖c‖ * mesh n) ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖c‖ ^ 2 * mesh n := by field_simp

theorem tendsto_exp_mul_mesh (c : ℂ) :
    Tendsto (fun n => Complex.exp (c * ((mesh n : ℝ) : ℂ))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => c * ((mesh n : ℝ) : ℂ)) atTop (𝓝 (c * 0)) :=
    ((Complex.continuous_ofReal.tendsto 0).comp tendsto_mesh).const_mul c |>.congr' (by simp)
  rw [mul_zero] at h1
  have := (Complex.continuous_exp.tendsto 0).comp h1
  rw [Complex.exp_zero] at this
  exact this

end phase

/-! ### Algebraic form of the plane-wave symbol -/

section algebra

variable {m : ℕ} [NeZero m]

/-- The first-order link data `a⁺_j = h⁻¹ (ω_j U_j(x) - I)`. -/
def linkPlus (h : ℝ) (U : TorusLinks d m K) (ω : Fin d → ℂ) (j : Fin d) (x : Grid d m) :
    Matrix (Fin K) (Fin K) ℂ :=
  (h : ℂ)⁻¹ • (ω j • U j x - 1)

/-- The first-order link data `a⁻_j = h⁻¹ (ω̄_j U_j(x - e_j)^* - I)`. -/
def linkMinus (h : ℝ) (U : TorusLinks d m K) (ω : Fin d → ℂ) (j : Fin d) (x : Grid d m) :
    Matrix (Fin K) (Fin K) ℂ :=
  (h : ℂ)⁻¹ • (conj (ω j) • (U j (x - Pi.single j 1))ᴴ - 1)

/-- **The plane-wave symbol in first-order form**: with `a^±_j` the first-order link data and
`b_j = h⁻¹ (c^j(x + e_j) - c^j(x - e_j))`,
`covPlaneSymbol = ½ Σ_j (c^j (2i)⁻¹ (a⁺ - a⁻) + (2i)⁻¹ b_j + (2i)⁻¹ (a⁺ c⁺ - a⁻ c⁻))
  - ϖ Γ ½ Σ_j (a⁺ + a⁻)`. -/
theorem covPlaneSymbol_eq (h ϖ : ℝ) (c : CoefficientField d m K) (U : TorusLinks d m K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (ω : Fin d → ℂ) (x : Grid d m) :
    covPlaneSymbol h ϖ c U Γ ω x =
      (2 : ℂ)⁻¹ • ∑ j, (c x j * ((2 * Complex.I)⁻¹ •
          (linkPlus h U ω j x - linkMinus h U ω j x)) +
        ((2 * Complex.I)⁻¹ • ((h : ℂ)⁻¹ • (c (x + Pi.single j 1) j - c (x - Pi.single j 1) j)) +
          (2 * Complex.I)⁻¹ • (linkPlus h U ω j x * c (x + Pi.single j 1) j -
            linkMinus h U ω j x * c (x - Pi.single j 1) j))) +
      (ϖ : ℂ) • (Γ * (-(2 : ℂ)⁻¹ • ∑ j, (linkPlus h U ω j x + linkMinus h U ω j x))) := by
  simp only [covPlaneSymbol]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [linkPlus, linkMinus, smul_mul_assoc, sub_mul, one_mul, mul_smul_comm, mul_sub,
      smul_sub, mul_one]
    module
  · congr 2
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [linkPlus, linkMinus, smul_sub, smul_add]
    module

/-- The continuum first-order link datum `A_j(y) = 2πik_j I + Ω_j(y)`. -/
def Coeffs.linkLimit (C : Coeffs d K) (k : Fin d → ℤ) (j : Fin d) (y : UnitAddTorus (Fin d)) :
    Matrix (Fin K) (Fin K) ℂ :=
  (2 * π * Complex.I * (k j : ℂ)) • 1 + C.Ω j y

/-- **The continuum symbol in the same first-order form** (with `a^± → ±A_j`, `b_j → 2∂_j c^j`,
`c^± → c`): `A_k(y) = ½ Σ_j (c^j (2i)⁻¹ (A - (-A)) + (2i)⁻¹ 2∂_j c^j + (2i)⁻¹ (A c - (-A) c))`. -/
theorem Coeffs.symbField_eq (C : Coeffs d K) (k : Fin d → ℤ) (y : UnitAddTorus (Fin d)) :
    C.symbField k y = (2 : ℂ)⁻¹ • ∑ j, (C.c j y * ((2 * Complex.I)⁻¹ •
          (C.linkLimit k j y - -C.linkLimit k j y)) +
        ((2 * Complex.I)⁻¹ • ((2 : ℂ) • C.dc j y) +
          (2 * Complex.I)⁻¹ • (C.linkLimit k j y * C.c j y - -C.linkLimit k j y * C.c j y))) := by
  rw [symbField_apply, pot_apply, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [linkLimit, sub_neg_eq_add, neg_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul, smul_add]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  match_scalars <;> field_simp <;> push_cast <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

end algebra

/-! ### Uniform convergence of the plane-wave symbol -/

section symbolLimit

open scoped Matrix.Norms.Operator

/-- `‖Aᴴ‖ ≤ N ‖A‖` for the `ℓ^∞` operator norm. -/
theorem linfty_norm_conjTranspose_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ‖Aᴴ‖ ≤ N * ‖A‖ :=
  ExactSpinTransport.norm_le_of_mulVec_le _ (by positivity) fun v =>
    ExactSpinTransport.norm_conjTranspose_mulVec_le A v

/-- A continuous matrix field sampled anywhere is uniformly bounded. -/
theorem uBdd_field {X : ℕ → Type*} (F : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ))
    (φ : ∀ n, X n → UnitAddTorus (Fin d)) : UBdd (fun n x => F (φ n x)) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_entries (fun _ : Fin 1 => F)
  exact UBdd.of_bound (K * B) fun n x => linfty_norm_le_of_entry _ hB0 fun a b => hB 0 _ a b

/-- Uniform continuity along mesh-size displacements: `F(x/m + t_n e_j) - F(x/m) → 0`. -/
theorem uSmall_field_line (F : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)) (j : Fin d)
    (t : ℕ → ℝ) (ht : ∀ n, |t n| ≤ mesh n) :
    USmall (fun n (x : Grid d (n + 1)) => F (samplePt x + lineVec j (t n)) - F (samplePt x)) := by
  intro ε hε
  set ε' : ℝ := ε / (K + 1)
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hosc⟩ := exists_delta_entries (fun _ : Fin 1 => F) hε'
  filter_upwards [(tendsto_order.1 tendsto_mesh).2 δ hδ] with n hn x
  refine (linfty_norm_le_of_entry _ hε'.le fun a b => ?_).trans ?_
  · rw [Matrix.sub_apply]
    exact (hosc _ _ ((dist_add_lineVec_le _ j _).trans_lt ((ht n).trans_lt hn)) 0 a b).le
  · rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith

namespace Coeffs

variable (C : Coeffs d K)

/-- **Uniform first-order expansion of exact transport links**:
`h⁻¹ (U_j(x) - I) - Ω_j(x/m) → 0` uniformly in the lattice point. -/
theorem uSmall_link {U : ∀ n, TorusLinks d (n + 1) K}
    (hU : ∀ n, C.IsTransportLinks (n + 1) (U n)) (j : Fin d) :
    USmall (fun n (x : Grid d (n + 1)) =>
      ((mesh n : ℝ) : ℂ)⁻¹ • (U n j x - 1) - C.Ω j (samplePt x)) := by
  obtain ⟨BΩ, hBΩ0, hBΩ⟩ := C.exists_connection_bound
  intro ε hε
  set ε' : ℝ := ε / 2 / (K + 1)
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hosc⟩ := exists_delta_entries C.Ω hε'
  set A0 := BΩ ^ 2 * ‖(1 : Matrix (Fin K) (Fin K) ℂ)‖ * Real.exp BΩ
  have hA0 : Tendsto (fun n => A0 * mesh n) atTop (𝓝 0) := by
    simpa using tendsto_mesh.const_mul A0
  filter_upwards [(tendsto_order.1 hA0).2 (ε / 2) (half_pos hε),
    (tendsto_order.1 tendsto_mesh).2 δ hδ] with n h1 h2 x
  obtain ⟨Φ, hΦ0, hΦ, hUx⟩ := hU n j x
  have hh := mesh_pos n
  have h0 : samplePt x + lineVec j (0 : ℝ) = samplePt x := by simp [lineVec]
  have hΩε : ∀ t ∈ Icc 0 (mesh n), ‖C.Ω j (samplePt x + lineVec j t) -
      C.Ω j (samplePt x + lineVec j 0)‖ ≤ K * ε' := by
    intro t ht
    rw [h0]
    refine linfty_norm_le_of_entry _ hε'.le fun a b => (hosc _ _ ?_ j a b).le
    refine (dist_add_lineVec_le _ j t).trans_lt ?_
    rw [abs_of_nonneg ht.1]; exact ht.2.trans_lt h2
  have key := norm_transport_sub_le_of_osc (Ω := fun t => C.Ω j (samplePt x + lineVec j t))
    (U := Φ) hh.le hBΩ0 (fun t _ => hBΩ j _) hΩε hΦ0 hΦ
  simp only [h0] at key
  have hm0 : ((mesh n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have e : ((mesh n : ℝ) : ℂ)⁻¹ • (U n j x - 1) - C.Ω j (samplePt x) =
      ((mesh n : ℝ) : ℂ)⁻¹ • (Φ (mesh n) - 1 - mesh n • C.Ω j (samplePt x)) := by
    rw [hUx, ← Complex.coe_smul, smul_sub (((mesh n : ℝ) : ℂ)⁻¹) _ (((mesh n : ℝ) : ℂ) • _),
      smul_smul, inv_mul_cancel₀ hm0, one_smul]
  rw [e, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hexp : Real.exp (BΩ * mesh n) ≤ Real.exp BΩ :=
    Real.exp_le_exp.2 (mul_le_of_le_one_right hBΩ0 inv_mesh_le_one)
  have hKε : (K : ℝ) * ε' ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  calc (mesh n)⁻¹ * ‖Φ (mesh n) - 1 - mesh n • C.Ω j (samplePt x)‖
      ≤ (mesh n)⁻¹ * ((BΩ ^ 2 * ‖(1 : Matrix (Fin K) (Fin K) ℂ)‖ * Real.exp (BΩ * mesh n) *
          mesh n + K * ε') * mesh n) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = BΩ ^ 2 * ‖(1 : Matrix (Fin K) (Fin K) ℂ)‖ * Real.exp (BΩ * mesh n) * mesh n + K * ε' := by
        field_simp
    _ ≤ A0 * mesh n + ε / 2 := by
        refine add_le_add ?_ hKε
        have : 0 ≤ BΩ ^ 2 * ‖(1 : Matrix (Fin K) (Fin K) ℂ)‖ := by positivity
        calc BΩ ^ 2 * ‖(1 : Matrix (Fin K) (Fin K) ℂ)‖ * Real.exp (BΩ * mesh n) * mesh n
            ≤ BΩ ^ 2 * ‖(1 : Matrix (Fin K) (Fin K) ℂ)‖ * Real.exp BΩ * mesh n := by gcongr
          _ = A0 * mesh n := rfl
    _ ≤ ε := by linarith

/-- **Difference quotients of `c^j` along `e_j`**: `t⁻¹ (c^j(x/m + t e_j) - c^j(x/m)) → ∂_j c^j`
uniformly, for `t = ±h`. -/
theorem uSmall_diffQuot (j : Fin d) (s : ℝ) (hs : |s| = 1) :
    USmall (fun n (x : Grid d (n + 1)) =>
      ((s * mesh n : ℝ) : ℂ)⁻¹ • (C.c j (samplePt x + lineVec j (s * mesh n)) - C.c j (samplePt x)) -
        C.dc j (samplePt x)) := by
  intro ε hε
  set ε' : ℝ := ε / (K + 1)
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hosc⟩ := exists_delta_entries C.dc hε'
  filter_upwards [(tendsto_order.1 tendsto_mesh).2 δ hδ] with n hn x
  have hh := mesh_pos n
  have hts : |s * mesh n| = mesh n := by rw [abs_mul, hs, one_mul, abs_of_pos hh]
  have ht0 : s * mesh n ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hts; exact hh.ne' hts.symm
  refine (linfty_norm_le_of_entry _ hε'.le fun a b => ?_).trans ?_
  · have hT := C.norm_entry_taylor_le j a b (fun y y' hyy => hosc y y' hyy j a b) (samplePt x)
      (s * mesh n) (by rw [hts]; exact hn)
    have e : (((s * mesh n : ℝ) : ℂ)⁻¹ • (C.c j (samplePt x + lineVec j (s * mesh n)) -
        C.c j (samplePt x)) - C.dc j (samplePt x)) a b =
        ((s * mesh n : ℝ) : ℂ)⁻¹ * (C.c j (samplePt x + lineVec j (s * mesh n)) a b -
          C.c j (samplePt x) a b - ((s * mesh n : ℝ) : ℂ) * C.dc j (samplePt x) a b) := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      have : ((s * mesh n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht0
      rw [mul_sub (((s * mesh n : ℝ) : ℂ)⁻¹) _ (((s * mesh n : ℝ) : ℂ) * _), ← mul_assoc,
        inv_mul_cancel₀ this, one_mul]
    rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, hts]
    calc (mesh n)⁻¹ * ‖C.c j (samplePt x + lineVec j (s * mesh n)) a b - C.c j (samplePt x) a b -
          ((s * mesh n : ℝ) : ℂ) * C.dc j (samplePt x) a b‖ ≤ (mesh n)⁻¹ * (ε' * mesh n) := by
          rw [hts] at hT; exact mul_le_mul_of_nonneg_left hT (by positivity)
      _ = ε' := by field_simp
  · rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith

end Coeffs

/-- The phase `ω_j^{(n)} = χ_k(e_j)` of the frequency `k` at mesh `1/(n+1)`. -/
abbrev phase (k : Fin d → ℤ) (n : ℕ) (j : Fin d) : ℂ := latticeChar (zcast (n + 1) k) (Pi.single j 1)

theorem norm_phase (k : Fin d → ℤ) (n : ℕ) (j : Fin d) : ‖phase k n j‖ = 1 :=
  norm_latticeChar' _ _

theorem conj_phase (k : Fin d → ℤ) (n : ℕ) (j : Fin d) :
    conj (phase k n j) = Complex.exp (-(2 * π * Complex.I * (k j : ℂ)) * ((mesh n : ℝ) : ℂ)) := by
  rw [phase, latticeChar_zcast_single, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  ring

namespace Coeffs

variable (C : Coeffs d K)

/-- `a⁺_j - A_j → 0` uniformly. -/
theorem uSmall_linkPlus {U : ∀ n, TorusLinks d (n + 1) K}
    (hU : ∀ n, C.IsTransportLinks (n + 1) (U n)) (k : Fin d → ℤ) (j : Fin d) :
    USmall (fun n (x : Grid d (n + 1)) =>
      linkPlus (mesh n) (U n) (phase k n) j x - C.linkLimit k j (samplePt x)) := by
  set c : ℂ := 2 * π * Complex.I * (k j : ℂ)
  have hω : ∀ n, phase k n j = Complex.exp (c * ((mesh n : ℝ) : ℂ)) := fun n =>
    latticeChar_zcast_single k j n
  have T1 := (UBdd.of_bound (X := fun n => Grid d (n + 1)) (f := fun n _ => phase k n j) 1
    fun n _ => (norm_phase k n j).le).smul_uSmall (C.uSmall_link hU j)
  have hs2 : Tendsto (fun n => (((mesh n : ℝ) : ℂ)⁻¹ * (phase k n j - 1) - c) •
      (1 : Matrix (Fin K) (Fin K) ℂ)) atTop (𝓝 0) := by
    have := ((tendsto_inv_mesh_mul_exp_sub_one c).sub_const c).smul_const
      (1 : Matrix (Fin K) (Fin K) ℂ)
    simp only [sub_self, zero_smul] at this
    simpa only [hω] using this
  have T2 := USmall.of_tendsto (X := fun n => Grid d (n + 1)) hs2
  have hs3 : Tendsto (fun n => phase k n j - 1) atTop (𝓝 0) := by
    have := (tendsto_exp_mul_mesh c).sub_const 1
    simp only [sub_self] at this
    simpa only [hω] using this
  have T3 := (USmall.of_tendsto (X := fun n => Grid d (n + 1)) hs3).smul_uBdd
    (uBdd_field (C.Ω j) fun n x => samplePt x)
  refine ((T1.add T2).add T3).congr fun n x => ?_
  simp only [linkPlus, linkLimit]
  module

/-- `a⁻_j + A_j → 0` uniformly. -/
theorem uSmall_linkMinus {U : ∀ n, TorusLinks d (n + 1) K}
    (hU : ∀ n, C.IsTransportLinks (n + 1) (U n)) (k : Fin d → ℤ) (j : Fin d) :
    USmall (fun n (x : Grid d (n + 1)) =>
      linkMinus (mesh n) (U n) (phase k n) j x + C.linkLimit k j (samplePt x)) := by
  set c : ℂ := 2 * π * Complex.I * (k j : ℂ)
  have hω : ∀ n, conj (phase k n j) = Complex.exp (-c * ((mesh n : ℝ) : ℂ)) := fun n =>
    conj_phase k n j
  -- the remainder at `x - e_j`
  have R := (C.uSmall_link hU j).comp (fun n (x : Grid d (n + 1)) => x - Pi.single j 1)
  have RH : USmall (fun n (x : Grid d (n + 1)) =>
      (((mesh n : ℝ) : ℂ)⁻¹ • (U n j (x - Pi.single j 1) - 1) -
        C.Ω j (samplePt (x - Pi.single j 1)))ᴴ) :=
    R.of_norm_le (K : ℝ) (Eventually.of_forall fun n x => linfty_norm_conjTranspose_le _)
  have T1 := (UBdd.of_bound (X := fun n => Grid d (n + 1)) (f := fun n _ => conj (phase k n j)) 1
    fun n _ => by rw [Complex.norm_conj, norm_phase]).smul_uSmall RH
  have hs2 : Tendsto (fun n => (((mesh n : ℝ) : ℂ)⁻¹ * (conj (phase k n j) - 1) + c) •
      (1 : Matrix (Fin K) (Fin K) ℂ)) atTop (𝓝 0) := by
    have := ((tendsto_inv_mesh_mul_exp_sub_one (-c)).add_const c).smul_const
      (1 : Matrix (Fin K) (Fin K) ℂ)
    simp only [neg_add_cancel, zero_smul] at this
    simpa only [hω] using this
  have T2 := USmall.of_tendsto (X := fun n => Grid d (n + 1)) hs2
  have hs3 : Tendsto (fun n => 1 - conj (phase k n j)) atTop (𝓝 0) := by
    have := (tendsto_exp_mul_mesh (-c)).const_sub 1
    simp only [sub_self] at this
    simpa only [hω] using this
  have T3 := (USmall.of_tendsto (X := fun n => Grid d (n + 1)) hs3).smul_uBdd
    (uBdd_field (C.Ω j) fun n (x : Grid d (n + 1)) => samplePt (x - Pi.single j 1))
  have T4 := (uSmall_field_line (C.Ω j) j (fun n => -mesh n)
    (fun n => by rw [abs_neg, abs_of_pos (mesh_pos n)])).neg
  refine (((T1.add T2).add T3).add T4).congr fun n x => ?_
  have hsub : samplePt (x - Pi.single j 1) = samplePt x + lineVec j (-mesh n) :=
    samplePt_sub_single x j
  have hstar : star (((mesh n : ℝ) : ℂ)⁻¹) = ((mesh n : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  simp only [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, C.Ω_skew, hstar]
  rw [← hsub]
  simp only [linkMinus, linkLimit]
  module

end Coeffs

end symbolLimit

/-! ### The symbol limit and (A3) -/

section A3

open scoped Matrix.Norms.Operator

variable {X : ℕ → Type*}

theorem UBdd.of_norm_le {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    {f : ∀ n, X n → E} {g : ∀ n, X n → F} (hg : UBdd g) (C : ℝ)
    (h : ∀ᶠ n in atTop, ∀ x, ‖f n x‖ ≤ C * ‖g n x‖) : UBdd f := by
  obtain ⟨B, hB0, hB⟩ := hg.nonneg_bound
  refine ⟨|C| * B, ?_⟩
  filter_upwards [hB, h] with n h1 h2 x
  calc ‖f n x‖ ≤ C * ‖g n x‖ := h2 x
    _ ≤ |C| * ‖g n x‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
    _ ≤ |C| * B := mul_le_mul_of_nonneg_left (h1 x) (abs_nonneg C)

theorem UBdd.comp {E : Type*} [SeminormedAddCommGroup E] {Y : ℕ → Type*} {f : ∀ n, X n → E}
    (hf : UBdd f) (φ : ∀ n, Y n → X n) : UBdd (fun n y => f n (φ n y)) := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨B, hB.mono fun n h y => h _⟩

theorem UBdd.mul {R : Type*} [NonUnitalSeminormedRing R] {f g : ∀ n, X n → R} (hf : UBdd f)
    (hg : UBdd g) : UBdd (fun n x => f n x * g n x) := by
  obtain ⟨A, hA0, hA⟩ := hf.nonneg_bound
  obtain ⟨B, hB0, hB⟩ := hg.nonneg_bound
  refine ⟨A * B, ?_⟩
  filter_upwards [hA, hB] with n h1 h2 x
  exact (norm_mul_le _ _).trans (mul_le_mul (h1 x) (h2 x) (norm_nonneg _) hA0)

/-- A component of `M v` is controlled by the operator norm of `M`. -/
theorem norm_mulVec_apply_le {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) (a : Fin N) :
    ‖(M *ᵥ v) a‖ ≤ ‖v‖ * ‖M‖ := by
  rw [mul_comm]
  exact (norm_le_pi_norm _ a).trans (linfty_opNorm_mulVec M v)

namespace Coeffs

variable (C : Coeffs d K)

/-- **Uniform convergence of the local plane-wave symbol of the covariant Wilson operator**
(`lem:supp-general-core` on plane waves): with exact transport links,
`sup_x ‖covPlaneSymbol_{1/m}(x) - A_k(x/m)‖ → 0`, where `A_k = Σ_j 2πk_j c^j + B` is the symbol
of `D̂_g` on `e^{2πik·x}`. -/
theorem uSmall_covPlaneSymbol_sub {U : ∀ n, TorusLinks d (n + 1) K}
    (hU : ∀ n, C.IsTransportLinks (n + 1) (U n)) (ϖ : ℝ) (Γ : Matrix (Fin K) (Fin K) ℂ)
    (k : Fin d → ℤ) :
    USmall (fun n (x : Grid d (n + 1)) =>
      covPlaneSymbol (mesh n) ϖ (C.sampled (n + 1)) (U n) Γ (phase k n) x -
        C.symbField k (samplePt x)) := by
  set Gr := fun n : ℕ => Grid d (n + 1)
  have hcp : ∀ j, USmall (X := Gr) (fun n x =>
      C.sampled (n + 1) (x + Pi.single j 1) j - C.c j (samplePt x)) := by
    intro j
    refine (uSmall_field_line (C.c j) j (fun n => mesh n)
      (fun n => (abs_of_pos (mesh_pos n)).le)).congr fun n x => ?_
    simp only [Coeffs.sampled]
    rw [samplePt_add_single]
  have hcm : ∀ j, USmall (X := Gr) (fun n x =>
      C.sampled (n + 1) (x - Pi.single j 1) j - C.c j (samplePt x)) := by
    intro j
    refine (uSmall_field_line (C.c j) j (fun n => -mesh n)
      (fun n => by rw [abs_neg, abs_of_pos (mesh_pos n)])).congr fun n x => ?_
    simp only [Coeffs.sampled]
    rw [samplePt_sub_single]
  have hb : ∀ j, USmall (X := Gr) (fun n x => ((mesh n : ℝ) : ℂ)⁻¹ •
      (C.sampled (n + 1) (x + Pi.single j 1) j - C.sampled (n + 1) (x - Pi.single j 1) j) -
        (2 : ℂ) • C.dc j (samplePt x)) := by
    intro j
    have h1 := C.uSmall_diffQuot j 1 (by simp)
    have h2 := C.uSmall_diffQuot j (-1) (by simp)
    refine (h1.add h2).congr fun n x => ?_
    simp only [Coeffs.sampled]
    rw [samplePt_add_single, samplePt_sub_single]
    simp only [one_mul, neg_one_mul, Complex.ofReal_neg, inv_neg, neg_smul, smul_sub]
    module
  have hcbdd : ∀ j, UBdd (X := Gr) (fun n x => C.c j (samplePt x)) := fun j =>
    uBdd_field (C.c j) _
  have hcpbdd : ∀ j, UBdd (X := Gr) (fun n x => C.sampled (n + 1) (x + Pi.single j 1) j) :=
    fun j => uBdd_field (C.c j) _
  have hcmbdd : ∀ j, UBdd (X := Gr) (fun n x => C.sampled (n + 1) (x - Pi.single j 1) j) :=
    fun j => uBdd_field (C.c j) _
  have hAbdd : ∀ j, UBdd (X := Gr) (fun n x => C.linkLimit k j (samplePt x)) := fun j =>
    (UBdd.of_bound (X := Gr) (f := fun _ _ => (2 * π * Complex.I * (k j : ℂ)) •
      (1 : Matrix (Fin K) (Fin K) ℂ)) _ fun _ _ => le_rfl).add (uBdd_field (C.Ω j) _)
  have hP := C.uSmall_linkPlus hU k
  have hM := C.uSmall_linkMinus hU k
  -- the per-direction error
  have hE : ∀ j, USmall (X := Gr) (fun n x =>
      C.c j (samplePt x) * ((2 * Complex.I)⁻¹ •
        ((linkPlus (mesh n) (U n) (phase k n) j x - C.linkLimit k j (samplePt x)) -
          (linkMinus (mesh n) (U n) (phase k n) j x + C.linkLimit k j (samplePt x)))) +
      ((2 * Complex.I)⁻¹ • (((mesh n : ℝ) : ℂ)⁻¹ •
          (C.sampled (n + 1) (x + Pi.single j 1) j - C.sampled (n + 1) (x - Pi.single j 1) j) -
            (2 : ℂ) • C.dc j (samplePt x)) +
        (2 * Complex.I)⁻¹ •
          ((linkPlus (mesh n) (U n) (phase k n) j x - C.linkLimit k j (samplePt x)) *
              C.sampled (n + 1) (x + Pi.single j 1) j +
            C.linkLimit k j (samplePt x) *
              (C.sampled (n + 1) (x + Pi.single j 1) j - C.c j (samplePt x)) -
          ((linkMinus (mesh n) (U n) (phase k n) j x + C.linkLimit k j (samplePt x)) *
              C.sampled (n + 1) (x - Pi.single j 1) j -
            C.linkLimit k j (samplePt x) *
              (C.sampled (n + 1) (x - Pi.single j 1) j - C.c j (samplePt x)))))) := by
    intro j
    refine ((hcbdd j).mul_uSmall (((hP j).sub (hM j)).const_smul _)).add
      (((hb j).const_smul _).add (USmall.const_smul ?_ _))
    exact (((hP j).mul_uBdd (hcpbdd j)).add ((hAbdd j).mul_uSmall (hcp j))).sub
      (((hM j).mul_uBdd (hcmbdd j)).sub ((hAbdd j).mul_uSmall (hcm j)))
  have hW : USmall (X := Gr) (fun n x => (ϖ : ℂ) • (Γ * (-(2 : ℂ)⁻¹ • ∑ j,
      ((linkPlus (mesh n) (U n) (phase k n) j x - C.linkLimit k j (samplePt x)) +
        (linkMinus (mesh n) (U n) (phase k n) j x + C.linkLimit k j (samplePt x)))))) := by
    refine USmall.const_smul ?_ _
    refine (UBdd.of_bound (X := Gr) (f := fun _ _ => Γ) _ fun _ _ => le_rfl).mul_uSmall ?_
    exact (USmall.sum Finset.univ fun j _ => (hP j).add (hM j)).const_smul _
  refine (((USmall.sum Finset.univ fun j _ => hE j).const_smul (2 : ℂ)⁻¹).add hW).congr
    fun n x => ?_
  rw [covPlaneSymbol_eq, C.symbField_eq]
  have hWsum : ∑ j, ((linkPlus (mesh n) (U n) (phase k n) j x - C.linkLimit k j (samplePt x)) +
      (linkMinus (mesh n) (U n) (phase k n) j x + C.linkLimit k j (samplePt x))) =
      ∑ j, (linkPlus (mesh n) (U n) (phase k n) j x + linkMinus (mesh n) (U n) (phase k n) j x) :=
    Finset.sum_congr rfl fun j _ => by abel
  rw [hWsum, add_sub_right_comm, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Coeffs.sampled, mul_smul_comm, mul_sub, sub_mul, mul_add, add_mul, neg_mul, mul_neg,
    smul_sub, smul_add]
  module

end Coeffs

/-- Uniform continuity at the cell scale: `F(x_{index y}/m) - F(y) → 0` uniformly in `y`. -/
theorem uSmall_field_index
    (F : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)) :
    USmall (X := fun _ => UnitAddTorus (Fin d)) (fun n y =>
      F (samplePt (index (n + 1) y)) - F y) := by
  intro ε hε
  set ε' : ℝ := ε / (K + 1)
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hosc⟩ := exists_delta_entries (fun _ : Fin 1 => F) hε'
  filter_upwards [(tendsto_order.1 tendsto_mesh).2 δ hδ] with n hn y
  refine (linfty_norm_le_of_entry _ hε'.le fun a b => ?_).trans ?_
  · rw [Matrix.sub_apply]
    refine (hosc _ _ ?_ 0 a b).le
    rw [dist_comm]
    exact (dist_samplePt_index_le y).trans_lt hn
  · rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith

end A3

/-! ### (A3) on plane waves: the cellwise sup estimate -/

section A3L2

open scoped Matrix.Norms.Operator

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem UBdd.congr {X : ℕ → Type*} {E : Type*} [SeminormedAddCommGroup E] {f g : ∀ n, X n → E}
    (hf : UBdd f) (h : ∀ n x, f n x = g n x) : UBdd g := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨B, hB.mono fun n hn x => by rw [← h]; exact hn x⟩

/-- A sequence converges if it is eventually `ε`-close for every `ε > 0`. -/
theorem tendsto_of_forall_eventually_norm_sub_le {E : Type*} [SeminormedAddCommGroup E]
    {F : ℕ → E} {f : E} (h : ∀ ε > 0, ∀ᶠ n in atTop, ‖F n - f‖ ≤ ε) :
    Tendsto F atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_order.2 ⟨fun b hb => Eventually.of_forall fun n =>
    lt_of_lt_of_le hb (norm_nonneg _), fun ε hε => ?_⟩
  filter_upwards [h (ε / 2) (half_pos hε)] with n hn
  exact lt_of_le_of_lt hn (half_lt_self hε)

/-- The `L²` distance on the (probability) torus is bounded by the sup distance of representatives. -/
theorem norm_L2_sub_le_of_forall {f g : L2T d} {F G : UnitAddTorus (Fin d) → ℂ}
    (hf : (⇑f : UnitAddTorus (Fin d) → ℂ) =ᵐ[volume] F)
    (hg : (⇑g : UnitAddTorus (Fin d) → ℂ) =ᵐ[volume] G) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ y, ‖F y - G y‖ ≤ ε) : ‖f - g‖ ≤ ε := by
  have hae : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin d))), ‖(f - g) y‖ ≤ ε := by
    filter_upwards [Lp.coeFn_sub f g, hf, hg] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    exact h y
  exact (Lp.norm_le_of_ae_bound hε hae).trans (le_of_eq (by simp [measureUnivNNReal]))

namespace Coeffs

variable (C : Coeffs d K)

/-- **(A3) on plane waves for the variable covariant Wilson operator** (`lem:supp-general-core`
in the form needed by `thm:supp-compact-spin-resolvent`): with `W_h = 𝒥⁰_h`, `S_h = (𝒥⁰_h)^*`
and exact transport links,
`𝒥⁰_h D̃^W_{g,h} (𝒥⁰_h)^* (e^{2πik·x} v) → A_k e^{2πik·x} v = D̂_g (e^{2πik·x} v)` in
`L²(𝕋ᵈ; ℂ^K)`. -/
theorem tendsto_covStage_planeWave {U : ∀ n, TorusLinks d (n + 1) K}
    (hU : ∀ n, C.IsTransportLinks (n + 1) (U n)) (ϖ : ℝ) (Γ : Matrix (Fin K) (Fin K) ℂ)
    (k : Fin d → ℤ) (v : Fin K → ℂ) :
    Tendsto (fun n => embed d K (n + 1) (covStage C (n + 1) ϖ (U n) Γ
        (ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap
          (vecL2 (planeWave k v))))) atTop
      (𝓝 (vecL2 (mulVecCM (C.symbField k) (planeWave k v)))) := by
  set T := fun _ : ℕ => UnitAddTorus (Fin d)
  set Sg : ∀ n, UnitAddTorus (Fin d) → Matrix (Fin K) (Fin K) ℂ := fun n y =>
    covPlaneSymbol (mesh n) ϖ (C.sampled (n + 1)) (U n) Γ (phase k n) (index (n + 1) y)
  have hsym : USmall (X := T) (fun n y => Sg n y - C.symbField k (samplePt (index (n + 1) y))) :=
    (C.uSmall_covPlaneSymbol_sub hU ϖ Γ k).comp fun n y => index (n + 1) y
  have hA : USmall (X := T) (fun n y => C.symbField k (samplePt (index (n + 1) y)) -
      C.symbField k y) := uSmall_field_index (C.symbField k)
  have hSbdd : UBdd (X := T) Sg := (hsym.uBdd.add (uBdd_field (C.symbField k)
    fun n y => samplePt (index (n + 1) y))).congr fun n y => by abel
  refine tendsto_spinor fun a => ?_
  -- bounded and small scalar pieces
  have hSv : UBdd (X := T) (fun n y => (Sg n y *ᵥ v) a) :=
    hSbdd.of_norm_le ‖v‖ (Eventually.of_forall fun n y => norm_mulVec_apply_le _ v a)
  have hχ : UBdd (X := T) (fun n y => latticeChar (zcast (n + 1) k) (index (n + 1) y)) :=
    UBdd.of_bound 1 fun n y => (norm_latticeChar' _ _).le
  have he : UBdd (X := T) (fun n y => mFourier k y) :=
    UBdd.of_bound 1 fun n y => ((mFourier k).norm_coe_le_norm y).trans (mFourier_norm).le
  have T1 : USmall (X := T) (fun n y => (modeFactor (n + 1) k - 1) *
      (latticeChar (zcast (n + 1) k) (index (n + 1) y) * (Sg n y *ᵥ v) a)) := by
    refine USmall.mul_uBdd ?_ (hχ.mul hSv)
    have := (tendsto_modeFactor (d := d) k).sub_const 1
    rw [sub_self] at this
    exact USmall.of_tendsto this
  have T2 : USmall (X := T) (fun n y => (latticeChar (zcast (n + 1) k) (index (n + 1) y) -
      mFourier k y) * (Sg n y *ᵥ v) a) := by
    refine USmall.mul_uBdd ?_ hSv
    refine USmall.of_bound (b := fun n => 2 * π * (∑ i, |(k i : ℝ)|) / ((n + 1 : ℕ) : ℝ)) ?_
      (Eventually.of_forall fun n y => ?_)
    · have : Tendsto (fun n => (2 * π * ∑ i, |(k i : ℝ)|) * mesh n) atTop
          (𝓝 ((2 * π * ∑ i, |(k i : ℝ)|) * 0)) := tendsto_mesh.const_mul _
      rw [mul_zero] at this
      exact this.congr fun n => by rw [mesh, div_eq_mul_inv]
    · rw [← mFourier_samplePt, norm_sub_rev]
      exact mFourier_sub_sample_le k y
  have T3 : USmall (X := T) (fun n y => mFourier k y *
      (((Sg n y - C.symbField k (samplePt (index (n + 1) y))) *ᵥ v) a)) :=
    he.mul_uSmall (hsym.of_norm_le ‖v‖
      (Eventually.of_forall fun n y => norm_mulVec_apply_le _ v a))
  have T4 : USmall (X := T) (fun n y => mFourier k y *
      (((C.symbField k (samplePt (index (n + 1) y)) - C.symbField k y) *ᵥ v) a)) :=
    he.mul_uSmall (hA.of_norm_le ‖v‖ (Eventually.of_forall fun n y => norm_mulVec_apply_le _ v a))
  have hg := ((T1.add T2).add T3).add T4
  refine tendsto_of_forall_eventually_norm_sub_le fun ε hε => ?_
  filter_upwards [hg ε hε] with n hn
  have hv : vecL2 (planeWave k v) = modeVec k (WithLp.toLp 2 v) := (modeVec_eq_vecL2 k _).symm
  rw [hv, covStage_adjoint_modeVec, embed_apply, vecL2_apply]
  have hs : ((scale (n + 1) d : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (scale_pos (n := n + 1) (d := d)).ne'
  refine norm_L2_sub_le_of_forall (coeFn_pcEmbedding _)
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume _) hε.le fun y => ?_
  refine le_of_eq_of_le ?_ (hn y)
  congr 1
  rw [FlatTorusSpinAtlas.comp_apply]
  simp only [eucl, PiLp.smul_apply, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul,
    compCM, mulVecCM, planeWave, ContinuousMap.coe_mk, Matrix.mulVec_smul, Matrix.sub_mulVec,
    Pi.sub_apply, Sg]
  field_simp
  ring

end Coeffs

end A3L2

/-! ### Assembly: the covariant Wilson discretization of the periodic extension -/

section assembly

namespace Coeffs

variable (C : Coeffs d K)

/-- **The covariant Wilson discretization of the variable-coefficient periodic extension**
(`eq:supp-general-Wilson` with sampled coefficients `ĉ^j(x/m)`, exact transport links and
fixed `ϖ ≠ 0`), as a `LatticeDiscretization`: (A2) is `exists_uniform_garding` and (A3) is
`tendsto_covStage_planeWave`; nothing is assumed beyond the data of the periodic extension
(continuous Hermitian `ĉ^j` with continuous `∂_j ĉ^j`, continuous skew-Hermitian connection,
uniform ellipticity of `(ĉ^j(y), Γ_⊥)`, Hermitian `Γ_⊥` commuting with the connection) and the
links being exact inverse spin parallel transport. -/
def wilsonDiscretization (Γ : Matrix (Fin K) (Fin K) ℂ) (hΓ : Γᴴ = Γ)
    (hΓΩ : ∀ j y, Γ * C.Ω j y = C.Ω j y * Γ) (ϖ : ℝ) (hϖ : ϖ ≠ 0) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : 0 ≤ Lam) (hell : ∀ y, UniformlyElliptic (fun j => C.c j y) Γ lam Lam)
    (U : ∀ n, TorusLinks d (n + 1) K) (hU : ∀ n, C.IsTransportLinks (n + 1) (U n)) :
    C.LatticeDiscretization :=
  C.covariantDiscretizationOfGarding ϖ U Γ hΓ (fun n => C.comm_of_isTransportLinks (hU n) Γ hΓΩ)
    (C.exists_uniform_garding Γ hΓ ϖ hϖ hlam hLam hell).choose
    (C.exists_uniform_garding Γ hΓ ϖ hϖ hlam hLam hell).choose_spec.1
    (fun n u => (C.exists_uniform_garding Γ hΓ ϖ hϖ hlam hLam hell).choose_spec.2 n (U n) (hU n) u)
    (fun k v => C.tendsto_covStage_planeWave hU ϖ Γ k v)

theorem wilsonDiscretization_stage (Γ : Matrix (Fin K) (Fin K) ℂ) (hΓ : Γᴴ = Γ)
    (hΓΩ : ∀ j y, Γ * C.Ω j y = C.Ω j y * Γ) (ϖ : ℝ) (hϖ : ϖ ≠ 0) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : 0 ≤ Lam) (hell : ∀ y, UniformlyElliptic (fun j => C.c j y) Γ lam Lam)
    (U : ∀ n, TorusLinks d (n + 1) K) (hU : ∀ n, C.IsTransportLinks (n + 1) (U n)) (n : ℕ) :
    (C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).stage n =
      covStage C (n + 1) ϖ (U n) Γ := rfl

variable {c₀ : Fin d → Matrix (Fin K) (Fin K) ℂ} (hc₀ : ∀ j, (c₀ j)ᴴ = c₀ j)

/-- **`thm:supp-compact-spin-resolvent`, clause `eq:supp-local-norm-resolvent` and the
spectral-projection clause, on the fixed smooth periodic coordinate extension with variable
coefficients.**  Let `C` be the coefficients of the periodic extension (continuous Hermitian
`ĉ^j` differentiable along `e_j` with continuous `∂_j ĉ^j`, continuous skew-Hermitian `Ω_j`),
`Γ_⊥` Hermitian, commuting with the connection, with `(ĉ^j(y), Γ_⊥)` uniformly elliptic doubled
Clifford data (`ĉ^j ĉ^k + ĉ^k ĉ^j = 2 g^{jk}(y)`, `λ|ξ|² ≤ g(y)(ξ,ξ) ≤ Λ|ξ|²`), `ϖ ≠ 0`, and
let `U` be exact inverse spin parallel transport links.  Let `D_h = D̃^W_{g,h}` be the covariant
Wilson operator `covStage` at `h = 1/(n+1)`, `𝒥⁰_h = embed` the piecewise-constant isometry.  Then:
1. every `D_h` is self-adjoint, and `stageRes` is its resolvent;
2. there is a self-adjoint realisation `D̂_g` of `-(i/2) Σ_j (ĉ^j ∇_j + ∇_j ĉ^j)` with domain
   `H¹`, acting as `C.op` there;
3. `‖𝒥⁰_h (D_h - z)⁻¹ (𝒥⁰_h)^* - (D̂_g - z)⁻¹‖ → 0` for every non-real `z`;
4. for `a < b` not eigenvalues of `D̂_g`, `‖𝒥⁰_h 1_{(a,b)}(D_h) (𝒥⁰_h)^* - 1_{(a,b)}(D̂_g)‖ → 0`.
-/
theorem supp_local_norm_resolvent (Γ : Matrix (Fin K) (Fin K) ℂ) (hΓ : Γᴴ = Γ)
    (hΓΩ : ∀ j y, Γ * C.Ω j y = C.Ω j y * Γ) (ϖ : ℝ) (hϖ : ϖ ≠ 0) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : 0 ≤ Lam) (hell : ∀ y, UniformlyElliptic (fun j => C.c j y) Γ lam Lam)
    (U : ∀ n, TorusLinks d (n + 1) K) (hU : ∀ n, C.IsTransportLinks (n + 1) (U n)) :
    (∀ n, IsSelfAdjoint (covStage C (n + 1) ϖ (U n) Γ)) ∧
    (∀ n {z : ℂ} (hz : z.im ≠ 0) g,
      covStage C (n + 1) ϖ (U n) Γ
          (((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).toStable hc₀).stageRes n
            hz g) -
        z • ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).toStable hc₀).stageRes n
            hz g = g) ∧
    ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).op.domain =
      LinearMap.range (sobolev hc₀).toLinearMap ∧
    IsSelfAdjoint ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).op ∧
    (∀ a : ℓ²(Idx d K, ℂ),
      ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).op
        ⟨sobolev hc₀ a, ⟨a, rfl⟩⟩ = C.op hc₀ a) ∧
    (∀ {z : ℂ} (hz : z.im ≠ 0), Tendsto (fun n =>
      ‖(embed d K (n + 1)).toContinuousLinearMap ∘L
        ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).toStable hc₀).stageRes n hz ∘L
        ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap -
        ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).resolvent z hz‖)
      atTop (𝓝 0)) ∧
    (∀ {a b : ℝ}, a < b →
      ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).opEigenspace
        (a : ℂ) = ⊥ →
      ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).opEigenspace
        (b : ℂ) = ⊥ →
      Tendsto (fun n =>
        ‖((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).toStable
            hc₀).toAtlas.embeddedSpectralProjection a b n -
          ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).spectralProjection
            a b‖) atTop (𝓝 0)) := by
  set L := C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU
  refine ⟨fun n => L.stage_selfAdjoint n, fun n z hz g => (L.toStable hc₀).stage_stageRes n hz g,
    L.dirac_domain hc₀, L.isSelfAdjoint_dirac hc₀, L.dirac_sobolev hc₀,
    fun hz => L.tendsto_norm_resolvent hc₀ hz,
    fun hab ha hb => L.tendsto_norm_spectralProjection hc₀ hab ha hb⟩

end Coeffs

end assembly

/-! ### Non-vacuity: a genuinely variable doubled coefficient on `𝕋¹` with a connection -/

section nonvacuity

open scoped Matrix.Norms.Operator

/-- The constant skew-Hermitian connection `Ω = i I` on `ℂ²`. -/
def iConn : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- **A non-constant doubled Clifford coefficient with a non-trivial connection** on `𝕋¹`:
`ĉ¹(x) = (3 + 2 cos 2πx) σ₁` on `ℂ²` (inverse metric `g(x) = (3 + 2 cos 2πx)² ∈ [1, 25]`),
`Γ_⊥ = σ₂`, connection `Ω = i I`. -/
def cosDoubledCoeffs : Coeffs 1 2 where
  c _ := cosField • ContinuousMap.const _ σ₁
  dc _ := cosFieldDeriv • ContinuousMap.const _ σ₁
  Ω _ := ContinuousMap.const _ iConn
  c_herm _ x := by
    simp only [ContinuousMap.smul_apply', ContinuousMap.const_apply, conjTranspose_smul,
      σ₁_conjTranspose]
    rw [Complex.star_def, conj_cosField]
  Ω_skew _ _ := by
    simp only [ContinuousMap.const_apply, iConn, conjTranspose_smul, conjTranspose_one,
      Complex.star_def, Complex.conj_I, neg_smul]
  hasDerivAt_c j y v := by
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    have := (hasDerivAt_cosField y).smul_const (σ₁ *ᵥ v)
    simpa [ContinuousMap.smul_apply', Matrix.smul_mulVec] using this

theorem cosDoubledCoeffs_c_apply (j : Fin 1) (y : UnitAddTorus (Fin 1)) :
    cosDoubledCoeffs.c j y = cosField y • σ₁ := rfl

theorem cosField_eq_re (y : UnitAddTorus (Fin 1)) : cosField y = ((cosField y).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (conj_cosField y)).symm

theorem one_le_re_cosField (y : UnitAddTorus (Fin 1)) :
    1 ≤ (cosField y).re ∧ (cosField y).re ≤ 5 := by
  have he : ‖mFourier freqOne y‖ ≤ 1 :=
    ((mFourier freqOne).norm_coe_le_norm y).trans (mFourier_norm).le
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (mFourier freqOne y)).trans he))
  have e : (cosField y).re = 3 + 2 * (mFourier freqOne y).re := by
    simp only [cosField, ContinuousMap.add_apply, ContinuousMap.const_apply, Complex.add_re]
    rw [mFourier_neg, Complex.conj_re]
    norm_num
    ring
  rw [e]
  constructor <;> linarith [hre.1, hre.2]

/-- The coefficient is genuinely variable: `ĉ¹(0) = 5 σ₁`. -/
theorem cosDoubledCoeffs_c_zero : cosDoubledCoeffs.c 0 0 = (5 : ℂ) • σ₁ := by
  rw [cosDoubledCoeffs_c_apply]
  congr 1
  have := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℂ => A 0 0) cosCoeffs_c_zero
  simpa [cosCoeffs] using this

/-- The doubled data `(ĉ¹(y), σ₂)` are uniformly elliptic with `λ = 1`, `Λ = 25`. -/
theorem cosDoubledCoeffs_elliptic (y : UnitAddTorus (Fin 1)) :
    UniformlyElliptic (fun j => cosDoubledCoeffs.c j y) σ₂ 1 25 := by
  set s := (cosField y).re with hs
  have hsy : cosField y = (s : ℂ) := cosField_eq_re y
  obtain ⟨h1, h5⟩ := one_le_re_cosField y
  refine ⟨fun j => cosDoubledCoeffs.c_herm j y, fun _ _ => s ^ 2, ⟨fun j k => ?_, fun j => ?_,
    σ₂_mul_σ₂⟩, fun ξ => ?_, fun ξ => ?_⟩
  · simp only [cosDoubledCoeffs_c_apply, hsy, smul_mul_smul_comm, σ₁_mul_σ₁, ← add_smul]
    congr 1
    push_cast
    ring
  · simp only [cosDoubledCoeffs_c_apply, mul_smul_comm, smul_mul_assoc, ← smul_add,
      σ₂_mul_σ₁_add, smul_zero]
  · rw [← hs] at h1
    have hs1 : 1 ≤ s ^ 2 := by nlinarith
    simp only [Fin.sum_univ_one, one_mul]
    nlinarith [mul_le_mul_of_nonneg_right hs1 (sq_nonneg (ξ 0))]
  · rw [← hs] at h1 h5
    have hs25 : s ^ 2 ≤ 25 := by nlinarith
    simp only [Fin.sum_univ_one]
    nlinarith [mul_le_mul_of_nonneg_right hs25 (sq_nonneg (ξ 0))]

theorem σ₂_comm_iConn (j : Fin 1) (y : UnitAddTorus (Fin 1)) :
    σ₂ * cosDoubledCoeffs.Ω j y = cosDoubledCoeffs.Ω j y * σ₂ := by
  simp only [cosDoubledCoeffs, ContinuousMap.const_apply, iConn, mul_smul_comm, smul_mul_assoc,
    Matrix.mul_one, Matrix.one_mul]

/-- The exact transport links of the constant connection: `U = exp(h i I)` (non-trivial). -/
def cosDoubledLinks (n : ℕ) : TorusLinks 1 (n + 1) 2 :=
  fun _ _ => NormedSpace.exp ((((n + 1 : ℕ) : ℝ)⁻¹) • iConn)

theorem cosDoubledCoeffs_isTransportLinks (n : ℕ) :
    cosDoubledCoeffs.IsTransportLinks (n + 1) (cosDoubledLinks n) := by
  intro j x
  refine ⟨fun t => NormedSpace.exp (t • iConn), by simp, fun t => ?_, rfl⟩
  exact hasDerivAt_exp_smul_const iConn t

/-- **Non-vacuity of `supp_local_norm_resolvent`** for the genuinely variable doubled coefficient
`(3 + 2 cos 2πx) σ₁` on `𝕋¹`, `Γ_⊥ = σ₂`, `ϖ = 1`, connection `i I` with its exact transport
links `exp(i h)` (Fourier frame `c₀ = 0`): the full conclusion holds. -/
example := cosDoubledCoeffs.supp_local_norm_resolvent (c₀ := fun _ => 0) (fun _ => by simp) σ₂
  σ₂_conjTranspose σ₂_comm_iConn 1 one_ne_zero one_pos (by norm_num)
  cosDoubledCoeffs_elliptic cosDoubledLinks cosDoubledCoeffs_isTransportLinks

/-- The resolvent clause at `z = i` for the variable example. -/
theorem cosDoubled_tendsto_norm_resolvent :
    Tendsto (fun n => ‖(embed 1 2 (n + 1)).toContinuousLinearMap ∘L
        ((cosDoubledCoeffs.wilsonDiscretization σ₂ σ₂_conjTranspose σ₂_comm_iConn 1 one_ne_zero
          one_pos (by norm_num) cosDoubledCoeffs_elliptic cosDoubledLinks
          cosDoubledCoeffs_isTransportLinks).toStable
          (c₀ := fun _ => 0) (fun _ => by simp)).stageRes n (z := Complex.I) (by simp) ∘L
        ContinuousLinearMap.adjoint (embed 1 2 (n + 1)).toContinuousLinearMap -
        ((cosDoubledCoeffs.wilsonDiscretization σ₂ σ₂_conjTranspose σ₂_comm_iConn 1 one_ne_zero
          one_pos (by norm_num) cosDoubledCoeffs_elliptic cosDoubledLinks
          cosDoubledCoeffs_isTransportLinks).dirac
          (c₀ := fun _ => 0) (fun _ => by simp)).resolvent Complex.I (by simp)‖) atTop (𝓝 0) :=
  (cosDoubledCoeffs.supp_local_norm_resolvent (c₀ := fun _ => 0) (fun _ => by simp) σ₂
    σ₂_conjTranspose σ₂_comm_iConn 1 one_ne_zero one_pos (by norm_num)
    cosDoubledCoeffs_elliptic cosDoubledLinks
    cosDoubledCoeffs_isTransportLinks).2.2.2.2.2.1 (by simp)

end nonvacuity

/-! ### The fixed doubled convention from undoubled data -/

section doubled

open scoped Matrix.Norms.Operator

variable {M : ℕ}

theorem dbl_apply (A : Matrix (Fin M) (Fin M) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ)
    (i j : Fin (M * 2)) :
    dbl A P i j = A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
      P (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := rfl

theorem dbl_neg_left (A : Matrix (Fin M) (Fin M) ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    dbl (-A) P = -dbl A P := by
  ext i j; simp [dbl_apply]

/-- `y ↦ F(y) ⊗ P` as a continuous matrix field. -/
def dblCM (F : C(UnitAddTorus (Fin d), Matrix (Fin M) (Fin M) ℂ)) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    C(UnitAddTorus (Fin d), Matrix (Fin (M * 2)) (Fin (M * 2)) ℂ) :=
  ⟨fun y => dbl (F y) P, continuous_pi fun i => continuous_pi fun j => by
    simp only [dbl_apply]
    exact ((continuous_apply _).comp ((continuous_apply _).comp F.continuous)).mul
      continuous_const⟩

theorem dblCM_apply (F : C(UnitAddTorus (Fin d), Matrix (Fin M) (Fin M) ℂ))
    (P : Matrix (Fin 2) (Fin 2) ℂ) (y : UnitAddTorus (Fin d)) : dblCM F P y = dbl (F y) P := rfl

/-- **The doubled coefficients of `eq:supp-doubled-clifford`**: from undoubled periodic
coefficients `c^j` (on `ℂ^M`) and connection `Ω_j`, the doubled data `ĉ^j = c^j ⊗ σ₁`,
`∂_j ĉ^j = ∂_j c^j ⊗ σ₁`, `Ω̂_j = Ω_j ⊗ I` on `ℂ^M ⊗ ℂ²`. -/
def Coeffs.doubled (C₀ : Coeffs d M) : Coeffs d (M * 2) where
  c j := dblCM (C₀.c j) σ₁
  dc j := dblCM (C₀.dc j) σ₁
  Ω j := dblCM (C₀.Ω j) 1
  c_herm j x := by rw [dblCM_apply, dbl_conjTranspose, C₀.c_herm, σ₁_conjTranspose]
  Ω_skew j x := by
    rw [dblCM_apply, dbl_conjTranspose, C₀.Ω_skew, conjTranspose_one, dbl_neg_left]
  hasDerivAt_c j y v := by
    rw [hasDerivAt_pi]
    intro a
    simp only [dblCM_apply, Matrix.mulVec, dotProduct, dbl_apply]
    exact HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
      ((C₀.hasDerivAt_entry j y _ _).mul_const _).mul_const _

/-- The doubled normal generator `Γ_⊥ = I ⊗ σ₂` is Hermitian. -/
theorem doubledNormal_herm : (dbl (1 : Matrix (Fin M) (Fin M) ℂ) σ₂)ᴴ = dbl 1 σ₂ := by
  rw [dbl_conjTranspose, Matrix.conjTranspose_one, σ₂_conjTranspose]

/-- `Γ_⊥ = I ⊗ σ₂` commutes with the doubled connection `Ω ⊗ I`. -/
theorem Coeffs.doubled_normal_comm (C₀ : Coeffs d M) (j : Fin d) (y : UnitAddTorus (Fin d)) :
    dbl (1 : Matrix (Fin M) (Fin M) ℂ) σ₂ * C₀.doubled.Ω j y =
      C₀.doubled.Ω j y * dbl 1 σ₂ := by
  change dbl 1 σ₂ * dbl (C₀.Ω j y) 1 = dbl (C₀.Ω j y) 1 * dbl 1 σ₂
  rw [dbl_mul, dbl_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]

/-- **Uniform ellipticity of the doubled data from the paper's undoubled data**: if
`c^j(y) c^k(y) + c^k(y) c^j(y) = 2 g^{jk}(y) I` (`eq:supp-clifford-coeff`) with
`λ|ξ|² ≤ g(y)(ξ,ξ) ≤ Λ|ξ|²` at every point, then `(ĉ^j(y), I ⊗ σ₂)` is uniformly elliptic. -/
theorem Coeffs.doubled_uniformlyElliptic (C₀ : Coeffs d M)
    (g : UnitAddTorus (Fin d) → Matrix (Fin d) (Fin d) ℝ) {lam Lam : ℝ}
    (hcl : ∀ y j k, C₀.c j y * C₀.c k y + C₀.c k y * C₀.c j y =
      ((2 * g y j k : ℝ) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))
    (hlow : ∀ y (ξ : Fin d → ℝ), lam * ∑ j, ξ j ^ 2 ≤ ∑ j, ∑ k, g y j k * (ξ j * ξ k))
    (hup : ∀ y (ξ : Fin d → ℝ), ∑ j, ∑ k, g y j k * (ξ j * ξ k) ≤ Lam * ∑ j, ξ j ^ 2)
    (y : UnitAddTorus (Fin d)) :
    UniformlyElliptic (fun j => C₀.doubled.c j y) (dbl 1 σ₂) lam Lam :=
  ⟨fun j => C₀.doubled.c_herm j y, g y, doubled_cliffordData (fun j => C₀.c j y) (g y) (hcl y),
    hlow y, hup y⟩

/-- **The grading clause on the periodic extension** (`thm:supp-general-Wilson-ellipticity`, "the
fixed doubled Clifford convention supplies the grading"): `γ̂ = I ⊗ σ₃` anticommutes with the
covariant Wilson operator of the doubled data with exact transport links. -/
theorem Coeffs.doubled_grading (C₀ : Coeffs d M) {m : ℕ} [NeZero m]
    {U : TorusLinks d m (M * 2)} (hU : C₀.doubled.IsTransportLinks m U) (h ϖ : ℝ)
    (u : TorusSection d m (M * 2)) :
    covVarWilson h ϖ (C₀.doubled.sampled m) U (dbl 1 σ₂) (matMul (dbl 1 σ₃) u) =
      -matMul (dbl 1 σ₃) (covVarWilson h ϖ (C₀.doubled.sampled m) U (dbl 1 σ₂) u) := by
  have hγΩ : ∀ j y, dbl (1 : Matrix (Fin M) (Fin M) ℂ) σ₃ * C₀.doubled.Ω j y =
      C₀.doubled.Ω j y * dbl 1 σ₃ := by
    intro j y
    change dbl 1 σ₃ * dbl (C₀.Ω j y) 1 = dbl (C₀.Ω j y) 1 * dbl 1 σ₃
    rw [dbl_mul, dbl_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]
  apply covVarWilson_matMul
  · rw [dbl_conjTranspose, Matrix.conjTranspose_one, σ₃_conjTranspose]
  · intro x j
    change dbl (C₀.c j _) σ₁ * dbl 1 σ₃ = -(dbl 1 σ₃ * dbl (C₀.c j _) σ₁)
    rw [dbl_mul, dbl_mul, Matrix.mul_one, Matrix.one_mul, σ₁_mul_σ₃, dbl_neg_right]
  · rw [dbl_mul, dbl_mul, σ₂_mul_σ₃, dbl_neg_right]
  · exact C₀.doubled.comm_of_isTransportLinks hU _ hγΩ

/-- **`eq:supp-local-norm-resolvent` in the paper's notation** (undoubled data, fixed doubled
convention): for undoubled periodic coefficients `C₀` with `c^j c^k + c^k c^j = 2 g^{jk}(y)` and
uniformly elliptic `g`, `ϖ ≠ 0` and exact transport links of `Ω ⊗ I`, the covariant Wilson
operators of `ĉ^j = c^j ⊗ σ₁`, `Γ_⊥ = I ⊗ σ₂` converge in norm-resolvent sense to the
self-adjoint `D̂_g` (domain `H¹`), with spectral projections. -/
theorem Coeffs.supp_local_norm_resolvent_doubled (C₀ : Coeffs d M)
    (g : UnitAddTorus (Fin d) → Matrix (Fin d) (Fin d) ℝ) {lam Lam : ℝ}
    (hcl : ∀ y j k, C₀.c j y * C₀.c k y + C₀.c k y * C₀.c j y =
      ((2 * g y j k : ℝ) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))
    (hlow : ∀ y (ξ : Fin d → ℝ), lam * ∑ j, ξ j ^ 2 ≤ ∑ j, ∑ k, g y j k * (ξ j * ξ k))
    (hup : ∀ y (ξ : Fin d → ℝ), ∑ j, ∑ k, g y j k * (ξ j * ξ k) ≤ Lam * ∑ j, ξ j ^ 2)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam) (ϖ : ℝ) (hϖ : ϖ ≠ 0)
    (U : ∀ n, TorusLinks d (n + 1) (M * 2)) (hU : ∀ n, C₀.doubled.IsTransportLinks (n + 1) (U n))
    {c₀ : Fin d → Matrix (Fin (M * 2)) (Fin (M * 2)) ℂ} (hc₀ : ∀ j, (c₀ j)ᴴ = c₀ j) :
    ((C₀.doubled.wilsonDiscretization (dbl 1 σ₂) doubledNormal_herm C₀.doubled_normal_comm ϖ hϖ
        hlam hLam (C₀.doubled_uniformlyElliptic g hcl hlow hup) U hU).dirac hc₀).op.domain =
        LinearMap.range (sobolev hc₀).toLinearMap ∧
    IsSelfAdjoint ((C₀.doubled.wilsonDiscretization (dbl 1 σ₂) doubledNormal_herm
        C₀.doubled_normal_comm ϖ hϖ hlam hLam (C₀.doubled_uniformlyElliptic g hcl hlow hup) U
        hU).dirac hc₀).op ∧
    (∀ {z : ℂ} (hz : z.im ≠ 0), Tendsto (fun n =>
      ‖(embed d (M * 2) (n + 1)).toContinuousLinearMap ∘L
        ((C₀.doubled.wilsonDiscretization (dbl 1 σ₂) doubledNormal_herm C₀.doubled_normal_comm ϖ
          hϖ hlam hLam (C₀.doubled_uniformlyElliptic g hcl hlow hup) U hU).toStable
            hc₀).stageRes n hz ∘L
        ContinuousLinearMap.adjoint (embed d (M * 2) (n + 1)).toContinuousLinearMap -
        ((C₀.doubled.wilsonDiscretization (dbl 1 σ₂) doubledNormal_herm C₀.doubled_normal_comm ϖ
          hϖ hlam hLam (C₀.doubled_uniformlyElliptic g hcl hlow hup) U hU).dirac hc₀).resolvent
            z hz‖) atTop (𝓝 0)) ∧
    (∀ {a b : ℝ}, a < b →
      ((C₀.doubled.wilsonDiscretization (dbl 1 σ₂) doubledNormal_herm C₀.doubled_normal_comm ϖ
          hϖ hlam hLam (C₀.doubled_uniformlyElliptic g hcl hlow hup) U hU).dirac hc₀).opEigenspace
        (a : ℂ) = ⊥ →
      ((C₀.doubled.wilsonDiscretization (dbl 1 σ₂) doubledNormal_herm C₀.doubled_normal_comm ϖ
          hϖ hlam hLam (C₀.doubled_uniformlyElliptic g hcl hlow hup) U hU).dirac hc₀).opEigenspace
        (b : ℂ) = ⊥ →
      Tendsto (fun n =>
        ‖((C₀.doubled.wilsonDiscretization (dbl 1 σ₂) doubledNormal_herm C₀.doubled_normal_comm ϖ
            hϖ hlam hLam (C₀.doubled_uniformlyElliptic g hcl hlow hup) U hU).toStable
            hc₀).toAtlas.embeddedSpectralProjection a b n -
          ((C₀.doubled.wilsonDiscretization (dbl 1 σ₂) doubledNormal_herm C₀.doubled_normal_comm
            ϖ hϖ hlam hLam (C₀.doubled_uniformlyElliptic g hcl hlow hup) U hU).dirac
              hc₀).spectralProjection a b‖) atTop (𝓝 0)) := by
  obtain ⟨-, -, hdom, hsa, -, hres, hspec⟩ := C₀.doubled.supp_local_norm_resolvent hc₀
    (dbl 1 σ₂) doubledNormal_herm C₀.doubled_normal_comm ϖ hϖ hlam hLam
    (C₀.doubled_uniformlyElliptic g hcl hlow hup) U hU
  exact ⟨hdom, hsa, hres, hspec⟩

end doubled

/-! ### Non-vacuity of the undoubled form -/

section nonvacuityDoubled

open scoped Matrix.Norms.Operator

/-- The undoubled variable coefficient `c¹(x) = (3 + 2 cos 2πx)` on `ℂ¹` satisfies the Clifford
relation with `g(x) = (3 + 2 cos 2πx)²`. -/
theorem cosCoeffs_clifford (y : UnitAddTorus (Fin 1)) (j k : Fin 1) :
    cosCoeffs.c j y * cosCoeffs.c k y + cosCoeffs.c k y * cosCoeffs.c j y =
      ((2 * (fun _ _ => (cosField y).re ^ 2 : Matrix (Fin 1) (Fin 1) ℝ) j k : ℝ) : ℂ) •
        (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  set s := (cosField y).re with hs
  have hsy : cosField y = (s : ℂ) := cosField_eq_re y
  change (cosField y • (1 : Matrix (Fin 1) (Fin 1) ℂ)) * (cosField y • 1) +
      (cosField y • 1) * (cosField y • 1) = _
  rw [hsy, smul_mul_smul_comm, Matrix.one_mul, ← add_smul]
  congr 1
  push_cast
  ring

theorem cosCoeffs_doubled_isTransportLinks (n : ℕ) :
    cosCoeffs.doubled.IsTransportLinks (n + 1) (fun _ _ => 1) := by
  intro j x
  refine ⟨fun _ => 1, rfl, fun t => ?_, rfl⟩
  have : (1 : Matrix (Fin (1 * 2)) (Fin (1 * 2)) ℂ) *
      cosCoeffs.doubled.Ω j (samplePt x + lineVec j t) = 0 := by
    change 1 * dbl (cosCoeffs.Ω j _) 1 = 0
    ext a b
    simp [dbl_apply, cosCoeffs]
  rw [this]
  exact hasDerivAt_const t _

/-- **Non-vacuity of `supp_local_norm_resolvent_doubled`** in the paper's undoubled notation:
`c¹(x) = 3 + 2 cos 2πx` on `ℂ¹` (genuinely variable), `g(x) = c¹(x)² ∈ [1, 25]`, doubled to
`ĉ¹ = c¹ ⊗ σ₁`, `Γ_⊥ = 1 ⊗ σ₂`, `ϖ = 1`. -/
example := cosCoeffs.supp_local_norm_resolvent_doubled
  (fun y => fun _ _ => (cosField y).re ^ 2) (lam := 1) (Lam := 25) cosCoeffs_clifford
  (fun y ξ => by
    obtain ⟨h1, -⟩ := one_le_re_cosField y
    have hs1 : 1 ≤ (cosField y).re ^ 2 := by nlinarith
    simp only [Fin.sum_univ_one, one_mul]
    nlinarith [mul_le_mul_of_nonneg_right hs1 (sq_nonneg (ξ 0))])
  (fun y ξ => by
    obtain ⟨h1, h5⟩ := one_le_re_cosField y
    have hs25 : (cosField y).re ^ 2 ≤ 25 := by nlinarith
    simp only [Fin.sum_univ_one]
    nlinarith [mul_le_mul_of_nonneg_right hs25 (sq_nonneg (ξ 0))])
  one_pos (by norm_num) 1 one_ne_zero (fun _ _ _ => 1) cosCoeffs_doubled_isTransportLinks
  (c₀ := fun _ => 0) (fun _ => by simp)

end nonvacuityDoubled

end RenewalGeometry.VariableTorusDirac
