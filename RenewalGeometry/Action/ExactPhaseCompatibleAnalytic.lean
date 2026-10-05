/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactPhaseCompatibleConnection
import RenewalGeometry.Analysis.LinkRemainderAnalytic

/-!
# Analyticity of the explicit phase-compatible finite action
  (clause (i) of `thm:supp-exact-action-provenance`; `eq:supp-exact-PiSigma`,
  `eq:supp-exact-full-palatini`, `eq:supp-exact-link-curvatures`, `eq:supp-exact-completed-action`,
  `eq:supp-exact-phase-action`; emergent-spacetime manuscript)

Clause (i): the action is an explicit analytic finite action in the coframe, temporal connection
and spatial link variables.

* Coframe arrays: `analyticAt_palCoeff`, `analyticAt_piArr`, `analyticAt_sigmaArr`,
  `analyticAt_matrixDet`, `analyticAt_detR` (polynomials in the entries of `e`).
* Link building blocks: `analyticAt_remE_comp` (entire), `analyticAt_plaquette_comp`,
  `analyticAt_remB_comp` (on the retained branch `‖U_□ - 1‖ < 1`).
* The retained branch `PlaqBranch h A` (every plaquette in the principal chart) is open
  (`isOpen_plaqBranch`, `isOpen_completedBranch`, `isOpen_phaseBranch`) and contains the flat
  connection (`plaqBranch_zero`).
* **`analyticAt_gridPair_completedDensity`**: for `h ≠ 0` the map
  `(e, A₀, A, Ȧ) ↦ ⟨completed density, 1⟩_h` is jointly analytic on the retained branch
  (`analyticOnNhd_gridPair_completedDensity`).  The literal density contains `D exp` (through
  `linkVel`) and `𝒥_{hA}` (through `𝒦_h`); these cancel exactly by `completedDensity_eq`, so the
  proof runs on the normal form, which involves only `det`, `Π`, `Σ`, `exp` and the Mercator
  logarithm.
* **`analyticAt_phaseLagr`**: the phase-compatible Lagrangian `(e, ∂_tΠ, A) ↦ L°` in Lorentz
  coordinates is jointly analytic on the retained branch (`analyticOnNhd_phaseLagr`).
* Non-vacuity at flat data: `analyticAt_gridPair_completedDensity_flat`,
  `analyticAt_phaseLagr_flat`.

Technical note: under the local `ℓ∞`-operator-norm instances on `M4`, continuous linear maps are
only built inside generic lemmas (`analyticAt_linear_of_bound`, `analyticAt_pi_apply`), and
matrix-valued analyticity is reduced to entries (`analyticAt_of_entries`).
-/

open Finset NormedSpace

noncomputable section

namespace RenewalGeometry.ExactPhaseAction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open LogBCH PalatiniEinsteinAlgebra

/-! ### Generic analytic helpers -/

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A linear map with an explicit norm bound is analytic (generic over normed spaces, so that it
applies to `M4` with its `ℓ∞`-operator norm without naming a continuous-linear-map type on `M4`). -/
theorem analyticAt_linear_of_bound (L : E →ₗ[ℝ] F) (C : ℝ) (hL : ∀ x, ‖L x‖ ≤ C * ‖x‖)
    (x : E) : AnalyticAt ℝ (fun y => L y) x :=
  (L.mkContinuous C hL).analyticAt x

/-- Evaluation of an analytic family of finite tuples at a fixed index is analytic. -/
theorem analyticAt_pi_apply {ι : Type*} [Fintype ι] {f : E → ι → F} {p : E}
    (hf : AnalyticAt ℝ f p) (i : ι) : AnalyticAt ℝ (fun q => f q i) p :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i).analyticAt (f p)).comp hf

end Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E}

/-! ### Matrix-level analyticity: entries, determinant, coframe arrays -/

/-- The matrix entry `X ↦ X a b` as a linear functional on `M4`. -/
def entryLin (a b : Fin 4) : M4 →ₗ[ℝ] ℝ where
  toFun X := X a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Matrix entries are analytic (`|X a b| ≤ ‖X‖`). -/
theorem analyticAt_entry (a b : Fin 4) (X : M4) : AnalyticAt ℝ (fun Y : M4 => Y a b) X :=
  analyticAt_linear_of_bound (entryLin a b) 1
    (fun Y => by rw [Real.norm_eq_abs, one_mul]; exact norm_entry_le Y a b) X

/-- Entries of an analytic matrix-valued map are analytic. -/
theorem analyticAt_entry_comp {f : E → M4} (hf : AnalyticAt ℝ f p) (a b : Fin 4) :
    AnalyticAt ℝ (fun q => f q a b) p :=
  (analyticAt_entry a b (f p)).comp hf

/-- A matrix-valued map is analytic as soon as all of its entries are
(`f = Σ_{a,b} f_{ab} E_{ab}`). -/
theorem analyticAt_of_entries {f : E → M4} (h : ∀ a b, AnalyticAt ℝ (fun q => f q a b) p) :
    AnalyticAt ℝ f p := by
  have hf : f = fun q => ∑ a, ∑ b, f q a b • Matrix.single a b (1 : ℝ) := by
    funext q
    conv_lhs => rw [Matrix.matrix_eq_sum_single (f q)]
    simp [Matrix.smul_single]
  rw [hf]
  refine Finset.analyticAt_fun_sum _ fun a _ => Finset.analyticAt_fun_sum _ fun b _ => ?_
  exact (h a b).smul analyticAt_const

/-- `det` is a polynomial in the entries, hence analytic on `M4`. -/
theorem analyticAt_matrixDet (X : M4) : AnalyticAt ℝ (fun Y : M4 => Y.det) X := by
  simp only [Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul ?_
  exact Finset.analyticAt_fun_prod _ fun i _ => analyticAt_entry _ _ X


/-- Transposition preserves analyticity. -/
theorem analyticAt_transpose_comp {f : E → M4} (hf : AnalyticAt ℝ f p) :
    AnalyticAt ℝ (fun q => Matrix.transpose (f q)) p :=
  analyticAt_of_entries fun a b => by
    simpa only [Matrix.transpose_apply] using analyticAt_entry_comp hf b a

/-- Multiplication by a fixed real scalar preserves analyticity. -/
theorem analyticAt_smul_comp (h : ℝ) {f : E → M4} (hf : AnalyticAt ℝ f p) :
    AnalyticAt ℝ (fun q => h • f q) p :=
  hf.const_smul (c := h)

/-- The coefficient bivector `W_{ρσ}(e)` is quadratic in `e`, hence analytic. -/
theorem analyticAt_palCoeff (ρ σ : Fin 4) (X : M4) :
    AnalyticAt ℝ (fun e : M4 => palCoeff e ρ σ) X := by
  refine analyticAt_of_entries fun K L => ?_
  simp only [palCoeff, Matrix.of_apply]
  refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun μ _ =>
    Finset.analyticAt_fun_sum _ fun ν _ => analyticAt_const.mul
      (Finset.analyticAt_fun_sum _ fun I _ => Finset.analyticAt_fun_sum _ fun J _ => ?_))
  exact (analyticAt_const.mul (analyticAt_entry _ _ X)).mul (analyticAt_entry _ _ X)

/-- **`Π_i(e) = χ η W_{0i}(e)ᵀ` is analytic in the coframe** (`eq:supp-exact-PiSigma`). -/
theorem analyticAt_piArr (χ : ℝ) (i : Fin 3) (X : M4) :
    AnalyticAt ℝ (fun e : M4 => piArr χ e i) X := by
  unfold piArr dualCoeff
  exact analyticAt_smul_comp χ
    (analyticAt_const.mul (analyticAt_transpose_comp (analyticAt_palCoeff 0 i.succ X)))

/-- **`Σ_ij(e) = χ η W_{ij}(e)ᵀ` is analytic in the coframe** (`eq:supp-exact-PiSigma`). -/
theorem analyticAt_sigmaArr (χ : ℝ) (i j : Fin 3) (X : M4) :
    AnalyticAt ℝ (fun e : M4 => sigmaArr χ e i j) X := by
  unfold sigmaArr dualCoeff
  exact analyticAt_smul_comp χ (analyticAt_const.mul
    (analyticAt_transpose_comp (analyticAt_palCoeff i.succ j.succ X)))

/-- The trace of an analytic matrix-valued map is analytic. -/
theorem analyticAt_trace_comp {f : E → M4} (hf : AnalyticAt ℝ f p) :
    AnalyticAt ℝ (fun q => Matrix.trace (f q)) p := by
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.analyticAt_fun_sum _ fun a _ => analyticAt_entry_comp hf a a

/-- The invariant pairing `b(f, g) = tr(f g)` of analytic maps is analytic. -/
theorem analyticAt_pairing_comp {f g : E → M4} (hf : AnalyticAt ℝ f p) (hg : AnalyticAt ℝ g p) :
    AnalyticAt ℝ (fun q => pairing (f q) (g q)) p :=
  analyticAt_trace_comp (hf.mul hg)

/-- The matrix exponential of an analytic map is analytic. -/
theorem analyticAt_exp_comp {f : E → M4} (hf : AnalyticAt ℝ f p) :
    AnalyticAt ℝ (fun q => exp (f q)) p :=
  (exp_analytic (𝕂 := ℝ) (f p)).comp hf

/-- The determinant of an analytic matrix-valued map is analytic. -/
theorem analyticAt_det_comp {f : E → M4} (hf : AnalyticAt ℝ f p) :
    AnalyticAt ℝ (fun q => (f q).det) p :=
  (analyticAt_matrixDet (f p)).comp hf

/-- The bracket `[f, g]` of analytic maps is analytic. -/
theorem analyticAt_bracket_comp {f g : E → M4} (hf : AnalyticAt ℝ f p) (hg : AnalyticAt ℝ g p) :
    AnalyticAt ℝ (fun q => bracket (f q) (g q)) p :=
  (hf.mul hg).sub (hg.mul hf)

/-- Explicit form of the oriented plaquette product `U_i U_{j,+i} U_{i,+j}⁻¹ U_j⁻¹`. -/
theorem expProd_plaqList (h : ℝ) (a b c d : M4) :
    expProd (plaqList h a b c d) =
      exp (h • a) * (exp (h • b) * (exp (-(h • c)) * exp (-(h • d)))) := by
  simp [plaqList]; rfl

/-- The oriented plaquette product is analytic in its four link variables. -/
theorem analyticAt_expProd_plaqList (h : ℝ) {a b c d : E → M4} (ha : AnalyticAt ℝ a p)
    (hb : AnalyticAt ℝ b p) (hc : AnalyticAt ℝ c p) (hd : AnalyticAt ℝ d p) :
    AnalyticAt ℝ (fun q => expProd (plaqList h (a q) (b q) (c q) (d q))) p := by
  simp only [expProd_plaqList]
  exact (analyticAt_exp_comp (analyticAt_smul_comp h ha)).mul
    ((analyticAt_exp_comp (analyticAt_smul_comp h hb)).mul
    ((analyticAt_exp_comp (analyticAt_smul_comp h hc).neg).mul
      (analyticAt_exp_comp (analyticAt_smul_comp h hd).neg)))

/-- **The literal plaquette curvature `B = h⁻² log(U_i U_{j,+i} U_{i,+j}⁻¹ U_j⁻¹)` is analytic
on the retained branch** `‖U_□ - 1‖ < 1` (`eq:supp-exact-link-curvatures`). -/
theorem analyticAt_plaquette_comp (h : ℝ) {a b c d : E → M4} (ha : AnalyticAt ℝ a p)
    (hb : AnalyticAt ℝ b p) (hc : AnalyticAt ℝ c p) (hd : AnalyticAt ℝ d p)
    (hbr : ‖expProd (plaqList h (a p) (b p) (c p) (d p)) - 1‖ < 1) :
    AnalyticAt ℝ (fun q => plaquette h (a q) (b q) (c q) (d q)) p := by
  unfold plaquette
  exact analyticAt_smul_comp _ ((LinkRemainder.analyticAt_logOnePlus hbr).comp
    (f := fun q => expProd (plaqList h (a q) (b q) (c q) (d q)) - 1)
    ((analyticAt_expProd_plaqList h ha hb hc hd).sub analyticAt_const))

/-- The commutator term `½ Σ_{r<s} [X_r, X_s]` of a plaquette is polynomial, hence analytic. -/
theorem analyticAt_commTerm_plaqX {a b c d : E → M4} (ha : AnalyticAt ℝ a p)
    (hb : AnalyticAt ℝ b p) (hc : AnalyticAt ℝ c p) (hd : AnalyticAt ℝ d p) :
    AnalyticAt ℝ (fun q => commTerm (plaqX (a q) (b q) (c q) (d q))) p := by
  simp only [plaqX, LinkRemainder.commTerm_four]
  have s3 := (hb.add hc.neg).add hd.neg
  have s2 := hc.neg.add hd.neg
  exact ((analyticAt_smul_comp _ ((ha.mul s3).sub (s3.mul ha))).add
    (analyticAt_smul_comp _ ((hb.mul s2).sub (s2.mul hb)))).add
    (analyticAt_smul_comp _ ((hc.neg.mul hd.neg).sub (hd.neg.mul hc.neg)))

/-- The plaquette remainder `ρ^B` is analytic on the retained branch. -/
theorem analyticAt_remB_comp (h : ℝ) {a b c d : E → M4} (ha : AnalyticAt ℝ a p)
    (hb : AnalyticAt ℝ b p) (hc : AnalyticAt ℝ c p) (hd : AnalyticAt ℝ d p)
    (hbr : ‖expProd (plaqList h (a p) (b p) (c p) (d p)) - 1‖ < 1) :
    AnalyticAt ℝ (fun q => remB h (a q) (b q) (c q) (d q)) p := by
  unfold remB
  exact ((analyticAt_plaquette_comp h ha hb hc hd hbr).sub
    (analyticAt_smul_comp _ (((ha.add hb).sub hc).sub hd))).sub
    (analyticAt_commTerm_plaqX ha hb hc hd)

/-- The electric link remainder `ρ^E = h⁻¹(Ad_{e^{ha}} - I - h ad_a) a0s` is entire. -/
theorem analyticAt_remE_comp (h : ℝ) {a b : E → M4} (ha : AnalyticAt ℝ a p)
    (hb : AnalyticAt ℝ b p) : AnalyticAt ℝ (fun q => remE h (a q) (b q)) p := by
  unfold remE
  exact analyticAt_smul_comp _
    (((((analyticAt_exp_comp (analyticAt_smul_comp h ha)).mul hb).mul
      (analyticAt_exp_comp (analyticAt_smul_comp h ha).neg)).sub hb).sub
      (analyticAt_smul_comp h (analyticAt_bracket_comp ha hb)))


/-- `Π_i` composed with an analytic coframe map is analytic. -/
theorem analyticAt_piArr_comp (χ : ℝ) (i : Fin 3) {f : E → M4} (hf : AnalyticAt ℝ f p) :
    AnalyticAt ℝ (fun q => piArr χ (f q) i) p :=
  (analyticAt_piArr χ i (f p)).comp hf

/-- `Σ_ij` composed with an analytic coframe map is analytic. -/
theorem analyticAt_sigmaArr_comp (χ : ℝ) (i j : Fin 3) {f : E → M4} (hf : AnalyticAt ℝ f p) :
    AnalyticAt ℝ (fun q => sigmaArr χ (f q) i j) p :=
  (analyticAt_sigmaArr χ i j (f p)).comp hf

/-- A sum `Σ_{i<j}` of analytic functions is analytic. -/
theorem analyticAt_sumLt {g : Fin 3 → Fin 3 → E → ℝ} (hg : ∀ i j, AnalyticAt ℝ (g i j) p) :
    AnalyticAt ℝ (fun q => sumLt fun i j => g i j q) p := by
  simp only [sumLt_eq]
  exact ((hg 0 1).add (hg 0 2)).add (hg 1 2)

variable {N : ℕ} [NeZero N]

/-! ### Fields on the periodic regulator and the completed density -/

/-- **The retained logarithm branch**: every oriented plaquette product of the spatial connection
`A` (spacing `h`) lies in the principal chart, `‖U_□ - 1‖ < 1`. -/
def PlaqBranch (h : ℝ) (A : Fin 3 → Site N → M4) : Prop :=
  ∀ i j x, ‖expProd (plaqList h (A i x) (A j (x + unitVec i)) (A i (x + unitVec j)) (A j x)) - 1‖
    < 1

/-- The forward difference `D_i^+` of an analytic field is analytic at every site. -/
theorem analyticAt_Dp_comp (h : ℝ) (i : Fin 3) {u : E → Site N → M4}
    (hu : ∀ x, AnalyticAt ℝ (fun q => u q x) p) (x : Site N) :
    AnalyticAt ℝ (fun q => Dp h i (u q) x) p := by
  unfold Dp
  exact analyticAt_smul_comp _ ((hu _).sub (hu x))

/-- The grid pairing `⟨f, 1⟩_h` of a sitewise analytic field is analytic. -/
theorem analyticAt_gridPair_comp (h : ℝ) {f : E → Site N → ℝ}
    (hf : ∀ x, AnalyticAt ℝ (fun q => f q x) p) :
    AnalyticAt ℝ (fun q => gridPair h (f q)) p := by
  unfold gridPair
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ => hf x)

/-- The link remainder density `r_h(e, A)` is analytic on the retained branch. -/
theorem analyticAt_remDensity_comp (χ h : ℝ) {e A0 : E → Site N → M4}
    {A : E → Fin 3 → Site N → M4} (he : ∀ x, AnalyticAt ℝ (fun q => e q x) p)
    (hA0 : ∀ x, AnalyticAt ℝ (fun q => A0 q x) p) (hA : ∀ i x, AnalyticAt ℝ (fun q => A q i x) p)
    (hbr : PlaqBranch h (A p)) (x : Site N) :
    AnalyticAt ℝ (fun q => remDensity χ h (e q) (A0 q) (A q) x) p := by
  unfold remDensity
  refine (Finset.analyticAt_fun_sum _ fun i _ => ?_).neg.add (analyticAt_sumLt fun i j => ?_)
  · exact analyticAt_pairing_comp (analyticAt_piArr_comp χ i (he x))
      (analyticAt_remE_comp h (hA i x) (hA0 _))
  · exact analyticAt_pairing_comp (analyticAt_sigmaArr_comp χ i j (he x))
      (analyticAt_remB_comp h (hA i x) (hA j _) (hA i _) (hA j x) (hbr i j x))

/-- The Cartan quadratic form `q_e(A)` is polynomial in `(e, A₀, A)`, hence analytic. -/
theorem analyticAt_qc_comp (χ : ℝ) {e A0 : E → Site N → M4}
    {A : E → Fin 3 → Site N → M4} (he : ∀ x, AnalyticAt ℝ (fun q => e q x) p)
    (hA0 : ∀ x, AnalyticAt ℝ (fun q => A0 q x) p) (hA : ∀ i x, AnalyticAt ℝ (fun q => A q i x) p)
    (x : Site N) :
    AnalyticAt ℝ (fun q => qc χ (e q) (A0 q) (A q) x) p := by
  unfold qc
  refine (Finset.analyticAt_fun_sum _ fun i _ => ?_).add (analyticAt_sumLt fun i j => ?_)
  · exact analyticAt_pairing_comp (analyticAt_piArr_comp χ i (he x))
      (analyticAt_bracket_comp (hA0 x) (hA i x))
  · exact analyticAt_pairing_comp (analyticAt_sigmaArr_comp χ i j (he x))
      (analyticAt_bracket_comp (hA i x) (hA j x))

/-- **Analyticity of the completed density** (pointwise, parametrised form): for `h ≠ 0`, along
analytic families of coframes and connections whose spatial connection is on the retained
branch at `p`.  The proof passes through the exact normal form `completedDensity_eq`, in which
the connection-velocity nonlinearity (`linkVel`, `𝒦_h`) cancels identically. -/
theorem analyticAt_completedDensity_comp {h : ℝ} (hh : h ≠ 0) (χ Λ : ℝ)
    {e A0 : E → Site N → M4} {A Adot : E → Fin 3 → Site N → M4}
    (he : ∀ x, AnalyticAt ℝ (fun q => e q x) p)
    (hA0 : ∀ x, AnalyticAt ℝ (fun q => A0 q x) p) (hA : ∀ i x, AnalyticAt ℝ (fun q => A q i x) p)
    (hAd : ∀ i x, AnalyticAt ℝ (fun q => Adot q i x) p)
    (hbr : PlaqBranch h (A p)) (x : Site N) :
    AnalyticAt ℝ (fun q => completedDensity χ Λ h (e q) (A0 q) (A q) (Adot q) x) p := by
  simp only [completedDensity_eq hh]
  refine (((((analyticAt_const.mul (analyticAt_det_comp (he x))).add
    (Finset.analyticAt_fun_sum _ fun i _ => ?_)).sub
    (Finset.analyticAt_fun_sum _ fun i _ => ?_)).add (analyticAt_sumLt fun i j => ?_)).add
    (analyticAt_qc_comp χ he hA0 hA x)).add (analyticAt_remDensity_comp χ h he hA0 hA hbr x)
  · exact analyticAt_pairing_comp (analyticAt_piArr_comp χ i (he x)) (hAd i x)
  · exact analyticAt_pairing_comp (analyticAt_piArr_comp χ i (he x)) (analyticAt_Dp_comp h i hA0 x)
  · exact analyticAt_pairing_comp (analyticAt_sigmaArr_comp χ i j (he x))
      ((analyticAt_Dp_comp h i (hA j) x).sub (analyticAt_Dp_comp h j (hA i) x))


/-- Evaluation `A ↦ A i x` of a spatial connection is analytic. -/
theorem analyticAt_eval2 (i : Fin 3) (x : Site N) (A : Fin 3 → Site N → M4) :
    AnalyticAt ℝ (fun B : Fin 3 → Site N → M4 => B i x) A :=
  analyticAt_pi_apply (analyticAt_pi_apply analyticAt_id i) x

/-- **The retained branch is open** in the spatial link variables. -/
theorem isOpen_plaqBranch (h : ℝ) : IsOpen {A : Fin 3 → Site N → M4 | PlaqBranch h A} := by
  have hset : {A : Fin 3 → Site N → M4 | PlaqBranch h A} = ⋂ i, ⋂ j, ⋂ x,
      {A : Fin 3 → Site N → M4 | ‖expProd (plaqList h (A i x) (A j (x + unitVec i))
        (A i (x + unitVec j)) (A j x)) - 1‖ < 1} := by
    ext A; simp [PlaqBranch]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun x => isOpen_lt (continuous_norm.comp ?_) continuous_const
  refine continuous_iff_continuousAt.2 fun A => ?_
  exact ((analyticAt_expProd_plaqList h (analyticAt_eval2 i x A) (analyticAt_eval2 j _ A)
    (analyticAt_eval2 i _ A) (analyticAt_eval2 j x A)).sub analyticAt_const).continuousAt

/-- **Non-vacuity**: the zero spatial connection (flat links `U = 1`) is on the retained branch. -/
theorem plaqBranch_zero (h : ℝ) : PlaqBranch h (0 : Fin 3 → Site N → M4) := by
  intro i j x
  simp [plaqList]

/-- **Joint analyticity of the completed density** (`eq:supp-exact-completed-action`): for `h ≠ 0`
the map `(e, A₀, A, Ȧ) ↦ ⟨χ det(e)(r - 2Λ) + q - q_h - 𝒦_h, 1⟩_h` is analytic at every
configuration whose plaquettes lie on the retained branch. -/
theorem analyticAt_gridPair_completedDensity {h : ℝ} (hh : h ≠ 0) (χ Λ : ℝ)
    (p : (Site N → M4) × (Site N → M4) × (Fin 3 → Site N → M4) × (Fin 3 → Site N → M4))
    (hbr : PlaqBranch h p.2.2.1) :
    AnalyticAt ℝ (fun q : (Site N → M4) × (Site N → M4) × (Fin 3 → Site N → M4) ×
        (Fin 3 → Site N → M4) => gridPair h (completedDensity χ Λ h q.1 q.2.1 q.2.2.1 q.2.2.2))
      p := by
  have h1 : AnalyticAt ℝ (fun q : (Site N → M4) × (Site N → M4) × (Fin 3 → Site N → M4) ×
      (Fin 3 → Site N → M4) => q.1) p := analyticAt_fst
  have h2 : AnalyticAt ℝ (fun q : (Site N → M4) × (Site N → M4) × (Fin 3 → Site N → M4) ×
      (Fin 3 → Site N → M4) => q.2.1) p := analyticAt_fst.comp analyticAt_snd
  have h3 : AnalyticAt ℝ (fun q : (Site N → M4) × (Site N → M4) × (Fin 3 → Site N → M4) ×
      (Fin 3 → Site N → M4) => q.2.2.1) p :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
  have h4 : AnalyticAt ℝ (fun q : (Site N → M4) × (Site N → M4) × (Fin 3 → Site N → M4) ×
      (Fin 3 → Site N → M4) => q.2.2.2) p :=
    analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)
  exact analyticAt_gridPair_comp h fun x => analyticAt_completedDensity_comp hh χ Λ
    (fun x => analyticAt_pi_apply h1 x) (fun x => analyticAt_pi_apply h2 x)
    (fun i x => analyticAt_pi_apply (analyticAt_pi_apply h3 i) x)
    (fun i x => analyticAt_pi_apply (analyticAt_pi_apply h4 i) x) hbr x


/-! ### The phase-compatible Lagrangian -/

/-- `ι c = Σ_k c_k G_k` of analytic Lorentz coordinates is analytic. -/
theorem analyticAt_iota_comp {c : E → Fin 6 → ℝ} (hc : ∀ k, AnalyticAt ℝ (fun q => c q k) p) :
    AnalyticAt ℝ (fun q => iota (c q)) p := by
  unfold iota
  exact Finset.analyticAt_fun_sum _ fun k _ => (hc k).smul analyticAt_const

open OddPhaseDerivativeReal in
/-- The phase-compatible temporal load `f°_{h,0} = Σ_i δ_iΠ_i` is analytic in the coframe
(`δ_i` is a finite kernel sum, `pd_apply`). -/
theorem analyticAt_load0Ph_comp (χ : ℝ) {e : E → Site N → M4}
    (he : ∀ x, AnalyticAt ℝ (fun q => e q x) p) (x : Site N) :
    AnalyticAt ℝ (fun q => load0Ph χ (e q) x) p := by
  simp only [load0Ph, pd_apply]
  exact Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun s _ =>
    analyticAt_smul_comp _ (analyticAt_piArr_comp χ i (he _))

open OddPhaseDerivativeReal in
/-- The phase-compatible spatial load `-Σ_j δ_jΣ_ji` is analytic in the coframe. -/
theorem analyticAt_loadSpPh_comp (χ : ℝ) {e : E → Site N → M4}
    (he : ∀ x, AnalyticAt ℝ (fun q => e q x) p) (i : Fin 3) (x : Site N) :
    AnalyticAt ℝ (fun q => loadSpPh χ (e q) i x) p := by
  simp only [loadSpPh, pd_apply]
  exact (Finset.analyticAt_fun_sum _ fun j _ => Finset.analyticAt_fun_sum _ fun s _ =>
    analyticAt_smul_comp _ (analyticAt_sigmaArr_comp χ j i (he _))).neg

/-- The phase-compatible normal-form density is analytic on the retained branch. -/
theorem analyticAt_nfDensityPh_comp (χ Λ h : ℝ) {e A0 : E → Site N → M4}
    {Pidot A : E → Fin 3 → Site N → M4} (he : ∀ x, AnalyticAt ℝ (fun q => e q x) p)
    (hPi : ∀ i x, AnalyticAt ℝ (fun q => Pidot q i x) p)
    (hA0 : ∀ x, AnalyticAt ℝ (fun q => A0 q x) p) (hA : ∀ i x, AnalyticAt ℝ (fun q => A q i x) p)
    (hbr : PlaqBranch h (A p)) (x : Site N) :
    AnalyticAt ℝ (fun q => nfDensityPh χ Λ h (e q) (Pidot q) (A0 q) (A q) x) p := by
  unfold nfDensityPh
  refine ((((analyticAt_const.mul (analyticAt_det_comp (he x))).add
    (analyticAt_pairing_comp (analyticAt_load0Ph_comp χ he x) (hA0 x))).add
    (Finset.analyticAt_fun_sum _ fun i _ => ?_)).add
    (analyticAt_qc_comp χ he hA0 hA x)).add (analyticAt_remDensity_comp χ h he hA0 hA hbr x)
  exact analyticAt_pairing_comp ((hPi i x).neg.add (analyticAt_loadSpPh_comp χ he i x)) (hA i x)

/-- **Clause (i) of `thm:supp-exact-action-provenance`** (`eq:supp-exact-phase-action`): the
instantaneous phase-compatible Lagrangian `(e, ∂_tΠ, A) ↦ L°(e, ∂_tΠ; A)` (`h = 1/N`, Lorentz
coordinates `Conn N`) is jointly analytic at every point whose plaquettes lie on the retained
branch. -/
theorem analyticAt_phaseLagr (χ Λ : ℝ)
    (p : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N)
    (hbr : PlaqBranch (hN N) (toA p.2.2)) :
    AnalyticAt ℝ (fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N =>
      phaseLagr χ Λ q.1 q.2.1 q.2.2) p := by
  have h1 : AnalyticAt ℝ (fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N => q.1) p :=
    analyticAt_fst
  have h2 : AnalyticAt ℝ (fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N => q.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  have h3 : AnalyticAt ℝ (fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N => q.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  have hc : ∀ x μ k, AnalyticAt ℝ
      (fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N => q.2.2 x μ k) p :=
    fun x μ k => analyticAt_pi_apply (analyticAt_pi_apply (analyticAt_pi_apply h3 x) μ) k
  unfold phaseLagr
  exact analyticAt_gridPair_comp _ fun x => analyticAt_nfDensityPh_comp χ Λ (hN N)
    (fun x => analyticAt_pi_apply h1 x)
    (fun i x => analyticAt_pi_apply (analyticAt_pi_apply h2 i) x)
    (fun x => analyticAt_iota_comp fun k => hc x 0 k)
    (fun i x => analyticAt_iota_comp fun k => hc x i.succ k) hbr x

/-- The zero coordinate connection has zero spatial matrices. -/
theorem toA_zero : toA (0 : Conn N) = 0 := by
  funext i x
  simp [toA, ← iota_zero]


/-! ### Supplements: `det(e) r(e, F)`, open branch sets, flat data -/

/-- The permutation-symbol Palatini density `det(e) r(e, F)` is analytic in the coframe. -/
theorem analyticAt_detR (Ef : Fin 3 → M4) (Bf : Fin 3 → Fin 3 → M4) (X : M4) :
    AnalyticAt ℝ (fun e : M4 => detR e Ef Bf) X := by
  have hfun : (fun e : M4 => detR e Ef Bf) = fun e => ∑ i, pairing (piArr 1 e i) (Ef i) +
      sumLt fun i j => pairing (sigmaArr 1 e i j) (Bf i j) := by
    funext e; rw [← palatini_contraction, one_mul]
  rw [hfun]
  exact (Finset.analyticAt_fun_sum _ fun i _ =>
    analyticAt_pairing_comp (analyticAt_piArr 1 i X) analyticAt_const).add
    (analyticAt_sumLt fun i j =>
      analyticAt_pairing_comp (analyticAt_sigmaArr 1 i j X) analyticAt_const)

/-- The retained-branch set of configurations `(e, A₀, A, Ȧ)` is open. -/
theorem isOpen_completedBranch (h : ℝ) :
    IsOpen {q : (Site N → M4) × (Site N → M4) × (Fin 3 → Site N → M4) × (Fin 3 → Site N → M4) |
      PlaqBranch h q.2.2.1} :=
  (isOpen_plaqBranch h).preimage (continuous_fst.comp (continuous_snd.comp continuous_snd))

/-- The completed density is analytic on the open retained-branch set. -/
theorem analyticOnNhd_gridPair_completedDensity {h : ℝ} (hh : h ≠ 0) (χ Λ : ℝ) :
    AnalyticOnNhd ℝ (fun q : (Site N → M4) × (Site N → M4) × (Fin 3 → Site N → M4) ×
        (Fin 3 → Site N → M4) => gridPair h (completedDensity χ Λ h q.1 q.2.1 q.2.2.1 q.2.2.2))
      {q | PlaqBranch h q.2.2.1} :=
  fun q hq => analyticAt_gridPair_completedDensity hh χ Λ q hq

/-- The spatial connection matrices depend continuously on the coordinate configuration. -/
theorem continuous_toA_snd :
    Continuous fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N => toA q.2.2 := by
  refine continuous_pi fun i => continuous_pi fun x => continuous_iff_continuousAt.2 fun q => ?_
  have h3 : AnalyticAt ℝ (fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N => q.2.2) q :=
    analyticAt_snd.comp analyticAt_snd
  exact (analyticAt_iota_comp fun k =>
    analyticAt_pi_apply (analyticAt_pi_apply (analyticAt_pi_apply h3 x) i.succ) k).continuousAt

/-- The retained-branch set of configurations `(e, ∂_tΠ, A)` is open. -/
theorem isOpen_phaseBranch :
    IsOpen {q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N | PlaqBranch (hN N) (toA q.2.2)} :=
  (isOpen_plaqBranch (hN N)).preimage continuous_toA_snd

/-- The phase-compatible Lagrangian is analytic on the open retained-branch set. -/
theorem analyticOnNhd_phaseLagr (χ Λ : ℝ) :
    AnalyticOnNhd ℝ (fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N =>
      phaseLagr χ Λ q.1 q.2.1 q.2.2) {q | PlaqBranch (hN N) (toA q.2.2)} :=
  fun q hq => analyticAt_phaseLagr χ Λ q hq

/-- **Non-vacuity at flat data**: the completed density is analytic at `e = 1`, `A = 0`. -/
theorem analyticAt_gridPair_completedDensity_flat {h : ℝ} (hh : h ≠ 0) (χ Λ : ℝ)
    (A0 : Site N → M4) (Adot : Fin 3 → Site N → M4) :
    AnalyticAt ℝ (fun q : (Site N → M4) × (Site N → M4) × (Fin 3 → Site N → M4) ×
        (Fin 3 → Site N → M4) => gridPair h (completedDensity χ Λ h q.1 q.2.1 q.2.2.1 q.2.2.2))
      ((fun _ => 1), A0, 0, Adot) :=
  analyticAt_gridPair_completedDensity hh χ Λ _ (plaqBranch_zero h)

/-- **Non-vacuity at flat data**: the phase-compatible Lagrangian is analytic at `e = 1`,
`A = 0`. -/
theorem analyticAt_phaseLagr_flat (χ Λ : ℝ) (Pidot : Fin 3 → Site N → M4) :
    AnalyticAt ℝ (fun q : (Site N → M4) × (Fin 3 → Site N → M4) × Conn N =>
      phaseLagr χ Λ q.1 q.2.1 q.2.2) ((fun _ => 1), Pidot, 0) :=
  analyticAt_phaseLagr χ Λ _ (by rw [toA_zero]; exact plaqBranch_zero _)

end RenewalGeometry.ExactPhaseAction
