/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallHigherE56

/-!
# Uniform higher bounds of Coulomb gauge states along a smooth family
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `mN_embX_le`, `sum_sN_le_coordL4` — the matrix connection `Σ_b a^b e_b` in `L⁴` against the
  coefficient norm `coordL4`;
* `exists_uniform_bound` — continuous images of the compact parameter interval are bounded;
* `coulombHigherBounds` (**main result**) — `UhlenbeckBall.CoulombHigherBounds c r L G` holds
  for every ball, Lie basis and set `G`: lifted Coulomb states of a jointly smooth family with
  small coefficient `L⁴` norm are uniformly bounded in `H⁶` (bounds `H² → H³ → H⁴` by
  absorption, `H⁵, H⁶` in the Banach algebras `H³, H⁴`).
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.HigherFinal

open SobolevOpen BallReg BallAlg SobAlg HigherNorms HigherIdent HigherLeibniz HigherE3 HigherE4
  HigherE56

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m d : ℕ}

/-! ### The matrix connection against its coefficients -/

/-- The basis constant `Σ_{ijb} (|Re e_b(i,j)| + |Im e_b(i,j)|)`. -/
def cL (L : LieBasis m d) : ℝ := ∑ i, ∑ j, ∑ b, (|(L.e b i j).re| + |(L.e b i j).im|)

theorem cL_nonneg (L : LieBasis m d) : 0 ≤ cL L :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem mN_embX_le {s : ℕ} [Fact (3 ≤ s)] (L : LieBasis m d) (x : Fin d → SobAlg c r s) :
    mN 4 (embX L x) ≤ cL L * ∑ b, sN 4 (x b) := by
  have hS : ∀ b, sN 4 (x b) ≤ ∑ b', sN 4 (x b') := fun b =>
    Finset.single_le_sum (f := fun b' => sN 4 (x b')) (fun _ _ => sN_nonneg _ _) (Finset.mem_univ b)
  have hsum0 : 0 ≤ ∑ b, sN 4 (x b) := Finset.sum_nonneg fun _ _ => sN_nonneg _ _
  unfold mN cL
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [embX_apply, Finset.sum_mul]
  have hre : sN 4 (∑ b, (L.e b i j).re • x b) ≤ ∑ b, |(L.e b i j).re| * ∑ b', sN 4 (x b') :=
    (sN_sum_le (by norm_num) _ _).trans (Finset.sum_le_sum fun b _ => by
      rw [sN_smul]; exact mul_le_mul_of_nonneg_left (hS b) (abs_nonneg _))
  have him : sN 4 (∑ b, (L.e b i j).im • x b) ≤ ∑ b, |(L.e b i j).im| * ∑ b', sN 4 (x b') :=
    (sN_sum_le (by norm_num) _ _).trans (Finset.sum_le_sum fun b _ => by
      rw [sN_smul]; exact mul_le_mul_of_nonneg_left (hS b) (abs_nonneg _))
  calc sN 4 (∑ b, (L.e b i j).re • x b) + sN 4 (∑ b, (L.e b i j).im • x b)
      ≤ ∑ b, |(L.e b i j).re| * ∑ b', sN 4 (x b') + ∑ b, |(L.e b i j).im| * ∑ b', sN 4 (x b') :=
        add_le_add hre him
    _ = _ := by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by ring

theorem sum_sN_le_coordL4 {a : Fin 4 → Fin d → SobAlg c r 4} (ha : coordL4 a ≠ ⊤) (μ : Fin 4) :
    ∑ b, sN 4 (a μ b) ≤ (coordL4 a).toReal := by
  have hfin : ∀ ν b, eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r)) ≠ ⊤ :=
    fun ν b => eLpNorm_fn_ne_top _ _
  unfold sN
  rw [← ENNReal.toReal_sum fun b _ => hfin μ b]
  refine ENNReal.toReal_mono ha ?_
  exact Finset.single_le_sum (f := fun ν => ∑ b, eLpNorm (fn (a ν b)) 4
    (volume.restrict (euclBall c r))) (fun _ _ => zero_le) (Finset.mem_univ μ)

/-! ### Uniform bounds along a compact parameter interval -/

theorem exists_uniform_bound {X Y : Type*} [TopologicalSpace X] [SeminormedAddCommGroup Y]
    {F : ℝ → X} (hF : Continuous F) {Φ : X → Y} (hΦ : Continuous Φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖Φ (F t)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn (hΦ.comp hF).continuousOn).isBounded
    |>.exists_norm_le
  refine ⟨max M 0, le_max_right _ _, fun t ht => (hM _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)⟩

/-! ### Uniform bounds on the smooth family -/

/-- `M` as a function of the level-`9` connection. -/
def mOf (G : Fin 4 → MatSob c r 9 m) : MatSob c r 8 m :=
  ∑ μ, (rhoM (G μ) * rhoM (G μ) + derM μ (G μ))

theorem continuous_mOf : Continuous (mOf (c := c) (r := r) (m := m)) := by
  unfold mOf
  refine continuous_finsetSum _ fun μ _ => ?_
  have h1 : Continuous fun G : Fin 4 → MatSob c r 9 m => rhoM (G μ) :=
    (rhoML (c := c) (r := r) (s := 8) (m := m)).continuous.comp (continuous_apply μ)
  exact (h1.mul h1).add ((derM (c := c) (r := r) (s := 8) (m := m) μ).continuous.comp
    (continuous_apply μ))

theorem gM_eq_mOf {Bf : CriticalGauge.MConn m} {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)} :
    gM (c := c) (r := r) Bf hB = mOf (fun μ => gB (c := c) (r := r) Bf hB μ) := rfl

theorem norm_pi_le' {ι : Type*} [Fintype ι] {Y : Type*} [SeminormedAddCommGroup Y] (G : ι → Y)
    (i : ι) {M : ℝ} (h : ‖G‖ ≤ M) : ‖G i‖ ≤ M := (norm_le_pi_norm G i).trans h

/-- **Uniform bounds on a jointly smooth family of connections** for `t ∈ [0,1]`. -/
theorem exists_family_bounds (Bf : ℝ → CriticalGauge.MConn m)
    (hBf : ∀ μ i j, ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) => Bf p.1 μ p.2 i j))
    (hBt : ∀ t μ i j, ContDiff ℝ ∞ (fun x => Bf t μ x i j)) :
    ∃ b β : ℝ, 0 ≤ b ∧ 0 ≤ β ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      BBounds (c := c) (r := r) (Bf t) (hBt t) b ∧
      (∀ μ, ‖restrM (by norm_num : 3 ≤ 9) (gB (c := c) (r := r) (Bf t) (hBt t) μ)‖ ≤ β) ∧
      ‖restrM (by norm_num : 3 ≤ 8) (gM (c := c) (r := r) (Bf t) (hBt t))‖ ≤ β ∧
      (∀ μ, ‖restrM (by norm_num : 4 ≤ 9) (gB (c := c) (r := r) (Bf t) (hBt t) μ)‖ ≤ β) ∧
      ‖restrM (by norm_num : 4 ≤ 8) (gM (c := c) (r := r) (Bf t) (hBt t))‖ ≤ β := by
  set F : ℝ → Fin 4 → MatSob c r 9 m := fun t μ => gB (c := c) (r := r) (Bf t) (hBt t) μ with hFdef
  have hF : Continuous F := continuous_pi fun μ =>
    continuous_matOfSmooth_param (F := fun t => Bf t μ) (fun i j => hBf μ i j) (fun t => hBt t μ)
  have dc : ∀ {s : ℕ} [Fact (3 ≤ s)] (ν : Fin 4),
      Continuous (derM (c := c) (r := r) (s := s) (m := m) ν) := fun ν => (derM ν).continuous
  obtain ⟨M1, hM10, hM1⟩ := exists_uniform_bound hF (continuous_id)
  obtain ⟨M2, hM20, hM2⟩ := exists_uniform_bound hF (Φ := fun G : Fin 4 → MatSob c r 9 m =>
    fun ν μ => derM ν (G μ)) (continuous_pi fun ν => continuous_pi fun μ =>
      (dc ν).comp (continuous_apply μ))
  obtain ⟨M3, hM30, hM3⟩ := exists_uniform_bound hF (Φ := fun G : Fin 4 → MatSob c r 9 m =>
    fun l ν μ => derM l (derM ν (G μ))) (continuous_pi fun l => continuous_pi fun ν =>
      continuous_pi fun μ => (dc l).comp ((dc ν).comp (continuous_apply μ)))
  obtain ⟨M4, hM40, hM4⟩ := exists_uniform_bound hF (Φ := fun G : Fin 4 → MatSob c r 9 m =>
    fun k l ν μ => derM k (derM l (derM ν (G μ)))) (continuous_pi fun k => continuous_pi fun l =>
      continuous_pi fun ν => continuous_pi fun μ =>
        (dc k).comp ((dc l).comp ((dc ν).comp (continuous_apply μ))))
  obtain ⟨M5, hM50, hM5⟩ := exists_uniform_bound hF (continuous_mOf (c := c) (r := r) (m := m))
  obtain ⟨M6, hM60, hM6⟩ := exists_uniform_bound hF (Φ := fun G : Fin 4 → MatSob c r 9 m =>
    fun ν => derM ν (mOf G)) (continuous_pi fun ν => (dc ν).comp continuous_mOf)
  obtain ⟨M7, hM70, hM7⟩ := exists_uniform_bound hF (Φ := fun G : Fin 4 → MatSob c r 9 m =>
    fun l ν => derM l (derM ν (mOf G))) (continuous_pi fun l => continuous_pi fun ν =>
      (dc l).comp ((dc ν).comp continuous_mOf))
  obtain ⟨C9, hC90, hC9⟩ := mN_le_norm (c := c) (r := r) (m := m) (s := 9) ⊤
  obtain ⟨C8, hC80, hC8⟩ := mN_le_norm (c := c) (r := r) (m := m) (s := 8) ⊤
  obtain ⟨C7, hC70, hC7⟩ := mN_le_norm (c := c) (r := r) (m := m) (s := 7) ⊤
  obtain ⟨C6, hC60, hC6⟩ := mN_le_norm (c := c) (r := r) (m := m) (s := 6) ⊤
  obtain ⟨D93, hD930, hD93⟩ := hM_le_norm (c := c) (r := r) (m := m) (s := 9) 3 (by norm_num)
  obtain ⟨D94, hD940, hD94⟩ := hM_le_norm (c := c) (r := r) (m := m) (s := 9) 4 (by norm_num)
  obtain ⟨D83, hD830, hD83⟩ := hM_le_norm (c := c) (r := r) (m := m) (s := 8) 3 (by norm_num)
  obtain ⟨D84, hD840, hD84⟩ := hM_le_norm (c := c) (r := r) (m := m) (s := 8) 4 (by norm_num)
  have hK3 := (Kal_pos c r 3).le
  have hK4 := (Kal_pos c r 4).le
  set b := C9 * M1 + C8 * M2 + C7 * M3 + C6 * M4 + C8 * M5 + C7 * M6 + C6 * M7 with hb
  set β := (m : ℝ) * Kal c r 3 * (D93 * M1) + (m : ℝ) * Kal c r 4 * (D94 * M1) +
    (m : ℝ) * Kal c r 3 * (D83 * M5) + (m : ℝ) * Kal c r 4 * (D84 * M5) with hβ
  have p1 := mul_nonneg hC90 hM10
  have p2 := mul_nonneg hC80 hM20
  have p3 := mul_nonneg hC70 hM30
  have p4 := mul_nonneg hC60 hM40
  have p5 := mul_nonneg hC80 hM50
  have p6 := mul_nonneg hC70 hM60
  have p7 := mul_nonneg hC60 hM70
  have hmK3 : 0 ≤ (m : ℝ) * Kal c r 3 := mul_nonneg (Nat.cast_nonneg _) hK3
  have hmK4 : 0 ≤ (m : ℝ) * Kal c r 4 := mul_nonneg (Nat.cast_nonneg _) hK4
  have q1 := mul_nonneg hmK3 (mul_nonneg hD930 hM10)
  have q2 := mul_nonneg hmK4 (mul_nonneg hD940 hM10)
  have q3 := mul_nonneg hmK3 (mul_nonneg hD830 hM50)
  have q4 := mul_nonneg hmK4 (mul_nonneg hD840 hM50)
  refine ⟨b, β, by linarith, by linarith, fun t ht => ⟨⟨fun μ => ?_, fun ν μ => ?_,
    fun l ν μ => ?_, fun k l ν μ => ?_, ?_, fun ν => ?_, fun l ν => ?_⟩, fun μ => ?_, ?_,
    fun μ => ?_, ?_⟩⟩
  · have := (hC9 _).trans (mul_le_mul_of_nonneg_left (norm_pi_le' (F t) μ (hM1 t ht)) hC90)
    exact this.trans (by linarith)
  · have := (hC8 _).trans (mul_le_mul_of_nonneg_left (norm_pi_le' _ μ
      (norm_pi_le' _ ν (hM2 t ht))) hC80)
    exact this.trans (by linarith)
  · have := (hC7 _).trans (mul_le_mul_of_nonneg_left (norm_pi_le' _ μ (norm_pi_le' _ ν
      (norm_pi_le' _ l (hM3 t ht)))) hC70)
    exact this.trans (by linarith)
  · have := (hC6 _).trans (mul_le_mul_of_nonneg_left (norm_pi_le' _ μ (norm_pi_le' _ ν
      (norm_pi_le' _ l (norm_pi_le' _ k (hM4 t ht))))) hC60)
    exact this.trans (by linarith)
  · rw [gM_eq_mOf]
    have := (hC8 _).trans (mul_le_mul_of_nonneg_left (hM5 t ht) hC80)
    exact this.trans (by linarith)
  · rw [gM_eq_mOf]
    have := (hC7 _).trans (mul_le_mul_of_nonneg_left (norm_pi_le' _ ν (hM6 t ht)) hC70)
    exact this.trans (by linarith)
  · rw [gM_eq_mOf]
    have := (hC6 _).trans (mul_le_mul_of_nonneg_left (norm_pi_le' _ ν
      (norm_pi_le' _ l (hM7 t ht))) hC60)
    exact this.trans (by linarith)
  · have := (norm_restrM_le_hM (by norm_num : 3 ≤ 9) (gB (c := c) (r := r) (Bf t) (hBt t) μ)).trans
      (mul_le_mul_of_nonneg_left ((hD93 _).trans (mul_le_mul_of_nonneg_left
        (norm_pi_le' (F t) μ (hM1 t ht)) hD930)) hmK3)
    exact this.trans (by linarith)
  · rw [gM_eq_mOf]
    have := (norm_restrM_le_hM (by norm_num : 3 ≤ 8) (mOf (F t))).trans
      (mul_le_mul_of_nonneg_left ((hD83 _).trans (mul_le_mul_of_nonneg_left (hM5 t ht) hD830))
        hmK3)
    exact this.trans (by linarith)
  · have := (norm_restrM_le_hM (by norm_num : 4 ≤ 9) (gB (c := c) (r := r) (Bf t) (hBt t) μ)).trans
      (mul_le_mul_of_nonneg_left ((hD94 _).trans (mul_le_mul_of_nonneg_left
        (norm_pi_le' (F t) μ (hM1 t ht)) hD940)) hmK4)
    exact this.trans (by linarith)
  · rw [gM_eq_mOf]
    have := (norm_restrM_le_hM (by norm_num : 4 ≤ 8) (mOf (F t))).trans
      (mul_le_mul_of_nonneg_left ((hD84 _).trans (mul_le_mul_of_nonneg_left (hM5 t ht) hD840))
        hmK4)
    exact this.trans (by linarith)

/-! ### The uniform higher bounds -/

instance instFact3' : Fact (3 ≤ 3 + 1) := ⟨by norm_num⟩
instance instFact4' : Fact (3 ≤ 4 + 1) := ⟨by norm_num⟩

set_option maxHeartbeats 1000000 in
/-- **Uniform `H⁶` bounds of Coulomb gauge states** (the closedness input of the continuity
method, `UhlenbeckBall.CoulombHigherBounds`), for every ball, Lie basis and set `G`. -/
theorem coulombHigherBounds (L : LieBasis m d) (G : Set (Matrix (Fin m) (Fin m) ℂ)) :
    UhlenbeckBall.CoulombHigherBounds c r L G := by
  obtain ⟨CS, cv, hK⟩ := exists_sobConsts (c := c) (r := r) (m := m)
  obtain ⟨CN0, hCN00, h2⟩ := hM2_le hK
  obtain ⟨θ3, hθ3, -, h3⟩ := hM3_le hK
  obtain ⟨θ4, hθ4, -, h4⟩ := hM4_le hK
  obtain ⟨C5, hC50, h5⟩ := hM_top_le (c := c) (r := r) (m := m) 3 (by norm_num) hK
  obtain ⟨C6, hC60, h6⟩ := hM_top_le (c := c) (r := r) (m := m) 4 (by norm_num) hK
  set A : ℝ := cL L * (2 * (m : ℝ) ^ 2) with hA
  have hA0 : 0 ≤ A := mul_nonneg (cL_nonneg L) (by positivity)
  set θ : ℝ := min θ3 θ4 with hθ
  have hθ0 : 0 < θ := lt_min hθ3 hθ4
  refine ⟨ENNReal.ofReal (θ / (A + 1)), ENNReal.ofReal_pos.mpr (by positivity),
    fun Bf hBf hBt κ hκ => ?_⟩
  have hκt : κ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hκ
  have hκr : κ.toReal ≤ θ / (A + 1) := ENNReal.toReal_le_of_le_ofReal (by positivity) hκ
  set δ : ℝ := A * κ.toReal with hδ
  have hδ0 : 0 ≤ δ := mul_nonneg hA0 ENNReal.toReal_nonneg
  have hδθ : δ ≤ θ := by
    calc δ = A * κ.toReal := rfl
      _ ≤ (A + 1) * (θ / (A + 1)) := mul_le_mul (by linarith) hκr ENNReal.toReal_nonneg
          (by positivity)
      _ = θ := by field_simp
  obtain ⟨b, β, hb0, hβ0, hfam⟩ := exists_family_bounds (c := c) (r := r) Bf hBf hBt
  set H2 : ℝ := CN0 * ((2 * (m : ℝ) ^ 2 * (cv * b) + 2 * (4 * (cv * δ * b)) +
    4 * (δ * (2 * (m : ℝ) ^ 2) * δ)) + cv * (2 * (m : ℝ) ^ 2)) with hH2
  obtain ⟨K3, hK3⟩ := h3 H2 b
  obtain ⟨K4, hK4⟩ := h4 K3 b
  set K5 : ℝ := C5 * (qA ((m : ℝ) * Kal c r 3) β K4 + cv * (2 * (m : ℝ) ^ 2)) with hK5
  set K6 : ℝ := C6 * (qA ((m : ℝ) * Kal c r 4) β K5 + cv * (2 * (m : ℝ) ^ 2)) with hK6
  refine ⟨(m : ℝ) * Kal c r 6 * K6, fun t ht u a hst => ?_⟩
  obtain ⟨hu, -, hN, ha, hact, hcoul, hS⟩ := hst
  have hcoulM : ∑ μ, derM μ (actM u (star u)
      (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf t κ) (hBt t κ)) μ) = 0 := by
    rw [Finset.sum_congr rfl fun μ _ => congrArg (derM μ) (hact μ)]
    exact AssemblyTools.sum_derM_embX_eq_zero L hcoul
  obtain ⟨uh, hlift⟩ := coulomb_gauge_lift (hBt t) hu hN hcoulM 5
  have hlift' : restrM (by norm_num : 5 ≤ 10) (show MatSob c r 10 m from uh) = u := hlift
  have hco : coordL4 a ≠ ⊤ := ne_top_of_le_ne_top hκt hS
  have hD4 : ∀ μ, mN 4 (gD (Bf t) (hBt t) (show MatSob c r 10 m from uh) μ) ≤ δ := by
    intro μ
    refine (mN_gD_le L hu hact hlift' μ).trans ?_
    have h1 := (mN_embX_le L (a μ)).trans (mul_le_mul_of_nonneg_left
      (sum_sN_le_coordL4 hco μ) (cL_nonneg L))
    have h2 : (coordL4 a).toReal ≤ κ.toReal := ENNReal.toReal_mono hκt hS
    calc mN 4 (embX L (a μ)) * (2 * (m : ℝ) ^ 2) ≤ cL L * (coordL4 a).toReal * (2 * (m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ cL L * κ.toReal * (2 * (m : ℝ) ^ 2) := by
          gcongr
          exact cL_nonneg L
      _ = δ := by rw [hδ, hA]; ring
  have hSet : HSet (Bf t) (hBt t) (show MatSob c r 10 m from uh) b δ :=
    ⟨lift_unitary hu hlift', by rw [hlift']; exact hN, lapM_eq_gQ L hu hact hcoul hlift', hD4,
      (hfam t ht).1, hb0, hδ0⟩
  have e2 := h2 hSet
  have e3 := hK3 hSet (hδθ.trans (min_le_left _ _)) e2
  have e4 := hK4 hSet (hδθ.trans (min_le_right _ _)) e3
  have e5 := h5 β K4 hβ0 hSet (hfam t ht).2.1 (hfam t ht).2.2.1 e4
  have e6 := h6 β K5 hβ0 hSet (hfam t ht).2.2.2.1 (hfam t ht).2.2.2.2 e5
  refine ⟨restrM (by norm_num : 6 ≤ 10) (show MatSob c r 10 m from uh), ?_, ?_⟩
  · rw [rhoM_eq_restrM, restrM_restrM]
    exact hlift'
  · refine (norm_restrM_le_hM _ _).trans ?_
    have hK6' : (m : ℝ) * Kal c r 6 ≥ 0 := mul_nonneg (Nat.cast_nonneg _) (Kal_pos c r 6).le
    exact mul_le_mul_of_nonneg_left e6 hK6'

end RenewalGeometry.BallAnalysis.HigherFinal
