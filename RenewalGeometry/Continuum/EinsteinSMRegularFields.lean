/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMRegularBosonic

/-!
# The regular branch, bosonic part: `eq:regular-bosonic-bound` gives `C¹` convergence and the
  reduced compactness certificate without screens (`thm:regular-branch`, lemmas L1, L3)

Rendering (as in `BoxBosonicCompactness.lean`): `H^{3+σ}(Q)` on a chart box `Q` is the restriction
space of `H^{3+σ}` on the torus of period `L` with corner `a` (`TorusRep`): every component of the
coframe, connection and Higgs field agrees on `Q` with `U ∘ chart a L` for a continuous
`U ∈ H^{3+σ}(𝕋⁴)` with `‖U‖²_{H^{3+σ}} ≤ B` (`RegularBosonicBound`).

* **`exists_subseq_bosonicC1`** (L3, chart transfer + `rellich_C1`) — every cutoff subsequence
  has a further subsequence along which `e_h, ∂e_h, A_h, ∂A_h, H_h, ∂H_h` are uniformly Cauchy on
  `Q` (`BosonicC1Cauchy`).
* **`reducedCertificate_of_C1`** (L1) — `C¹`-Cauchy bosonic fields, the coframe chart condition,
  strong spinor data and banks in a compact physical set satisfy the reduced certificate (R1)–(R5)
  of `def:reduced-certificate` on `Q`; the common compact screens of the coframe, curvature and
  covariant-gradient packets are produced by `hasCommonCompactScreen_of_cauchy`.
* `lpPrecompact_coframe_of_C1` — the coframes are precompact in `L^∞(Q)`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal BigOperators

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace RegularBranch

open SobolevOpen (pd box IsTest MemW12)

set_option linter.unusedSectionVars false

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-! ### The hypothesis `eq:regular-bosonic-bound` -/

/-- **`eq:regular-bosonic-bound` on a chart box** (restriction-space rendering): every coframe,
connection and Higgs component of every `z_h` agrees on `Q` with the pull-back by `chart a L` of a
continuous function bounded in `H^{3+σ}(𝕋⁴)` by `B`. -/
def RegularBosonicBound (Q : ChartBox T) (a : E4) (L σ B : ℝ) (z : ℕ → SmoothFields T left) :
    Prop :=
  (∀ n (p : Fin 4 × Fin 4), TorusRep a L (3 + σ) B Q.set
      (fun x => (((z n).z.e x p.1 p.2 : ℝ) : ℂ))) ∧
    (∀ n (q : Fin 4 × Fin 5 × Fin 5), TorusRep a L (3 + σ) B Q.set
      (fun x => (z n).z.A x q.1 q.2.1 q.2.2)) ∧
    (∀ n (i : Fin 2), TorusRep a L (3 + σ) B Q.set (fun x => (z n).z.H x i))

/-- **Uniform `C¹` Cauchy property of the bosonic fields on `Q`.** -/
def BosonicC1Cauchy (Q : ChartBox T) (z : ℕ → SmoothFields T left) : Prop :=
  UCauchyOn Q.set (fun n => (z n).z.e) ∧ (∀ μ, UCauchyOn Q.set (fun n => pd (z n).z.e μ)) ∧
    UCauchyOn Q.set (fun n => (z n).z.A) ∧ (∀ μ, UCauchyOn Q.set (fun n => pd (z n).z.A μ)) ∧
    UCauchyOn Q.set (fun n => (z n).z.H) ∧ ∀ μ, UCauchyOn Q.set (fun n => pd (z n).z.H μ)

theorem BosonicC1Cauchy.comp {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    (h : BosonicC1Cauchy Q z) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    BosonicC1Cauchy Q (fun k => z (φ k)) :=
  ⟨h.1.comp hφ, fun μ => (h.2.1 μ).comp hφ, h.2.2.1.comp hφ, fun μ => (h.2.2.2.1 μ).comp hφ,
    h.2.2.2.2.1.comp hφ, fun μ => (h.2.2.2.2.2 μ).comp hφ⟩

/-! ### Components -/

theorem UCauchyOn.congr {F : Type*} [NormedAddCommGroup F] {S : Set E4} {u v : ℕ → E4 → F}
    (h : UCauchyOn S u) (he : ∀ n, ∀ x ∈ S, u n x = v n x) : UCauchyOn S v := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun m n hm hn x hx => by rw [← he m x hx, ← he n x hx]; exact hN m n hm hn x hx⟩

theorem UCauchyOn.real_of_complex {S : Set E4} {u : ℕ → E4 → ℝ}
    (h : UCauchyOn S (fun n x => ((u n x : ℝ) : ℂ))) : UCauchyOn S u := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun m n hm hn x hx => ?_⟩
  have := hN m n hm hn x hx
  rwa [← Complex.ofReal_sub, Complex.norm_real] at this

theorem UCauchyOn.clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {S : Set E4} {u : ℕ → E4 → F} (h : UCauchyOn S u)
    (L : F →L[ℝ] G) : UCauchyOn S (fun n x => L (u n x)) := fun ε hε => by
  obtain ⟨N, hN⟩ := h (ε / (‖L‖ + 1)) (by positivity)
  refine ⟨N, fun m n hm hn x hx => ?_⟩
  rw [← map_sub]
  refine (L.le_opNorm _).trans ?_
  have := hN m n hm hn x hx
  calc ‖L‖ * ‖u m x - u n x‖ ≤ ‖L‖ * (ε / (‖L‖ + 1)) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg L]

/-- Fields smooth on the cylinder are bounded on the box. -/
theorem bounded_on_box {F : Type*} [NormedAddCommGroup F] (Q : ChartBox T) {f : E4 → F}
    (hf : ContinuousOn f (cylSlab T)) : ∃ C, ∀ x ∈ Q.set, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := Q.isCompact_closure.exists_bound_of_continuousOn
    (hf.mono Q.closure_subset_cylSlab)
  exact ⟨C, fun x hx => hC x (subset_closure hx)⟩

theorem mem_cylSlab_of_box (Q : ChartBox T) {x : E4} (hx : x ∈ Q.set) : x ∈ cylSlab T :=
  Q.closure_subset_cylSlab (subset_closure hx)

/-! ### Extraction (L3) -/

/-- The components of the bosonic fields. -/
abbrev Comp := (Fin 4 × Fin 4) ⊕ ((Fin 4 × Fin 5 × Fin 5) ⊕ Fin 2)

/-- The scalar component functions. -/
def compFun (w : SmoothFields T left) : Comp → E4 → ℂ
  | .inl p => fun x => ((w.z.e x p.1 p.2 : ℝ) : ℂ)
  | .inr (.inl q) => fun x => w.z.A x q.1 q.2.1 q.2.2
  | .inr (.inr i) => fun x => w.z.H x i

theorem differentiableAt_compFun (w : SmoothFields T left) (c : Comp) {x : E4}
    (hx : x ∈ cylSlab T) : DifferentiableAt ℝ (compFun w c) x := by
  rcases c with p | q | i
  · exact (coframeEntryL p.1 p.2).differentiableAt.comp x
      (differentiableAt_of_contDiffOn_slab w.smooth_e hx)
  · exact (connEntryL q.1 q.2.1 q.2.2).differentiableAt.comp x
      (differentiableAt_of_contDiffOn_slab w.smooth_A hx)
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) i).differentiableAt.comp x
      (differentiableAt_of_contDiffOn_slab w.smooth_H hx)

/-- `C¹` Cauchy property of one component along a subsequence. -/
def CompC1 (Q : ChartBox T) (z : ℕ → SmoothFields T left) (c : Comp) (s : ℕ → ℕ) : Prop :=
  UCauchyOn Q.set (fun k => compFun (z (s k)) c) ∧
    ∀ i, UCauchyOn Q.set (fun k => pd (compFun (z (s k)) c) i)

theorem exists_subseq_compC1 (Q : ChartBox T) (a : E4) {L σ B : ℝ} (hL : 0 < L) (hσ : 0 < σ)
    {z : ℕ → SmoothFields T left} (hbos : RegularBosonicBound Q a L σ B z) (c : Comp)
    (s : ℕ → ℕ) : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CompC1 Q z c (s ∘ ψ) := by
  have hrep : ∀ n, TorusRep a L (3 + σ) B Q.set (compFun (z (s n)) c) := by
    intro n
    rcases c with p | q | i
    · exact hbos.1 _ p
    · exact hbos.2.1 _ q
    · exact hbos.2.2 _ i
  obtain ⟨φ, hφ, h1, h2⟩ := exists_subseq_C1_cauchy a hL (by linarith) Q.isOpen hrep
    (fun n x hx => differentiableAt_compFun _ c (mem_cylSlab_of_box Q hx))
  exact ⟨φ, hφ, h1, h2⟩

/-- **L3: `C¹` extraction.**  Under `eq:regular-bosonic-bound`, every subsequence has a further
subsequence along which the bosonic fields and their first partial derivatives are uniformly
Cauchy on `Q`. -/
theorem exists_subseq_bosonicC1 (Q : ChartBox T) (a : E4) {L σ B : ℝ} (hL : 0 < L) (hσ : 0 < σ)
    {z : ℕ → SmoothFields T left} (hbos : RegularBosonicBound Q a L σ B z) (ns : ℕ → ℕ)
    (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ BosonicC1Cauchy Q (fun k => z (ns (ψ k))) := by
  classical
  set E := Fintype.equivFin Comp
  set P : ℕ → (ℕ → ℕ) → Prop := fun m s => ∀ h : m < Fintype.card Comp,
    CompC1 Q z (E.symm ⟨m, h⟩) (ns ∘ s)
  obtain ⟨D, hD, hPD⟩ := exists_diagonal_subseq P
    (fun m s hs => by
      by_cases hm : m < Fintype.card Comp
      · obtain ⟨ψ, hψ, hc⟩ := exists_subseq_compC1 Q a hL hσ hbos (E.symm ⟨m, hm⟩) (ns ∘ s)
        exact ⟨ψ, hψ, fun _ => hc⟩
      · exact ⟨id, strictMono_id, fun h => absurd h hm⟩)
    (fun m s ψ hψ hP h => ⟨(hP h).1.comp hψ, fun i => ((hP h).2 i).comp hψ⟩)
    (fun m s k hs hP h => ⟨(hP h).1.of_tail, fun i => ((hP h).2 i).of_tail⟩)
  have hall : ∀ c : Comp, CompC1 Q z c (ns ∘ D) := fun c => by
    have := hPD (E c) (E c).2
    simpa using this
  refine ⟨D, hD, ?_⟩
  have hsm := fun k => (z (ns (D k)))
  -- assemble the fibre-valued fields
  have hdiff : ∀ k (c : Comp) (i : Fin 4) x, x ∈ Q.set →
      pd (compFun (z (ns (D k))) c) i x = match c with
        | .inl p => ((pd (z (ns (D k))).z.e i x p.1 p.2 : ℝ) : ℂ)
        | .inr (.inl q) => pd (z (ns (D k))).z.A i x q.1 q.2.1 q.2.2
        | .inr (.inr j) => pd (z (ns (D k))).z.H i x j := by
    intro k c i x hx
    have hxs := mem_cylSlab_of_box Q hx
    rcases c with p | q | j
    · exact pd_clm_comp (differentiableAt_of_contDiffOn_slab (z (ns (D k))).smooth_e hxs)
        (coframeEntryL p.1 p.2) i
    · exact pd_clm_comp (differentiableAt_of_contDiffOn_slab (z (ns (D k))).smooth_A hxs)
        (connEntryL q.1 q.2.1 q.2.2) i
    · exact pd_clm_comp (differentiableAt_of_contDiffOn_slab (z (ns (D k))).smooth_H hxs)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) j) i
  refine ⟨?_, fun μ => ?_, ?_, fun μ => ?_, ?_, fun μ => ?_⟩
  · exact UCauchyOn.pi fun p => UCauchyOn.pi fun q =>
      UCauchyOn.real_of_complex (hall (.inl (p, q))).1
  · refine UCauchyOn.pi fun p => UCauchyOn.pi fun q => UCauchyOn.real_of_complex ?_
    exact ((hall (.inl (p, q))).2 μ).congr fun k x hx => hdiff k (.inl (p, q)) μ x hx
  · exact UCauchyOn.pi fun ν => UCauchyOn.pi fun i => UCauchyOn.pi fun j =>
      (hall (.inr (.inl (ν, i, j)))).1
  · exact UCauchyOn.pi fun ν => UCauchyOn.pi fun i => UCauchyOn.pi fun j =>
      ((hall (.inr (.inl (ν, i, j)))).2 μ).congr fun k x hx =>
        hdiff k (.inr (.inl (ν, i, j))) μ x hx
  · exact UCauchyOn.pi fun i => (hall (.inr (.inr i))).1
  · exact UCauchyOn.pi fun i => ((hall (.inr (.inr i))).2 μ).congr fun k x hx =>
      hdiff k (.inr (.inr i)) μ x hx


/-! ### The packets (L1) -/

section Packets

variable (Q : ChartBox T) {z : ℕ → SmoothFields T left}

theorem memLp_box {F : Type*} [NormedAddCommGroup F] {f : E4 → F}
    (hf : ContinuousOn f (cylSlab T)) (p : ℝ≥0∞) : MemLp f p Q.μ :=
  memLp_of_continuousOn_closure Q.isOpen Q.isCompact_closure (hf.mono Q.closure_subset_cylSlab) p

theorem continuousOn_pd_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E4 → F} (hf : ContDiffOn ℝ ∞ f (cylSlab T))
    (L : F →L[ℝ] G) (i : Fin 4) : ContinuousOn (fun x => pd (fun y => L (f y)) i x) (cylSlab T) :=
  continuousOn_pd_slab (L.contDiff.comp_contDiffOn hf) i

theorem continuous_comm2 : Continuous fun p : LieFibre × LieFibre => comm p.1 p.2 := by
  unfold comm mmul; fun_prop

theorem continuous_higgsAct2 : Continuous fun p : LieFibre × HiggsFibre => higgsAct p.1 p.2 := by
  refine continuous_pi fun i => ?_
  simp only [higgsAct]
  fun_prop

theorem continuousOn_curvatureF {A : E4 → ConnFibre} (hA : ContDiffOn ℝ ∞ A (cylSlab T)) :
    ContinuousOn (curvatureF A) (cylSlab T) := by
  have h1 : ∀ ν : Fin 4, ContDiffOn ℝ ∞ (fun y => A y ν) (cylSlab T) := fun ν =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => LieFibre) ν).contDiff.comp_contDiffOn
      hA
  have hc : ∀ ν : Fin 4, ContinuousOn (fun y => A y ν) (cylSlab T) := fun ν => (h1 ν).continuousOn
  have e : curvatureF A = fun x μ ν => pd (fun y => A y ν) μ x - pd (fun y => A y μ) ν x +
      comm (A x μ) (A x ν) := rfl
  rw [e]
  refine continuousOn_pi.mpr fun μ => continuousOn_pi.mpr fun ν => ?_
  have k1 := continuousOn_pd_slab (h1 ν) μ
  have k2 := continuousOn_pd_slab (h1 μ) ν
  have k3 := continuous_comm2.comp_continuousOn ((hc μ).prodMk (hc ν))
  exact (k1.sub k2).add k3

theorem continuousOn_covDerivHiggs {A : E4 → ConnFibre} {H : E4 → HiggsFibre}
    (hA : ContDiffOn ℝ ∞ A (cylSlab T)) (hH : ContDiffOn ℝ ∞ H (cylSlab T)) :
    ContinuousOn (covDerivHiggs A H) (cylSlab T) := by
  have e : covDerivHiggs A H = fun x μ => pd H μ x + higgsAct (A x μ) (H x) := rfl
  rw [e]
  refine continuousOn_pi.mpr fun μ => ?_
  have hc : ContinuousOn (fun y => A y μ) (cylSlab T) :=
    (continuous_apply μ).comp_continuousOn hA.continuousOn
  exact (continuousOn_pd_slab hH μ).add
    (continuous_higgsAct2.comp_continuousOn (hc.prodMk hH.continuousOn))

/-- The curvature components on the box in terms of the `C¹` data. -/
theorem curvatureF_entry (w : SmoothFields T left) {x : E4} (hx : x ∈ Q.set) (μ ν : Fin 4)
    (i j : Fin 5) : curvatureF w.z.A x μ ν i j = connEntryL ν i j (pd w.z.A μ x) -
      connEntryL μ i j (pd w.z.A ν x) + commEntryL μ ν i j (w.z.A x) (w.z.A x) := by
  have hd := differentiableAt_of_contDiffOn_slab w.smooth_A (mem_cylSlab_of_box Q hx)
  have e1 := pd_clm_comp hd (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => LieFibre) ν) μ
  have e2 := pd_clm_comp hd (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => LieFibre) μ) ν
  simp only [ContinuousLinearMap.proj_apply] at e1 e2
  simp only [curvatureF, e1, e2, connEntryL, commEntryL, Pi.add_apply, Pi.sub_apply]
  rfl

theorem ucauchy_A_bound (hC1 : BosonicC1Cauchy Q z) :
    ∃ CA, ∀ n, ∀ x ∈ Q.set, ‖(z n).z.A x‖ ≤ CA :=
  hC1.2.2.1.bounded fun n => bounded_on_box Q (z n).smooth_A.continuousOn

theorem ucauchy_H_bound (hC1 : BosonicC1Cauchy Q z) :
    ∃ CH, ∀ n, ∀ x ∈ Q.set, ‖(z n).z.H x‖ ≤ CH :=
  hC1.2.2.2.2.1.bounded fun n => bounded_on_box Q (z n).smooth_H.continuousOn

theorem ucauchy_curvatureF (hC1 : BosonicC1Cauchy Q z) :
    UCauchyOn Q.set (fun n => curvatureF (z n).z.A) := by
  obtain ⟨CA, hCA⟩ := ucauchy_A_bound Q hC1
  refine UCauchyOn.pi fun μ => UCauchyOn.pi fun ν => UCauchyOn.pi fun i => UCauchyOn.pi fun j => ?_
  refine ((((hC1.2.2.2.1 μ).clm (connEntryL ν i j)).sub ((hC1.2.2.2.1 ν).clm
    (connEntryL μ i j))).add (UCauchyOn.bilin (commEntryL μ ν i j) hC1.2.2.1 hC1.2.2.1 hCA hCA)).congr
    fun n x hx => (curvatureF_entry Q (z n) hx μ ν i j).symm

theorem ucauchy_covDerivHiggs (hC1 : BosonicC1Cauchy Q z) :
    UCauchyOn Q.set (fun n => covDerivHiggs (z n).z.A (z n).z.H) := by
  obtain ⟨CA, hCA⟩ := ucauchy_A_bound Q hC1
  obtain ⟨CH, hCH⟩ := ucauchy_H_bound Q hC1
  have hb := UCauchyOn.bilin higgsActL hC1.2.2.1 hC1.2.2.2.2.1 hCA hCH
  refine UCauchyOn.pi fun μ => ((hC1.2.2.2.2.2 μ).add (hb.component μ)).congr fun n x _ => rfl

theorem UCauchyOn.ofReal {S : Set E4} {u : ℕ → E4 → ℝ} (h : UCauchyOn S u) :
    UCauchyOn S (fun n x => ((u n x : ℝ) : ℂ)) := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun m n hm hn x hx => ?_⟩
  rw [← Complex.ofReal_sub, Complex.norm_real]
  exact hN m n hm hn x hx

theorem ucauchy_coframeC (hC1 : BosonicC1Cauchy Q z) :
    UCauchyOn Q.set (fun n => coframeC (z n).z.e) :=
  UCauchyOn.pi fun p => (((hC1.1.component p.1).component p.2).ofReal :
    UCauchyOn Q.set (fun n x => (((z n).z.e x p.1 p.2 : ℝ) : ℂ)))

theorem ucauchy_coframeGrad (hC1 : BosonicC1Cauchy Q z) :
    UCauchyOn Q.set (fun n => coframeGrad (z n).z.e) :=
  UCauchyOn.pi fun i => UCauchyOn.pi fun p =>
    ((((hC1.2.1 i).component p.1).component p.2).ofReal :
      UCauchyOn Q.set (fun n x => ((pd (z n).z.e i x p.1 p.2 : ℝ) : ℂ)))

theorem ucauchy_coframeJetPacket (hC1 : BosonicC1Cauchy Q z) :
    UCauchyOn Q.set (fun n => coframeJetPacket (z n).z.e) :=
  UCauchyOn.pi fun q => ((ucauchy_coframeGrad Q hC1).component q.1).component q.2

theorem ucauchy_curvaturePacket (hC1 : BosonicC1Cauchy Q z) :
    UCauchyOn Q.set (fun n => curvaturePacket (z n).z.A) :=
  UCauchyOn.pi fun q => ((((ucauchy_curvatureF Q hC1).component q.1).component q.2.1).component
    q.2.2.1).component q.2.2.2

theorem ucauchy_covGradPacket (hC1 : BosonicC1Cauchy Q z) :
    UCauchyOn Q.set (fun n => covGradPacket (z n).z.A (z n).z.H) :=
  UCauchyOn.pi fun q => ((ucauchy_covDerivHiggs Q hC1).component q.1).component q.2

theorem add_half_le {a b : ℝ≥0∞} {ε : ℝ} (hε : 0 < ε) (ha : a ≤ ENNReal.ofReal (ε / 2))
    (hb : b ≤ ENNReal.ofReal (ε / 2)) : a + b ≤ ENNReal.ofReal ε := by
  calc a + b ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add ha hb
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

set_option maxHeartbeats 1000000 in
/-- **L1: the reduced compactness certificate from `C¹` convergence.**  `C¹`-Cauchy bosonic
fields on `Q`, the coframe chart condition, strong spinor data and banks in a compact physical set
satisfy (R1)–(R5) of `def:reduced-certificate` on `Q`; the common compact screens are
consequences (`hasCommonCompactScreen_of_cauchy`). -/
theorem reducedCertificate_of_C1 {θ : ℕ → CoefficientBank Ysec} (hC1 : BosonicC1Cauchy Q z)
    (hch : CoframeChartCondition Q z) (hsp : SpinorStrongRoute Q z)
    (hbank : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P) : ReducedCertificate Q z θ := by
  have hsmA := fun n => (z n).smooth_A
  have hsmH := fun n => (z n).smooth_H
  have hsme := fun n => (z n).smooth_e
  have hH1 : H1Cauchy Q (fun n => coframeC (z n).z.e) (fun n => coframeGrad (z n).z.e) := by
    intro ε hε
    obtain ⟨N₁, h₁⟩ := lpCauchy_of_UCauchyOn Q (ucauchy_coframeC Q hC1) 2 (ε / 2) (by positivity)
    obtain ⟨N₂, h₂⟩ := lpCauchy_of_UCauchyOn Q (ucauchy_coframeGrad Q hC1) 2 (ε / 2)
      (by positivity)
    exact ⟨max N₁ N₂, fun m hm n hn => add_half_le hε (h₁ m (le_of_max_le_left hm) n
      (le_of_max_le_left hn)) (h₂ m (le_of_max_le_right hm) n (le_of_max_le_right hn))⟩
  have mJ : ∀ n, MemLp (coframeJetPacket (z n).z.e) 2 Q.μ := fun n => memLp_box Q
    (continuousOn_pi.mpr fun (q : Fin 4 × (Fin 4 × Fin 4)) => Complex.continuous_ofReal.comp_continuousOn
      (((continuous_apply q.2.2).comp (continuous_apply q.2.1)).comp_continuousOn
        (continuousOn_pd_slab (hsme n) q.1))) 2
  have mA4 : ∀ n, MemLp (z n).z.A 4 Q.μ := fun n => memLp_box Q (hsmA n).continuousOn 4
  have mF : ∀ n, MemLp (curvatureF (z n).z.A) 2 Q.μ := fun n =>
    memLp_box Q (continuousOn_curvatureF (hsmA n)) 2
  have mFP : ∀ n, MemLp (curvaturePacket (z n).z.A) 2 Q.μ := fun n => memLp_box Q
    (continuousOn_pi.mpr fun (q : Fin 4 × Fin 4 × Fin 5 × Fin 5) =>
      (((((continuous_apply q.2.2.2).comp (continuous_apply q.2.2.1)).comp
      (continuous_apply q.2.1)).comp (continuous_apply q.1)).comp_continuousOn
        (continuousOn_curvatureF (hsmA n)))) 2
  have mH : ∀ n, MemLp (z n).z.H 2 Q.μ := fun n => memLp_box Q (hsmH n).continuousOn 2
  have mK : ∀ n, MemLp (covDerivHiggs (z n).z.A (z n).z.H) 2 Q.μ := fun n =>
    memLp_box Q (continuousOn_covDerivHiggs (hsmA n) (hsmH n)) 2
  have mKP : ∀ n, MemLp (covGradPacket (z n).z.A (z n).z.H) 2 Q.μ := fun n => memLp_box Q
    (continuousOn_pi.mpr fun (q : Fin 4 × Fin 2) => (((continuous_apply q.2).comp
      (continuous_apply q.1)).comp_continuousOn (continuousOn_covDerivHiggs (hsmA n) (hsmH n)))) 2
  have f1 : H1Bounded Q (fun n => coframeC (z n).z.e) (fun n => coframeGrad (z n).z.e) :=
    (H1Cauchy.strong (fun n => memH1_coframe_of_smooth Q Q.isCompact_closure
      Q.closure_subset_cylSlab (hsme n)) hH1).1
  have f2 : HasCommonCompactScreen Q (fun n => coframeJetPacket (z n).z.e) :=
    hasCommonCompactScreen_of_cauchy Q mJ (lpCauchy_of_UCauchyOn Q (ucauchy_coframeJetPacket Q hC1) 2)
  have f3 : LpPrecompact 4 Q.μ (fun n => (z n).z.A) :=
    lpPrecompact_of_cauchy mA4 (lpCauchy_of_UCauchyOn Q hC1.2.2.1 4)
  have f4 : LpBounded 2 Q.μ (fun n => curvatureF (z n).z.A) :=
    (lpPrecompact_of_cauchy mF (lpCauchy_of_UCauchyOn Q (ucauchy_curvatureF Q hC1) 2)).lpBounded
      (by norm_num)
  have f5 : HasCommonCompactScreen Q (fun n => curvaturePacket (z n).z.A) :=
    hasCommonCompactScreen_of_cauchy Q mFP
      (lpCauchy_of_UCauchyOn Q (ucauchy_curvaturePacket Q hC1) 2)
  have f6 : LpBounded 2 Q.μ (fun n => (z n).z.H) :=
    (lpPrecompact_of_cauchy mH (lpCauchy_of_UCauchyOn Q hC1.2.2.2.2.1 2)).lpBounded (by norm_num)
  have f7 : LpBounded 2 Q.μ (fun n => covDerivHiggs (z n).z.A (z n).z.H) :=
    (lpPrecompact_of_cauchy mK (lpCauchy_of_UCauchyOn Q (ucauchy_covDerivHiggs Q hC1) 2)).lpBounded
      (by norm_num)
  have f8 : HasCommonCompactScreen Q (fun n => covGradPacket (z n).z.A (z n).z.H) :=
    hasCommonCompactScreen_of_cauchy Q mKP (lpCauchy_of_UCauchyOn Q (ucauchy_covGradPacket Q hC1) 2)
  exact ⟨hch, f1, f2, f3, f4, f5, f6, f7, f8, hsp.1.1, hsp.2.1, hbank⟩

/-- The coframes are precompact in `L^∞(Q)`. -/
theorem lpPrecompact_coframe_of_C1 (hC1 : BosonicC1Cauchy Q z) :
    LpPrecompact ⊤ Q.μ (fun n => (z n).z.e) :=
  lpPrecompact_of_cauchy (fun n => memLp_box Q (z n).smooth_e.continuousOn ⊤)
    (lpCauchy_of_UCauchyOn Q hC1.1 ⊤)

end Packets

end RegularBranch
end EinsteinSM
end RenewalGeometry
