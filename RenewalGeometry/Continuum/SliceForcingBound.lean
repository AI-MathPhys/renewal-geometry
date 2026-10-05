/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SlabMoserComposition

/-!
# Slice-wise forcing bounds (`lem:actual-jet-complete-forcing` at a single time)

Generic infrastructure (no renewal notions) for the first-exit argument of `prop:coupled-bootstrap`
of the Einstein–Standard-Model action-closure manuscript: inside the tube the chart-margin
condition is known only **at the current time**, so the derivative-counted forcing bound must be
applied slice by slice with a constant independent of the time.

* `sd_congr_slice`, **`Q_congr_slice`** — spatial word derivatives and the slice norms `Q_k(t)`
  only see the slice `{t} × ℝ^d`;
* **`slice_forcing_bound`** — `SlabMoser.writer_forcing_bound` with the chart-margin condition
  and the forcing identity required only on the slice at time `t` (the constant `C_M` does not
  depend on `t`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.SliceForcing

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy SlabMoser

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-- Spatial word derivatives of smooth functions agreeing on a slice agree on that slice. -/
theorem sd_congr_slice : ∀ (w : List (Fin d)) {f g : ST d → ℝ}, ContDiff ℝ ∞ f →
    ContDiff ℝ ∞ g → ∀ t : ℝ, (∀ y, f (Fin.cons t y) = g (Fin.cons t y)) →
    ∀ y, sd w f (Fin.cons t y) = sd w g (Fin.cons t y)
  | [], _, _, _, _, _, h => h
  | i :: w, f, g, hf, hg, t, h => by
    rw [sd_cons, sd_cons]
    refine sd_congr_slice w (contDiff_pd_top hf _) (contDiff_pd_top hg _) t fun y => ?_
    rw [← pd_slice i ((hf.differentiable (by simp)) _),
      ← pd_slice i ((hg.differentiable (by simp)) _)]
    have : (fun y => f (Fin.cons t y)) = fun y => g (Fin.cons t y) := funext h
    rw [this]

/-- **`Q_k(t)` only sees the slice at time `t`.** -/
theorem Q_congr_slice {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t : ℝ)
    (h : ∀ y, f (Fin.cons t y) = g (Fin.cons t y)) (k : ℕ) : Q k f t = Q k g t :=
  Q_congr fun w _ y => sd_congr_slice w hf hg t h y

/-- **The derivative-counted forcing bound on one slice** (`eq:actual-jet-complete-forcing`):
as `SlabMoser.writer_forcing_bound`, but the state is required to take values in the chart margin
`K` and the field `F` to agree with the forcing only on the slice `{t} × ℝ^d`; the constant `C_M`
is uniform in `t`. -/
theorem slice_forcing_bound {k m : ℕ} (hm : (d : ℝ) / 2 < m) (hk : 2 * m ≤ k + 1)
    {X Y YD Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [AddCommGroup Y] [Module ℝ Y]
    [AddCommGroup YD] [Module ℝ YD] [AddCommGroup Z] [Module ℝ Z] {a b : ℕ}
    (eX : (Fin n → ℝ) ≃L[ℝ] X) (eY : (Fin a → ℝ) →ₗ[ℝ] Y) (eYD : (Fin b → ℝ) →ₗ[ℝ] YD)
    (pZ : Z →ₗ[ℝ] ℝ) {O K : Set X} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (Bm : X → Y →ₗ[ℝ] Z) (Dm : X → YD →ₗ[ℝ] Z) (Qm : Fin d → X → YD →ₗ[ℝ] Z)
    (Gc G0 : X → (Fin 4 → ℝ) →ₗ[ℝ] Z) (Gj : Fin d → X → (Fin 4 → ℝ) →ₗ[ℝ] Z)
    (hB : ∀ y, ContDiffOn ℝ ∞ (fun x => pZ (Bm x y)) O)
    (hD : ∀ y, ContDiffOn ℝ ∞ (fun x => pZ (Dm x y)) O)
    (hQ : ∀ j y, ContDiffOn ℝ ∞ (fun x => pZ (Qm j x y)) O)
    (hGc : ∀ y, ContDiffOn ℝ ∞ (fun x => pZ (Gc x y)) O)
    (hG0 : ∀ y, ContDiffOn ℝ ∞ (fun x => pZ (G0 x y)) O)
    (hGj : ∀ j y, ContDiffOn ℝ ∞ (fun x => pZ (Gj j x y)) O) {R : ℝ} (hR : 0 ≤ R) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ u : Fin n → ST d → ℝ, (∀ i, ContDiff ℝ ∞ (u i)) →
      (∀ i, IsSPeriodic (u i)) → ∀ {RB : Fin a → ST d → ℝ} {RD : Fin b → ST d → ℝ}
      {C dtC : Fin 4 → ST d → ℝ}, (∀ i, ContDiff ℝ ∞ (RB i)) → (∀ i, ContDiff ℝ ∞ (RD i)) →
      (∀ l, ContDiff ℝ ∞ (C l)) → (∀ l, ContDiff ℝ ∞ (dtC l)) →
      (∀ i, IsSPeriodic (RB i)) → (∀ i, IsSPeriodic (RD i)) → (∀ l, IsSPeriodic (C l)) →
      (∀ l, IsSPeriodic (dtC l)) →
      ∀ t : ℝ, (∀ y : Fin d → ℝ, eX (fun i => u i (Fin.cons t y)) ∈ K) →
      energyQ k u t ≤ R ^ 2 → ∀ F : ST d → ℝ, ContDiff ℝ ∞ F →
      (∀ x : ST d, x 0 = t → F x =
        pZ (Bm (eX fun i => u i x) (eY fun i => RB i x)) +
        pZ (Dm (eX fun i => u i x) (eYD fun i => RD i x)) +
        ∑ j, pZ (Qm j (eX fun i => u i x) (eYD fun i => pd (RD i) j.succ x)) +
        pZ (Gc (eX fun i => u i x) fun l => C l x) +
        pZ (G0 (eX fun i => u i x) fun l => dtC l x) +
        ∑ j, pZ (Gj j (eX fun i => u i x) fun l => pd (C l) j.succ x)) →
      Q k F t ≤ CM * (∑ i, Q k (RB i) t + ∑ i, Q (k + 1) (RD i) t + ∑ l, Q (k + 1) (C l) t +
        ∑ l, Q k (dtC l) t) := by
  -- coefficient maps in coordinates, smooth on the open chart preimage
  set O' := eX ⁻¹' O with hO'
  set K' := eX ⁻¹' K with hK'
  have hO'o : IsOpen O' := hO.preimage eX.continuous
  have hK'c : IsCompact K' := by
    have := hK.image eX.symm.continuous
    rwa [hK', ← ContinuousLinearEquiv.image_symm_eq_preimage]
  have hK'O' : K' ⊆ O' := fun v hv => hKO hv
  have hsm : ∀ {f : X → ℝ}, ContDiffOn ℝ ∞ f O → ContDiffOn ℝ ∞ (fun v => f (eX v)) O' :=
    fun hf => hf.comp eX.contDiff.contDiffOn fun v hv => hv
  have hext : ∀ {f : X → ℝ}, ContDiffOn ℝ ∞ f O →
      ∃ f' : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ f' ∧ ∀ v ∈ K', f' v = f (eX v) :=
    fun hf => exists_contDiff_eqOn hO'o hK'c hK'O' (hsm hf)
  choose Φb hΦb hΦbK using fun i : Fin a => hext (hB (eY (Pi.single i 1)))
  choose Φd hΦd hΦdK using fun i : Fin b => hext (hD (eYD (Pi.single i 1)))
  choose Φq hΦq hΦqK using fun (p : Fin b) (j : Fin d) => hext (hQ j (eYD (Pi.single p 1)))
  choose Φc hΦc hΦcK using fun l : Fin 4 => hext (hGc (Pi.single l 1))
  choose Φc0 hΦc0 hΦc0K using fun l : Fin 4 => hext (hG0 (Pi.single l 1))
  choose Φcj hΦcj hΦcjK using fun (l : Fin 4) (j : Fin d) => hext (hGj j (Pi.single l 1))
  set Φbd : Fin a ⊕ Fin b → (Fin n → ℝ) → ℝ := Sum.elim Φb Φd with hΦbd
  have hΦbd' : ∀ i, ContDiff ℝ ∞ (Φbd i) := by
    intro i; rcases i with i | i
    · exact hΦb i
    · exact hΦd i
  obtain ⟨CM, hCM0, hCM⟩ := forcing_bound_comp (n := n) hm hk hΦbd' hΦq hΦc hΦc0 hΦcj hR
  refine ⟨2 * CM, by positivity, ?_⟩
  intro u hu hup RB RD C dtC hRB hRD hC hdtC pRB pRD pC pdtC t hK hEt F hF hFeq
  set RBD : Fin a ⊕ Fin b → ST d → ℝ := Sum.elim RB RD with hRBD
  have hRBD' : ∀ i, ContDiff ℝ ∞ (RBD i) := by
    intro i; rcases i with i | i
    · exact hRB i
    · exact hRD i
  have pRBD : ∀ i, IsSPeriodic (RBD i) := by
    intro i; rcases i with i | i
    · exact pRB i
    · exact pRD i
  have hbound := hCM u hu hup hRBD' hRD hC hdtC pRBD pRD pC pdtC t hEt
  have hFE : ContDiff ℝ ∞ (ActualJetForcing.forcingErr (fun i => compF (Φbd i) u) RBD
      (fun p j => compF (Φq p j) u) RD (fun l => compF (Φc l) u) (fun l => compF (Φc0 l) u)
      (fun l j => compF (Φcj l j) u) C dtC) := by
    unfold ActualJetForcing.forcingErr
    refine ContDiff.add (ContDiff.add (ContDiff.sum fun i _ => (contDiff_compF (hΦbd' i) hu).mul
      (hRBD' i)) (ContDiff.sum fun p _ => (contDiff_compF (hΦq p.1 p.2) hu).mul
      (contDiff_pd_top (hRD p.1) _))) (ContDiff.add (ContDiff.add (ContDiff.sum fun l _ =>
      (contDiff_compF (hΦc l) hu).mul (hC l)) (ContDiff.sum fun l _ =>
      (contDiff_compF (hΦc0 l) hu).mul (hdtC l))) (ContDiff.sum fun p _ =>
      (contDiff_compF (hΦcj p.1 p.2) hu).mul (contDiff_pd_top (hC p.1) _)))
  have hQeq : Q k F t = Q k (ActualJetForcing.forcingErr (fun i => compF (Φbd i) u) RBD
      (fun p j => compF (Φq p j) u) RD (fun l => compF (Φc l) u) (fun l => compF (Φc0 l) u)
      (fun l j => compF (Φcj l j) u) C dtC) t := by
    refine Q_congr_slice hF hFE t (fun y => ?_) k
    set x : ST d := Fin.cons t y with hxdef
    have hx : x 0 = t := rfl
    have hv : (fun i => u i x) ∈ K' := hK y
    rw [hFeq x hx]
    unfold ActualJetForcing.forcingErr
    simp only [compF]
    have e3 : pZ (Gc (eX fun i => u i x) fun l => C l x) =
        ∑ l, pZ (Gc (eX fun i => u i x) (Pi.single l 1)) * C l x :=
      linear_coord LinearMap.id (Gc _) pZ _
    have e4 : pZ (G0 (eX fun i => u i x) fun l => dtC l x) =
        ∑ l, pZ (G0 (eX fun i => u i x) (Pi.single l 1)) * dtC l x :=
      linear_coord LinearMap.id (G0 _) pZ _
    rw [linear_coord eY (Bm _) pZ, linear_coord eYD (Dm _) pZ, e3, e4]
    have e1 : ∀ j, pZ (Qm j (eX fun i => u i x) (eYD fun i => pd (RD i) j.succ x)) =
        ∑ p, pZ (Qm j (eX fun i => u i x) (eYD (Pi.single p 1))) * pd (RD p) j.succ x :=
      fun j => linear_coord eYD (Qm j _) pZ _
    have e2 : ∀ j, pZ (Gj j (eX fun i => u i x) fun l => pd (C l) j.succ x) =
        ∑ l, pZ (Gj j (eX fun i => u i x) (Pi.single l 1)) * pd (C l) j.succ x :=
      fun j => linear_coord LinearMap.id (Gj j _) pZ _
    simp only [e1, e2]
    rw [Fintype.sum_sum_type]
    simp only [hRBD, hΦbd, Sum.elim_inl, Sum.elim_inr]
    simp only [hΦbK _ _ hv, hΦdK _ _ hv, hΦqK _ _ _ hv, hΦcK _ _ hv, hΦc0K _ _ hv,
      hΦcjK _ _ _ hv]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
      Finset.sum_comm (s := Finset.univ (α := Fin d)),
      Finset.sum_comm (s := Finset.univ (α := Fin d))]
    ring
  rw [hQeq]
  refine hbound.trans ?_
  rw [Fintype.sum_sum_type]
  simp only [hRBD, Sum.elim_inl, Sum.elim_inr]
  have hDk : ∑ i, Q k (RD i) t ≤ ∑ i, Q (k + 1) (RD i) t :=
    Finset.sum_le_sum fun i _ => Q_mono (Nat.le_succ k) (RD i) t
  have h1 : 0 ≤ ∑ i, Q k (RB i) t := Finset.sum_nonneg fun i _ => Q_nonneg k _ t
  have h2 : 0 ≤ ∑ i, Q k (RD i) t := Finset.sum_nonneg fun i _ => Q_nonneg k _ t
  have h3 : 0 ≤ ∑ l, Q (k + 1) (C l) t := Finset.sum_nonneg fun i _ => Q_nonneg _ _ t
  have h4 : 0 ≤ ∑ l, Q k (dtC l) t := Finset.sum_nonneg fun i _ => Q_nonneg k _ t
  nlinarith

end RenewalGeometry.SliceForcing
