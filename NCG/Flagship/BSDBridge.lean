/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# BSD common-source comparison bridge
  (`thm:BSD-bridge-master`, flagship manuscript)

* `kernel_dim_conjugation`: unitarily (indeed similarly)
  equivalent finite operators have equal kernel dimension — the
  physical-source completeness step turning the moment
  identification into equality of distinguished zero
  multiplicities;
* `bsd_bridge`: the bridge — if the analytic jet realization has
  nullity `min(r_an, m)` (the proved analytic-rank selector
  `thm:BSD-jet-master`), the independent Mordell–Weil/Selmer
  loading has zero space of dimension `r_alg`, the two minimal
  realizations are similar, and `m` exceeds both ranks, then
  `r_an = r_alg`.

Rendering disclosed: per the manuscript's BSD-scope firewall, the
all-order common-source moment identification (the hypothesis
`hjet` linking the conjugated loading to the analytic jet
nullity) is the missing arithmetic theorem — it is displayed
here, not claimed; the leading-coefficient, regulator, and
Tate–Shafarevich parts of BSD are beyond rank equality.
-/

open Matrix

namespace NCG

/-- Similar finite operators have equal kernel dimension: the
kernel of `U J U⁻¹` is the image of the kernel of `J` under the
invertible `U`. -/
theorem kernel_dim_conjugation {m : Type*} [Fintype m]
    [DecidableEq m] (J U : Matrix m m ℂ) (hU : IsUnit U.det) :
    Module.finrank ℂ
        (LinearMap.ker (U * J * U⁻¹).mulVecLin)
      = Module.finrank ℂ (LinearMap.ker J.mulVecLin) := by
  have hker : LinearMap.ker (U * J * U⁻¹).mulVecLin
      = Submodule.map U.mulVecLin
          (LinearMap.ker J.mulVecLin) := by
    ext v
    constructor
    · intro hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
      refine Submodule.mem_map.mpr
        ⟨U⁻¹.mulVec v, ?_, ?_⟩
      · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
          Matrix.mulVec_mulVec]
        have h2 := congrArg U⁻¹.mulVec hv
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
        rw [show U⁻¹ * (U * J * U⁻¹) = J * U⁻¹ by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hU,
            Matrix.one_mul]] at h2
        exact h2
      · rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
          Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
        show U * J * U⁻¹ * U = U * J by
          rw [Matrix.mul_assoc (U * J),
            Matrix.nonsing_inv_mul _ hU, Matrix.mul_one],
        ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  rw [hker]
  refine le_antisymm (Submodule.finrank_map_le _ _) ?_
  calc Module.finrank ℂ (LinearMap.ker J.mulVecLin)
      = Module.finrank ℂ (Submodule.map U⁻¹.mulVecLin
          (Submodule.map U.mulVecLin
            (LinearMap.ker J.mulVecLin))) := by
        rw [← Submodule.map_comp]
        have hcomp : U⁻¹.mulVecLin.comp U.mulVecLin
            = LinearMap.id := by
          refine LinearMap.ext fun v => ?_
          rw [LinearMap.comp_apply, Matrix.mulVecLin_apply,
            Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
            Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec,
            LinearMap.id_apply]
        rw [hcomp, Submodule.map_id]
    _ ≤ Module.finrank ℂ (Submodule.map U.mulVecLin
          (LinearMap.ker J.mulVecLin)) :=
        Submodule.finrank_map_le _ _

/-- `thm:BSD-bridge-master`: the moment identification (similar
minimal realizations, displayed) transfers the analytic jet
nullity `min(r_an, m)` to the algebraic zero dimension `r_alg`,
so `r_an = r_alg` once `m` exceeds both. -/
theorem bsd_bridge {m : Type*} [Fintype m] [DecidableEq m]
    (Jalg U : Matrix m m ℂ) (hU : IsUnit U.det)
    (ran ralg M : ℕ)
    (hjet : Module.finrank ℂ
        (LinearMap.ker (U * Jalg * U⁻¹).mulVecLin)
      = min ran M)
    (halg : Module.finrank ℂ
        (LinearMap.ker Jalg.mulVecLin) = ralg)
    (hran : ran < M) :
    ran = ralg := by
  have h := kernel_dim_conjugation Jalg U hU
  rw [hjet, halg] at h
  omega

end NCG
