/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.PressureGauge

/-!
# The Gallavotti–Cohen symmetry of the deficiency pressure
(GR_emergence, Phase 2)

`thm:renewal-gc-symmetry`: under single-affinity local detailed
balance, the tilted Perron pressure satisfies
`Λ_B(χ) = Λ_B(-𝒜 - χ)`.

The mechanism is a similarity: detailed balance says the tilted
kernel at `χ` is carried to the *transpose* of the tilted kernel at
`-𝒜 - χ` by the diagonal conjugation with the stationary law `π`.
The Gelfand–Fekete radius `pRad` is invariant under both operations
(`pRad_transpose` below and the pre-existing `pRad_diag_conj`), so
the pressures agree.

* `entrySum_transpose`, `growthSeq_transpose`, `pRad_transpose`,
  `hasDiagWitness_transpose` — transpose invariance of the pressure
  data;
* `pRad_of_detailed_balance` — the abstract similarity form: if
  `π_x M_{xy} = π_y M'_{yx}` entrywise with `π > 0`, then
  `pRad M' = pRad M`;
* `tiltedKernel`, `gallavotti_cohen_symmetry` — the
  Gallavotti–Cohen symmetry for the tilted deficiency kernel:
  `pRad(M(-𝒜-χ)) = pRad(M(χ))`, i.e. `Λ_B(χ) = Λ_B(-𝒜-χ)` at the
  Perron level.  The rate-function and cumulant corollaries
  (`I_B(j) - I_B(-j) = -𝒜j`, the cumulant hierarchy) are the
  Legendre/analytic layer over this identity.
-/

namespace NCG

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## Transpose invariance of the pressure -/

omit [DecidableEq V] [Nonempty V] in
theorem entrySum_transpose (A : Matrix V V ℝ) :
    entrySum Aᵀ = entrySum A := by
  unfold entrySum
  have h1 : ∀ x y : V, Aᵀ x y = A y x := fun x y => rfl
  simp_rw [h1]
  exact Finset.sum_comm

omit [Nonempty V] in
theorem growthSeq_transpose (A : Matrix V V ℝ) (k : ℕ) :
    growthSeq Aᵀ k = growthSeq A k := by
  unfold growthSeq
  rw [← Matrix.transpose_pow, entrySum_transpose]

omit [Nonempty V] in
/-- The Gelfand–Fekete radius is transpose invariant. -/
theorem pRad_transpose (A : Matrix V V ℝ) : pRad Aᵀ = pRad A := by
  unfold pRad
  have h : (fun k : ℕ => growthSeq Aᵀ k / k)
      = fun k : ℕ => growthSeq A k / k := by
    funext k
    rw [growthSeq_transpose]
  rw [h]

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem entryNonneg_transpose {A : Matrix V V ℝ} (hA : EntryNonneg A) :
    EntryNonneg Aᵀ := fun x y => hA y x

omit [Nonempty V] in
theorem hasDiagWitness_transpose {A : Matrix V V ℝ}
    (hw : HasDiagWitness A) : HasDiagWitness Aᵀ := by
  obtain ⟨x, m, hm, hpos⟩ := hw
  refine ⟨x, m, hm, ?_⟩
  rw [← Matrix.transpose_pow]
  exact hpos

/-! ## The detailed-balance similarity -/

/-- **Abstract Gallavotti–Cohen mechanism**: if two nonnegative
kernels are related by the stationary detailed-balance similarity
`π_x M_{xy} = π_y M'_{yx}` with `π > 0`, they have the same Perron
radius. -/
theorem pRad_of_detailed_balance {M M' : Matrix V V ℝ}
    (pi : V → ℝ) (hpi : ∀ x, 0 < pi x)
    (hM : EntryNonneg M) (hw : HasDiagWitness M)
    (hDB : ∀ x y, pi x * M x y = pi y * M' y x) :
    pRad M' = pRad M := by
  have hsim : M' = Matrix.diagonal (fun x => (pi x)⁻¹) * Mᵀ
      * Matrix.diagonal (fun x => ((pi x)⁻¹)⁻¹) := by
    ext x y
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single y]
    · rw [Matrix.diagonal_mul, Matrix.transpose_apply,
        Matrix.diagonal_apply_eq, inv_inv]
      have h := hDB y x
      have hx := (hpi x).ne'
      field_simp
      linarith [h]
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ y) h
  rw [hsim]
  exact (pRad_diag_conj (entryNonneg_transpose hM)
    (hasDiagWitness_transpose hw) (fun x => (pi x)⁻¹)
    (fun x => inv_pos.mpr (hpi x))).trans (pRad_transpose M)

/-! ## `thm:renewal-gc-symmetry` -/

/-- The `χ`-tilted deficiency kernel `M(χ)_{xy} = W_{xy}·e^{χ b(x,y)}`. -/
noncomputable def tiltedKernel (W : Matrix V V ℝ) (b : V → V → ℝ)
    (chi : ℝ) : Matrix V V ℝ :=
  Matrix.of fun x y => W x y * Real.exp (chi * b x y)

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem tiltedKernel_nonneg {W : Matrix V V ℝ} (hW : EntryNonneg W)
    (b : V → V → ℝ) (chi : ℝ) :
    EntryNonneg (tiltedKernel W b chi) := by
  intro x y
  exact mul_nonneg (hW x y) (Real.exp_pos _).le

/-- `thm:renewal-gc-symmetry` (**Gallavotti–Cohen symmetry**): under
single-affinity local detailed balance
`π_x W_{xy} = π_y W_{yx} e^{𝒜 b(x,y)}` with antisymmetric deficiency
increment `b`, the tilted Perron radius obeys the fluctuation
symmetry `pRad(M(-𝒜-χ)) = pRad(M(χ))` — i.e. the physical-depth
pressure satisfies `Λ_B(χ) = Λ_B(-𝒜-χ)`. -/
theorem gallavotti_cohen_symmetry (W : Matrix V V ℝ)
    (b : V → V → ℝ) (pi : V → ℝ) (Aff chi : ℝ)
    (hW : EntryNonneg W) (hpi : ∀ x, 0 < pi x)
    (hanti : ∀ x y, b y x = -b x y)
    (hDB : ∀ x y, pi x * W x y
      = pi y * W y x * Real.exp (Aff * b x y))
    (hw : HasDiagWitness (tiltedKernel W b chi)) :
    pRad (tiltedKernel W b (-Aff - chi))
      = pRad (tiltedKernel W b chi) := by
  apply pRad_of_detailed_balance pi hpi
    (tiltedKernel_nonneg hW b chi) hw
  intro x y
  have hgoal : tiltedKernel W b chi x y
      = W x y * Real.exp (chi * b x y) := rfl
  have hgoal' : tiltedKernel W b (-Aff - chi) y x
      = W y x * Real.exp ((-Aff - chi) * b y x) := rfl
  rw [hgoal, hgoal']
  have h1 : Real.exp ((-Aff - chi) * b y x)
      = Real.exp ((Aff + chi) * b x y) := by
    rw [hanti x y]
    ring_nf
  rw [h1]
  have h2 := hDB x y
  calc pi x * (W x y * Real.exp (chi * b x y))
      = (pi x * W x y) * Real.exp (chi * b x y) := by ring
    _ = (pi y * W y x * Real.exp (Aff * b x y))
        * Real.exp (chi * b x y) := by rw [h2]
    _ = pi y * (W y x * (Real.exp (Aff * b x y)
        * Real.exp (chi * b x y))) := by ring
    _ = pi y * (W y x * Real.exp ((Aff + chi) * b x y)) := by
        rw [← Real.exp_add]
        ring_nf

end NCG
