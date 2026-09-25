/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Normalized rational Hermitian dynamic functions and their Hankel form

Paper `predictive_spectral_geometry`, label `def:supp-rational-Hermitian`.

A normalized rational Hermitian dynamic function `Q` is encoded through its
Laurent coefficients at infinity,
`Q(z) = -∑_{n ≥ 0} M_n z^{-n-1}` with `M_n = M_n^*`
(`eq:supp-rational-Laurent`; the symmetry `Q(z̄)^* = Q(z)` of
`eq:supp-rational-symmetry` is exactly the Hermitian property of every `M_n`,
and `Q(∞) = 0` is the strict properness of the expansion).  Rationality is
encoded, following Kronecker's theorem, as finiteness of the Hankel rank:
the Pontryagin state space below is finite dimensional.

* `hankelColumn M j h = (M_{j+r} h)_{r ≥ 0}` is a Hankel column and
  `hankelColumnSpace M` is the span `𝒦_Q` of all Hankel columns.
* `hankelForm M` is the indefinite Hankel form
  `[c_i(u), c_j(v)]_Q = ⟪u, M_{i+j} v⟫` (`eq:supp-Hankel-form`), extended
  sesquilinearly to formal column combinations `ℕ →₀ H`
  (`hankelForm_single_single`).
* `hankelNull M` is its null space and `hankelState M` the quotient
  Pontryagin state space; `hankelNull_eq_ker` shows that the null space is
  exactly the kernel of the column map, so the quotient is canonically the
  literal column span `𝒦_Q` (`hankelStateEquivColumnSpace`).
* `hankelShift M` is `A_Q c_j(h) = c_{j+1}(h)` and `hankelSource M` is
  `Γ_Q h = c_0(h)`, both descended to the quotient
  (`hankelShift_mk_single`, `hankelSource_apply`).
* `NormalizedRationalHermitianData H` bundles the Hermitian coefficient
  sequence with the finite-rank (rationality) condition.
-/

open scoped InnerProductSpace

namespace RenewalGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Laurent series `Q(z) = -∑_{n ≥ 0} M_n z^{-n-1}` of
`eq:supp-rational-Laurent`, as a function of `z` (a `tsum`, which is the
rational function `Q` outside a disc when the Hankel rank is finite). -/
noncomputable def laurentDynamicFunction [FiniteDimensional ℂ H]
    (M : ℕ → H →ₗ[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  -∑' n : ℕ, (z⁻¹ ^ (n + 1)) • LinearMap.toContinuousLinearMap (M n)

/-- The Hankel column `c_j(h) = (M_{j+r} h)_{r ≥ 0}` of
`def:supp-rational-Hermitian`. -/
def hankelColumn (M : ℕ → H →ₗ[ℂ] H) (j : ℕ) (h : H) : ℕ → H :=
  fun r => M (j + r) h

/-- The column `c_j` as a linear map `H → (ℕ → H)`. -/
def hankelColumnLinear (M : ℕ → H →ₗ[ℂ] H) (j : ℕ) : H →ₗ[ℂ] (ℕ → H) :=
  LinearMap.pi fun r => M (j + r)

@[simp] theorem hankelColumnLinear_apply (M : ℕ → H →ₗ[ℂ] H) (j : ℕ) (h : H) :
    hankelColumnLinear M j h = hankelColumn M j h := rfl

/-- The formal-to-literal column map: a formal combination `∑_j c_j(u_j)`
(an element of `ℕ →₀ H`) is sent to the sequence `∑_j c_j(u_j) ∈ ℕ → H`. -/
noncomputable def hankelColumnMap (M : ℕ → H →ₗ[ℂ] H) :
    (ℕ →₀ H) →ₗ[ℂ] (ℕ → H) :=
  Finsupp.lsum ℂ fun j => hankelColumnLinear M j

@[simp] theorem hankelColumnMap_single (M : ℕ → H →ₗ[ℂ] H) (j : ℕ) (h : H) :
    hankelColumnMap M (Finsupp.single j h) = hankelColumn M j h := by
  simp [hankelColumnMap, Finsupp.lsum_single]

/-- `𝒦_Q`: the span of all Hankel columns (the range of the column map). -/
noncomputable def hankelColumnSpace (M : ℕ → H →ₗ[ℂ] H) : Submodule ℂ (ℕ → H) :=
  LinearMap.range (hankelColumnMap M)

theorem hankelColumn_mem_hankelColumnSpace (M : ℕ → H →ₗ[ℂ] H) (j : ℕ) (h : H) :
    hankelColumn M j h ∈ hankelColumnSpace M :=
  ⟨Finsupp.single j h, hankelColumnMap_single M j h⟩

/-- The span of the Hankel columns is the range of the column map. -/
theorem hankelColumnSpace_eq_span (M : ℕ → H →ₗ[ℂ] H) :
    hankelColumnSpace M =
      Submodule.span ℂ (Set.range fun p : ℕ × H => hankelColumn M p.1 p.2) := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
    | single j h =>
        rw [hankelColumnMap_single]
        exact Submodule.subset_span ⟨(j, h), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hankelColumn_mem_hankelColumnSpace M p.1 p.2

/-- One conjugate-linear slice of the Hankel form:
`u ↦ (v ↦ ∑_j ⟪u, M_{i+j} v_j⟫)`. -/
noncomputable def hankelFormSlice (M : ℕ → H →ₗ[ℂ] H) (i : ℕ) :
    H →ₗ⋆[ℂ] ((ℕ →₀ H) →ₗ[ℂ] ℂ) where
  toFun u := Finsupp.lsum ℂ fun j => (innerₛₗ ℂ u).comp (M (i + j))
  map_add' u u' := by
    apply Finsupp.lhom_ext
    intro j h
    simp [Finsupp.lsum_single]
  map_smul' c u := by
    apply Finsupp.lhom_ext
    intro j h
    simp [Finsupp.lsum_single]

/-- **`eq:supp-Hankel-form`.**  The indefinite Hankel form
`[c_i(u), c_j(v)]_Q = ⟪u, M_{i+j} v⟫`, extended sesquilinearly to formal
column combinations. -/
noncomputable def hankelForm (M : ℕ → H →ₗ[ℂ] H) :
    (ℕ →₀ H) →ₗ⋆[ℂ] ((ℕ →₀ H) →ₗ[ℂ] ℂ) :=
  Finsupp.lsum ℂ fun i => hankelFormSlice M i

/-- The defining formula of the Hankel form on two Hankel columns. -/
theorem hankelForm_single_single (M : ℕ → H →ₗ[ℂ] H) (i j : ℕ) (u v : H) :
    hankelForm M (Finsupp.single i u) (Finsupp.single j v) = ⟪u, M (i + j) v⟫_ℂ := by
  simp [hankelForm, hankelFormSlice, Finsupp.lsum_single]

/-- For Hermitian coefficients, the Hankel form is the pairing of the literal
column sequence against the formal coefficients:
`[u, v]_Q = ∑_j ⟪(∑_i c_i(u_i))_j, v_j⟫`. -/
theorem hankelForm_eq_column_pairing (M : ℕ → H →ₗ[ℂ] H)
    (hM : ∀ n, (M n).IsSymmetric) (u v : ℕ →₀ H) :
    hankelForm M u v =
      Finsupp.lsum ℂ (fun j => innerₛₗ ℂ (hankelColumnMap M u j)) v := by
  induction u using Finsupp.induction_linear with
  | zero => simp [hankelForm, Finsupp.sum]
  | add u u' hu hu' =>
      rw [map_add, LinearMap.add_apply, hu, hu', map_add]
      have : (Finsupp.lsum ℂ fun j =>
          innerₛₗ ℂ ((hankelColumnMap M u + hankelColumnMap M u') j)) =
          (Finsupp.lsum ℂ fun j => innerₛₗ ℂ (hankelColumnMap M u j)) +
          (Finsupp.lsum ℂ fun j => innerₛₗ ℂ (hankelColumnMap M u' j)) := by
        apply Finsupp.lhom_ext
        intro j h
        simp [Finsupp.lsum_single]
      rw [this, LinearMap.add_apply]
  | single i x =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v v' hv hv' => rw [map_add, map_add, hv, hv']
      | single j y =>
          rw [hankelForm_single_single, hankelColumnMap_single]
          simp [Finsupp.lsum_single, hankelColumn, hM (i + j) x y]

/-- The null space of the Hankel form (its left radical). -/
noncomputable def hankelNull (M : ℕ → H →ₗ[ℂ] H) : Submodule ℂ (ℕ →₀ H) :=
  LinearMap.ker (hankelForm M)

theorem mem_hankelNull_iff (M : ℕ → H →ₗ[ℂ] H) (u : ℕ →₀ H) :
    u ∈ hankelNull M ↔ ∀ v, hankelForm M u v = 0 := by
  simp only [hankelNull, LinearMap.mem_ker]
  constructor
  · intro h v; rw [h]; rfl
  · intro h; exact LinearMap.ext h

/-- **Null space = kernel of the column map.**  For Hermitian coefficients a
formal combination is null for the Hankel form exactly when its literal
column sequence vanishes, so "quotienting the null space" identifies the
Pontryagin state space with the literal column span `𝒦_Q`. -/
theorem hankelNull_eq_ker (M : ℕ → H →ₗ[ℂ] H) (hM : ∀ n, (M n).IsSymmetric) :
    hankelNull M = LinearMap.ker (hankelColumnMap M) := by
  ext u
  rw [mem_hankelNull_iff, LinearMap.mem_ker]
  constructor
  · intro h
    funext j
    have hj := h (Finsupp.single j (hankelColumnMap M u j))
    rw [hankelForm_eq_column_pairing M hM] at hj
    simp only [Finsupp.lsum_single, innerₛₗ_apply_apply] at hj
    exact inner_self_eq_zero.mp hj
  · intro h v
    rw [hankelForm_eq_column_pairing M hM, h]
    simp [Finsupp.lsum_apply, Finsupp.sum]

/-- The Pontryagin state space of `def:supp-rational-Hermitian`: formal column
combinations modulo the null space of the Hankel form. -/
abbrev hankelState (M : ℕ → H →ₗ[ℂ] H) := (ℕ →₀ H) ⧸ hankelNull M

/-- The state space is canonically the literal column span `𝒦_Q`. -/
noncomputable def hankelStateEquivColumnSpace (M : ℕ → H →ₗ[ℂ] H)
    (hM : ∀ n, (M n).IsSymmetric) :
    hankelState M ≃ₗ[ℂ] hankelColumnSpace M :=
  (Submodule.quotEquivOfEq _ _ (hankelNull_eq_ker M hM)).trans
    (hankelColumnMap M).quotKerEquivRange

/-- The Hankel form is Hermitian symmetric for Hermitian coefficients. -/
theorem hankelForm_conj_symm (M : ℕ → H →ₗ[ℂ] H) (hM : ∀ n, (M n).IsSymmetric)
    (u v : ℕ →₀ H) :
    hankelForm M v u = starRingEnd ℂ (hankelForm M u v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' => simp [hu, hu']
  | single i x =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v v' hv hv' => simp [hv, hv']
      | single j y =>
          rw [hankelForm_single_single, hankelForm_single_single, inner_conj_symm,
            Nat.add_comm j i]
          exact (hM (i + j) y x).symm

/-- The descended Hankel form on the state space (well defined because the
null space is two-sided by `hankelForm_conj_symm`). -/
noncomputable def hankelStateForm (M : ℕ → H →ₗ[ℂ] H) (hM : ∀ n, (M n).IsSymmetric) :
    hankelState M → hankelState M → ℂ :=
  Quotient.lift₂ (fun u v => hankelForm M u v) (by
    intro u v u' v' huu' hvv'
    have hu : u - u' ∈ hankelNull M := (Submodule.quotientRel_def _).mp huu'
    have hv : v - v' ∈ hankelNull M := (Submodule.quotientRel_def _).mp hvv'
    rw [mem_hankelNull_iff] at hu hv
    have h1 : hankelForm M u v = hankelForm M u' v := by
      have := hu v
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
      exact this
    have h2 : hankelForm M u' v = hankelForm M u' v' := by
      have := hv u'
      rw [hankelForm_conj_symm M hM, map_sub, map_sub, sub_eq_zero] at this
      exact (starRingEnd ℂ).injective this
    exact h1.trans h2)

@[simp] theorem hankelStateForm_mk (M : ℕ → H →ₗ[ℂ] H) (hM : ∀ n, (M n).IsSymmetric)
    (u v : ℕ →₀ H) :
    hankelStateForm M hM (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      hankelForm M u v := rfl

/-- The formal shift `c_j(h) ↦ c_{j+1}(h)` on formal column combinations. -/
noncomputable def hankelFormalShift : (ℕ →₀ H) →ₗ[ℂ] (ℕ →₀ H) :=
  Finsupp.lmapDomain H ℂ (· + 1)

@[simp] theorem hankelFormalShift_single (j : ℕ) (h : H) :
    hankelFormalShift (Finsupp.single j h) = Finsupp.single (j + 1) (h : H) := by
  simp [hankelFormalShift, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The literal column of a shifted formal combination is the sequence shift:
`c(shift u)_r = c(u)_{r+1}`. -/
theorem hankelColumnMap_shift (M : ℕ → H →ₗ[ℂ] H) (u : ℕ →₀ H) (r : ℕ) :
    hankelColumnMap M (hankelFormalShift u) r = hankelColumnMap M u (r + 1) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single j h =>
      simp only [hankelFormalShift_single, hankelColumnMap_single, hankelColumn]
      rw [Nat.add_assoc, Nat.add_comm 1 r]

/-- The formal shift preserves the null space (Hankel structure
`M_{(i+1)+j} = M_{i+(j+1)}`). -/
theorem hankelFormalShift_null_le (M : ℕ → H →ₗ[ℂ] H) (hM : ∀ n, (M n).IsSymmetric) :
    hankelNull M ≤ (hankelNull M).comap hankelFormalShift := by
  intro u hu
  rw [hankelNull_eq_ker M hM, LinearMap.mem_ker] at hu
  rw [Submodule.mem_comap, hankelNull_eq_ker M hM, LinearMap.mem_ker]
  funext r
  rw [hankelColumnMap_shift, hu]
  rfl

/-- **`A_Q`**: the shift `A_Q c_j(h) = c_{j+1}(h)` on the Pontryagin state
space of `def:supp-rational-Hermitian`. -/
noncomputable def hankelShift (M : ℕ → H →ₗ[ℂ] H) (hM : ∀ n, (M n).IsSymmetric) :
    hankelState M →ₗ[ℂ] hankelState M :=
  (hankelNull M).mapQ (hankelNull M) hankelFormalShift (hankelFormalShift_null_le M hM)

theorem hankelShift_mk_single (M : ℕ → H →ₗ[ℂ] H) (hM : ∀ n, (M n).IsSymmetric)
    (j : ℕ) (h : H) :
    hankelShift M hM (Submodule.Quotient.mk (Finsupp.single j h)) =
      Submodule.Quotient.mk (Finsupp.single (j + 1) h) := by
  simp [hankelShift, Submodule.mapQ_apply]

/-- **`Γ_Q`**: the source `Γ_Q h = c_0(h)` on the Pontryagin state space. -/
noncomputable def hankelSource (M : ℕ → H →ₗ[ℂ] H) : H →ₗ[ℂ] hankelState M :=
  (hankelNull M).mkQ.comp (Finsupp.lsingle 0)

theorem hankelSource_apply (M : ℕ → H →ₗ[ℂ] H) (h : H) :
    hankelSource M h = Submodule.Quotient.mk (Finsupp.single 0 h) := rfl

/-- Iterating the shift on the source produces every Hankel column
`A_Q^j Γ_Q h = c_j(h)`. -/
theorem hankelShift_pow_source (M : ℕ → H →ₗ[ℂ] H) (hM : ∀ n, (M n).IsSymmetric)
    (j : ℕ) (h : H) :
    ((hankelShift M hM) ^ j) (hankelSource M h) =
      Submodule.Quotient.mk (Finsupp.single j h) := by
  induction j with
  | zero => simp [hankelSource_apply]
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hankelShift_mk_single]

/-- The Hankel form reads the Laurent coefficients off the state space:
`[A_Q^i Γ_Q u, A_Q^j Γ_Q v]_Q = ⟪u, M_{i+j} v⟫`. -/
theorem hankelStateForm_shift_pow_source (M : ℕ → H →ₗ[ℂ] H)
    (hM : ∀ n, (M n).IsSymmetric) (i j : ℕ) (u v : H) :
    hankelStateForm M hM (((hankelShift M hM) ^ i) (hankelSource M u))
      (((hankelShift M hM) ^ j) (hankelSource M v)) = ⟪u, M (i + j) v⟫_ℂ := by
  rw [hankelShift_pow_source, hankelShift_pow_source, hankelStateForm_mk,
    hankelForm_single_single]

/-- **`def:supp-rational-Hermitian`.**  A normalized rational Hermitian dynamic
function, encoded by its Laurent coefficients `M_n = M_n^*` at infinity
(`eq:supp-rational-Laurent`, which is `eq:supp-rational-symmetry`), with
rationality encoded as finite Hankel rank: the Pontryagin state space
`𝒦_Q / null` is finite dimensional. -/
structure NormalizedRationalHermitianData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The Laurent coefficients `M_n` of `Q(z) = -∑ M_n z^{-n-1}`. -/
  coeff : ℕ → H →ₗ[ℂ] H
  /-- `M_n = M_n^*`, i.e. `Q(z̄)^* = Q(z)`. -/
  coeff_symmetric : ∀ n, (coeff n).IsSymmetric
  /-- Rationality (Kronecker): finite Hankel rank. -/
  finiteRank : FiniteDimensional ℂ (hankelState coeff)

namespace NormalizedRationalHermitianData

variable (Q : NormalizedRationalHermitianData H)

/-- The dynamic function `Q(z)` of the data. -/
noncomputable def toFun [FiniteDimensional ℂ H] (z : ℂ) : H →L[ℂ] H :=
  laurentDynamicFunction Q.coeff z

/-- The Pontryagin state space `𝒦_Q` (after quotienting the null space). -/
abbrev State := hankelState Q.coeff

/-- The indefinite Hankel form `[·,·]_Q` on the state space. -/
noncomputable def form : Q.State → Q.State → ℂ :=
  hankelStateForm Q.coeff Q.coeff_symmetric

/-- The shift `A_Q`. -/
noncomputable def shift : Q.State →ₗ[ℂ] Q.State := hankelShift Q.coeff Q.coeff_symmetric

/-- The source `Γ_Q`. -/
noncomputable def source : H →ₗ[ℂ] Q.State := hankelSource Q.coeff

instance : FiniteDimensional ℂ Q.State := Q.finiteRank

/-- The state space is the literal span of the Hankel columns. -/
noncomputable def stateEquivColumnSpace : Q.State ≃ₗ[ℂ] hankelColumnSpace Q.coeff :=
  hankelStateEquivColumnSpace Q.coeff Q.coeff_symmetric

theorem form_shift_pow_source (i j : ℕ) (u v : H) :
    Q.form ((Q.shift ^ i) (Q.source u)) ((Q.shift ^ j) (Q.source v)) =
      ⟪u, Q.coeff (i + j) v⟫_ℂ :=
  hankelStateForm_shift_pow_source Q.coeff Q.coeff_symmetric i j u v

end NormalizedRationalHermitianData

end RenewalGeometry
