/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical chiral projectors and the charged inventory

`thm:canonical-chiral-projectors` and `lem:complete-typed-source` of the spacetime–gauge
duality manuscript.

The saturated carrier `𝒦_F^min` is `ℂ^ι` (`ι` finite).  It carries Hermitian nonabelian
generators `X_j`, the Hermitian central generator `Y` and a chirality grading `Γ`
(`GaugeCarrier`).  A target type `f` is a finite `V_f` with Hermitian `ρ_f(X_j)`, a real
central weight `y_f` and the Schur property (every operator commuting with all `ρ_f(X_j)` is
scalar: irreducibility) (`TargetType`).

* `tester`: the positive tester `𝕋_{f,ε} = ∑_j 𝓡_j^*𝓡_j + 𝓨^*𝓨 + 𝓖^*𝓖` on `Hom(V_f, 𝒦)`
  (`eq:canonical-type-tester`), adjoints taken for the Hilbert–Schmidt pairing;
  `mem_intertwiners_iff`: its kernel `𝓘_{f,ε}` is exactly the space of `T` with
  `X_j T = T ρ_f(X_j)`, `Y T = y_f T`, `Γ T = ε T`;
* `multInner`: `⟨S, T⟩_mult = d_f⁻¹ Tr(S^*T)`; `schur_gram`: `S^*T = ⟨S,T⟩_mult I` on `𝓘`;
* for an orthonormal basis (`IsONBasis`; one exists: `exists_onBasis`):
  `onBasis_gram` (`T_a^*T_b = δ_ab I`), `projector_isHermitian`, `projector_idem`,
  `projector_basis_independent`, `range_projector` (the range is the complete isotypic
  subspace `span{T v : T ∈ 𝓘}`), `finrank_intertwiners` and `rank_projector`
  (`n = dim 𝓘 = rank P / d_f`), `evalMatrix_unitary` (`ev_f(v ⊗ T) = T v` is unitary onto
  `P 𝒦`);
* inventory (`Inventory`): `P_SM`, `P_mir`, `P_ex` are orthogonal projections, mutually
  orthogonal, with `P_gch = P_SM + P_mir + P_ex` and
  `Δ_inv = Tr(P_gch − P_SM) = rank P_mir + rank P_ex`; `Δ_inv = 0` iff `P_gch = P_SM`, and a
  nonzero residual projection has operator norm one (`inventory_split`);
* `lem:complete-typed-source`: `typedSource_range` — the contraction
  `S_f(v̄ ⊗ e) = (⟨v| ⊗ I) ev_f^* P_f Z_F e` of a source bank onto `𝒦_F^min` is onto `N_f`.

Renderings disclosed: the chirality sign is any complex `ε` in the single-type part and
`±1` (`sgn : Bool → ℂ`) in the inventory; `P_F = I` on `𝒦_F^min = ℂ^ι`; `P_0^F` is any
Hermitian idempotent whose fixed vectors are exactly the fully gauge-trivial vectors; the
distinct target types are assumed pairwise inequivalent (an intertwiner `V_f → V_g` with
equal central weight vanishes for `f ≠ g`) and nontrivial (no nonzero gauge-trivial vector) —
both hold for the standard-model table; `V_f ⊗ 𝓘` is written in the coordinates of the
orthonormal basis, so `V_f ⊗ 𝓘 ≅ ℂ^{V_f × Fin n}` isometrically; the conjugate space `V̄_f`
is written in the conjugate basis.
-/

open Matrix
open scoped ComplexOrder

namespace RenewalGeometry
namespace CanonicalChiralProjectors

set_option linter.unusedSectionVars false

/-- The represented gauge data on the saturated carrier `𝒦_F^min = ℂ^ι`. -/
structure GaugeCarrier (ι J : Type*) [Fintype ι] [DecidableEq ι] where
  /-- Hermitian nonabelian infinitesimal generators `X_j` -/
  X : J → Matrix ι ι ℂ
  /-- the Hermitian central generator `Y` (normalized by `y = 6Y`) -/
  Y : Matrix ι ι ℂ
  /-- the chirality grading `Γ_F` -/
  Γ : Matrix ι ι ℂ
  X_herm : ∀ j, (X j)ᴴ = X j
  Y_herm : Yᴴ = Y
  Γ_herm : Γᴴ = Γ
  Γ_sq : Γ * Γ = 1
  Γ_comm_X : ∀ j, Γ * X j = X j * Γ
  Γ_comm_Y : Γ * Y = Y * Γ

/-- An irreducible target gauge type `V_f` with Hermitian generators `ρ_f(X_j)` and central
weight `y_f`. -/
structure TargetType (J V : Type*) [Fintype V] [DecidableEq V] where
  /-- the represented generators `ρ_f(X_j)` -/
  ρ : J → Matrix V V ℂ
  /-- the central weight `y_f` -/
  y : ℝ
  ρ_herm : ∀ j, (ρ j)ᴴ = ρ j
  /-- Schur property (irreducibility): the commutant of the `ρ_f(X_j)` is scalar. -/
  irred : ∀ M : Matrix V V ℂ, (∀ j, M * ρ j = ρ j * M) → ∃ c : ℂ, M = c • 1

variable {ι J V : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype V] [DecidableEq V]

/-! ### Hilbert–Schmidt adjoint pairs -/

section HS

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Left multiplication `T ↦ A T` as a linear map. -/
def lmul (A : Matrix m m ℂ) : Matrix m n ℂ →ₗ[ℂ] Matrix m n ℂ where
  toFun T := A * T
  map_add' := Matrix.mul_add A
  map_smul' c T := Matrix.mul_smul A c T

/-- Right multiplication `T ↦ T B` as a linear map. -/
def rmul (B : Matrix n n ℂ) : Matrix m n ℂ →ₗ[ℂ] Matrix m n ℂ where
  toFun T := T * B
  map_add' S T := Matrix.add_mul S T B
  map_smul' c T := Matrix.smul_mul c T B

/-- `D'` is the Hilbert–Schmidt adjoint of `D`. -/
def IsHSAdjoint (D D' : Matrix m n ℂ →ₗ[ℂ] Matrix m n ℂ) : Prop :=
  ∀ T S, (Tᴴ * D' S).trace = ((D T)ᴴ * S).trace

theorem isHSAdjoint_lmul (A : Matrix m m ℂ) :
    IsHSAdjoint (lmul (n := n) A) (lmul Aᴴ) := by
  intro T S
  simp only [lmul, LinearMap.coe_mk, AddHom.coe_mk, conjTranspose_mul, Matrix.mul_assoc]

theorem isHSAdjoint_rmul (B : Matrix n n ℂ) :
    IsHSAdjoint (rmul (m := m) B) (rmul Bᴴ) := by
  intro T S
  simp only [rmul, LinearMap.coe_mk, AddHom.coe_mk, conjTranspose_mul]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

theorem isHSAdjoint_smul (c : ℂ) :
    IsHSAdjoint (c • LinearMap.id : Matrix m n ℂ →ₗ[ℂ] Matrix m n ℂ) (star c • LinearMap.id) := by
  intro T S
  simp only [LinearMap.smul_apply, LinearMap.id_apply, conjTranspose_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_smul]

theorem IsHSAdjoint.sub {D D' E E' : Matrix m n ℂ →ₗ[ℂ] Matrix m n ℂ}
    (hD : IsHSAdjoint D D') (hE : IsHSAdjoint E E') : IsHSAdjoint (D - E) (D' - E') := by
  intro T S
  simp only [LinearMap.sub_apply, Matrix.mul_sub, conjTranspose_sub, Matrix.sub_mul,
    Matrix.trace_sub, hD T S, hE T S]

theorem trace_adjoint_comp {D D' : Matrix m n ℂ →ₗ[ℂ] Matrix m n ℂ} (h : IsHSAdjoint D D')
    (T : Matrix m n ℂ) : (Tᴴ * D' (D T)).trace = ((D T)ᴴ * D T).trace := h T (D T)

theorem trace_gram_nonneg (A : Matrix m n ℂ) : 0 ≤ (Aᴴ * A).trace :=
  (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg

end HS

/-! ### The tester and the intertwiner space -/

section Tester

variable (G : GaugeCarrier ι J) (τ : TargetType J V) (ε : ℂ)

/-- `𝓡_{f,j}(T) = X_j T − T ρ_f(X_j)`. -/
def gaugeDefect (j : J) : Matrix ι V ℂ →ₗ[ℂ] Matrix ι V ℂ := lmul (G.X j) - rmul (τ.ρ j)

/-- `𝓨_f(T) = Y T − y_f T`. -/
def chargeDefect : Matrix ι V ℂ →ₗ[ℂ] Matrix ι V ℂ := lmul G.Y - (τ.y : ℂ) • LinearMap.id

/-- `𝓖_{f,ε}(T) = Γ T − ε T`. -/
def chiralDefect : Matrix ι V ℂ →ₗ[ℂ] Matrix ι V ℂ := lmul G.Γ - ε • LinearMap.id

/-- Hilbert–Schmidt adjoints of the three defects. -/
def gaugeDefectAdj (j : J) : Matrix ι V ℂ →ₗ[ℂ] Matrix ι V ℂ :=
  lmul (G.X j)ᴴ - rmul (τ.ρ j)ᴴ

def chargeDefectAdj : Matrix ι V ℂ →ₗ[ℂ] Matrix ι V ℂ :=
  lmul G.Yᴴ - star (τ.y : ℂ) • LinearMap.id

def chiralDefectAdj : Matrix ι V ℂ →ₗ[ℂ] Matrix ι V ℂ := lmul G.Γᴴ - star ε • LinearMap.id

/-- **The canonical type tester** `𝕋_{f,ε} = ∑_j 𝓡_j^*𝓡_j + 𝓨^*𝓨 + 𝓖^*𝓖`
(`eq:canonical-type-tester`). -/
def tester : Matrix ι V ℂ →ₗ[ℂ] Matrix ι V ℂ :=
  (∑ j, gaugeDefectAdj G τ j ∘ₗ gaugeDefect G τ j) + chargeDefectAdj G τ ∘ₗ chargeDefect G τ +
    chiralDefectAdj G ε ∘ₗ chiralDefect G ε

/-- The intertwiner space `𝓘_{f,ε} = Ker 𝕋_{f,ε}`. -/
def intertwiners : Submodule ℂ (Matrix ι V ℂ) := LinearMap.ker (tester G τ ε)

theorem trace_tester (T : Matrix ι V ℂ) :
    (Tᴴ * tester G τ ε T).trace =
      (∑ j, ((gaugeDefect G τ j T)ᴴ * gaugeDefect G τ j T).trace) +
        ((chargeDefect G τ T)ᴴ * chargeDefect G τ T).trace +
        ((chiralDefect G ε T)ᴴ * chiralDefect G ε T).trace := by
  have h1 : ∀ j, IsHSAdjoint (gaugeDefect G τ j) (gaugeDefectAdj G τ j) := fun j =>
    (isHSAdjoint_lmul _).sub (isHSAdjoint_rmul _)
  have h2 : IsHSAdjoint (chargeDefect G τ) (chargeDefectAdj G τ) :=
    (isHSAdjoint_lmul _).sub (isHSAdjoint_smul _)
  have h3 : IsHSAdjoint (chiralDefect (V := V) G ε) (chiralDefectAdj G ε) :=
    (isHSAdjoint_lmul _).sub (isHSAdjoint_smul _)
  simp only [tester, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, Matrix.mul_add, Matrix.trace_add, Matrix.mul_sum, Matrix.trace_sum]
  rw [trace_adjoint_comp h2, trace_adjoint_comp h3]
  congr 2
  exact Finset.sum_congr rfl fun j _ => trace_adjoint_comp (h1 j) T

/-- **Kernel of the tester**: `𝓘_{f,ε}` is exactly the space of gauge intertwiners of type `f`,
charge `y_f` and chirality `ε`. -/
theorem mem_intertwiners_iff (T : Matrix ι V ℂ) :
    T ∈ intertwiners G τ ε ↔
      (∀ j, G.X j * T = T * τ.ρ j) ∧ G.Y * T = (τ.y : ℂ) • T ∧ G.Γ * T = ε • T := by
  have hg : ∀ j, gaugeDefect G τ j T = G.X j * T - T * τ.ρ j := fun j => rfl
  have hc : chargeDefect G τ T = G.Y * T - (τ.y : ℂ) • T := rfl
  have hχ : chiralDefect G ε T = G.Γ * T - ε • T := rfl
  constructor
  · intro hT
    have h0 : (Tᴴ * tester G τ ε T).trace = 0 := by
      rw [show tester G τ ε T = 0 from hT, Matrix.mul_zero, Matrix.trace_zero]
    rw [trace_tester] at h0
    have hs := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
      trace_gram_nonneg (gaugeDefect G τ j T)
    have hc0 := trace_gram_nonneg (chargeDefect G τ T)
    have hχ0 := trace_gram_nonneg (chiralDefect G ε T)
    obtain ⟨h12, h3⟩ := (add_eq_zero_iff_of_nonneg (add_nonneg hs hc0) hχ0).1 h0
    obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg hs hc0).1 h12
    have h1' := (Finset.sum_eq_zero_iff_of_nonneg fun j (_ : j ∈ Finset.univ) =>
      trace_gram_nonneg (gaugeDefect G τ j T)).1 h1
    refine ⟨fun j => ?_, ?_, ?_⟩
    · have := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 (h1' j (Finset.mem_univ j))
      rw [hg] at this
      exact sub_eq_zero.1 this
    · have := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h2
      rw [hc] at this
      exact sub_eq_zero.1 this
    · have := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h3
      rw [hχ] at this
      exact sub_eq_zero.1 this
  · rintro ⟨h1, h2, h3⟩
    have e1 : ∀ j, gaugeDefect G τ j T = 0 := fun j => by rw [hg, h1 j, sub_self]
    have e2 : chargeDefect G τ T = 0 := by rw [hc, h2, sub_self]
    have e3 : chiralDefect G ε T = 0 := by rw [hχ, h3, sub_self]
    show tester G τ ε T = 0
    simp only [tester, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.comp_apply, e1, e2, e3, map_zero, Finset.sum_const_zero, add_zero]

/-- The multiplicity inner product `⟨S, T⟩_mult = d_f⁻¹ Tr(S^*T)`. -/
noncomputable def multInner (S T : Matrix ι V ℂ) : ℂ :=
  (Fintype.card V : ℂ)⁻¹ * (Sᴴ * T).trace

/-- `S^*T` commutes with every `ρ_f(X_j)` for intertwiners `S, T`. -/
theorem gram_commute {S T : Matrix ι V ℂ} (hS : S ∈ intertwiners G τ ε)
    (hT : T ∈ intertwiners G τ ε) (j : J) :
    Sᴴ * T * τ.ρ j = τ.ρ j * (Sᴴ * T) := by
  have hS' := ((mem_intertwiners_iff G τ ε S).1 hS).1 j
  have hT' := ((mem_intertwiners_iff G τ ε T).1 hT).1 j
  have hSX : Sᴴ * G.X j = τ.ρ j * Sᴴ := by
    have := congrArg Matrix.conjTranspose hS'
    rwa [conjTranspose_mul, conjTranspose_mul, G.X_herm, τ.ρ_herm] at this
  rw [Matrix.mul_assoc, ← hT', ← Matrix.mul_assoc, hSX, Matrix.mul_assoc]

/-- **Schur relation**: for intertwiners `S, T`, `S^*T = ⟨S, T⟩_mult I`. -/
theorem schur_gram [Nonempty V] {S T : Matrix ι V ℂ} (hS : S ∈ intertwiners G τ ε)
    (hT : T ∈ intertwiners G τ ε) :
    Sᴴ * T = multInner S T • (1 : Matrix V V ℂ) := by
  obtain ⟨c, hc⟩ := τ.irred (Sᴴ * T) (gram_commute G τ ε hS hT)
  have hcard : (Fintype.card V : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have : multInner S T = c := by
    rw [multInner, hc, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    field_simp
  rw [this, hc]

end Tester

/-! ### Orthonormal bases and the canonical projector -/

section Basis

variable (G : GaugeCarrier ι J) (τ : TargetType J V) (ε : ℂ)

/-- An orthonormal basis `T_1, …, T_n` of `𝓘_{f,ε}` for the multiplicity inner product. -/
structure IsONBasis {n : ℕ} (T : Fin n → Matrix ι V ℂ) : Prop where
  mem : ∀ a, T a ∈ intertwiners G τ ε
  orth : ∀ a b, multInner (T a) (T b) = if a = b then 1 else 0
  span : Submodule.span ℂ (Set.range T) = intertwiners G τ ε

/-- The canonical projector `P_{f,ε} = ∑_a T_a T_a^*`. -/
def projector {n : ℕ} (T : Fin n → Matrix ι V ℂ) : Matrix ι ι ℂ := ∑ a, T a * (T a)ᴴ

variable {G τ ε}
variable {n : ℕ} {T : Fin n → Matrix ι V ℂ}

/-- `T_a^*T_b = δ_ab I_{V_f}` (`eq:canonical-chiral-projector`). -/
theorem onBasis_gram [Nonempty V] (hT : IsONBasis G τ ε T) (a b : Fin n) :
    (T a)ᴴ * T b = if a = b then 1 else 0 := by
  rw [schur_gram G τ ε (hT.mem a) (hT.mem b), hT.orth]
  split_ifs <;> simp

theorem projector_isHermitian (T : Fin n → Matrix ι V ℂ) : (projector T)ᴴ = projector T := by
  simp only [projector, conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose]

theorem projector_mul_basis [Nonempty V] (hT : IsONBasis G τ ε T) (b : Fin n) :
    projector T * T b = T b := by
  simp only [projector, Matrix.sum_mul, Matrix.mul_assoc, onBasis_gram hT]
  rw [Finset.sum_eq_single b (fun x _ hx => by rw [if_neg hx, Matrix.mul_zero]) (by simp),
    if_pos rfl, Matrix.mul_one]

/-- `P S = S` for every `S ∈ 𝓘_{f,ε}`. -/
theorem projector_mul_of_mem [Nonempty V] (hT : IsONBasis G τ ε T) {S : Matrix ι V ℂ}
    (hS : S ∈ intertwiners G τ ε) : projector T * S = S := by
  rw [← hT.span] at hS
  induction hS using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact projector_mul_basis hT b
  | zero => exact Matrix.mul_zero _
  | add x y _ _ hx hy => rw [Matrix.mul_add, hx, hy]
  | smul c x _ hx => rw [Matrix.mul_smul, hx]

theorem projector_idem [Nonempty V] (hT : IsONBasis G τ ε T) :
    projector T * projector T = projector T := by
  have h : ∀ a, projector T * (T a * (T a)ᴴ) = T a * (T a)ᴴ := fun a => by
    rw [← Matrix.mul_assoc, projector_mul_basis hT]
  show projector T * (∑ a, T a * (T a)ᴴ) = _
  rw [Matrix.mul_sum]
  simp only [h]
  rfl

/-- **Basis independence** of `P_{f,ε}`. -/
theorem projector_basis_independent [Nonempty V] {n' : ℕ} {T' : Fin n' → Matrix ι V ℂ}
    (hT : IsONBasis G τ ε T) (hT' : IsONBasis G τ ε T') : projector T = projector T' := by
  have h1 : projector T * projector T' = projector T' := by
    have h : ∀ a, projector T * (T' a * (T' a)ᴴ) = T' a * (T' a)ᴴ := fun a => by
      rw [← Matrix.mul_assoc, projector_mul_of_mem hT (hT'.mem a)]
    show projector T * (∑ a, T' a * (T' a)ᴴ) = _
    rw [Matrix.mul_sum]
    simp only [h]
    rfl
  have h2 : projector T' * projector T = projector T := by
    have h : ∀ a, projector T' * (T a * (T a)ᴴ) = T a * (T a)ᴴ := fun a => by
      rw [← Matrix.mul_assoc, projector_mul_of_mem hT' (hT.mem a)]
    show projector T' * (∑ a, T a * (T a)ᴴ) = _
    rw [Matrix.mul_sum]
    simp only [h]
    rfl
  have h3 := congrArg Matrix.conjTranspose h1
  rw [conjTranspose_mul, projector_isHermitian, projector_isHermitian, h2] at h3
  exact h3

/-- The complete `(f, ε)`-isotypic subspace `span{T v : T ∈ 𝓘_{f,ε}, v ∈ V_f}`. -/
def isotypic (G : GaugeCarrier ι J) (τ : TargetType J V) (ε : ℂ) : Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ {x | ∃ S ∈ intertwiners G τ ε, ∃ v : V → ℂ, x = S *ᵥ v}

/-- **The range of `P_{f,ε}` is the complete isotypic subspace.** -/
theorem range_projector [Nonempty V] (hT : IsONBasis G τ ε T) :
    LinearMap.range (projector T).mulVecLin = isotypic G τ ε := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    simp only [Matrix.mulVecLin_apply, projector, Matrix.sum_mulVec]
    refine Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨T a, hT.mem a, (T a)ᴴ *ᵥ x, ?_⟩
    rw [Matrix.mulVec_mulVec]
  · rw [isotypic, Submodule.span_le]
    rintro _ ⟨S, hS, v, rfl⟩
    refine ⟨S *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, projector_mul_of_mem hT hS]

/-- The orthonormal basis is linearly independent. -/
theorem onBasis_linearIndependent [Nonempty V] (hT : IsONBasis G τ ε T) :
    LinearIndependent ℂ T := by
  rw [Fintype.linearIndependent_iff]
  intro g hg b
  have := congrArg (fun M => (T b)ᴴ * M) hg
  simp only [Matrix.mul_sum, Matrix.mul_smul, onBasis_gram hT, Matrix.mul_zero] at this
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
  obtain ⟨v⟩ := ‹Nonempty V›
  have := congrFun (congrFun this v) v
  simpa using this

/-- `n_{f,ε} = dim 𝓘_{f,ε}`. -/
theorem finrank_intertwiners [Nonempty V] (hT : IsONBasis G τ ε T) :
    Module.finrank ℂ (intertwiners G τ ε) = n := by
  rw [← hT.span, finrank_span_eq_card (onBasis_linearIndependent hT), Fintype.card_fin]

/-- The rank of an idempotent complex matrix is its trace. -/
theorem rank_eq_trace_of_idem {m : Type*} [Fintype m] [DecidableEq m]
    (Q : Matrix m m ℂ) (hQ : Q * Q = Q) : (Q.rank : ℂ) = Q.trace := by
  have hidem : IsIdempotentElem Q.toLin' := by
    change Q.toLin' * Q.toLin' = Q.toLin'
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hQ]
  have h := LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ hidem)
  rw [Matrix.trace_toLin'_eq] at h
  rw [h]
  rfl

theorem trace_projector [Nonempty V] (hT : IsONBasis G τ ε T) :
    (projector T).trace = (n * Fintype.card V : ℕ) := by
  simp only [projector, Matrix.trace_sum]
  rw [Finset.sum_congr rfl fun a _ => by rw [Matrix.trace_mul_comm, onBasis_gram hT, if_pos rfl]]
  simp

/-- **`rank P_{f,ε} = n_{f,ε} d_f`**, i.e. `n_{f,ε} = dim 𝓘_{f,ε} = rank P_{f,ε} / d_f`. -/
theorem rank_projector [Nonempty V] (hT : IsONBasis G τ ε T) :
    (projector T).rank = n * Fintype.card V ∧
      Module.finrank ℂ (intertwiners G τ ε) = (projector T).rank / Fintype.card V := by
  have h := rank_eq_trace_of_idem _ (projector_idem hT)
  rw [trace_projector hT] at h
  have h' : (projector T).rank = n * Fintype.card V := by exact_mod_cast h
  refine ⟨h', ?_⟩
  rw [h', finrank_intertwiners hT, Nat.mul_div_cancel _ Fintype.card_pos]

/-- The evaluation map `ev_f : V_f ⊗ 𝓘 → 𝒦`, `v ⊗ T_a ↦ T_a v`, in the coordinates of the
orthonormal basis. -/
def evalMatrix (T : Fin n → Matrix ι V ℂ) : Matrix ι (V × Fin n) ℂ :=
  Matrix.of fun i va => T va.2 i va.1

theorem evalMatrix_mulVec_single (T : Fin n → Matrix ι V ℂ) (v : V) (a : Fin n) :
    evalMatrix T *ᵥ Pi.single (v, a) 1 = T a *ᵥ Pi.single v 1 := by
  ext i
  simp [evalMatrix, Matrix.mulVec_single]

/-- **The evaluation map is unitary onto `P_{f,ε} 𝒦`**: `ev^* ev = I` and `ev ev^* = P_{f,ε}`. -/
theorem evalMatrix_unitary [Nonempty V] (hT : IsONBasis G τ ε T) :
    (evalMatrix T)ᴴ * evalMatrix T = 1 ∧ evalMatrix T * (evalMatrix T)ᴴ = projector T := by
  constructor
  · ext ⟨v, a⟩ ⟨w, b⟩
    have h := congrFun (congrFun (onBasis_gram hT a b) v) w
    simp only [Matrix.mul_apply, conjTranspose_apply, evalMatrix, Matrix.of_apply] at h ⊢
    rw [h]
    by_cases hab : a = b
    · subst hab; simp [Matrix.one_apply, Prod.ext_iff]
    · simp [hab, Prod.ext_iff]
  · ext i k
    simp only [Matrix.mul_apply, conjTranspose_apply, evalMatrix, Matrix.of_apply, projector,
      Matrix.sum_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]

end Basis

/-! ### Existence of an orthonormal basis -/

section Existence

variable (G : GaugeCarrier ι J) (τ : TargetType J V) (ε : ℂ)

/-- Flattening `Matrix ι V ℂ ≃ EuclideanSpace ℂ (ι × V)`. -/
noncomputable def flatten : Matrix ι V ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (ι × V) :=
  (Matrix.ofLinearEquiv ℂ).symm.trans
    ((LinearEquiv.curry ℂ ℂ ι V).symm.trans (WithLp.linearEquiv 2 ℂ (ι × V → ℂ)).symm)

theorem flatten_apply (S : Matrix ι V ℂ) (p : ι × V) : flatten S p = S p.1 p.2 := rfl

theorem inner_flatten (S T : Matrix ι V ℂ) :
    inner ℂ (flatten S) (flatten T) = (Sᴴ * T).trace := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp [flatten_apply, mul_comm]

/-- **An orthonormal basis of `𝓘_{f,ε}` exists.** -/
theorem exists_onBasis [Nonempty V] :
    ∃ T : Fin (Module.finrank ℂ (intertwiners G τ ε)) → Matrix ι V ℂ,
      IsONBasis G τ ε T := by
  set I := intertwiners G τ ε
  let I' : Submodule ℂ (EuclideanSpace ℂ (ι × V)) := I.map (flatten (ι := ι) (V := V) : Matrix ι V ℂ →ₗ[ℂ] EuclideanSpace ℂ (ι × V))
  have hdim : Module.finrank ℂ I' = Module.finrank ℂ I :=
    (LinearEquiv.submoduleMap flatten I).finrank_eq.symm
  let b := stdOrthonormalBasis ℂ I'
  let d : ℂ := ((Real.sqrt (Fintype.card V : ℝ) : ℝ) : ℂ)
  let T : Fin (Module.finrank ℂ I) → Matrix ι V ℂ := fun a =>
    d • flatten.symm (b (Fin.cast hdim.symm a) : EuclideanSpace ℂ (ι × V))
  have hmemI' : ∀ a, ((b a : I') : EuclideanSpace ℂ (ι × V)) ∈ I' := fun a => (b a).2
  have hmem : ∀ a, T a ∈ I := by
    intro a
    obtain ⟨S, hS, hSe⟩ := hmemI' (Fin.cast hdim.symm a)
    refine I.smul_mem _ ?_
    rw [← hSe]
    simpa using hS
  have hcard : (Fintype.card V : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hdd : star d * d = (Fintype.card V : ℂ) := by
    simp only [d, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  refine ⟨T, hmem, fun a a' => ?_, ?_⟩
  · have hon := b.orthonormal
    have hinner : inner ℂ (b (Fin.cast hdim.symm a) : EuclideanSpace ℂ (ι × V))
        (b (Fin.cast hdim.symm a')) = if a = a' then 1 else 0 := by
      rw [← Submodule.coe_inner, orthonormal_iff_ite.1 hon]
      simp [Fin.cast_inj]
    simp only [multInner, T, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul]
    rw [← inner_flatten, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hinner]
    have h1 : (Fintype.card V : ℂ)⁻¹ * (star d * d) = 1 := by rw [hdd, inv_mul_cancel₀ hcard]
    linear_combination (if a = a' then (1 : ℂ) else 0) * h1
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact hmem a
    · intro S hS
      have hS' : flatten S ∈ I' := ⟨S, hS, rfl⟩
      have hspan := b.toBasis.sum_repr ⟨flatten S, hS'⟩
      have hS'' : S = ∑ a, (d⁻¹ * b.repr ⟨flatten S, hS'⟩ (Fin.cast hdim.symm a)) • T a := by
        have hd : d ≠ 0 := by
          intro h0
          have := hdd
          rw [h0, mul_zero] at this
          exact hcard this.symm
        have := congrArg (fun y : I' => flatten.symm (y : EuclideanSpace ℂ (ι × V))) hspan
        simp only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
          Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
          LinearEquiv.symm_apply_apply] at this
        refine this.symm.trans ?_
        rw [← (Fin.castOrderIso hdim.symm).toEquiv.sum_comp]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [T, smul_smul, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.cast_cast,
          Fin.cast_eq_self]
        rw [mul_comm _ d, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
      rw [hS'']
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Existence

/-! ### The charged inventory -/

section Inventory

/-- The chirality signs `true ↦ +1`, `false ↦ −1`. -/
def sgn (b : Bool) : ℂ := if b then 1 else -1

theorem sgn_ne {b b' : Bool} (h : b ≠ b') : sgn b - sgn b' ≠ 0 := by
  cases b <;> cases b' <;> simp_all [sgn] <;> norm_num

theorem star_sgn (b : Bool) : star (sgn b) = sgn b := by cases b <;> simp [sgn]

variable {𝓕 : Type*} [Fintype 𝓕] [DecidableEq 𝓕] {Vf : 𝓕 → Type*} [∀ f, Fintype (Vf f)]
  [∀ f, DecidableEq (Vf f)]

/-- The charged inventory data: target types with pairwise inequivalent irreducible actions,
physical chiralities, orthonormal bases of every `𝓘_{f,±}` and the gauge-trivial projector. -/
structure Inventory (G : GaugeCarrier ι J) (Vf : 𝓕 → Type*) [∀ f, Fintype (Vf f)]
    [∀ f, DecidableEq (Vf f)] where
  τ : ∀ f, TargetType J (Vf f)
  /-- the physical chirality `ε_f` (`true ↦ +1`) -/
  εp : 𝓕 → Bool
  n : 𝓕 → Bool → ℕ
  T : ∀ f b, Fin (n f b) → Matrix ι (Vf f) ℂ
  onb : ∀ f b, IsONBasis G (τ f) (sgn b) (T f b)
  nonempty : ∀ f, Nonempty (Vf f)
  /-- pairwise inequivalence of distinct target types -/
  ineq : ∀ f g, f ≠ g → ∀ M : Matrix (Vf g) (Vf f) ℂ,
    (∀ j, M * (τ f).ρ j = (τ g).ρ j * M) → ((τ f).y : ℂ) = (τ g).y → M = 0
  /-- target types are gauge nontrivial -/
  nontriv : ∀ f (w : Vf f → ℂ), (∀ j, (τ f).ρ j *ᵥ w = 0) → ((τ f).y : ℂ) • w = 0 → w = 0
  /-- the projector `P_0^F` onto the fully gauge-trivial subspace -/
  P0 : Matrix ι ι ℂ
  P0_idem : P0 * P0 = P0
  P0_herm : P0ᴴ = P0
  P0_fix : ∀ x, P0 *ᵥ x = x ↔ (∀ j, G.X j *ᵥ x = 0) ∧ G.Y *ᵥ x = 0

variable {G : GaugeCarrier ι J} (D : Inventory G Vf)

namespace Inventory

/-- `P_{f,±}`. -/
def P (f : 𝓕) (b : Bool) : Matrix ι ι ℂ := projector (D.T f b)

def Pgch : Matrix ι ι ℂ := 1 - D.P0
def Psm : Matrix ι ι ℂ := ∑ f, D.P f (D.εp f)
def Pmir : Matrix ι ι ℂ := ∑ f, D.P f (!D.εp f)
def Pall : Matrix ι ι ℂ := ∑ f, (D.P f true + D.P f false)
def Pex : Matrix ι ι ℂ := D.Pgch - D.Pall

theorem P_herm (f b) : (D.P f b)ᴴ = D.P f b := projector_isHermitian _

theorem P_idem (f b) : D.P f b * D.P f b = D.P f b := by
  haveI := D.nonempty f
  exact projector_idem (D.onb f b)

/-- Schur separation of distinct target types. -/
theorem gram_eq_zero_of_ne {f g : 𝓕} (hfg : f ≠ g) (b b' : Bool) (a : Fin (D.n f b))
    (c : Fin (D.n g b')) : (D.T g b' c)ᴴ * D.T f b a = 0 := by
  have hS := (mem_intertwiners_iff G (D.τ g) (sgn b') _).1 ((D.onb g b').mem c)
  have hT := (mem_intertwiners_iff G (D.τ f) (sgn b) _).1 ((D.onb f b).mem a)
  set S := D.T g b' c
  set T := D.T f b a
  have hcomm : ∀ j, Sᴴ * T * (D.τ f).ρ j = (D.τ g).ρ j * (Sᴴ * T) := by
    intro j
    have hSX : Sᴴ * G.X j = (D.τ g).ρ j * Sᴴ := by
      have := congrArg Matrix.conjTranspose (hS.1 j)
      rwa [conjTranspose_mul, conjTranspose_mul, G.X_herm, (D.τ g).ρ_herm] at this
    rw [Matrix.mul_assoc, ← hT.1 j, ← Matrix.mul_assoc, hSX, Matrix.mul_assoc]
  have hY : ((D.τ f).y : ℂ) • (Sᴴ * T) = ((D.τ g).y : ℂ) • (Sᴴ * T) := by
    have hSY : Sᴴ * G.Y = ((D.τ g).y : ℂ) • Sᴴ := by
      have := congrArg Matrix.conjTranspose hS.2.1
      rwa [conjTranspose_mul, G.Y_herm, conjTranspose_smul, Complex.star_def,
        Complex.conj_ofReal] at this
    calc ((D.τ f).y : ℂ) • (Sᴴ * T) = Sᴴ * (G.Y * T) := by rw [hT.2.1, Matrix.mul_smul]
      _ = ((D.τ g).y : ℂ) • (Sᴴ * T) := by rw [← Matrix.mul_assoc, hSY, Matrix.smul_mul]
  by_cases hy : ((D.τ f).y : ℂ) = (D.τ g).y
  · exact D.ineq f g hfg _ hcomm hy
  · have : (((D.τ f).y : ℂ) - (D.τ g).y) • (Sᴴ * T) = 0 := by rw [sub_smul, hY, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hy)

/-- Chirality separation inside one target type. -/
theorem gram_eq_zero_of_chir (f : 𝓕) {b b' : Bool} (hb : b ≠ b') (a : Fin (D.n f b))
    (c : Fin (D.n f b')) : (D.T f b' c)ᴴ * D.T f b a = 0 := by
  have hS := (mem_intertwiners_iff G (D.τ f) (sgn b') _).1 ((D.onb f b').mem c)
  have hT := (mem_intertwiners_iff G (D.τ f) (sgn b) _).1 ((D.onb f b).mem a)
  set S := D.T f b' c
  set T := D.T f b a
  have hSΓ : Sᴴ * G.Γ = sgn b' • Sᴴ := by
    have := congrArg Matrix.conjTranspose hS.2.2
    rwa [conjTranspose_mul, G.Γ_herm, conjTranspose_smul, star_sgn] at this
  have h1 : sgn b • (Sᴴ * T) = sgn b' • (Sᴴ * T) := by
    calc sgn b • (Sᴴ * T) = Sᴴ * (G.Γ * T) := by rw [hT.2.2, Matrix.mul_smul]
      _ = sgn b' • (Sᴴ * T) := by rw [← Matrix.mul_assoc, hSΓ, Matrix.smul_mul]
  have : (sgn b - sgn b') • (Sᴴ * T) = 0 := by rw [sub_smul, h1, sub_self]
  exact (smul_eq_zero.1 this).resolve_left (sgn_ne hb)

theorem P_mul_P_of_ne {f g : 𝓕} (hfg : f ≠ g) (b b' : Bool) : D.P g b' * D.P f b = 0 := by
  simp only [P, projector, Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_assoc]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
  rw [← Matrix.mul_assoc (D.T g b' c)ᴴ, D.gram_eq_zero_of_ne hfg b b' a c, Matrix.zero_mul,
    Matrix.mul_zero]

theorem P_mul_P_of_chir (f : 𝓕) {b b' : Bool} (hb : b ≠ b') : D.P f b' * D.P f b = 0 := by
  simp only [P, projector, Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_assoc]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
  rw [← Matrix.mul_assoc (D.T f b' c)ᴴ, D.gram_eq_zero_of_chir f hb a c, Matrix.zero_mul,
    Matrix.mul_zero]

/-- Target projectors kill the gauge-trivial sector. -/
theorem P_mul_P0 (f : 𝓕) (b : Bool) : D.P f b * D.P0 = 0 := by
  have hzero : ∀ a, (D.T f b a)ᴴ * D.P0 = 0 := by
    intro a
    have hT := (mem_intertwiners_iff G (D.τ f) (sgn b) _).1 ((D.onb f b).mem a)
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    simp only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
    rw [← Matrix.mulVec_mulVec]
    set y := D.P0 *ᵥ x
    have hy : (∀ j, G.X j *ᵥ y = 0) ∧ G.Y *ᵥ y = 0 :=
      (D.P0_fix y).1 (by simp only [y, Matrix.mulVec_mulVec, D.P0_idem])
    apply D.nontriv f
    · intro j
      have h1 : (D.τ f).ρ j * (D.T f b a)ᴴ = (D.T f b a)ᴴ * G.X j := by
        have := congrArg Matrix.conjTranspose (hT.1 j)
        rw [conjTranspose_mul, conjTranspose_mul, G.X_herm, (D.τ f).ρ_herm] at this
        exact this.symm
      rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, hy.1 j, Matrix.mulVec_zero]
    · have h2 : ((D.τ f).y : ℂ) • (D.T f b a)ᴴ = (D.T f b a)ᴴ * G.Y := by
        have := congrArg Matrix.conjTranspose hT.2.1
        rw [conjTranspose_mul, G.Y_herm, conjTranspose_smul, Complex.star_def,
          Complex.conj_ofReal] at this
        exact this.symm
      rw [← Matrix.smul_mulVec, h2, ← Matrix.mulVec_mulVec, hy.2, Matrix.mulVec_zero]
  simp only [P, projector, Matrix.sum_mul, Matrix.mul_assoc, hzero, Matrix.mul_zero,
    Finset.sum_const_zero]

theorem P0_mul_P (f : 𝓕) (b : Bool) : D.P0 * D.P f b = 0 := by
  have := congrArg Matrix.conjTranspose (D.P_mul_P0 f b)
  rwa [conjTranspose_mul, D.P0_herm, D.P_herm, conjTranspose_zero] at this

theorem Psm_add_Pmir : D.Psm + D.Pmir = D.Pall := by
  simp only [Psm, Pmir, Pall, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  cases D.εp f
  · simp only [Bool.not_false]; abel
  · rfl

/-- `P_f(β f) * P_g(β' g)` summed: orthogonality of two selections that differ everywhere. -/
theorem sum_mul_sum_of_ne (β β' : 𝓕 → Bool) (hββ' : ∀ f, β f ≠ β' f) :
    (∑ f, D.P f (β f)) * ∑ g, D.P g (β' g) = 0 := by
  simp only [Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_eq_zero fun f _ => Finset.sum_eq_zero fun g _ => ?_
  by_cases hfg : f = g
  · subst hfg; exact D.P_mul_P_of_chir (b := β' f) (b' := β f) f (hββ' f).symm
  · exact D.P_mul_P_of_ne (f := f) (g := g) hfg (β' f) (β g)

theorem sum_idem (β : 𝓕 → Bool) :
    (∑ f, D.P f (β f)) * ∑ g, D.P g (β g) = ∑ f, D.P f (β f) := by
  simp only [Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_eq_single g (fun f _ hfg => D.P_mul_P_of_ne (Ne.symm hfg) _ _)
    (by simp), D.P_idem]

theorem sum_herm (β : 𝓕 → Bool) : (∑ f, D.P f (β f))ᴴ = ∑ f, D.P f (β f) := by
  simp only [conjTranspose_sum, D.P_herm]

theorem sum_mul_P0 (β : 𝓕 → Bool) : (∑ f, D.P f (β f)) * D.P0 = 0 := by
  simp only [Matrix.sum_mul, D.P_mul_P0, Finset.sum_const_zero]

theorem P0_mul_sum (β : 𝓕 → Bool) : D.P0 * (∑ f, D.P f (β f)) = 0 := by
  simp only [Matrix.mul_sum, D.P0_mul_P, Finset.sum_const_zero]

/-- An orthogonal projection (Hermitian idempotent) of nonzero value has `L²` operator norm
one. -/
theorem norm_eq_one_of_projection {m : Type*} [Fintype m] [DecidableEq m] (Q : Matrix m m ℂ)
    (hQ : Q * Q = Q) (hQH : Qᴴ = Q) (hne : Q ≠ 0) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm Q = 1 := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.instL2OpNormedRing
  letI : CStarRing (Matrix m m ℂ) := Matrix.instCStarRing
  have h := CStarRing.norm_star_mul_self (x := Q)
  rw [Matrix.star_eq_conjTranspose, hQH, hQ] at h
  have hpos : ‖Q‖ ≠ 0 := norm_ne_zero_iff.2 hne
  have : ‖Q‖ * (‖Q‖ - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.1 this with h0 | h1
  · exact absurd h0 hpos
  · exact (sub_eq_zero.1 h1)

end Inventory

open Inventory in
/-- **`thm:canonical-chiral-projectors`, inventory split** (`eq:future-visible-inventory-split`,
`eq:future-visible-inventory-residual`).  `P_SM`, `P_mir`, `P_ex` are orthogonal projections,
pairwise orthogonal, with `P_gch = P_SM + P_mir + P_ex`; the residual
`Δ_inv = Tr(P_gch − P_SM) = rank P_mir + rank P_ex`; `Δ_inv = 0` iff `P_gch = P_SM`; and if
`Δ_inv ≠ 0` then `Δ_inv ≥ 1` and the residual projection `P_gch − P_SM` has operator norm one. -/
theorem inventory_split :
    (D.Psm * D.Psm = D.Psm ∧ D.Psmᴴ = D.Psm) ∧
    (D.Pmir * D.Pmir = D.Pmir ∧ D.Pmirᴴ = D.Pmir) ∧
    (D.Pex * D.Pex = D.Pex ∧ D.Pexᴴ = D.Pex) ∧
    (D.Psm * D.Pmir = 0 ∧ D.Psm * D.Pex = 0 ∧ D.Pmir * D.Pex = 0) ∧
    D.Pgch = D.Psm + D.Pmir + D.Pex ∧
    (D.Pgch - D.Psm).trace = ((D.Pmir.rank + D.Pex.rank : ℕ) : ℂ) ∧
    (D.Pgch - D.Psm).rank = D.Pmir.rank + D.Pex.rank ∧
    ((D.Pgch - D.Psm).rank = 0 ↔ D.Pgch = D.Psm) ∧
    ((D.Pgch - D.Psm).rank ≠ 0 → 1 ≤ (D.Pgch - D.Psm).rank ∧
      @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (D.Pgch - D.Psm) = 1) := by
  have hne : ∀ f, D.εp f ≠ !D.εp f := fun f => by cases D.εp f <;> simp
  -- basic facts
  have hsm2 : D.Psm * D.Psm = D.Psm := D.sum_idem D.εp
  have hmir2 : D.Pmir * D.Pmir = D.Pmir := D.sum_idem fun f => !D.εp f
  have hsmH : D.Psmᴴ = D.Psm := D.sum_herm D.εp
  have hmirH : D.Pmirᴴ = D.Pmir := D.sum_herm fun f => !D.εp f
  have hsmmir : D.Psm * D.Pmir = 0 := D.sum_mul_sum_of_ne _ _ hne
  have hmirsm : D.Pmir * D.Psm = 0 := D.sum_mul_sum_of_ne _ _ fun f => (hne f).symm
  have hsm0 : D.Psm * D.P0 = 0 := D.sum_mul_P0 D.εp
  have hmir0 : D.Pmir * D.P0 = 0 := D.sum_mul_P0 _
  have h0sm : D.P0 * D.Psm = 0 := D.P0_mul_sum D.εp
  have h0mir : D.P0 * D.Pmir = 0 := D.P0_mul_sum _
  have hall : D.Pall = D.Psm + D.Pmir := D.Psm_add_Pmir.symm
  have hex : D.Pex = 1 - D.P0 - (D.Psm + D.Pmir) := by rw [Pex, Pgch, hall]
  have hP0 := D.P0_idem
  have hexH : D.Pexᴴ = D.Pex := by
    rw [hex, conjTranspose_sub, conjTranspose_sub, conjTranspose_one, conjTranspose_add,
      D.P0_herm, hsmH, hmirH]
  have hex2 : D.Pex * D.Pex = D.Pex := by
    rw [hex]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hP0, hsm2, hmir2, hsmmir, hmirsm, hsm0, hmir0, h0sm, h0mir]
    abel
  have hsmex : D.Psm * D.Pex = 0 := by
    rw [hex]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, hsm2, hsmmir, hsm0]
    abel
  have hmirex : D.Pmir * D.Pex = 0 := by
    rw [hex]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, hmir2, hmirsm, hmir0]
    abel
  have hsplit : D.Pgch = D.Psm + D.Pmir + D.Pex := by rw [Pex, hall]; abel
  have hres : D.Pgch - D.Psm = D.Pmir + D.Pex := by rw [hsplit]; abel
  have hexmir : D.Pex * D.Pmir = 0 := by
    have := congrArg Matrix.conjTranspose hmirex
    rwa [conjTranspose_mul, hmirH, hexH, conjTranspose_zero] at this
  have hres2 : (D.Pgch - D.Psm) * (D.Pgch - D.Psm) = D.Pgch - D.Psm := by
    rw [hres, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hmir2, hex2, hmirex, hexmir]
    abel
  have hresH : (D.Pgch - D.Psm)ᴴ = D.Pgch - D.Psm := by
    rw [hres, conjTranspose_add, hmirH, hexH]
  have htrace : (D.Pgch - D.Psm).trace = ((D.Pmir.rank + D.Pex.rank : ℕ) : ℂ) := by
    rw [hres, Matrix.trace_add, ← rank_eq_trace_of_idem _ hmir2, ← rank_eq_trace_of_idem _ hex2]
    push_cast; rfl
  have hrank : (D.Pgch - D.Psm).rank = D.Pmir.rank + D.Pex.rank := by
    have := rank_eq_trace_of_idem _ hres2
    rw [htrace] at this
    exact_mod_cast this
  have hzero : (D.Pgch - D.Psm).rank = 0 ↔ D.Pgch = D.Psm := by
    constructor
    · intro h0
      have := rank_eq_trace_of_idem _ hres2
      have hsq : ((D.Pgch - D.Psm)ᴴ * (D.Pgch - D.Psm)).trace = 0 := by
        rw [hresH, hres2, ← this, h0, Nat.cast_zero]
      exact sub_eq_zero.1 (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 hsq)
    · intro h0
      rw [h0, sub_self]
      exact Matrix.rank_zero
  refine ⟨⟨hsm2, hsmH⟩, ⟨hmir2, hmirH⟩, ⟨hex2, hexH⟩, ⟨hsmmir, hsmex, hmirex⟩, hsplit, htrace,
    hrank, hzero, fun hnz => ⟨Nat.one_le_iff_ne_zero.2 hnz, ?_⟩⟩
  refine norm_eq_one_of_projection _ hres2 hresH fun h0 => hnz ?_
  rw [hzero]
  exact sub_eq_zero.1 h0

end Inventory

/-! ### `lem:complete-typed-source` -/

section TypedSource

variable {G : GaugeCarrier ι J} {τ : TargetType J V} {ε : ℂ} {n : ℕ}
  {T : Fin n → Matrix ι V ℂ} {Esat : Type*} [Fintype Esat]

/-- `Ẑ_f = ev_f^* P_{f,ε} Z_F`. -/
def typedBank (T : Fin n → Matrix ι V ℂ) (Z : Matrix ι Esat ℂ) : Matrix (V × Fin n) Esat ℂ :=
  (evalMatrix T)ᴴ * projector T * Z

/-- The contraction `S_f : V̄_f ⊗ E_sat → N_f`, `S_f(v̄ ⊗ e) = (⟨v| ⊗ I) Ẑ_f e`, written in the
conjugate basis of `V̄_f` and the orthonormal basis of `N_f = 𝓘_{f,ε}`
(`eq:complete-typed-source-synthesis`). -/
def typedSource (T : Fin n → Matrix ι V ℂ) (Z : Matrix ι Esat ℂ) :
    Matrix (Fin n) (V × Esat) ℂ :=
  Matrix.of fun a ve => typedBank T Z (ve.1, a) ve.2

/-- On a pure tensor `v̄ ⊗ e` the contraction is `(⟨v| ⊗ I) Ẑ_f e`. -/
theorem typedSource_apply_pure [DecidableEq Esat] (Z : Matrix ι Esat ℂ) (v : V → ℂ)
    (e : Esat) :
    typedSource T Z *ᵥ (fun ke => star (v ke.1) * if ke.2 = e then 1 else 0) =
      fun a => ∑ k, star (v k) * typedBank T Z (k, a) e := by
  ext a
  simp only [typedSource, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **`lem:complete-typed-source`**: if `Z_F` synthesizes the whole saturated carrier
(`Ran Z_F = 𝒦_F^min`), the contraction `S_f` is onto the multiplicity space `N_f`
(in orthonormal coordinates `ℂ^n`), and the corresponding intertwiners `∑_a (S_f x)_a T_a`
exhaust `𝓘_{f,ε}`. -/
theorem typedSource_range [Nonempty V] (hT : IsONBasis G τ ε T) (Z : Matrix ι Esat ℂ)
    (hZ : LinearMap.range Z.mulVecLin = ⊤) :
    LinearMap.range (typedSource T Z).mulVecLin = ⊤ ∧
      Submodule.map (Fintype.linearCombination ℂ T) (LinearMap.range (typedSource T Z).mulVecLin)
        = intertwiners G τ ε := by
  classical
  obtain ⟨hEE, hEP⟩ := evalMatrix_unitary hT
  have hbank : typedBank T Z = (evalMatrix T)ᴴ * Z := by
    rw [typedBank, ← hEP, ← Matrix.mul_assoc, hEE, Matrix.one_mul]
  have hsurj : LinearMap.range (typedSource T Z).mulVecLin = ⊤ := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨k0⟩ := ‹Nonempty V›
    let target : V × Fin n → ℂ := fun ka => if ka.1 = k0 then u ka.2 else 0
    obtain ⟨z, hz⟩ : evalMatrix T *ᵥ target ∈ LinearMap.range Z.mulVecLin := by
      rw [hZ]; trivial
    simp only [Matrix.mulVecLin_apply] at hz
    have hZt : typedBank T Z *ᵥ z = target := by
      rw [hbank, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_mulVec, hEE, Matrix.one_mulVec]
    refine ⟨fun ke => if ke.1 = k0 then z ke.2 else 0, ?_⟩
    ext a
    have := congrFun hZt (k0, a)
    simp only [target, if_true] at this
    rw [← this]
    simp only [Matrix.mulVecLin_apply, typedSource, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Fintype.sum_prod_type, mul_ite, mul_zero]
    rw [Finset.sum_eq_single k0 (fun x _ hx => by simp [hx]) (by simp)]
    simp
  refine ⟨hsurj, ?_⟩
  rw [hsurj, Submodule.map_top, Fintype.range_linearCombination, hT.span]

end TypedSource

end CanonicalChiralProjectors
end RenewalGeometry
