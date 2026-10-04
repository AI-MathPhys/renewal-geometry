/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.NativeWilsonCompactness
import RenewalGeometry.GaugeTheory.DeterminantHodgeNormalizationExact

/-!
# Determinant compactness, admissibility and flux from the full curvature screen
  (`lem:determinant-screen-flux`, Einstein–SM action closure)

Setting (the paper's periodic comparison box of side `L > 0`, `h_k = L / n_k`, `n_k → ∞`, a
four-dimensional grid `(ℤ/n_k)^ι`, `card ι = 4`).  `G_SM` links `U_k`; for every oriented
coordinate pair `μ < ν` a logarithm `L_k(x, μ, ν) ∈ 𝔤 = M₃(ℂ) × M₂(ℂ)` of the full plaquette
(`exp L = P_{U,μν}(x)` in both factors), and the literal full curvature packet
`𝔽_k(x) = (h_k⁻² L_k(x, μ, ν))_{μ<ν}` (`curvPacket`).  Norms: each factor carries the operator
norm (unitarily invariant), pairs and packets the max norm (equivalent to the invariant
Euclidean metric up to a constant depending only on the dimension, which changes neither
boundedness nor vanishing moduli).  The adjoint representation `Ad U` acts on packets
(`adPacket`); `wilsonShift` and `openLink` are those of `thm:native-Wilson-compactness`.

Hypotheses (exactly those of the lemma): `sup_k ‖𝔽_k‖_{2,h} < ∞` and the full-box adjoint
Wilson screen `lim_{ρ↓0} limsup_k Ω_{h_k}(𝔽_k; ρ) = 0` (used for positive displacements, as in
`NativeWilsonCompactness`).  No bound on logarithms of the links is assumed.

Conclusions (`determinant_screen_flux`), with `u = χ(U)`, `φ = Arg χ(P_U)`, `f = h⁻² φ`:
1. eventually `f_h = ℓ_c(𝔽_h)` exactly;
2. eventually `‖T_{μ,m} f - f‖_{2,h} ≤ 2 ‖W_{μ,m}𝔽 - 𝔽‖_{2,h}` for all `μ, m` (so
   `ω_h(f; ρ) ≤ 2 Ω_h(𝔽; ρ)`);
3. `max_{x,μ,ν} |φ_{μν,h}(x)| → 0`;
4. `R_h^0 f_h` is precompact in `L²` (`TotallyBounded`, unit-torus rendering of
   `lem:native-discrete-KR`);
5. eventually `d_h f_h = 0` exactly (all cube sums vanish);
6. coordinate-plane fluxes are `2π m`, `m ∈ ℤ`, eventually independent of the transverse base
   point, with `\bar f = 2π m / L²` and `2π |m| ≤ ‖f_{μν}‖_{2,h}`;
7. the integer vectors `(m_{μν,h})_{μ<ν}` are bounded and constant along a subsequence.

**`prop:native-determinant-split`** (`native_determinant_split`): under the same screen and zero
determinant flux for all large `k`, the logarithms of all oriented plaquettes (`extLog`,
`P_{νμ} = P_{μν}⁻¹`) are eventually admissible, so `DeterminantFlux.native_determinant_split_exact`
applies for every large `k` (exact normalization with the paper's potential, `V ∈ G_ss`,
`F_h(V) = Π_ss F_h(U')`, `Ad V = Ad U'`, central lift changes); moreover the semisimple curvature
screen of `V` is bounded by `c_ss = 1 + 2‖Z_c‖` times the full screen of `U` (`ss_screen_le`:
central factors act trivially in `Ad`, `Π_ss` is `Ad`-equivariant).

The proof is the paper's: the scalar-magnitude part of the proved
`thm:native-Wilson-compactness` gives uniform integrability of `|R^0 𝔽|²`, hence
`max_x h⁴|𝔽_h(x)|² → 0` (`exists_tail_le` plus the cell mass); the logarithms become small, so
`χ(e^X) = e^{iℓ_c(X)}` identifies `φ = h² ℓ_c(𝔽)` (`DeterminantFlux.ellC_eq_arg_smChi`); the
`Ad`-invariant functional `ℓ_c` turns Wilson differences into ordinary differences; then
`native_discrete_KR` and `DeterminantFlux.determinant_screen_flux_exact`.
-/

open Filter Topology Set Finset

namespace RenewalGeometry.DeterminantScreenFlux

open DeterminantFlux DeterminantSplit SMDescentYukawa NativeWilsonCompactness
  TorusPiecewiseConstantTranslation

noncomputable section

/-! ### The Lie-pair space with operator norms -/

/-- `𝔤_SM ⊂ M₃(ℂ) × M₂(ℂ)` with the (unitarily invariant) operator norm on each factor and the
max norm on pairs. -/
def OpPair : Type := Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ

section Instances

open scoped Matrix.Norms.L2Operator

instance : NormedAddCommGroup OpPair :=
  inferInstanceAs (NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ))

instance : NormedSpace ℂ OpPair :=
  inferInstanceAs (NormedSpace ℂ (Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ))

instance : FiniteDimensional ℂ OpPair :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ))

/-- View a Lie pair in the normed space `OpPair`. -/
def toOp (X : LiePair) : OpPair := X

/-- Back to Lie pairs. -/
def ofOp (X : OpPair) : LiePair := X

@[simp] theorem ofOp_toOp (X : LiePair) : ofOp (toOp X) = X := rfl

theorem toOp_smul (c : ℂ) (X : LiePair) : toOp (c • X) = c • toOp X := rfl

theorem ofOp_sub (X Y : OpPair) : ofOp (X - Y) = ofOp X - ofOp Y := rfl

theorem ofOp_smul (c : ℂ) (X : OpPair) : ofOp (c • X) = c • ofOp X := rfl

theorem matrix_entry_le_l2 {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (i j : m) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h := A.l2_opNorm_mulVec (EuclideanSpace.single j 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le
    ((EuclideanSpace.equiv m ℂ).symm (A.mulVec (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  refine le_trans (le_of_eq ?_) this
  congr 1
  simp

theorem norm_toOp_eq (X : LiePair) :
    ‖toOp X‖ = max ‖(X.1 : Matrix (Fin 3) (Fin 3) ℂ)‖ ‖(X.2 : Matrix (Fin 2) (Fin 2) ℂ)‖ :=
  Prod.norm_def _

/-- Entries of the weak factor are bounded by the pair norm. -/
theorem entry_snd_le (X : LiePair) (i j : Fin 2) : ‖X.2 i j‖ ≤ ‖toOp X‖ := by
  rw [norm_toOp_eq]
  exact (matrix_entry_le_l2 X.2 i j).trans (le_max_right _ _)

/-- Entries of the colour factor are bounded by the pair norm. -/
theorem entry_fst_le (X : LiePair) (i j : Fin 3) : ‖X.1 i j‖ ≤ ‖toOp X‖ := by
  rw [norm_toOp_eq]
  exact (matrix_entry_le_l2 X.1 i j).trans (le_max_left _ _)

/-- `|ℓ_c(X)| ≤ 2 ‖X‖`. -/
theorem norm_ellC_le_two (X : LiePair) : ‖ellC X‖ ≤ 2 * ‖toOp X‖ :=
  norm_ellC_le X _ (entry_snd_le X)

/-- Unitary conjugation is isometric for the operator norm. -/
theorem norm_unitary_conj {m : Type*} [Fintype m] [DecidableEq m] (U A : Matrix m m ℂ)
    (hU : U ∈ Matrix.unitaryGroup m ℂ) : ‖U * A * star U‖ = ‖A‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU), CStarRing.norm_mem_unitary_mul _ hU]

theorem smU3_mem_unitaryGroup (y : SMGaugeGroup) : smU3 y ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
  ((y : SMGaugeU3 × SMGaugeU2).1).2

theorem ofOp_add (X Y : OpPair) : ofOp (X + Y) = ofOp X + ofOp Y := rfl

theorem conj_cancel {m : Type*} [Fintype m] [DecidableEq m] (U A : Matrix m m ℂ)
    (h : star U * U = 1) : star U * (U * A * star U) * U = A := by
  rw [show star U * (U * A * star U) * U = (star U * U) * A * (star U * U) by
    simp only [mul_assoc], h, one_mul, mul_one]

/-- The adjoint action of `g ∈ G_SM` on `𝔤_SM`, as a linear isometry. -/
def adPair (g : SMGaugeGroup) : OpPair ≃ₗᵢ[ℂ] OpPair where
  toFun X := toOp (smU3 g * (ofOp X).1 * star (smU3 g), smU2 g * (ofOp X).2 * star (smU2 g))
  invFun X := toOp (star (smU3 g) * (ofOp X).1 * smU3 g, star (smU2 g) * (ofOp X).2 * smU2 g)
  map_add' X Y := by
    rw [ofOp_add]
    change ((_, _) : LiePair) = ((_, _) : LiePair) + ((_, _) : LiePair)
    simp only [Prod.fst_add, Prod.snd_add, Matrix.mul_add, Matrix.add_mul, Prod.mk_add_mk]
  map_smul' c X := by
    rw [ofOp_smul]
    change ((_, _) : LiePair) = c • ((_, _) : LiePair)
    simp only [Prod.smul_fst, Prod.smul_snd, Matrix.mul_smul, Matrix.smul_mul,
      RingHom.id_apply, Prod.smul_mk]
  left_inv X := by
    have h3 := (Matrix.mem_unitaryGroup_iff' (A := smU3 g)).1 (smU3_mem_unitaryGroup g)
    have h2 := (Matrix.mem_unitaryGroup_iff' (A := smU2 g)).1 (smU2_mem_unitaryGroup g)
    change ((_, _) : LiePair) = X
    simp only [ofOp, toOp]
    rw [conj_cancel _ _ h3, conj_cancel _ _ h2]
    rfl
  right_inv X := by
    have h3 := (Matrix.mem_unitaryGroup_iff (A := smU3 g)).1 (smU3_mem_unitaryGroup g)
    have h2 := (Matrix.mem_unitaryGroup_iff (A := smU2 g)).1 (smU2_mem_unitaryGroup g)
    have e3 := conj_cancel (star (smU3 g)) (ofOp X).1 (by rw [star_star]; exact h3)
    have e2 := conj_cancel (star (smU2 g)) (ofOp X).2 (by rw [star_star]; exact h2)
    rw [star_star] at e3 e2
    change ((smU3 g * (star (smU3 g) * (ofOp X).1 * smU3 g) * star (smU3 g),
      smU2 g * (star (smU2 g) * (ofOp X).2 * smU2 g) * star (smU2 g)) : LiePair) = X
    rw [e3, e2]
    rfl
  norm_map' X := by
    change ‖toOp ((_, _) : LiePair)‖ = ‖toOp (ofOp X)‖
    rw [norm_toOp_eq, norm_toOp_eq, norm_unitary_conj _ _ (smU3_mem_unitaryGroup g),
      norm_unitary_conj _ _ (smU2_mem_unitaryGroup g)]

end Instances

theorem adPair_apply (g : SMGaugeGroup) (X : OpPair) :
    ofOp (adPair g X) = (smU3 g * (ofOp X).1 * star (smU3 g), smU2 g * (ofOp X).2 * star (smU2 g)) :=
  rfl

/-- **`ℓ_c` is `Ad`-invariant.** -/
theorem ellC_adPair (g : SMGaugeGroup) (X : OpPair) : ellC (ofOp (adPair g X)) = ellC (ofOp X) := by
  rw [adPair_apply]
  simp only [ellC]
  congr 1
  rw [Matrix.trace_mul_cycle, (Matrix.mem_unitaryGroup_iff'.1 (smU2_mem_unitaryGroup g)), one_mul]

/-! ### Packets, adjoint Wilson links and the invariant functional -/

/-- The oriented coordinate pairs `μ < ν` of the four-dimensional grid. -/
abbrev PairIdx : Type := {p : Fin 4 × Fin 4 // p.1 < p.2}

/-- Curvature packets `(Y_{μν})_{μ<ν}`. -/
abbrev Packet : Type := PairIdx → OpPair

/-- The adjoint action of `g` on packets (componentwise), a linear isometry. -/
def adPacket (g : SMGaugeGroup) : Packet ≃ₗᵢ[ℂ] Packet where
  toLinearEquiv := LinearEquiv.piCongrRight fun _ => (adPair g).toLinearEquiv
  norm_map' Y := by
    simp only [Pi.norm_def, LinearEquiv.piCongrRight_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.nnnorm_map]

/-- The represented links `ρ(U_μ(x)) = Ad U_μ(x)` on curvature packets. -/
def adLinks {N : ℕ} (U : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup) (μ : Fin 4)
    (x : Fin 4 → ZMod N) : Packet ≃ₗᵢ[ℂ] Packet :=
  adPacket (U x μ)

/-- The literal full curvature packet `𝔽(x) = (h⁻² L(x, μ, ν))_{μ<ν}`. -/
def curvPacket {N : ℕ} (h : ℝ) (Lg : (Fin 4 → ZMod N) → Fin 4 → Fin 4 → LiePair)
    (x : Fin 4 → ZMod N) : Packet :=
  fun p => toOp ((((h ^ 2)⁻¹ : ℝ) : ℂ) • Lg x p.1.1 p.1.2)

/-- The determinant curvature packet `f = h⁻² Arg χ(P_U)` (`eq:determinant-real-curvature`). -/
def detPacket {N : ℕ} (h : ℝ) (U : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup)
    (x : Fin 4 → ZMod N) : PairIdx → ℝ :=
  fun p => Complex.arg (smChi (plaq gridShift U x p.1.1 p.1.2)) / h ^ 2

/-- `ℓ_c` is invariant under the open adjoint links. -/
theorem ellC_openLink {N : ℕ} (U : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup) (μ : Fin 4)
    (m : ℕ) (x : Fin 4 → ZMod N) (v : Packet) (p : PairIdx) :
    ellC (ofOp ((openLink (adLinks U) μ m x v) p)) = ellC (ofOp (v p)) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
      change ellC (ofOp (adPair (U x μ) ((openLink (adLinks U) μ m (x + Pi.single μ 1) v) p))) = _
      rw [ellC_adPair, ih]

theorem ellC_smul (c : ℂ) (X : LiePair) : ellC (c • X) = c * ellC X := by
  simp only [ellC, Prod.smul_snd, Matrix.trace_smul, smul_eq_mul, mul_div_assoc]

theorem ellC_sub (X Y : LiePair) : ellC (X - Y) = ellC X - ellC Y := by
  simp only [ellC, Prod.snd_sub, Matrix.trace_sub, sub_div]

/-! ### Grid norms -/

theorem gridL2Norm_eq_gridNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ}
    (hL : 0 < L) (N : ℕ) [NeZero N] (u : (Fin 4 → ZMod N) → E) :
    GridSobolev.gridL2Norm (L / N) u = L ^ 2 * gridNorm u := by
  unfold GridSobolev.gridL2Norm periodicHodgeNormSq gridNorm
  rw [Fintype.card_fin]
  have : (L / N) ^ 4 * ∑ x : Fin 4 → ZMod N, ‖u x‖ ^ 2 =
      (L ^ 2) ^ 2 * ((1 / (N : ℝ)) ^ 4 * ∑ g : Fin 4 → ZMod N, ‖u g‖ ^ 2) := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- The cell mass: `N⁻² ‖Y x‖ ≤ ‖Y‖_{2,h}` (unit torus, four dimensions). -/
theorem cell_le_gridNorm {E : Type*} [NormedAddCommGroup E] {N : ℕ} [NeZero N]
    (Y : (Fin 4 → ZMod N) → E) (x : Fin 4 → ZMod N) :
    (1 / (N : ℝ)) ^ 2 * ‖Y x‖ ≤ gridNorm Y := by
  unfold gridNorm
  rw [Fintype.card_fin]
  refine Real.le_sqrt_of_sq_le ?_
  have h1 : ‖Y x‖ ^ 2 ≤ ∑ g, ‖Y g‖ ^ 2 :=
    Finset.single_le_sum (f := fun g => ‖Y g‖ ^ 2) (fun g _ => sq_nonneg _) (Finset.mem_univ x)
  calc ((1 / (N : ℝ)) ^ 2 * ‖Y x‖) ^ 2 = (1 / (N : ℝ)) ^ 4 * ‖Y x‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- Pointwise control from the amplitude tail: `N⁻² ‖Y x‖ ≤ max(q(R), R N⁻²)`. -/
theorem cell_le_tail {E : Type*} [NormedAddCommGroup E] {N : ℕ} [NeZero N]
    (Y : (Fin 4 → ZMod N) → E) {R : ℝ} (hR : 0 ≤ R) (x : Fin 4 → ZMod N) :
    (1 / (N : ℝ)) ^ 2 * ‖Y x‖ ≤ gridNorm (tailPart R Y) + (1 / (N : ℝ)) ^ 2 * R := by
  by_cases h : R < ‖Y x‖
  · have := cell_le_gridNorm (tailPart R Y) x
    simp only [tailPart, h, ↓reduceIte] at this
    have h0 : 0 ≤ (1 / (N : ℝ)) ^ 2 * R := by positivity
    linarith
  · have : ‖Y x‖ ≤ R := not_lt.1 h
    have h1 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2)
    linarith [gridNorm_nonneg (tailPart R Y)]

/-! ### The screen hypotheses -/

/-- **The hypotheses of `lem:determinant-screen-flux`** on the periodic box of side `L`
(`h_k = L / n_k`, `n_k → ∞`): `L_k(x,μ,ν)` (`μ < ν`) are logarithms of the full plaquettes of the
`G_SM` links `U_k`; the literal full curvature `𝔽_k = h_k⁻² L_k` is bounded in `L²_h` and its
full-box adjoint Wilson modulus vanishes as `ρ ↓ 0` (positive displacements). -/
structure CurvatureScreen (L : ℝ) (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (U : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → SMGaugeGroup)
    (Lg : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → Fin 4 → LiePair) : Prop where
  pos : 0 < L
  tendsto : Tendsto n atTop atTop
  exp_fst : ∀ k x μ ν, μ < ν → NormedSpace.exp (Lg k x μ ν).1 = smU3 (plaq gridShift (U k) x μ ν)
  exp_snd : ∀ k x μ ν, μ < ν → NormedSpace.exp (Lg k x μ ν).2 = smU2 (plaq gridShift (U k) x μ ν)
  bdd : ∃ M, ∀ k, GridSobolev.gridL2Norm (L / n k) (curvPacket (L / n k) (Lg k)) ≤ M
  screen : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m →
    (m : ℝ) * (L / n k) ≤ ρ →
      GridSobolev.gridL2Norm (L / n k) (wilsonShift (adLinks (U k)) μ m
        (curvPacket (L / n k) (Lg k)) - curvPacket (L / n k) (Lg k)) ≤ ε

variable {L : ℝ} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
  {U : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → SMGaugeGroup}
  {Lg : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → Fin 4 → LiePair}

theorem CurvatureScreen.bdd_unit (S : CurvatureScreen L n U Lg) :
    ∃ M, ∀ k, gridNorm (curvPacket (L / n k) (Lg k)) ≤ M := by
  obtain ⟨M, hM⟩ := S.bdd
  refine ⟨M / L ^ 2, fun k => ?_⟩
  have := hM k
  rw [gridL2Norm_eq_gridNorm S.pos] at this
  rw [le_div_iff₀ (by have := S.pos; positivity)]
  linarith

theorem CurvatureScreen.screen_unit (S : CurvatureScreen L n U Lg) :
    ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
      gridNorm (wilsonShift (adLinks (U k)) μ m (curvPacket (L / n k) (Lg k)) -
        curvPacket (L / n k) (Lg k)) ≤ ε := by
  intro ε hε
  have hL := S.pos
  obtain ⟨ρ, hρ, hev⟩ := S.screen (L ^ 2 * ε) (by positivity)
  refine ⟨ρ / L, by positivity, hev.mono fun k hk μ m hm hmρ => ?_⟩
  have hk' := hk μ m hm (by
    have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
    calc (m : ℝ) * (L / n k) = (m : ℝ) / n k * L := by ring
      _ ≤ ρ / L * L := mul_le_mul_of_nonneg_right hmρ hL.le
      _ = ρ := by field_simp)
  rw [gridL2Norm_eq_gridNorm hL] at hk'
  exact le_of_mul_le_mul_left hk' (by positivity)

/-- **Eventual uniform smallness of the scaled full curvature** `h² 𝔽_h = L_h`: the
scalar-magnitude part of `thm:native-Wilson-compactness` (uniform integrability of
`|R^0 𝔽|²`) and the cell mass give `max_x h⁴ |𝔽_h(x)|² → 0`. -/
theorem CurvatureScreen.eventually_small (S : CurvatureScreen L n U Lg) :
    ∀ δ > 0, ∀ᶠ k in atTop, ∀ x (p : PairIdx), ‖toOp (Lg k x p.1.1 p.1.2)‖ ≤ δ := by
  intro δ hδ
  have hL := S.pos
  obtain ⟨M, hM⟩ := S.bdd_unit
  have hUI := native_wilson_magnitude_unifIntegrable n S.tendsto (fun k => adLinks (U k))
    (fun k => curvPacket (L / n k) (Lg k)) ⟨M, hM⟩ S.screen_unit
  set ε : ℝ := δ / (2 * L ^ 2) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨C, hC0, hC⟩ := exists_tail_le n (fun k => curvPacket (L / n k) (Lg k)) hM hUI hεpos
  have hlim : Tendsto (fun k => (1 / (n k : ℝ)) ^ 2 * C) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp S.tendsto
    have h2 : Tendsto (fun k => 1 / (n k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h1
    simpa using (h2.pow 2).mul_const C
  filter_upwards [hlim.eventually (gt_mem_nhds hεpos)] with k hk x p
  have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
  have hcell := cell_le_tail (curvPacket (L / n k) (Lg k)) hC0 x
  have htail := hC C le_rfl k
  have hpt : ‖curvPacket (L / n k) (Lg k) x p‖ ≤ ‖curvPacket (L / n k) (Lg k) x‖ :=
    norm_le_pi_norm _ p
  have hval : ‖curvPacket (L / n k) (Lg k) x p‖ =
      ((L / n k) ^ 2)⁻¹ * ‖toOp (Lg k x p.1.1 p.1.2)‖ := by
    simp only [curvPacket, toOp_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
  have hfin : (1 / (n k : ℝ)) ^ 2 * ‖curvPacket (L / n k) (Lg k) x‖ ≤ 2 * ε := by
    have := hk.le; linarith
  have key : ‖toOp (Lg k x p.1.1 p.1.2)‖ =
      L ^ 2 * ((1 / (n k : ℝ)) ^ 2 * ‖curvPacket (L / n k) (Lg k) x p‖) := by
    rw [hval]; field_simp
  rw [key]
  calc L ^ 2 * ((1 / (n k : ℝ)) ^ 2 * ‖curvPacket (L / n k) (Lg k) x p‖)
      ≤ L ^ 2 * (2 * ε) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (mul_le_mul_of_nonneg_left hpt (by positivity)).trans hfin
    _ = δ := by rw [hε]; field_simp

/-! ### Principal arguments of the Abelian plaquettes -/

theorem abPhase_self {N : ℕ} (u : (Fin 4 → ZMod N) → Fin 4 → ℂ) (hu : ∀ x μ, u x μ ≠ 0)
    (x : Fin 4 → ZMod N) (μ : Fin 4) : abPhase u x μ μ = 0 := by
  have h1 := hu x μ
  have h2 := hu (x + unitStep μ) μ
  simp only [abPhase, abPlaq]
  rw [show u x μ * u (x + unitStep μ) μ / (u (x + unitStep μ) μ * u x μ) = 1 by field_simp]
  exact Complex.arg_one

theorem abPhase_swap {N : ℕ} (u : (Fin 4 → ZMod N) → Fin 4 → ℂ) (hu : ∀ x μ, u x μ ≠ 0)
    (x : Fin 4 → ZMod N) (μ ν : Fin 4) (h : abPhase u x μ ν ≠ Real.pi) :
    abPhase u x ν μ = -abPhase u x μ ν := by
  have hinv : abPlaq u x ν μ = (abPlaq u x μ ν)⁻¹ := by
    have := hu x μ; have := hu x ν; have := hu (x + unitStep μ) ν; have := hu (x + unitStep ν) μ
    simp only [abPlaq]
    field_simp
  simp only [abPhase] at h ⊢
  rw [hinv, Complex.arg_inv, if_neg h]

theorem abPhase_eq_arg {N : ℕ} (V : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup)
    (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    abPhase (fun x μ => smChi (V x μ)) x μ ν = Complex.arg (smChi (plaq gridShift V x μ ν)) := by
  simp only [abPhase, smChi_plaq_eq_abPlaq]

/-- A fixed admissible radius: `2 c₀ < min(r, π)` with `r = pairChart`, and `2c₀ < π/3`. -/
def c₀ : ℝ := min pairChart (Real.pi / 3) / 4

theorem c₀_pos : 0 < c₀ := by
  unfold c₀; have := pairChart_pos; have := Real.pi_pos; positivity

theorem two_c₀_lt : 2 * c₀ < min pairChart Real.pi := by
  unfold c₀
  have h1 := pairChart_pos
  have h2 := Real.pi_pos
  rcases le_total pairChart (Real.pi / 3) with h | h
  · rw [min_eq_left h, lt_min_iff]; constructor <;> linarith
  · rw [min_eq_right h, lt_min_iff]; constructor <;> linarith

/-- **`f_h = ℓ_c(𝔽_h)` eventually** (first identity of `eq:determinant-inherited-screen`): for
large `k`, `ℓ_c(L_k(x,μ,ν)) = Arg χ(P_{U_k,μν}(x))` exactly. -/
theorem CurvatureScreen.eventually_ellC (S : CurvatureScreen L n U Lg) :
    ∀ᶠ k in atTop, ∀ x (p : PairIdx),
      ellC (Lg k x p.1.1 p.1.2) = (Complex.arg (smChi (plaq gridShift (U k) x p.1.1 p.1.2)) : ℂ) := by
  filter_upwards [S.eventually_small c₀ c₀_pos] with k hk x p
  exact ellC_eq_arg_smChi _ _ c₀ two_c₀_lt (S.exp_snd k x _ _ p.2)
    (fun i j => (entry_snd_le _ i j).trans (hk x p))

/-- **`max_{x,μ,ν} |φ_{μν,h}(x)| → 0`.** -/
theorem CurvatureScreen.eventually_phase_small (S : CurvatureScreen L n U Lg) :
    ∀ δ > 0, ∀ᶠ k in atTop, ∀ x μ ν, |abPhase (fun x μ => smChi (U k x μ)) x μ ν| ≤ δ := by
  intro δ hδ
  set δ' := min δ 1 with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ one_pos
  filter_upwards [S.eventually_small (δ' / 2) (by positivity), S.eventually_ellC] with k hk he
  have hu : ∀ x μ, smChi (U k x μ) ≠ 0 := fun x μ => smChi_ne_zero _
  have hlt : ∀ x (p : PairIdx), |abPhase (fun x μ => smChi (U k x μ)) x p.1.1 p.1.2| ≤ δ' := by
    intro x p
    rw [abPhase_eq_arg]
    have h1 := norm_ellC_le_two (Lg k x p.1.1 p.1.2)
    rw [he x p, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [hk x p]
  intro x μ ν
  rcases lt_trichotomy μ ν with h | rfl | h
  · exact (hlt x ⟨(μ, ν), h⟩).trans (min_le_left _ _)
  · rw [abPhase_self _ hu, abs_zero]; exact hδ.le
  · have h1 := hlt x ⟨(ν, μ), h⟩
    have hne : abPhase (fun x μ => smChi (U k x μ)) x ν μ ≠ Real.pi := by
      intro hπ
      rw [hπ, abs_of_pos Real.pi_pos] at h1
      have : δ' ≤ 1 := min_le_right _ _
      linarith [Real.pi_gt_three]
    rw [abPhase_swap _ hu x ν μ hne, abs_neg]
    exact h1.trans (min_le_left _ _)


/-! ### The ordinary modulus of `f` and the assembly -/

/-- `f = Re ℓ_c(𝔽)` eventually (pointwise form). -/
theorem CurvatureScreen.eventually_detPacket (S : CurvatureScreen L n U Lg) :
    ∀ᶠ k in atTop, ∀ x (p : PairIdx),
      ellC (ofOp (curvPacket (L / n k) (Lg k) x p)) = (detPacket (L / n k) (U k) x p : ℂ) := by
  filter_upwards [S.eventually_ellC] with k he x p
  simp only [curvPacket, ofOp_toOp, ellC_smul, he x p, detPacket]
  push_cast
  ring

theorem norm_detPacket_le {N : ℕ} (h : ℝ) (U : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup)
    (Y : (Fin 4 → ZMod N) → Packet)
    (he : ∀ x (p : PairIdx), ellC (ofOp (Y x p)) = (detPacket h U x p : ℂ)) (x : Fin 4 → ZMod N) :
    ‖detPacket h U x‖ ≤ 2 * ‖Y x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_
  have h1 := norm_ellC_le_two (ofOp (Y x p))
  rw [he x p, Complex.norm_real] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm (Y x) p) (by norm_num))

/-- **Modulus transfer** `ω_h(f) ≤ 2 Ω_h(𝔽)` (pointwise form): the `Ad`-invariant functional
`ℓ_c` turns the adjoint Wilson difference into the ordinary difference of `f`. -/
theorem norm_shift_detPacket_le {N : ℕ} [NeZero N] (h : ℝ)
    (U : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup) (Y : (Fin 4 → ZMod N) → Packet)
    (he : ∀ x (p : PairIdx), ellC (ofOp (Y x p)) = (detPacket h U x p : ℂ)) (μ : Fin 4) (m : ℕ)
    (x : Fin 4 → ZMod N) :
    ‖(shift μ (m : ℤ) (detPacket h U) - detPacket h U) x‖ ≤
      2 * ‖(wilsonShift (adLinks U) μ m Y - Y) x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_
  have key : ((((shift μ (m : ℤ) (detPacket h U) - detPacket h U) x) p : ℝ) : ℂ) =
      ellC (ofOp (((wilsonShift (adLinks U) μ m Y - Y) x) p)) := by
    simp only [Pi.sub_apply, shift_natCast_apply, wilsonShift]
    rw [ofOp_sub, ellC_sub, ellC_openLink, he, he]
    push_cast; ring
  have h1 := norm_ellC_le_two (ofOp (((wilsonShift (adLinks U) μ m Y - Y) x) p))
  rw [← key, Complex.norm_real] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ p) (by norm_num))

theorem gridNorm_le_two_mul {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {N : ℕ}
    [NeZero N] (u : (Fin 4 → ZMod N) → E) (v : (Fin 4 → ZMod N) → F) (h : ∀ x, ‖u x‖ ≤ 2 * ‖v x‖) :
    gridNorm u ≤ 2 * gridNorm v := by
  have h1 : gridNorm u ≤ gridNorm (fun x => 2 * ‖v x‖) :=
    gridNorm_mono fun x => (h x).trans (le_of_eq (by
      rw [Real.norm_of_nonneg (by positivity)]))
  rwa [gridNorm_const_mul _ (by norm_num), gridNorm_norm] at h1

theorem exists_bound_of_eventually (g : ℕ → ℝ) {M : ℝ} (h : ∀ᶠ k in atTop, g k ≤ M) :
    ∃ M', ∀ k, g k ≤ M' := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 h
  refine ⟨max M (∑ j ∈ Finset.range K, |g j|), fun k => ?_⟩
  by_cases hk : K ≤ k
  · exact le_max_of_le_left (hK k hk)
  · refine le_max_of_le_right ((le_abs_self _).trans ?_)
    exact Finset.single_le_sum (f := fun j => |g j|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.2 (not_le.1 hk))

/-- **`lem:determinant-screen-flux`.**  Under the full curvature screen (bounded literal curvature
in `L²_h`, vanishing full-box adjoint Wilson modulus), with `u = χ(U)`, `φ = Arg χ(P_U)`,
`f = h⁻² φ` (`detPacket`), `h_k = L / n_k`:
1. eventually `f_h = ℓ_c(𝔽_h)`;
2. eventually `‖T_{μ,m} f - f‖_{2,h} ≤ 2 ‖W_{μ,m} 𝔽 - 𝔽‖_{2,h}` for all `μ, m`;
3. `max_{x,μ,ν} |φ_{μν}(x)| → 0`;
4. `R_h^0 f_h` is precompact in `L²`;
5. eventually `d_h f_h = 0` (all cube sums vanish);
6. every coordinate-plane flux is `2π m` with `m ∈ ℤ`; eventually it is independent of the
   transverse base point, `\bar f_{μν} = 2π m / L²` and `2π |m| ≤ ‖f_{μν}‖_{2,h}`;
7. the integer vectors `(m_{μν})_{μ<ν}` are bounded and constant along a subsequence. -/
theorem determinant_screen_flux (S : CurvatureScreen L n U Lg) :
    (∀ᶠ k in atTop, ∀ x (p : PairIdx),
      ellC (ofOp (curvPacket (L / n k) (Lg k) x p)) = (detPacket (L / n k) (U k) x p : ℂ)) ∧
    (∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ),
      GridSobolev.gridL2Norm (L / n k) (shift μ (m : ℤ) (detPacket (L / n k) (U k)) -
        detPacket (L / n k) (U k)) ≤
      2 * GridSobolev.gridL2Norm (L / n k) (wilsonShift (adLinks (U k)) μ m
        (curvPacket (L / n k) (Lg k)) - curvPacket (L / n k) (Lg k))) ∧
    (∀ δ > 0, ∀ᶠ k in atTop, ∀ x μ ν, |abPhase (fun x μ => smChi (U k x μ)) x μ ν| ≤ δ) ∧
    TotallyBounded (range fun k => pcLp (detPacket (L / n k) (U k))) ∧
    (∀ᶠ k in atTop, ∀ x μ ν κ, cubeSum (abPhase (fun x μ => smChi (U k x μ))) x μ ν κ = 0) ∧
    (∀ k x₀ μ ν, ∃ m : ℤ, planeFlux (fun x μ => smChi (U k x μ)) x₀ μ ν = 2 * Real.pi * m) ∧
    (∀ᶠ k in atTop, ∀ x₀ μ ν, planeFlux (fun x μ => smChi (U k x μ)) x₀ μ ν =
      planeFlux (fun x μ => smChi (U k x μ)) 0 μ ν) ∧
    (∀ᶠ k in atTop, ∀ μ ν (m : ℤ),
      planeFlux (fun x μ => smChi (U k x μ)) 0 μ ν = 2 * Real.pi * m →
      ((n k : ℝ) * (L / n k))⁻¹ ^ 4 * ((L / n k) ^ 4 *
        ∑ x, abPhase (fun x μ => smChi (U k x μ)) x μ ν / (L / n k) ^ 2) =
        2 * Real.pi * m / ((n k : ℝ) * (L / n k)) ^ 2 ∧
      2 * Real.pi * |(m : ℝ)| ≤ Real.sqrt ((L / n k) ^ 4 *
        ∑ x, (abPhase (fun x μ => smChi (U k x μ)) x μ ν / (L / n k) ^ 2) ^ 2)) ∧
    (∃ m : ℕ → PairIdx → ℤ,
      (∀ k (p : PairIdx), planeFlux (fun x μ => smChi (U k x μ)) 0 p.1.1 p.1.2 =
        2 * Real.pi * m k p) ∧
      (∃ C : ℝ, ∀ k p, |(m k p : ℝ)| ≤ C) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ j, m (ψ j) = m (ψ 0)) := by
  have hL := S.pos
  have hι : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
  set u : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → ℂ := fun k x μ => smChi (U k x μ) with hu_def
  have hu : ∀ k x μ, ‖u k x μ‖ = 1 := fun k x μ => norm_smChi _
  have hE := S.eventually_detPacket
  -- (2) modulus transfer
  have hmod : ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ),
      gridNorm (shift μ (m : ℤ) (detPacket (L / n k) (U k)) - detPacket (L / n k) (U k)) ≤
      2 * gridNorm (wilsonShift (adLinks (U k)) μ m (curvPacket (L / n k) (Lg k)) -
        curvPacket (L / n k) (Lg k)) := by
    filter_upwards [hE] with k he μ m
    exact gridNorm_le_two_mul _ _ (norm_shift_detPacket_le _ _ _ he μ m)
  -- smallness of the phases
  have hsmall := S.eventually_phase_small
  have hπ3 : ∀ᶠ k in atTop, ∀ x μ ν, |Complex.arg (smChi (plaq gridShift (U k) x μ ν))| <
      Real.pi / 3 := by
    filter_upwards [hsmall (Real.pi / 4) (by positivity)] with k hk x μ ν
    rw [← abPhase_eq_arg]
    exact (hk x μ ν).trans_lt (by linarith [Real.pi_pos])
  have hexact := hπ3.mono fun k hk => determinant_screen_flux_exact hι (U k) hk
  -- boundedness of `f` in `L²`
  obtain ⟨M, hM⟩ := S.bdd_unit
  have hfb : ∀ᶠ k in atTop, gridNorm (detPacket (L / n k) (U k)) ≤ 2 * M := by
    filter_upwards [hE] with k he
    exact (gridNorm_le_two_mul _ _ (norm_detPacket_le _ _ _ he)).trans
      (mul_le_mul_of_nonneg_left (hM k) (by norm_num))
  obtain ⟨M', hM'⟩ := exists_bound_of_eventually _ hfb
  -- (4) precompactness
  have hTB : TotallyBounded (range fun k => pcLp (detPacket (L / n k) (U k))) := by
    refine native_discrete_KR n S.tendsto (fun k => detPacket (L / n k) (U k)) ⟨M', hM'⟩ ?_
    intro ε hε
    obtain ⟨ρ, hρ, hev⟩ := S.screen_unit (ε / 2) (by positivity)
    refine ⟨ρ, hρ, ?_⟩
    filter_upwards [hev, hmod] with k hk hk' μ m hm hmρ
    have := hk' μ m
    have := hk μ m hm hmρ
    linarith
  -- integer fluxes for all `k`
  have hint : ∀ k x₀ μ ν, ∃ m : ℤ, planeFlux (u k) x₀ μ ν = 2 * Real.pi * m :=
    fun k x₀ μ ν => planeFlux_integer (u k) (hu k) x₀ μ ν
  refine ⟨hE, ?_, hsmall, hTB, ?_, hint, ?_, ?_, ?_⟩
  · filter_upwards [hmod] with k hk μ m
    rw [gridL2Norm_eq_gridNorm hL, gridL2Norm_eq_gridNorm hL]
    have := hk μ m
    nlinarith [sq_nonneg L]
  · filter_upwards [hexact] with k hk
    exact hk.2.1
  · filter_upwards [hexact] with k hk
    exact hk.2.2.2.1
  · filter_upwards [hexact] with k hk μ ν m hm
    have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
    have hh : 0 < L / n k := by positivity
    exact ⟨mean_curvature_eq_flux (u k) hk.2.1 hι μ ν (L / n k) hh m hm,
      two_pi_abs_flux_le (u k) hk.2.1 hι μ ν (L / n k) hh m hm⟩
  · -- (7) bounded integer vectors and a constant subsequence
    set m : ℕ → PairIdx → ℤ := fun k p => Classical.choose (hint k 0 p.1.1 p.1.2) with hm_def
    have hm : ∀ k (p : PairIdx), planeFlux (u k) 0 p.1.1 p.1.2 = 2 * Real.pi * m k p :=
      fun k p => Classical.choose_spec (hint k 0 p.1.1 p.1.2)
    -- eventual bound `2π |m| ≤ ‖f‖_{2,h} ≤ 2 L² M`
    have hbound : ∀ᶠ k in atTop, ∑ p, |(m k p : ℝ)| ≤ Fintype.card PairIdx * (L ^ 2 * M) := by
      filter_upwards [hexact, hfb] with k hk hfk
      have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
      have hh : 0 < L / n k := by positivity
      have hone : ∀ p : PairIdx, |(m k p : ℝ)| ≤ L ^ 2 * M := by
        intro p
        have h1 := two_pi_abs_flux_le (u k) hk.2.1 hι p.1.1 p.1.2 (L / n k) hh (m k p) (hm k p)
        have h2 : Real.sqrt ((L / n k) ^ 4 *
            ∑ x, (abPhase (u k) x p.1.1 p.1.2 / (L / n k) ^ 2) ^ 2) ≤
            GridSobolev.gridL2Norm (L / n k) (detPacket (L / n k) (U k)) := by
          unfold GridSobolev.gridL2Norm periodicHodgeNormSq
          rw [hι]
          refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_)
            (by positivity))
          have h3 : |abPhase (u k) x p.1.1 p.1.2 / (L / n k) ^ 2| ≤
              ‖detPacket (L / n k) (U k) x‖ := by
            have := norm_le_pi_norm (detPacket (L / n k) (U k) x) p
            rw [Real.norm_eq_abs] at this
            rw [show abPhase (u k) x p.1.1 p.1.2 = _ from abPhase_eq_arg (U k) x p.1.1 p.1.2]
            exact this
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h3 2
        rw [gridL2Norm_eq_gridNorm hL] at h2
        have h4 : 2 * Real.pi * |(m k p : ℝ)| ≤ L ^ 2 * (2 * M) :=
          h1.trans (h2.trans (mul_le_mul_of_nonneg_left hfk (by positivity)))
        have hπ := Real.pi_gt_three
        nlinarith [abs_nonneg (m k p : ℝ), sq_nonneg L]
      calc ∑ p, |(m k p : ℝ)| ≤ ∑ _p : PairIdx, L ^ 2 * M := Finset.sum_le_sum fun p _ => hone p
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    obtain ⟨C, hC⟩ := exists_bound_of_eventually _ hbound
    have hCm : ∀ k p, |(m k p : ℝ)| ≤ C := fun k p =>
      (Finset.single_le_sum (f := fun p => |(m k p : ℝ)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ p)).trans (hC k)
    refine ⟨m, hm, ⟨C, hCm⟩, ?_⟩
    -- pigeonhole
    set B : ℕ := ⌈C⌉₊
    have hmem : ∀ k p, m k p ∈ Set.Icc (-(B : ℤ)) B := by
      intro k p
      have h1 := hCm k p
      have h2 : C ≤ (B : ℝ) := Nat.le_ceil C
      have h3 : |(m k p : ℝ)| ≤ (B : ℝ) := h1.trans h2
      rw [abs_le] at h3
      constructor
      · have : (-(B : ℝ)) ≤ (m k p : ℝ) := h3.1
        exact_mod_cast this
      · have : (m k p : ℝ) ≤ (B : ℝ) := h3.2
        exact_mod_cast this
    let G : ℕ → (PairIdx → Set.Icc (-(B : ℤ)) B) := fun k p => ⟨m k p, hmem k p⟩
    obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber G
    have hinf : (G ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
    have hfreq : ∃ᶠ k in atTop, G k = y := Nat.frequently_atTop_iff_infinite.2 hinf
    obtain ⟨ψ, hψ, hψy⟩ := extraction_of_frequently_atTop hfreq
    refine ⟨ψ, hψ, fun j => ?_⟩
    funext p
    have h1 := congrArg (fun F => (F p : ℤ)) (hψy j)
    have h2 := congrArg (fun F => (F p : ℤ)) (hψy 0)
    simp only [G] at h1 h2
    rw [h1, h2]


/-- Non-vacuity of the screen hypotheses: trivial links with zero logarithms on the box of side
`2π` (grids `n_k = k + 1`). -/
theorem curvatureScreen_trivial :
    CurvatureScreen (2 * Real.pi) (fun k => k + 1) (fun _ _ _ => 1) (fun _ _ _ _ => 0) := by
  have hp : ∀ (N : ℕ) (x : Fin 4 → ZMod N) (μ ν : Fin 4),
      plaq gridShift (fun _ _ => (1 : SMGaugeGroup)) x μ ν = 1 := by
    intro N x μ ν; simp [plaq]
  have hc : ∀ (N : ℕ) (h : ℝ), curvPacket (N := N) h (fun _ _ _ => 0) = 0 := by
    intro N h; funext x p; simp [curvPacket, toOp]; rfl
  have h0 : ∀ (N : ℕ) [NeZero N] (h : ℝ),
      GridSobolev.gridL2Norm h (0 : (Fin 4 → ZMod N) → Packet) = 0 := by
    intro N _ h; simp [GridSobolev.gridL2Norm, periodicHodgeNormSq]
  refine ⟨by positivity, tendsto_add_atTop_nat 1, fun k x μ ν _ => ?_, fun k x μ ν _ => ?_,
    ⟨0, fun k => ?_⟩, fun ε hε => ⟨1, one_pos, Eventually.of_forall fun k μ m _ _ => ?_⟩⟩
  · rw [hp]; simp
  · rw [hp]; simp
  · rw [hc, h0]
  · rw [hc]
    have : wilsonShift (adLinks fun _ _ => (1 : SMGaugeGroup)) μ m
        (0 : (Fin 4 → ZMod (k + 1)) → Packet) = 0 := by
      funext x; simp [wilsonShift]
    rw [this, sub_zero, h0]; exact hε.le


/-! ### `prop:native-determinant-split` for screened sequences -/

theorem scalar_conj {m : Type*} [Fintype m] [DecidableEq m] (e : ℂ) (he : e * star e = 1)
    (Y A : Matrix m m ℂ) : (e • Y) * A * star (e • Y) = Y * A * star Y := by
  rw [star_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, mul_comm, he,
    one_smul]

theorem exp_mul_star (θ : ℝ) :
    Complex.exp (θ * Complex.I) * star (Complex.exp (θ * Complex.I)) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp

/-- Central elements act trivially in the adjoint representation. -/
theorem adPair_centralElem_mul (s : ℝ) (y : SMGaugeGroup) :
    adPair (centralElem s * y) = adPair y := by
  have h3 : smU3 (centralElem s * y) = Complex.exp ((-(s / 3) : ℝ) * Complex.I) • smU3 y := by
    rw [map_mul, centralElem_U3, Matrix.smul_mul, Matrix.one_mul]; push_cast; ring_nf
  have h2 : smU2 (centralElem s * y) = Complex.exp (((s / 2) : ℝ) * Complex.I) • smU2 y := by
    rw [map_mul, centralElem_U2, Matrix.smul_mul, Matrix.one_mul]; push_cast; ring_nf
  refine LinearIsometryEquiv.ext fun X => ?_
  change toOp (_, _) = toOp (_, _)
  rw [h3, h2, scalar_conj _ (exp_mul_star _), scalar_conj _ (exp_mul_star _)]

/-- **Adjoint Wilson transport of `V` equals that of `U`** (central factors act trivially). -/
theorem adLinks_splitLinks {N : ℕ} (h : ℝ) (t : (Fin 4 → ZMod N) → ℝ)
    (a : (Fin 4 → ZMod N) → Fin 4 → ℝ) (U : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup) :
    adLinks (splitLinks gridShift h t a U) = adLinks U := by
  funext μ x
  simp only [adLinks, adPacket, splitLinks, gaugeTr, central_conj, adPair_centralElem_mul]

/-- The semisimple projection `Π_ss` on `OpPair`. -/
def piSSOp (X : OpPair) : OpPair := toOp (piSS (ofOp X))

/-- The norm constant of `Π_ss`. -/
def cSS : ℝ := 1 + 2 * ‖toOp Zc‖

theorem piSSOp_eq (X : OpPair) : piSSOp X = X - ellC (ofOp X) • toOp Zc := rfl

theorem norm_piSSOp_le (X : OpPair) : ‖piSSOp X‖ ≤ cSS * ‖X‖ := by
  rw [piSSOp_eq, cSS]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul]
  have := norm_ellC_le_two (ofOp X)
  have e : toOp (ofOp X) = X := rfl
  rw [e] at this
  nlinarith [norm_nonneg (toOp Zc), norm_nonneg X, norm_nonneg (ellC (ofOp X))]

theorem piSSOp_sub (X Y : OpPair) : piSSOp (X - Y) = piSSOp X - piSSOp Y := by
  rw [piSSOp_eq, piSSOp_eq, piSSOp_eq, ofOp_sub, ellC_sub, sub_smul]; abel

theorem adPair_Zc (g : SMGaugeGroup) : adPair g (toOp Zc) = toOp Zc := by
  have h3 := (Matrix.mem_unitaryGroup_iff (A := smU3 g)).1 (smU3_mem_unitaryGroup g)
  have h2 := (Matrix.mem_unitaryGroup_iff (A := smU2 g)).1 (smU2_mem_unitaryGroup g)
  change toOp (_, _) = toOp Zc
  simp only [ofOp_toOp, Zc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h3, h2]

theorem piSSOp_adPair (g : SMGaugeGroup) (X : OpPair) :
    piSSOp (adPair g X) = adPair g (piSSOp X) := by
  rw [piSSOp_eq, piSSOp_eq, map_sub, map_smul, adPair_Zc, ellC_adPair]

theorem piSSOp_openLink {N : ℕ} (U : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup) (μ : Fin 4)
    (m : ℕ) (x : Fin 4 → ZMod N) (v : Packet) (p : PairIdx) :
    piSSOp ((openLink (adLinks U) μ m x v) p) =
      (openLink (adLinks U) μ m x (fun q => piSSOp (v q))) p := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
      change piSSOp (adPair (U x μ) ((openLink (adLinks U) μ m (x + Pi.single μ 1) v) p)) =
        adPair (U x μ) ((openLink (adLinks U) μ m (x + Pi.single μ 1)
          (fun q => piSSOp (v q))) p)
      rw [piSSOp_adPair, ih]

/-- The semisimple curvature packet `Π_ss 𝔽 = (h⁻² Π_ss L)_{μ<ν}`; by
`eq:determinant-semisimple-curvature` it is the literal curvature of `V` for small `h`. -/
def ssPacket {N : ℕ} (h : ℝ) (Lg : (Fin 4 → ZMod N) → Fin 4 → Fin 4 → LiePair)
    (x : Fin 4 → ZMod N) : Packet :=
  fun p => piSSOp (curvPacket h Lg x p)

theorem gridL2Norm_le_const_mul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ} [NeZero N] {h c : ℝ} (hc : 0 ≤ c)
    (u : (Fin 4 → ZMod N) → E) (v : (Fin 4 → ZMod N) → F) (huv : ∀ x, ‖u x‖ ≤ c * ‖v x‖) :
    GridSobolev.gridL2Norm h u ≤ c * GridSobolev.gridL2Norm h v := by
  unfold GridSobolev.gridL2Norm periodicHodgeNormSq
  rw [Fintype.card_fin]
  have h4 : 0 ≤ h ^ 4 := by positivity
  have hs : h ^ 4 * ∑ x, ‖u x‖ ^ 2 ≤ c ^ 2 * (h ^ 4 * ∑ x, ‖v x‖ ^ 2) := by
    calc h ^ 4 * ∑ x, ‖u x‖ ^ 2 ≤ h ^ 4 * ∑ x, (c * ‖v x‖) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ =>
            pow_le_pow_left₀ (norm_nonneg _) (huv x) 2) h4
      _ = c ^ 2 * (h ^ 4 * ∑ x, ‖v x‖ ^ 2) := by
          simp_rw [mul_pow]; rw [← Finset.mul_sum]; ring
  calc Real.sqrt (h ^ 4 * ∑ x, ‖u x‖ ^ 2)
      ≤ Real.sqrt (c ^ 2 * (h ^ 4 * ∑ x, ‖v x‖ ^ 2)) := Real.sqrt_le_sqrt hs
    _ = c * Real.sqrt (h ^ 4 * ∑ x, ‖v x‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- **The semisimple curvature screen is bounded by the full screen**: for any site lifts `t` and
potential `a`, the Wilson differences of `Π_ss 𝔽` transported by `V = e^{-haZ_c} U^{e^{tZ_c}}`
are bounded by `c_ss` times the Wilson differences of `𝔽` transported by `U`
(`prop:native-determinant-split`). -/
theorem ss_screen_le {N : ℕ} [NeZero N] {h : ℝ} (t : (Fin 4 → ZMod N) → ℝ)
    (a : (Fin 4 → ZMod N) → Fin 4 → ℝ) (U : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup)
    (Lg : (Fin 4 → ZMod N) → Fin 4 → Fin 4 → LiePair) (μ : Fin 4) (m : ℕ) :
    GridSobolev.gridL2Norm h (wilsonShift (adLinks (splitLinks gridShift h t a U)) μ m
        (ssPacket h Lg) - ssPacket h Lg) ≤
      cSS * GridSobolev.gridL2Norm h (wilsonShift (adLinks U) μ m (curvPacket h Lg) -
        curvPacket h Lg) := by
  rw [adLinks_splitLinks]
  refine gridL2Norm_le_const_mul (by unfold cSS; positivity) _ _ fun x => ?_
  refine (pi_norm_le_iff_of_nonneg (by unfold cSS; positivity)).2 fun p => ?_
  have hpt : ((wilsonShift (adLinks U) μ m (ssPacket h Lg) - ssPacket h Lg) x) p =
      piSSOp (((wilsonShift (adLinks U) μ m (curvPacket h Lg) - curvPacket h Lg) x) p) := by
    simp only [Pi.sub_apply, wilsonShift, piSSOp_sub, piSSOp_openLink]
    rfl
  rw [hpt]
  exact (norm_piSSOp_le _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ p)
    (by unfold cSS; positivity))

/-- Logarithms of all oriented plaquettes from those with `μ < ν`
(`P_{νμ} = P_{μν}⁻¹`, `P_{μμ} = 1`). -/
def extLog {N : ℕ} (Lg : (Fin 4 → ZMod N) → Fin 4 → Fin 4 → LiePair) (x : Fin 4 → ZMod N)
    (μ ν : Fin 4) : LiePair :=
  if μ < ν then Lg x μ ν else if ν < μ then -(Lg x ν μ) else 0

theorem plaq_swap {N : ℕ} (V : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup) (x : Fin 4 → ZMod N)
    (μ ν : Fin 4) : plaq gridShift V x ν μ = (plaq gridShift V x μ ν)⁻¹ := by
  simp only [plaq, mul_inv_rev, inv_inv, mul_assoc]

theorem plaq_self {N : ℕ} (V : (Fin 4 → ZMod N) → Fin 4 → SMGaugeGroup) (x : Fin 4 → ZMod N)
    (μ : Fin 4) : plaq gridShift V x μ μ = 1 := by
  simp [plaq]

theorem smU3_inv (y : SMGaugeGroup) : smU3 y⁻¹ = (smU3 y)⁻¹ :=
  (Matrix.inv_eq_left_inv (by rw [← map_mul, inv_mul_cancel, map_one])).symm

theorem smU2_inv (y : SMGaugeGroup) : smU2 y⁻¹ = (smU2 y)⁻¹ :=
  (Matrix.inv_eq_left_inv (by rw [← map_mul, inv_mul_cancel, map_one])).symm

theorem CurvatureScreen.extLog_spec (S : CurvatureScreen L n U Lg) (k : ℕ)
    (x : Fin 4 → ZMod (n k)) (μ ν : Fin 4) :
    NormedSpace.exp (extLog (Lg k) x μ ν).1 = smU3 (plaq gridShift (U k) x μ ν) ∧
      NormedSpace.exp (extLog (Lg k) x μ ν).2 = smU2 (plaq gridShift (U k) x μ ν) := by
  unfold extLog
  rcases lt_trichotomy μ ν with h | rfl | h
  · rw [if_pos h]; exact ⟨S.exp_fst k x μ ν h, S.exp_snd k x μ ν h⟩
  · rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), plaq_self]
    simp
  · rw [if_neg (not_lt.2 h.le), if_pos h, plaq_swap _ x ν μ, smU3_inv, smU2_inv]
    simp only [Prod.fst_neg, Prod.snd_neg, Matrix.exp_neg]
    rw [S.exp_fst k x ν μ h, S.exp_snd k x ν μ h]
    exact ⟨rfl, rfl⟩

theorem CurvatureScreen.extLog_small (S : CurvatureScreen L n U Lg) :
    ∀ᶠ k in atTop, ∀ x μ ν, (∀ i j, ‖(extLog (Lg k) x μ ν).1 i j‖ ≤ c₀) ∧
      ∀ i j, ‖(extLog (Lg k) x μ ν).2 i j‖ ≤ c₀ := by
  filter_upwards [S.eventually_small c₀ c₀_pos] with k hk x μ ν
  unfold extLog
  rcases lt_trichotomy μ ν with h | rfl | h
  · rw [if_pos h]
    exact ⟨fun i j => (entry_fst_le _ i j).trans (hk x ⟨(μ, ν), h⟩),
      fun i j => (entry_snd_le _ i j).trans (hk x ⟨(μ, ν), h⟩)⟩
  · rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
    exact ⟨fun i j => by simp [c₀_pos.le], fun i j => by simp [c₀_pos.le]⟩
  · rw [if_neg (not_lt.2 h.le), if_pos h]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using (entry_fst_le _ i j).trans (hk x ⟨(ν, μ), h⟩)
    · simpa using (entry_snd_le _ i j).trans (hk x ⟨(ν, μ), h⟩)

/-- **`prop:native-determinant-split` for screened sequences.**  Let the full curvature screen
hold and the determinant flux vanish (for all large `k`).  Then, for all large `k`, with the
paper's potential `a⁰ = δ_h Δ_h^† f` and the logarithms `L = extLog L_k`, there are constants
`c` and site lifts `t` such that (all conclusions of `native_determinant_split_exact`):
the Abelian normalization holds with `δ_h(a⁰ + c) = 0`; `ℓ_c(L) = h² f`; `V ∈ G_ss` exactly;
`P_{U'} = e^{h² f Z_c} P_V`; the chart logarithm of `P_V` is `Π_ss L`, i.e.
`F_h(V) = Π_ss F_h(U')` (`eq:determinant-semisimple-curvature`); `Ad V = Ad U'`; lift changes are
central `G_ss` gauges `z₆^k`; and, for all `μ, m`, the semisimple curvature screen of `V` is
bounded by `c_ss` times the full screen of `U` (`ss_screen_le`). -/
theorem native_determinant_split (S : CurvatureScreen L n U Lg)
    (hflux : ∀ᶠ k in atTop, ∀ μ ν, planeFlux (fun x μ => smChi (U k x μ)) 0 μ ν = 0) :
    ∀ᶠ k in atTop,
    let h := L / n k
    let a0 := detPotential (fun x μ => smChi (U k x μ)) h
    ∃ (cst : Fin 4 → ℝ) (t : (Fin 4 → ZMod (n k)) → ℝ),
      (∀ μ, -Real.pi < n k * h * cst μ ∧ n k * h * cst μ ≤ Real.pi) ∧
      (∀ x μ, Complex.exp (t x * Complex.I) * smChi (U k x μ) *
        Complex.exp (-(t (gridShift x μ) * Complex.I)) =
          Complex.exp (h * ((a0 x μ + cst μ : ℝ) : ℂ) * Complex.I)) ∧
      (∀ x, gridDiv (fun x μ => a0 x μ + cst μ) x = 0) ∧
      let a : (Fin 4 → ZMod (n k)) → Fin 4 → ℝ := fun x μ => a0 x μ + cst μ
      let f : (Fin 4 → ZMod (n k)) → Fin 4 → Fin 4 → ℝ :=
        fun x μ ν => Complex.arg (smChi (plaq gridShift (U k) x μ ν)) / h ^ 2
      (∀ x μ ν, ellC (extLog (Lg k) x μ ν) = (h ^ 2 * f x μ ν : ℝ)) ∧
      (∀ x μ, smChi (splitLinks gridShift h t a (U k) x μ) = 1 ∧
        (smU3 (splitLinks gridShift h t a (U k) x μ)).det = 1 ∧
        (smU2 (splitLinks gridShift h t a (U k) x μ)).det = 1) ∧
      (∀ x μ ν, plaq gridShift (gaugeTr gridShift (fun x => centralElem (t x)) (U k)) x μ ν =
        centralElem (h ^ 2 * f x μ ν) * plaq gridShift (splitLinks gridShift h t a (U k)) x μ ν) ∧
      (∀ x μ ν, ∀ Y ∈ pairBall pairChart,
        NormedSpace.exp Y.1 = smU3 (plaq gridShift (splitLinks gridShift h t a (U k)) x μ ν) →
        NormedSpace.exp Y.2 = smU2 (plaq gridShift (splitLinks gridShift h t a (U k)) x μ ν) →
        Y = piSS (extLog (Lg k) x μ ν)) ∧
      (∀ x μ w, splitLinks gridShift h t a (U k) x μ * w *
          (splitLinks gridShift h t a (U k) x μ)⁻¹ =
        gaugeTr gridShift (fun x => centralElem (t x)) (U k) x μ * w *
          (gaugeTr gridShift (fun x => centralElem (t x)) (U k) x μ)⁻¹) ∧
      (∀ (j : (Fin 4 → ZMod (n k)) → ℤ) x μ,
        splitLinks gridShift h (fun x => t x + 2 * Real.pi * j x) a (U k) x μ =
          gaugeTr gridShift (fun x => zSix ^ j x) (splitLinks gridShift h t a (U k)) x μ) ∧
      (∀ (μ : Fin 4) (m : ℕ),
        GridSobolev.gridL2Norm h (wilsonShift (adLinks (splitLinks gridShift h t a (U k))) μ m
            (ssPacket h (Lg k)) - ssPacket h (Lg k)) ≤
          cSS * GridSobolev.gridL2Norm h (wilsonShift (adLinks (U k)) μ m
            (curvPacket h (Lg k)) - curvPacket h (Lg k))) := by
  have hL := S.pos
  filter_upwards [hflux, S.extLog_small, S.eventually_phase_small (Real.pi / 4) (by positivity)]
    with k hfk hsk hph
  intro h a0
  have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
  have hh : 0 < h := by positivity
  have hsmall : ∀ x μ ν, |Complex.arg (smChi (plaq gridShift (U k) x μ ν))| < Real.pi / 3 := by
    intro x μ ν
    rw [← abPhase_eq_arg]
    exact (hph x μ ν).trans_lt (by linarith [Real.pi_pos])
  obtain ⟨cst, t, h1, h2, h3, h4⟩ := native_determinant_split_exact (U k) hh hsmall hfk c₀
    two_c₀_lt (extLog (Lg k)) (fun x μ ν => (S.extLog_spec k x μ ν).1)
    (fun x μ ν => (S.extLog_spec k x μ ν).2) (fun x μ ν => (hsk x μ ν).1)
    (fun x μ ν => (hsk x μ ν).2)
  obtain ⟨h5, h6, h7, h8, h9, h10⟩ := h4
  exact ⟨cst, t, h1, h2, h3, h5, h6, h7, h8, h9, h10, fun μ m => ss_screen_le t _ (U k) (Lg k) μ m⟩


/-- Non-vacuity of `native_determinant_split`: the trivial screened sequence has zero
determinant flux. -/
theorem planeFlux_trivial (N : ℕ) [NeZero N] (μ ν : Fin 4) :
    planeFlux (fun (x : Fin 4 → ZMod N) (μ : Fin 4) => smChi ((fun _ _ => (1 : SMGaugeGroup)) x μ))
      0 μ ν = 0 := by
  simp [planeFlux, abPhase, abPlaq]

end

end RenewalGeometry.DeterminantScreenFlux
