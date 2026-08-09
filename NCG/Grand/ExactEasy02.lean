/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.GrandCountermodels
import NCG.Grand.RecordChain
import NCG.Grand.GrandNoGoPair
import NCG.Grand.GaplessComparison
import NCG.Grand.ZenoLedger
import NCG.Grand.NonminimalFactorization
import NCG.Grand.GrandNotMonoidal
import NCG.Grand.FreshInvisibility

/-!
# Exact re-encodings, EASY batch 02 (Gran-Tensor manuscript)

Exact full-statement formalizations of the following records, each
previously covered only by partial-progress slices:

* `cth:ambient-invisible` — `ambientInvisibleExact`: the ambient
  extension `𝓗' = 𝓗 ⊕ 𝓩`, `U'_g = U_g ⊕ V_g`, `T' = T ⊕ A`,
  `S' = S ⊕ 0` keeps every declared source moment, and the
  previously dropped equivariant layer is restored: `U'` is again a
  unitary representation, commutes with `T'`, and intertwines `S'`.
* `cth:ar-unrecorded-no-go` — `unrecordedNoGoExact`: for every
  `X ≥ 2` an explicit bare core with history algebra `ℂ` (dimension
  one, trivial constant table) into which neither the record ladder
  `ℂ^X` nor the record algebra `M_X(ℂ)` embeds.
* `cth:coherence-no-go` — `coherenceNoGoExact`: no rule that is a
  function of the two diagonal CP branches alone identifies the
  off-diagonal coherence of every (unitary) realization.
* `cth:finite-complete-not-uniform` — `finiteCompleteNotUniformExact`:
  invertibility for every `ε > 0`, the least Rayleigh quotient of
  `S_ε^*S_ε` (i.e. `λ_min`) pinched in `[0, ε²/2]` and tending to `0`
  as `ε ↓ 0`, and failure of any uniform frame floor.
* `cth:growing-ledger-gap` — `growingLedgerGapBoxed`,
  `growingLedgerGapExact`: the boxed bound `q_N^{N-1} ≥ κ^{-1/2}`
  and the boxed liminf clause `liminf q_N ≥ 1`.
* `cth:nonminimal-factorization` — `nonminimalFactorizationExact`:
  one scalar table with a one-dimensional support-minimal
  realization and a positive nonminimal realization whose ambient
  Hilbert–Schmidt-adjoint pair is noncommutative.
* `cth:pairwise-not-monoidal-new` — `pairwiseNotMonoidalExact`: two
  unital `*`-algebra structures on one Hilbert transfer datum with
  identical degree-one/pairwise moments; one commutative, the other
  noncommutative and simple (every nonzero element two-sidedly
  absorbs to the unit).
* `cth:private-fingerprint-no-provenance-channel` —
  `privateFingerprintNoProvenanceChannelExact`: the one-way
  extension propagates the provenance space by `D₀`, routes nothing
  into the active future, keeps every declared packet marginal, and
  the marginals impose no condition on `D₀`.
* `cth:relative-interface-frame` — `relativeInterfaceFrameWitness`,
  `relativeInterfaceFrameExact`: the `diag(2,1)/diag(1,2)`
  equal-spectra pair with different glued responses; no
  similarity-invariant rule computes the glued response.
* `cth:renewal-Zeno` — `renewalZenoNormCollapse`, `renewalZenoJump`,
  `renewalZenoRateDeficit`, `renewalZenoExact`: the displayed norm
  collapse, the jump discontinuity of the limiting family, and the
  order-`τ` deficit rate `e^{-λτ_X}` giving the finite dense rate
  `e^{-λt}`.
-/

open Matrix Filter Topology

namespace NCG

/-! ## `cth:ambient-invisible` -/

open scoped ComplexOrder in
/-- `cth:ambient-invisible` (exact): let `(𝓗, U, T, S)` be an
equivariant source realization (`U` a unitary representation
commuting with `T` and intertwining `S` through the port
representation `W`) and let a nonzero space `𝓩` carry a
representation `V` and a positive contraction `A` commuting with it.
For the ambient extension `U'_g = U_g ⊕ V_g`, `T' = T ⊕ A`,
`S' = S ⊕ 0`: (1) every declared source moment `S'ᴴT'ⁿS'` equals
`SᴴTⁿS`; (2) `U'` is multiplicative; (3) `U'` is unitary;
(4) `U'` commutes with `T'`; (5) `U'` intertwines `S'` through the
same port representation — the extension is again an equivariant
source realization with identical data, although `𝓩` may carry
arbitrary additional sectors.  ("Representation" is rendered as a
unitary multiplicative family, the Hilbert-space reading.) -/
theorem ambientInvisibleExact {G m z p : Type*} [Mul G]
    [Fintype m] [Fintype z] [Fintype p]
    [DecidableEq m] [DecidableEq z]
    (U : G → Matrix m m ℂ) (V : G → Matrix z z ℂ)
    (W : G → Matrix p p ℂ)
    (T : Matrix m m ℂ) (A : Matrix z z ℂ) (S : Matrix m p ℂ)
    (_hZ : Nonempty z)
    (_hA0 : A.PosSemidef)
    (_hA1 : (1 - A).PosSemidef)
    (hUmul : ∀ g h, U (g * h) = U g * U h)
    (hVmul : ∀ g h, V (g * h) = V g * V h)
    (hUuni : ∀ g, (U g)ᴴ * U g = 1)
    (hVuni : ∀ g, (V g)ᴴ * V g = 1)
    (hUT : ∀ g, U g * T = T * U g)
    (hUS : ∀ g, U g * S = S * W g)
    (hAV : ∀ g, A * V g = V g * A) :
    (∀ n : ℕ,
      (Matrix.fromRows S (0 : Matrix z p ℂ))ᴴ
          * Matrix.fromBlocks T 0 0 A ^ n
          * Matrix.fromRows S (0 : Matrix z p ℂ)
        = Sᴴ * T ^ n * S)
    ∧ (∀ g h, Matrix.fromBlocks (U (g * h)) 0 0 (V (g * h))
        = Matrix.fromBlocks (U g) 0 0 (V g)
          * Matrix.fromBlocks (U h) 0 0 (V h))
    ∧ (∀ g, (Matrix.fromBlocks (U g) 0 0 (V g))ᴴ
        * Matrix.fromBlocks (U g) 0 0 (V g) = 1)
    ∧ (∀ g, Matrix.fromBlocks (U g) 0 0 (V g)
          * Matrix.fromBlocks T 0 0 A
        = Matrix.fromBlocks T 0 0 A
          * Matrix.fromBlocks (U g) 0 0 (V g))
    ∧ (∀ g, Matrix.fromBlocks (U g) 0 0 (V g)
          * Matrix.fromRows S (0 : Matrix z p ℂ)
        = Matrix.fromRows S (0 : Matrix z p ℂ) * W g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- declared source moments are unchanged
    intro n
    rw [Matrix.fromBlocks_diagonal_pow,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp
  · -- the direct-sum layer is multiplicative
    intro g h
    rw [Matrix.fromBlocks_multiply]
    simp [hUmul, hVmul]
  · -- the direct-sum layer is unitary
    intro g
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp [hUuni g, hVuni g, Matrix.fromBlocks_one]
  · -- the direct-sum layer commutes with `T' = T ⊕ A`
    intro g
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hUT g, hAV g]
  · -- the direct-sum layer intertwines `S' = S ⊕ 0`
    intro g
    rw [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
    simp [hUS g]

/-! ## `cth:ar-unrecorded-no-go` -/

/-- `cth:ar-unrecorded-no-go` (exact): for every `X ≥ 2` there is a
bare finite predictive core — the one-dimensional scalar core
`T = S = 1` on `ℂ¹` — whose record-discarded history algebra is `ℂ`:
it realizes the trivial constant table, its carrier has dimension
one, and it contains no pointed `X`-endpoint successor corner:
neither the `X`-dimensional record ladder `ℂ^X` nor the record
algebra `M_X(ℂ)` embeds into it.  Hence the core⇒arithmetic
implication `𝕋^core ⟹ 𝕋^ar` fails in general. -/
theorem unrecordedNoGoExact (X : ℕ) (hX : 2 ≤ X) :
    ∃ T S : Matrix (Fin 1) (Fin 1) ℂ,
      (∀ n : ℕ, Sᴴ * T ^ n * S = 1)
      ∧ Module.finrank ℂ (Matrix (Fin 1) (Fin 1) ℂ) = 1
      ∧ (¬∃ g : (Fin X → ℂ) →ₗ[ℂ] Matrix (Fin 1) (Fin 1) ℂ,
          Function.Injective g)
      ∧ ¬∃ f : Matrix (Fin X) (Fin X) ℂ →ₗ[ℂ]
          Matrix (Fin 1) (Fin 1) ℂ, Function.Injective f := by
  have hdim1 : Module.finrank ℂ (Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    rw [Module.finrank_matrix]
    simp
  refine ⟨1, 1, ?_, hdim1, ?_, ?_⟩
  · intro n
    simp
  · rintro ⟨g, hg⟩
    have hle := LinearMap.finrank_le_finrank_of_injective hg
    rw [Module.finrank_fin_fun, hdim1] at hle
    omega
  · rintro ⟨f, hf⟩
    have hle := LinearMap.finrank_le_finrank_of_injective hf
    have hdimX : Module.finrank ℂ (Matrix (Fin X) (Fin X) ℂ)
        = X * X := by
      rw [Module.finrank_matrix]
      simp
    rw [hdimX, hdim1] at hle
    nlinarith

/-! ## `cth:coherence-no-go` -/

/-- `cth:coherence-no-go` (exact): no rule derived only from the two
diagonal CP branches identifies the physical off-diagonal coherence
of every realization.  A "rule from the diagonal branches" is any
function `R` of the diagonal branch data `X ↦ (Φ X) i i`; the
realizations range over the unitary conjugation channels.  The
identity and `Z`-conjugation channels have identical diagonal branch
data but coherences `+1` and `-1` on the score word `E₀₁`, so no
such `R` exists. -/
theorem coherenceNoGoExact :
    ¬∃ R : (Matrix (Fin 2) (Fin 2) ℂ → Fin 2 → ℂ) → ℂ,
      ∀ U : Matrix (Fin 2) (Fin 2) ℂ, Uᴴ * U = 1 →
        R (fun X i => (U * X * Uᴴ) i i)
          = (U * (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℂ) * Uᴴ) 0 1 := by
  rintro ⟨R, hR⟩
  have hZH : clockZᴴ = clockZ := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [clockZ, Matrix.conjTranspose_apply]
  have hZuni : clockZᴴ * clockZ = 1 := by
    rw [hZH]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [clockZ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply]
  have h1 := hR 1 (by simp)
  have hZ := hR clockZ hZuni
  have hdata : (fun X i => (clockZ * X * clockZᴴ) i i)
      = fun (X : Matrix (Fin 2) (Fin 2) ℂ) i =>
          ((1 : Matrix (Fin 2) (Fin 2) ℂ) * X
            * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) i i := by
    funext X i
    rw [hZH, Matrix.conjTranspose_one, Matrix.mul_one,
      Matrix.one_mul]
    exact coherence_no_go.1 X i
  rw [hdata, h1] at hZ
  have hL : ((1 : Matrix (Fin 2) (Fin 2) ℂ)
      * (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℂ)
      * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) 0 1 = 1 := by
    simp
  have hRr : (clockZ
      * (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℂ)
      * clockZᴴ) 0 1
      = -1 := by
    rw [hZH]
    simp [clockZ, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.single_apply, Matrix.vecMul, dotProduct]
  rw [hL, hRr] at hZ
  norm_num at hZ

/-! ## `cth:finite-complete-not-uniform` -/

/-- The least Rayleigh value of `SᵀS`: the infimum of
`‖Sv‖²/‖v‖²` over nonzero `v` — the Courant–Fischer description of
`λ_min(S^*S)`. -/
noncomputable def rayleighFloor (S : Matrix (Fin 2) (Fin 2) ℝ) :
    ℝ :=
  sInf {r : ℝ | ∃ v : Fin 2 → ℝ, v ⬝ᵥ v ≠ 0
    ∧ r = ((S *ᵥ v) ⬝ᵥ (S *ᵥ v)) / (v ⬝ᵥ v)}

/-- `cth:finite-complete-not-uniform` (exact): for every `ε > 0`
the synthesis `S_ε = [[1,1],[0,ε]]` is invertible (source
complete), while `λ_min(S_ε^*S_ε)` — rendered as the least Rayleigh
value `rayleighFloor` — is pinched in `[0, ε²/2]` and tends to `0`
as `ε ↓ 0`.  Therefore pointwise finite source completeness gives
no uniform frame floor (the bounded-pseudoinverse and continuum
clauses of the manuscript are glosses of this failure). -/
theorem finiteCompleteNotUniformExact :
    (∀ ε : ℝ, 0 < ε →
      IsUnit (!![1, 1; 0, ε] : Matrix (Fin 2) (Fin 2) ℝ))
    ∧ (∀ ε : ℝ, 0 ≤ rayleighFloor !![1, 1; 0, ε]
        ∧ rayleighFloor !![1, 1; 0, ε] ≤ ε ^ 2 / 2)
    ∧ Tendsto (fun ε : ℝ => rayleighFloor !![1, 1; 0, ε])
        (𝓝[>] 0) (𝓝 0)
    ∧ ¬∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∀ v : Fin 2 → ℝ,
        c * (v ⬝ᵥ v)
          ≤ (!![1, 1; 0, ε] *ᵥ v) ⬝ᵥ (!![1, 1; 0, ε] *ᵥ v) := by
  obtain ⟨hinv, hray, hdot2, -⟩ := finite_complete_not_uniform
  have hnn : ∀ v : Fin 2 → ℝ, 0 ≤ v ⬝ᵥ v := fun v =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hmem : ∀ ε : ℝ, ε ^ 2 / 2 ∈ {r : ℝ | ∃ v : Fin 2 → ℝ,
      v ⬝ᵥ v ≠ 0 ∧ r = ((!![1, 1; 0, ε] *ᵥ v) ⬝ᵥ
        (!![1, 1; 0, ε] *ᵥ v)) / (v ⬝ᵥ v)} := by
    intro ε
    refine ⟨![1, -1], ?_, ?_⟩
    · rw [hdot2]
      norm_num
    · rw [hdot2, hray ε]
  have hbdd : ∀ ε : ℝ, BddBelow {r : ℝ | ∃ v : Fin 2 → ℝ,
      v ⬝ᵥ v ≠ 0 ∧ r = ((!![1, 1; 0, ε] *ᵥ v) ⬝ᵥ
        (!![1, 1; 0, ε] *ᵥ v)) / (v ⬝ᵥ v)} := by
    intro ε
    refine ⟨0, ?_⟩
    rintro r ⟨v, hv, rfl⟩
    exact div_nonneg (hnn _) (hnn v)
  have hpinch : ∀ ε : ℝ, 0 ≤ rayleighFloor !![1, 1; 0, ε]
      ∧ rayleighFloor !![1, 1; 0, ε] ≤ ε ^ 2 / 2 := by
    intro ε
    constructor
    · refine le_csInf ⟨_, hmem ε⟩ ?_
      rintro r ⟨v, hv, rfl⟩
      exact div_nonneg (hnn _) (hnn v)
    · exact csInf_le (hbdd ε) (hmem ε)
  refine ⟨fun ε hε => hinv ε (ne_of_gt hε), hpinch, ?_, ?_⟩
  · -- λ_min collapses as ε ↓ 0
    have hhalf : Tendsto (fun ε : ℝ => ε ^ 2 / 2) (𝓝[>] 0)
        (𝓝 0) := by
      have h := ((continuous_pow 2).div_const (2 : ℝ)).tendsto
        (0 : ℝ)
      simpa using h.mono_left nhdsWithin_le_nhds
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hhalf (fun ε => (hpinch ε).1)
      (fun ε => (hpinch ε).2)
  · -- no uniform frame floor
    rintro ⟨c, hc, hall⟩
    have hε : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
    have h := hall (Real.sqrt c) hε ![1, -1]
    rw [hdot2, hray (Real.sqrt c), Real.sq_sqrt hc.le] at h
    linarith

/-! ## `cth:growing-ledger-gap` -/

/-- `cth:growing-ledger-gap`, first boxed clause (exact form): for
the nilpotent history-copy shift on `ℂ^N` and a physical metric `G`
with Rayleigh bounds `m, M`, condition number at most `κ`
(`M ≤ κ·m`), any uniform `G`-contraction factor `q ≥ 0` of the
shift obeys `q^{N-1} ≥ κ^{-1/2}`. -/
theorem growingLedgerGapBoxed (N : ℕ) (hN : 1 ≤ N) (κ : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (m M q : ℝ)
    (hm : 0 < m) (hq : 0 ≤ q) (hcond : M ≤ κ * m)
    (hlow : ∀ x : Fin N → ℝ, m * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G *ᵥ x))
    (hupp : ∀ x : Fin N → ℝ, x ⬝ᵥ (G *ᵥ x) ≤ M * (x ⬝ᵥ x))
    (hcontr : ∀ x : Fin N → ℝ,
      (ledgerShift N *ᵥ x) ⬝ᵥ (G *ᵥ (ledgerShift N *ᵥ x))
        ≤ q ^ 2 * (x ⬝ᵥ (G *ᵥ x))) :
    (Real.sqrt κ)⁻¹ ≤ q ^ (N - 1) := by
  have hbase := growing_ledger_gap N hN G m M q hlow hupp hcontr
  have hpow : q ^ (2 * (N - 1)) = (q ^ (N - 1)) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hpow] at hbase
  set a := q ^ (N - 1) with ha
  have ha0 : 0 ≤ a := pow_nonneg hq _
  have hstep : a ^ 2 * M ≤ a ^ 2 * (κ * m) :=
    mul_le_mul_of_nonneg_left hcond (sq_nonneg a)
  have h1 : (1 : ℝ) ≤ a ^ 2 * κ := by nlinarith
  have hκ : 0 < κ := by nlinarith [sq_nonneg a]
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hsq : Real.sqrt κ * Real.sqrt κ = κ :=
    Real.mul_self_sqrt hκ.le
  have has : 1 ≤ a * Real.sqrt κ := by
    nlinarith [mul_nonneg ha0 hs.le]
  rw [inv_eq_one_div, div_le_iff₀ hs]
  linarith

/-- `cth:growing-ledger-gap` (exact, both boxed clauses): along a
sequence of history-copy shifts with uniformly conditioned physical
metrics (`cond(G_N) ≤ κ`), the contraction factors obey the boxed
bound `q_N^{N-1} ≥ κ^{-1/2}` for every `N ≥ 1`, all `c < 1` are
eventually exceeded, and the boxed liminf clause
`liminf q_N ≥ 1` holds (liminf taken in the extended reals, the
standard reading for a possibly unbounded real sequence): no
uniformly conditioned metric gives the growing ledger a
noncollapsing transient contraction gap. -/
theorem growingLedgerGapExact (κ : ℝ)
    (G : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ) (m M q : ℕ → ℝ)
    (hm : ∀ N, 0 < m N) (hq : ∀ N, 0 ≤ q N)
    (hcond : ∀ N, M N ≤ κ * m N)
    (hlow : ∀ N (x : Fin N → ℝ),
      m N * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G N *ᵥ x))
    (hupp : ∀ N (x : Fin N → ℝ),
      x ⬝ᵥ (G N *ᵥ x) ≤ M N * (x ⬝ᵥ x))
    (hcontr : ∀ N (x : Fin N → ℝ),
      (ledgerShift N *ᵥ x) ⬝ᵥ (G N *ᵥ (ledgerShift N *ᵥ x))
        ≤ q N ^ 2 * (x ⬝ᵥ (G N *ᵥ x))) :
    (∀ N, 1 ≤ N → (Real.sqrt κ)⁻¹ ≤ q N ^ (N - 1))
    ∧ (∀ c : ℝ, c < 1 → ∀ᶠ N in atTop, c < q N)
    ∧ (1 : EReal) ≤ Filter.atTop.liminf
        fun N => ((q N : ℝ) : EReal) := by
  have hbox : ∀ N, 1 ≤ N → (Real.sqrt κ)⁻¹ ≤ q N ^ (N - 1) :=
    fun N hN => growingLedgerGapBoxed N hN κ (G N) (m N) (M N)
      (q N) (hm N) (hq N) (hcond N) (hlow N) (hupp N) (hcontr N)
  -- the condition number is at least one
  have hx1 : (![1] : Fin 1 → ℝ) ⬝ᵥ ![1] = 1 := by
    simp [dotProduct, Fin.sum_univ_one]
  have hκ1 : (1 : ℝ) ≤ κ := by
    have hl := hlow 1 ![1]
    have hu := hupp 1 ![1]
    rw [hx1] at hl hu
    nlinarith [hcond 1, hm 1]
  have hinvpos : 0 < (Real.sqrt κ)⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hκ1))
  have hev : ∀ c : ℝ, c < 1 → ∀ᶠ N in atTop, c < q N := by
    intro c hc
    rcases lt_or_ge c 0 with hc0 | hc0
    · exact Filter.Eventually.of_forall fun N =>
        lt_of_lt_of_le hc0 (hq N)
    · have htend : Tendsto (fun N : ℕ => c ^ (N - 1)) atTop
          (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc).comp
          (tendsto_sub_atTop_nat 1)
      filter_upwards [htend.eventually_lt_const hinvpos,
        Filter.eventually_ge_atTop 1] with N h1 h2
      by_contra hcon
      push_neg at hcon
      have hmono := pow_le_pow_left₀ (hq N) hcon (N - 1)
      have hb := hbox N h2
      linarith
  refine ⟨hbox, hev, ?_⟩
  refine (Filter.le_liminf_iff).mpr fun y hy => ?_
  obtain ⟨r, hyr, hr1⟩ := EReal.exists_between_coe_real hy
  have hr1' : r < 1 := by exact_mod_cast hr1
  filter_upwards [hev r hr1'] with N hN
  calc y < (r : EReal) := hyr
    _ < ((q N : ℝ) : EReal) := by exact_mod_cast hN

/-! ## `cth:nonminimal-factorization` -/

open scoped ComplexOrder in
/-- `cth:nonminimal-factorization` (exact): the same scalar
operational process (the trivial constant table `Tr(TⁿP₀) = 1`) has
a one-dimensional support-minimal history algebra — realized by the
scalar core on `ℂ¹`, carrier dimension one — and a nonminimal
positive realization (the reset channel on `M₂(ℂ)`, positivity
preserved) whose ambient Hilbert–Schmidt-adjoint pair `(T, T*)` is
noncommutative.  Hence arbitrary unreduced positive factorizations
are not interchangeable with the minimal one. -/
theorem nonminimalFactorizationExact :
    (∀ n : ℕ, ((resetT ^ n) resetP).trace = 1)
    ∧ (∀ n : ℕ,
        (((1 : Module.End ℂ (Matrix (Fin 1) (Fin 1) ℂ)) ^ n)
          (1 : Matrix (Fin 1) (Fin 1) ℂ)).trace = 1)
    ∧ Module.finrank ℂ (Matrix (Fin 1) (Fin 1) ℂ) = 1
    ∧ resetP.PosSemidef
    ∧ (∀ X : Matrix (Fin 2) (Fin 2) ℂ, X.PosSemidef →
        (resetT X).PosSemidef)
    ∧ (∀ X Y : Matrix (Fin 2) (Fin 2) ℂ,
        (Xᴴ * resetT Y).trace = ((resetTstar X)ᴴ * Y).trace)
    ∧ resetT * resetTstar ≠ resetTstar * resetT := by
  obtain ⟨hadj, -, -, -, htable, hnc⟩ := nonminimal_factorization
  have hPpsd : resetP.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [resetP, Matrix.conjTranspose_apply]
    · intro x
      have hx : star x ⬝ᵥ (resetP *ᵥ x) = star (x 0) * x 0 := by
        simp [resetP, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [hx]
      exact star_mul_self_nonneg (x 0)
  refine ⟨htable, ?_, ?_, hPpsd, ?_, hadj, hnc⟩
  · intro n
    simp
  · rw [Module.finrank_matrix]
    simp
  · intro X hX
    have hT : resetT X = X.trace • resetP := rfl
    rw [hT]
    exact hPpsd.smul hX.trace_nonneg

/-! ## `cth:pairwise-not-monoidal-new` -/

/-- The transported `M₂(ℂ)` star (conjugate transpose read through
the row-major identification). -/
def starM2 (f : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ofM2 (toM2 f)ᴴ

/-- `M₂(ℂ)` is simple, in elementary form: every nonzero matrix
two-sidedly absorbs to the unit with two terms. -/
lemma m2AbsorbUnit (F : Matrix (Fin 2) (Fin 2) ℂ) (hF : F ≠ 0) :
    ∃ A B A' B' : Matrix (Fin 2) (Fin 2) ℂ,
      A * F * B + A' * F * B' = 1 := by
  have hex : ∃ i j, F i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hF (by ext i j; simpa using h i j)
  obtain ⟨i, j, hij⟩ := hex
  refine ⟨Matrix.single 0 i (F i j)⁻¹, Matrix.single j 0 1,
    Matrix.single 1 i (F i j)⁻¹, Matrix.single j 1 1, ?_⟩
  rw [Matrix.single_mul_mul_single, Matrix.single_mul_mul_single]
  have hval : (F i j)⁻¹ * F i j * 1 = 1 := by
    rw [mul_one, inv_mul_cancel₀ hij]
  rw [hval]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.single_apply, Matrix.one_apply]

/-- `cth:pairwise-not-monoidal-new` (exact): on one Hilbert
source-transfer datum (the standard orthonormal family of `ℂ⁴` with
its single inner product, hence identical degree-one and pairwise
source moments) there are two finite unital `*`-algebra structures:
the pointwise one — commutative, with multiplicative star — and the
transported `M₂(ℂ)` one — associative, unital, with
antimultiplicative involutive star, noncommutative, and simple
(every nonzero element two-sidedly generates the unit).  The
degree-one and pairwise data cannot see the multiplication. -/
theorem pairwiseNotMonoidalExact :
    (∀ i j : Fin 4,
      (star (Pi.single i 1 : Fin 4 → ℂ)) ⬝ᵥ Pi.single j 1
        = if i = j then 1 else 0)
    ∧ (∀ f g : Fin 4 → ℂ, f * g = g * f)
    ∧ (∀ f g : Fin 4 → ℂ, star (f * g) = star f * star g)
    ∧ (∀ f g h : Fin 4 → ℂ,
        mulM2 (mulM2 f g) h = mulM2 f (mulM2 g h))
    ∧ (∀ f : Fin 4 → ℂ,
        mulM2 (ofM2 1) f = f ∧ mulM2 f (ofM2 1) = f)
    ∧ (∀ f g : Fin 4 → ℂ,
        starM2 (mulM2 f g) = mulM2 (starM2 g) (starM2 f))
    ∧ (∀ f : Fin 4 → ℂ, starM2 (starM2 f) = f)
    ∧ (∃ f g : Fin 4 → ℂ, mulM2 f g ≠ mulM2 g f)
    ∧ (∀ f : Fin 4 → ℂ, f ≠ 0 →
        ∃ a b a' b' : Fin 4 → ℂ,
          mulM2 (mulM2 a f) b + mulM2 (mulM2 a' f) b'
            = ofM2 1) := by
  obtain ⟨hmom, hcomm, hnc⟩ := pairwise_not_monoidal
  have hofM2add : ∀ X Y : Matrix (Fin 2) (Fin 2) ℂ,
      ofM2 X + ofM2 Y = ofM2 (X + Y) := by
    intro X Y
    funext k
    fin_cases k <;> simp [ofM2, Matrix.add_apply]
  refine ⟨hmom, hcomm, fun f g => star_mul' f g, mulM2_assoc,
    mulM2_one, ?_, ?_, hnc, ?_⟩
  · -- transported star is antimultiplicative
    intro f g
    rw [starM2, starM2, starM2, mulM2, mulM2, toM2_ofM2,
      toM2_ofM2, toM2_ofM2, Matrix.conjTranspose_mul]
  · -- transported star is involutive
    intro f
    rw [starM2, starM2, toM2_ofM2,
      Matrix.conjTranspose_conjTranspose, ofM2_toM2]
  · -- the transported structure is simple
    intro f hf
    have hM : toM2 f ≠ 0 := by
      intro h
      apply hf
      rw [← ofM2_toM2 f, h]
      funext k
      fin_cases k <;> simp [ofM2]
    obtain ⟨A, B, A', B', hABs⟩ := m2AbsorbUnit (toM2 f) hM
    refine ⟨ofM2 A, ofM2 B, ofM2 A', ofM2 B', ?_⟩
    simp only [mulM2, toM2_ofM2]
    rw [hofM2add, hABs]

/-! ## `cth:private-fingerprint-no-provenance-channel` -/

open scoped ComplexOrder in
/-- `cth:private-fingerprint-no-provenance-channel` (exact): fix the
active packet block map `M` and the private-phase coupling `C`.
For every contraction `D₀` on an additional centered provenance
space there is a one-way extension — `[[M, 0], [D₀C, D₀]]` — which
(1) propagates the provenance space by `D₀` during the private
phase, (2) routes no provenance coordinate into the active future,
(3) leaves every declared packet marginal (all renewal
probabilities, endpoint data and old-private Grams are functions of
these matrix elements) unchanged, and (4) produces marginals
independent of `D₀`: the existing marginals impose no condition on
`D₀`. -/
theorem privateFingerprintNoProvenanceChannelExact
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b]
    (M : Matrix a a ℂ) (C : Matrix b a ℂ) (D₀ : Matrix b b ℂ)
    (_hD₀ : (1 - D₀ᴴ * D₀).PosSemidef) :
    (∀ k : ℕ,
      ((Matrix.fromBlocks M 0 (D₀ * C) D₀) ^ k).toBlocks₂₂
        = D₀ ^ k)
    ∧ (∀ k : ℕ,
      ((Matrix.fromBlocks M 0 (D₀ * C) D₀) ^ k).toBlocks₁₂ = 0)
    ∧ (∀ (k : ℕ) (u v : a → ℂ),
      star (Sum.elim u (0 : b → ℂ)) ⬝ᵥ
          ((Matrix.fromBlocks M 0 (D₀ * C) D₀) ^ k *ᵥ
            Sum.elim v 0)
        = star u ⬝ᵥ (M ^ k *ᵥ v))
    ∧ (∀ (D₁ : Matrix b b ℂ) (k : ℕ) (u v : a → ℂ),
      star (Sum.elim u (0 : b → ℂ)) ⬝ᵥ
          ((Matrix.fromBlocks M 0 (D₀ * C) D₀) ^ k *ᵥ
            Sum.elim v 0)
        = star (Sum.elim u (0 : b → ℂ)) ⬝ᵥ
            ((Matrix.fromBlocks M 0 (D₁ * C) D₁) ^ k *ᵥ
              Sum.elim v 0)) := by
  have hform : ∀ (D : Matrix b b ℂ) (k : ℕ),
      ∃ Ck : Matrix b a ℂ,
        (Matrix.fromBlocks M 0 (D * C) D) ^ k
          = Matrix.fromBlocks (M ^ k) 0 Ck (D ^ k) := by
    intro D k
    induction k with
    | zero =>
      exact ⟨0, by simp [Matrix.fromBlocks_one]⟩
    | succ k ih =>
      obtain ⟨Ck, hCk⟩ := ih
      refine ⟨Ck * M + D ^ k * (D * C), ?_⟩
      rw [pow_succ, hCk, Matrix.fromBlocks_multiply]
      congr 1 <;> simp [pow_succ]
  have hmarg : ∀ (D : Matrix b b ℂ) (k : ℕ) (u v : a → ℂ),
      star (Sum.elim u (0 : b → ℂ)) ⬝ᵥ
          ((Matrix.fromBlocks M 0 (D * C) D) ^ k *ᵥ
            Sum.elim v 0)
        = star u ⬝ᵥ (M ^ k *ᵥ v) := by
    intro D k u v
    obtain ⟨Ck, hCk⟩ := hform D k
    have hstar : star (Sum.elim u (0 : b → ℂ))
        = Sum.elim (star u) (0 : b → ℂ) := by
      funext x
      cases x <;> simp
    rw [hCk, Matrix.fromBlocks_mulVec, hstar,
      sumElim_dotProduct_sumElim]
    simp
  refine ⟨?_, ?_, hmarg D₀, ?_⟩
  · intro k
    obtain ⟨Ck, hCk⟩ := hform D₀ k
    rw [hCk]
    exact Matrix.toBlocks_fromBlocks₂₂ _ _ _ _
  · intro k
    obtain ⟨Ck, hCk⟩ := hform D₀ k
    rw [hCk]
    exact Matrix.toBlocks_fromBlocks₁₂ _ _ _ _
  · intro D₁ k u v
    rw [hmarg D₀ k u v, hmarg D₁ k u v]

/-! ## `cth:relative-interface-frame` -/

/-- The explicit equal-spectra witness pair: the interface blocks
`diag(2,1)` and `diag(1,2)` are conjugate by the orthogonal swap
(identical complete spectra `{1,2}`), yet the two glued Schur
responses through the shared interface differ (`3/4` vs `2/3`). -/
theorem relativeInterfaceFrameWitness :
    ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)ᵀ
        * !![0, 1; 1, 0] = 1)
    ∧ (!![0, 1; 1, 0] * !![2, 0; 0, 1]
        * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)ᵀ
        = !![1, 0; 0, 2])
    ∧ (![1, 1] ⬝ᵥ
        (((!![2, 0; 0, 1] + !![2, 0; 0, 1]
          : Matrix (Fin 2) (Fin 2) ℚ))⁻¹ *ᵥ ![1, 1]) = 3 / 4)
    ∧ (![1, 1] ⬝ᵥ
        (((!![2, 0; 0, 1] + !![1, 0; 0, 2]
          : Matrix (Fin 2) (Fin 2) ℚ))⁻¹ *ᵥ ![1, 1]) = 2 / 3) := by
  have hinv1 : ((!![2, 0; 0, 1] + !![2, 0; 0, 1]
      : Matrix (Fin 2) (Fin 2) ℚ))⁻¹ = !![1/4, 0; 0, 1/2] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.add_apply,
        Fin.sum_univ_two, Matrix.one_apply]
  have hinv2 : ((!![2, 0; 0, 1] + !![1, 0; 0, 2]
      : Matrix (Fin 2) (Fin 2) ℚ))⁻¹ = !![1/3, 0; 0, 1/3] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.add_apply,
        Fin.sum_univ_two, Matrix.one_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two, Matrix.one_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two]
  · rw [hinv1]
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · rw [hinv2]
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `cth:relative-interface-frame` (exact): complete spectra of the
component interface blocks do not determine the glued response
without their relative interface frame — no rule `Φ` of the
component blocks that is invariant under an orthogonal change of
component frame (hence a function of the component spectra alone)
can reproduce the glued Schur response through the shared
interface.  Witness: `diag(2,1)` glued with itself versus with its
swap conjugate `diag(1,2)`. -/
theorem relativeInterfaceFrameExact :
    ¬∃ Φ : Matrix (Fin 2) (Fin 2) ℚ →
        Matrix (Fin 2) (Fin 2) ℚ → ℚ,
      (∀ A B P : Matrix (Fin 2) (Fin 2) ℚ, Pᵀ * P = 1 →
        Φ A (P * B * Pᵀ) = Φ A B)
      ∧ ∀ A B : Matrix (Fin 2) (Fin 2) ℚ,
          Φ A B = ![1, 1] ⬝ᵥ ((A + B)⁻¹ *ᵥ ![1, 1]) := by
  rintro ⟨Φ, hframe, hresp⟩
  obtain ⟨hP, hPH, hr1, hr2⟩ := relativeInterfaceFrameWitness
  have hinvar := hframe !![2, 0; 0, 1] !![2, 0; 0, 1]
    !![0, 1; 1, 0] hP
  rw [hPH] at hinvar
  have h1 := hresp !![2, 0; 0, 1] !![2, 0; 0, 1]
  have h2 := hresp !![2, 0; 0, 1] !![1, 0; 0, 2]
  rw [hr1] at h1
  rw [hr2] at h2
  rw [h1, h2] at hinvar
  norm_num at hinvar

/-! ## `cth:renewal-Zeno` -/

/-- `cth:renewal-Zeno`, displayed collapse (exact): if the per-cycle
contractions obey `‖K_X‖ ≤ q < 1` uniformly, then
`‖K_X^{⌊t/τ_X⌋}‖ ≤ q^{⌊t/τ_X⌋} → 0` for every `t > 0` along any
cutoff sequence `τ ↓ 0`. -/
theorem renewalZenoNormCollapse {E : Type*} [NormedRing E]
    [NormOneClass E] (K : ℕ → E) (q t : ℝ) (hq0 : 0 ≤ q)
    (hq1 : q < 1) (ht : 0 < t) (hK : ∀ j, ‖K j‖ ≤ q)
    (τ : ℕ → ℝ) (hpos : ∀ j, 0 < τ j)
    (hτ : Tendsto τ atTop (𝓝 0)) :
    (∀ j n : ℕ, ‖K j ^ n‖ ≤ q ^ n)
    ∧ Tendsto (fun j => ‖K j ^ ⌊t / τ j⌋₊‖) atTop (𝓝 0) := by
  have hbound : ∀ j n : ℕ, ‖K j ^ n‖ ≤ q ^ n := by
    intro j n
    calc ‖K j ^ n‖ ≤ ‖K j‖ ^ n := norm_pow_le _ n
      _ ≤ q ^ n := pow_le_pow_left₀ (norm_nonneg _) (hK j) n
  refine ⟨hbound, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds (renewal_zeno q t hq0 hq1 ht τ hpos hτ)
    (fun j => norm_nonneg _) (fun j => hbound j _)

/-- `cth:renewal-Zeno`, jump clause (exact): a family which is `e`
at `t = 0` and the equilibrium value `P ≠ e` for every `t > 0` is
not continuous at `t = 0` from within `[0, ∞)` — it is not a
nontrivial strongly continuous continuum evolution. -/
theorem renewalZenoJump {E : Type*} [TopologicalSpace E]
    [T2Space E] (e P : E) (hP : P ≠ e) :
    ¬ContinuousWithinAt
      (fun s : ℝ => if s = 0 then e else P) (Set.Ici 0) 0 := by
  intro hcont
  have h1 : Tendsto (fun s : ℝ => if s = 0 then e else P)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝 (if (0 : ℝ) = 0 then e else P)) := hcont
  rw [if_pos rfl] at h1
  have h2 : Tendsto (fun s : ℝ => if s = 0 then e else P)
      (𝓝[>] (0 : ℝ)) (𝓝 P) := by
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        (if s = 0 then e else P) = P := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [if_neg (ne_of_gt hs)]
    rw [tendsto_congr' hev]
    exact tendsto_const_nhds
  exact hP (tendsto_nhds_unique h2
    (h1.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)))

/-- `cth:renewal-Zeno`, jump clause on finite matrices: for a
nontrivial equilibrium projection `P ≠ 1`, the limiting family
(identity at `t = 0`, `P` for `t > 0`) is discontinuous at `0`. -/
theorem renewalZenoJumpMatrix {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P ≠ 1) :
    ¬ContinuousWithinAt
      (fun s : ℝ => if s = 0 then (1 : Matrix (Fin d) (Fin d) ℂ)
        else P) (Set.Ici 0) 0 :=
  renewalZenoJump 1 P hP

/-- `cth:renewal-Zeno`, deficit clause (exact): with the order-`τ`
deficit `‖K_X‖ ≤ e^{-λτ_X}`, the per-cycle bound compounds to the
finite dense physical rate: `(e^{-λτ_X})^{⌊t/τ_X⌋} → e^{-λt}`. -/
theorem renewalZenoRateDeficit (lam t : ℝ) (ht : 0 < t)
    (τ : ℕ → ℝ) (hpos : ∀ j, 0 < τ j)
    (hτ : Tendsto τ atTop (𝓝 0)) :
    Tendsto (fun j => Real.exp (-lam * τ j) ^ ⌊t / τ j⌋₊)
      atTop (𝓝 (Real.exp (-lam * t))) := by
  have hup : ∀ j, τ j * ⌊t / τ j⌋₊ ≤ t := by
    intro j
    have h1 : (⌊t / τ j⌋₊ : ℝ) ≤ t / τ j :=
      Nat.floor_le (div_nonneg ht.le (hpos j).le)
    have h2 := mul_le_mul_of_nonneg_left h1 (hpos j).le
    have heq : τ j * (t / τ j) = t := by
      field_simp [ne_of_gt (hpos j)]
    linarith
  have hlo : ∀ j, t - τ j ≤ τ j * ⌊t / τ j⌋₊ := by
    intro j
    have h1 : t / τ j - 1 < (⌊t / τ j⌋₊ : ℝ) :=
      Nat.sub_one_lt_floor _
    have h2 := mul_lt_mul_of_pos_left h1 (hpos j)
    have heq : τ j * (t / τ j) = t := by
      field_simp [ne_of_gt (hpos j)]
    rw [mul_sub, mul_one, heq] at h2
    linarith
  have hs : Tendsto (fun j => τ j * ⌊t / τ j⌋₊) atTop (𝓝 t) := by
    have hg : Tendsto (fun j => t - τ j) atTop (𝓝 t) := by
      simpa using tendsto_const_nhds.sub hτ
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg
      tendsto_const_nhds hlo hup
  have hexp : Tendsto
      (fun j => Real.exp (-lam * (τ j * ⌊t / τ j⌋₊))) atTop
      (𝓝 (Real.exp (-lam * t))) := by
    have hmul : Tendsto (fun j => -lam * (τ j * ⌊t / τ j⌋₊))
        atTop (𝓝 (-lam * t)) := hs.const_mul (-lam)
    exact (Real.continuous_exp.tendsto _).comp hmul
  refine (tendsto_congr fun j => ?_).mpr hexp
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- `cth:renewal-Zeno` (exact bundle): with `τ_X ↓ 0` and a uniform
per-cycle contraction `‖K_X‖ ≤ q < 1` acting on a transient sector
whose equilibrium value `P` differs from the identity, for every
`t > 0`: the displayed bound `‖K_X^{⌊t/τ_X⌋}‖ ≤ q^{⌊t/τ_X⌋} → 0`
holds, the limiting family (identity at `t = 0`, equilibrium for
`t > 0`) has a jump at `0` and is therefore not a nontrivial
strongly continuous continuum evolution, and the order-`τ` deficit
`‖K_X‖ ≤ e^{-λτ_X}` instead compounds to the finite dense rate
`e^{-λt}`. -/
theorem renewalZenoExact {E : Type*} [NormedRing E]
    [NormOneClass E] (K : ℕ → E) (P : E) (q lam t : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ht : 0 < t)
    (hK : ∀ j, ‖K j‖ ≤ q) (hP : P ≠ 1)
    (τ : ℕ → ℝ) (hpos : ∀ j, 0 < τ j)
    (hτ : Tendsto τ atTop (𝓝 0)) :
    (∀ j, ‖K j ^ ⌊t / τ j⌋₊‖ ≤ q ^ ⌊t / τ j⌋₊)
    ∧ Tendsto (fun j => q ^ ⌊t / τ j⌋₊) atTop (𝓝 0)
    ∧ Tendsto (fun j => ‖K j ^ ⌊t / τ j⌋₊‖) atTop (𝓝 0)
    ∧ ¬ContinuousWithinAt
        (fun s : ℝ => if s = 0 then (1 : E) else P)
        (Set.Ici 0) 0
    ∧ Tendsto (fun j => Real.exp (-lam * τ j) ^ ⌊t / τ j⌋₊)
        atTop (𝓝 (Real.exp (-lam * t))) := by
  obtain ⟨hbound, hcoll⟩ := renewalZenoNormCollapse K q t hq0
    hq1 ht hK τ hpos hτ
  exact ⟨fun j => hbound j _,
    renewal_zeno q t hq0 hq1 ht τ hpos hτ, hcoll,
    renewalZenoJump 1 P hP,
    renewalZenoRateDeficit lam t ht τ hpos hτ⟩

end NCG
