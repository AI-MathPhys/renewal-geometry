/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CliffordGenerates

/-!
# The Jordan–Wigner Clifford factor in every even rank

Concrete content for `thm:clifford-factor`
(`manuscripts/renewal_emergence/renewal_emergence.tex`): for every `m`, the twisted group algebra
of the standard nondegenerate `F₂^{2m}` commutator form is realized
irreducibly on `(ℂ²)^{⊗m}` as the **full matrix algebra**
`M_{2^m}(ℂ) ≅ Cl_{2m}(ℂ)`, by the Jordan–Wigner construction.

This file builds the slotwise tensor calculus:

* `piKron` — matrices of product form
  `T(M)(f,g) = ∏_j M_j(f_j, g_j)` on the index type `Fin m → Fin 2`;
* `piKron_mul` — they multiply slotwise (Fubini);
* `piKron_one`, `piKron_trace`, `piKron_conjTranspose`,
  `piKron_neg_slot` — unit, multiplicative trace, slotwise star, and
  sign extraction from a single negated slot;
* `slotEmbed` — the single-slot embedding `E_j(A)`, with
  `prod_slotEmbed`: products of single-slot embeddings over a finset
  assemble the product form.
-/

namespace NCG.CommonOrigin

open Matrix

variable {m : ℕ}

/-- The product-form (slotwise Kronecker) matrix
`T(M)(f,g) = ∏_j M_j(f_j, g_j)`. -/
def piKron (M : Fin m → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  Matrix.of fun f g => ∏ j, M j (f j) (g j)

@[simp] theorem piKron_apply (M : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (f g : Fin m → Fin 2) :
    piKron M f g = ∏ j, M j (f j) (g j) := rfl

/-- Product forms multiply slotwise. -/
theorem piKron_mul (M N : Fin m → Matrix (Fin 2) (Fin 2) ℂ) :
    piKron M * piKron N = piKron (fun j => M j * N j) := by
  ext f g
  rw [Matrix.mul_apply, piKron_apply]
  have h1 : ∀ h : Fin m → Fin 2,
      piKron M f h * piKron N h g
        = ∏ j, (M j (f j) (h j) * N j (h j) (g j)) := by
    intro h
    rw [piKron_apply, piKron_apply, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun h _ => h1 h,
    ← Fintype.piFinset_univ]
  have h2 : (∑ h ∈ Fintype.piFinset
        fun _ : Fin m => (Finset.univ : Finset (Fin 2)),
      ∏ j, M j (f j) (h j) * N j (h j) (g j))
      = ∏ j, ∑ x : Fin 2, M j (f j) x * N j x (g j) :=
    (Finset.prod_univ_sum (t := fun _ => Finset.univ)
      (f := fun j x => M j (f j) x * N j x (g j))).symm
  refine h2.trans ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply]

/-- The unit is the product form of units. -/
theorem piKron_one :
    piKron (fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
    := by
  ext f g
  rw [piKron_apply]
  by_cases hfg : f = g
  · rw [hfg, Matrix.one_apply_eq]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hfg]
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hfg
    refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
    rw [Matrix.one_apply_ne hj₀]

/-- The trace of a product form is the product of the slot traces. -/
theorem piKron_trace (M : Fin m → Matrix (Fin 2) (Fin 2) ℂ) :
    (piKron M).trace = ∏ j, (M j).trace := by
  rw [Matrix.trace]
  have h1 : ∀ f : Fin m → Fin 2,
      (piKron M).diag f = ∏ j, M j (f j) (f j) := fun f => rfl
  rw [Finset.sum_congr rfl fun f _ => h1 f,
    ← Fintype.piFinset_univ]
  have h2 : (∑ f ∈ Fintype.piFinset
        fun _ : Fin m => (Finset.univ : Finset (Fin 2)),
      ∏ j, M j (f j) (f j))
      = ∏ j, ∑ x : Fin 2, M j x x :=
    (Finset.prod_univ_sum (t := fun _ => Finset.univ)
      (f := fun j x => M j x x)).symm
  refine h2.trans ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.trace]
  rfl

/-- Conjugate transpose acts slotwise on product forms. -/
theorem piKron_conjTranspose
    (M : Fin m → Matrix (Fin 2) (Fin 2) ℂ) :
    (piKron M)ᴴ = piKron (fun j => (M j)ᴴ) := by
  ext f g
  rw [Matrix.conjTranspose_apply, piKron_apply, piKron_apply]
  rw [star_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply]

/-- Negating a single slot negates the product form. -/
theorem piKron_neg_slot (M : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (j₀ : Fin m) :
    piKron (Function.update M j₀ (-(M j₀)))
      = -(piKron M) := by
  ext f g
  rw [piKron_apply, Matrix.neg_apply, piKron_apply]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀)]
  have h1 : ∀ j ∈ Finset.univ.erase j₀,
      Function.update M j₀ (-(M j₀)) j (f j) (g j)
        = M j (f j) (g j) := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [Finset.prod_congr rfl h1, Function.update_self,
    Matrix.neg_apply]
  ring

/-- Scaling a single slot scales the product form. -/
theorem piKron_smul_slot (M : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (j₀ : Fin m) (c : ℂ) :
    piKron (Function.update M j₀ (c • M j₀))
      = c • piKron M := by
  ext f g
  rw [piKron_apply, Matrix.smul_apply, piKron_apply, smul_eq_mul]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀)]
  have h1 : ∀ j ∈ Finset.univ.erase j₀,
      Function.update M j₀ (c • M j₀) j (f j) (g j)
        = M j (f j) (g j) := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [Finset.prod_congr rfl h1, Function.update_self,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- The single-slot embedding `E_j(A)`. -/
def slotEmbed (j : Fin m) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  piKron (Function.update (fun _ => 1) j A)

/-- Distinct single-slot embeddings commute. -/
theorem slotEmbed_commute {j k : Fin m} (hjk : j ≠ k)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Commute (slotEmbed j A) (slotEmbed k B) := by
  change slotEmbed j A * slotEmbed k B
    = slotEmbed k B * slotEmbed j A
  rw [slotEmbed, slotEmbed, piKron_mul, piKron_mul]
  congr 1
  funext l
  by_cases hlj : l = j
  · rw [hlj, Function.update_self,
      Function.update_of_ne hjk, Matrix.mul_one,
      Matrix.one_mul]
  · rw [Function.update_of_ne hlj]
    by_cases hlk : l = k
    · rw [hlk, Function.update_self, Matrix.one_mul,
        Matrix.mul_one]
    · rw [Function.update_of_ne hlk, Matrix.one_mul]

/-- Products of single-slot embeddings over a finset assemble the
product form supported on that finset. -/
theorem noncommProd_slotEmbed (s : Finset (Fin m))
    (F : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (hcomm : (s : Set (Fin m)).Pairwise fun j k =>
      Commute (slotEmbed j (F j)) (slotEmbed k (F k))) :
    s.noncommProd (fun j => slotEmbed j (F j)) hcomm
      = piKron (fun j => if j ∈ s then F j else 1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.noncommProd_empty]
    rw [show (fun j : Fin m =>
        if j ∈ (∅ : Finset (Fin m)) then F j else 1)
      = fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ) from by
        funext j
        rw [if_neg (Finset.notMem_empty j)]]
    rw [piKron_one]
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    rw [ih, slotEmbed, piKron_mul]
    congr 1
    funext j
    by_cases hja : j = a
    · rw [hja, Function.update_self,
        if_pos (Finset.mem_insert_self a s), if_neg ha,
        Matrix.mul_one]
    · rw [Function.update_of_ne hja, Matrix.one_mul]
      by_cases hjs : j ∈ s
      · rw [if_pos hjs,
          if_pos (Finset.mem_insert_of_mem hjs)]
      · rw [if_neg hjs, if_neg (by
          rw [Finset.mem_insert]
          push Not
          exact ⟨hja, hjs⟩)]

/-! ## Product-form Clifford algebra -/

/-- Squares of slotwise involutions. -/
theorem piKron_sq_one {M : Fin m → Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ j, M j * M j = 1) : piKron M * piKron M = 1 := by
  rw [piKron_mul, show (fun j => M j * M j)
    = fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) ℂ)
    from funext h, piKron_one]

/-- Product forms anticommute when exactly one slot anticommutes
and the others commute. -/
theorem piKron_anticomm {M N : Fin m → Matrix (Fin 2) (Fin 2) ℂ}
    (j₀ : Fin m) (hj : M j₀ * N j₀ = -(N j₀ * M j₀))
    (hother : ∀ j, j ≠ j₀ → M j * N j = N j * M j) :
    piKron M * piKron N = -(piKron N * piKron M) := by
  rw [piKron_mul, piKron_mul]
  have h1 : (fun j => M j * N j)
      = Function.update (fun j => N j * M j) j₀
          (-((fun j => N j * M j) j₀)) := by
    funext j
    by_cases hjj : j = j₀
    · rw [hjj, Function.update_self]
      exact hj
    · rw [Function.update_of_ne hjj]
      exact hother j hjj
  rw [h1, piKron_neg_slot]

/-! ## The Jordan–Wigner generators -/

/-- The Jordan–Wigner slot pattern: `σ₃` before the active slot,
the given Pauli at it, `1` after. -/
def jwSlots (i : Fin m) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    Fin m → Matrix (Fin 2) (Fin 2) ℂ :=
  fun j => if j < i then pauli3 else if j = i then P else 1

/-- The `2m` Jordan–Wigner Clifford generators on `(ℂ²)^{⊗m}`. -/
def jwGamma (x : Fin m × Bool) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  piKron (jwSlots x.1 (if x.2 then pauli2 else pauli1))

/-- **Clifford squares**: `Γ_x² = 1`. -/
theorem jwGamma_sq (x : Fin m × Bool) :
    jwGamma x * jwGamma x = 1 := by
  refine piKron_sq_one fun j => ?_
  rw [jwSlots]
  by_cases h1 : j < x.1
  · rw [if_pos h1]
    exact pauli3_sq
  · rw [if_neg h1]
    by_cases h2 : j = x.1
    · rw [if_pos h2]
      cases hb : x.2
      · rw [if_neg (by simp)]
        exact pauli1_sq
      · rw [if_pos rfl]
        exact pauli2_sq
    · rw [if_neg h2, Matrix.one_mul]

/-- Anticommutation for generators at the same site. -/
theorem jwGamma_anticomm_same (i : Fin m) :
    jwGamma (i, false) * jwGamma (i, true)
      = -(jwGamma (i, true) * jwGamma (i, false)) := by
  refine piKron_anticomm i ?_ ?_
  · rw [jwSlots, jwSlots, if_neg (lt_irrefl i), if_pos rfl,
      if_neg (lt_irrefl i), if_pos rfl]
    rw [if_neg (by simp), if_pos rfl]
    exact pauli12_anticomm
  · intro j hj
    simp only [jwSlots]
    by_cases h1 : j < i
    · simp [h1]
    · simp [h1, hj]

/-- Anticommutation for generators at ordered distinct sites: the
Jordan–Wigner string anticommutes at the earlier active slot. -/
theorem jwGamma_anticomm_lt {i i' : Fin m} (h : i < i')
    (b b' : Bool) :
    jwGamma (i, b) * jwGamma (i', b')
      = -(jwGamma (i', b') * jwGamma (i, b)) := by
  refine piKron_anticomm i ?_ ?_
  · rw [jwSlots, jwSlots, if_neg (lt_irrefl i), if_pos rfl,
      if_pos h]
    cases b
    · rw [if_neg (by simp)]
      exact pauli13_anticomm
    · rw [if_pos rfl]
      exact pauli23_anticomm
  · intro j hj
    rw [jwSlots, jwSlots]
    by_cases h1 : j < i
    · rw [if_pos h1, if_pos (lt_trans h1 h)]
    · rw [if_neg h1, if_neg (fun hji : j = i => hj hji)]
      rw [Matrix.one_mul, Matrix.mul_one]

/-- **Clifford anticommutation** for all distinct generators. -/
theorem jwGamma_anticomm {x y : Fin m × Bool} (hxy : x ≠ y) :
    jwGamma x * jwGamma y = -(jwGamma y * jwGamma x) := by
  rcases x with ⟨i, b⟩
  rcases y with ⟨i', b'⟩
  rcases lt_trichotomy i i' with h | h | h
  · exact jwGamma_anticomm_lt h b b'
  · subst h
    have hbb : b ≠ b' := by
      intro hc
      exact hxy (by rw [hc])
    cases hb : b
    · cases hb' : b'
      · exfalso
        apply hbb
        rw [hb, hb']
      · exact jwGamma_anticomm_same i
    · cases hb' : b'
      · have h2 := jwGamma_anticomm_same i
        rw [show jwGamma (i, true) * jwGamma (i, false)
            = -(jwGamma (i, false) * jwGamma (i, true)) from by
          rw [h2, neg_neg]]
      · exfalso
        apply hbb
        rw [hb, hb']
  · have h2 := jwGamma_anticomm_lt h b' b
    rw [show jwGamma (i, b) * jwGamma (i', b')
        = -(jwGamma (i', b') * jwGamma (i, b)) from by
      rw [h2, neg_neg]]

/-- **The Clifford relations in rank `2m`**
(`thm:clifford-factor`, existence): the `2m` Jordan–Wigner
generators satisfy `Γ_x Γ_y + Γ_y Γ_x = 2δ_{xy} 1`. -/
theorem jwGamma_clifford (x y : Fin m × Bool) :
    jwGamma x * jwGamma y + jwGamma y * jwGamma x
      = (if x = y then (2 : ℂ) else 0) • 1 := by
  by_cases h : x = y
  · rw [h, if_pos rfl, jwGamma_sq]
    ext p q
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [if_neg h, jwGamma_anticomm h, zero_smul]
    exact neg_add_cancel _

/-- Each generator is Hermitian. -/
theorem jwGamma_herm (x : Fin m × Bool) :
    (jwGamma x)ᴴ = jwGamma x := by
  rw [jwGamma, piKron_conjTranspose]
  congr 1
  funext j
  rw [jwSlots]
  by_cases h1 : j < x.1
  · rw [if_pos h1]
    exact pauli3_herm
  · rw [if_neg h1]
    by_cases h2 : j = x.1
    · rw [if_pos h2]
      cases x.2
      · rw [if_neg (by simp)]
        exact pauli1_herm
      · rw [if_pos rfl]
        exact pauli2_herm
    · rw [if_neg h2]
      exact Matrix.conjTranspose_one

/-! ## The Pauli-word basis and generation -/

/-- The Pauli words in every rank. -/
def pauliWord (w : Fin m → Fin 4) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  piKron (fun j => pauli4 (w j))

/-- Trace orthogonality of the Pauli words:
`Tr(W_x W_y) = 2^m δ_{xy}`. -/
theorem pauliWord_trace_mul (x y : Fin m → Fin 4) :
    (pauliWord x * pauliWord y).trace
      = if x = y then (2 : ℂ) ^ m else 0 := by
  rw [pauliWord, pauliWord, piKron_mul, piKron_trace]
  by_cases h : x = y
  · rw [if_pos h, h]
    have h1 : ∀ j : Fin m,
        (pauli4 (y j) * pauli4 (y j)).trace = 2 := by
      intro j
      rw [pauli4_trace_mul, if_pos rfl]
    rw [Finset.prod_congr rfl fun j _ => h1 j,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h]
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
    rw [pauli4_trace_mul, if_neg hj₀]

/-- Linear independence of the `4^m` Pauli words. -/
theorem pauliWord_linearIndependent :
    LinearIndependent ℂ (pauliWord (m := m)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg x
  have h1 : ((∑ y, g y • pauliWord y) * pauliWord x).trace = 0
      := by
    rw [hg, Matrix.zero_mul, Matrix.trace_zero]
  rw [Finset.sum_mul, Matrix.trace_sum] at h1
  have h2 : ∀ y : Fin m → Fin 4,
      ((g y • pauliWord y) * pauliWord x).trace
        = (if y = x then g y * 2 ^ m else 0) := by
    intro y
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      pauliWord_trace_mul]
    by_cases h : y = x
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl fun y _ => h2 y,
    Finset.sum_ite_eq' Finset.univ x (fun y => g y * 2 ^ m),
    if_pos (Finset.mem_univ x)] at h1
  rcases mul_eq_zero.mp h1 with h3 | h3
  · exact h3
  · exact absurd h3 (pow_ne_zero m two_ne_zero)

/-- The Pauli words span the full matrix algebra. -/
theorem pauliWord_span :
    Submodule.span ℂ (Set.range (pauliWord (m := m))) = ⊤ := by
  refine
    pauliWord_linearIndependent.span_eq_top_of_card_eq_finrank ?_
  rw [Module.finrank_matrix, Fintype.card_fun, Fintype.card_fun]
  simp only [Fintype.card_fin, Module.finrank_self, mul_one]
  rw [← mul_pow]
  norm_num

/-! ## Membership of the words in the generated algebra -/

theorem slotEmbed_smul (j : Fin m) (c : ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    slotEmbed j (c • A) = c • slotEmbed j A := by
  rw [slotEmbed, slotEmbed]
  have h1 : Function.update
      (fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) ℂ)) j (c • A)
      = Function.update
          (Function.update (fun _ => 1) j A) j
          (c • (Function.update
            (fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) ℂ))
              j A j)) := by
    rw [Function.update_self, Function.update_idem]
  rw [h1, piKron_smul_slot]

/-- The generator product at a site is the `σ₃` slot embedding up
to the phase `i`. -/
theorem jwGamma_prod_site (i : Fin m) :
    jwGamma (i, false) * jwGamma (i, true)
      = Complex.I • slotEmbed i pauli3 := by
  rw [show jwGamma (i, false) = piKron (jwSlots i pauli1)
      from rfl,
    show jwGamma (i, true) = piKron (jwSlots i pauli2) from rfl,
    piKron_mul]
  have h2 : (fun j => jwSlots i pauli1 j * jwSlots i pauli2 j)
      = Function.update
          (fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) ℂ)) i
          (pauli1 * pauli2) := by
    funext j
    rw [jwSlots, jwSlots]
    by_cases h3 : j < i
    · rw [if_pos h3, if_pos h3,
        Function.update_of_ne (ne_of_lt h3)]
      exact pauli3_sq
    · by_cases h4 : j = i
      · rw [if_neg h3, if_neg h3, if_pos h4, if_pos h4, h4,
          Function.update_self]
      · rw [if_neg h3, if_neg h3, if_neg h4, if_neg h4,
          Function.update_of_ne h4, Matrix.one_mul]
  rw [h2, pauli12_eq_I_pauli3]
  change slotEmbed i (Complex.I • pauli3)
    = Complex.I • slotEmbed i pauli3
  exact slotEmbed_smul i Complex.I pauli3

/-- The `σ₃`-string before a site. -/
def jwString (i : Fin m) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  piKron (fun j => if j < i then pauli3 else 1)

/-- The string absorbs into the generator to expose the bare slot
embedding: `S_{<i} Γ_{(i,0)} = E_i(σ₁)` and similarly for `σ₂`. -/
theorem jwString_mul_gamma (i : Fin m) (b : Bool) :
    jwString i * jwGamma (i, b)
      = slotEmbed i (if b then pauli2 else pauli1) := by
  rw [jwString,
    show jwGamma (i, b)
      = piKron (jwSlots i (if b then pauli2 else pauli1))
      from rfl,
    piKron_mul]
  change piKron _ = piKron _
  congr 1
  funext j
  rw [jwSlots]
  by_cases h3 : j < i
  · rw [if_pos h3, if_pos h3,
      Function.update_of_ne (ne_of_lt h3)]
    exact pauli3_sq
  · by_cases h4 : j = i
    · rw [if_neg h3, if_neg h3, if_pos h4, h4,
        Function.update_self, Matrix.one_mul]
    · rw [if_neg h3, if_neg h3, if_neg h4,
        Function.update_of_ne h4, Matrix.one_mul]

/-- Every slot embedding of a Pauli lies in the algebra generated
by the Jordan–Wigner system. -/
theorem slotEmbed_mem_adjoin (i : Fin m) (p : Fin 4) :
    slotEmbed i (pauli4 p)
      ∈ Algebra.adjoin ℂ (Set.range (jwGamma (m := m))) := by
  classical
  set S := Algebra.adjoin ℂ (Set.range (jwGamma (m := m)))
    with hS
  have hg : ∀ x : Fin m × Bool, jwGamma x ∈ S :=
    fun x => Algebra.subset_adjoin ⟨x, rfl⟩
  have h3 : ∀ i' : Fin m, slotEmbed i' pauli3 ∈ S := by
    intro i'
    have h4 : slotEmbed i' pauli3
        = (-Complex.I)
          • (jwGamma (i', false) * jwGamma (i', true)) := by
      rw [jwGamma_prod_site, smul_smul,
        show -Complex.I * Complex.I = 1 from by
          rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]
    rw [h4]
    exact Subalgebra.smul_mem S (mul_mem (hg _) (hg _)) _
  have hstring : ∀ i' : Fin m, jwString i' ∈ S := by
    intro i'
    have h5 := noncommProd_slotEmbed
      (Finset.univ.filter (· < i')) (fun _ => pauli3)
      (fun j _ k _ hjk => slotEmbed_commute hjk _ _)
    have h6 : jwString i'
        = piKron (fun j =>
            if j ∈ Finset.univ.filter (· < i')
              then pauli3 else 1) := by
      rw [jwString]
      congr 1
      funext j
      by_cases h7 : j < i'
      · rw [if_pos h7, if_pos (Finset.mem_filter.mpr
          ⟨Finset.mem_univ j, h7⟩)]
      · have h8 : j ∉ Finset.univ.filter (· < i') := by
          rw [Finset.mem_filter]
          rintro ⟨-, hlt⟩
          exact h7 hlt
        rw [if_neg h7, if_neg h8]
    rw [h6, ← h5]
    exact Submonoid.noncommProd_mem
      S.toSubsemiring.toSubmonoid _ _ _ fun j _ => h3 j
  fin_cases p
  · change slotEmbed i (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ S
    have h7 : slotEmbed i (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
        := by
      rw [slotEmbed, Function.update_eq_self, piKron_one]
    rw [h7]
    exact one_mem S
  · change slotEmbed i pauli1 ∈ S
    have h8 : slotEmbed i pauli1
        = jwString i * jwGamma (i, false) := by
      rw [jwString_mul_gamma]
      rfl
    rw [h8]
    exact mul_mem (hstring i) (hg _)
  · change slotEmbed i pauli2 ∈ S
    have h8 : slotEmbed i pauli2
        = jwString i * jwGamma (i, true) := by
      rw [jwString_mul_gamma]
      rfl
    rw [h8]
    exact mul_mem (hstring i) (hg _)
  · exact h3 i

/-- Every Pauli word lies in the generated algebra. -/
theorem pauliWord_mem_adjoin (w : Fin m → Fin 4) :
    pauliWord w
      ∈ Algebra.adjoin ℂ (Set.range (jwGamma (m := m))) := by
  classical
  have h5 := noncommProd_slotEmbed Finset.univ
    (fun j => pauli4 (w j))
    (fun j _ k _ hjk => slotEmbed_commute hjk _ _)
  have h6 : pauliWord w
      = piKron (fun j =>
          if j ∈ (Finset.univ : Finset (Fin m))
            then pauli4 (w j) else 1) := by
    rw [pauliWord]
    congr 1
    funext j
    rw [if_pos (Finset.mem_univ j)]
  rw [h6, ← h5]
  exact Submonoid.noncommProd_mem
    (Algebra.adjoin ℂ (Set.range (jwGamma (m := m)))
      ).toSubsemiring.toSubmonoid _ _ _
    fun j _ => slotEmbed_mem_adjoin j (w j)

/-- **Theorem `thm:clifford-factor` (identification)**: the
Jordan–Wigner Clifford system generates the full matrix factor
`M_{2^m}(ℂ)` in every rank. -/
theorem jwGamma_generates :
    Algebra.adjoin ℂ (Set.range (jwGamma (m := m))) = ⊤ := by
  rw [eq_top_iff]
  intro X _
  have h1 : Submodule.span ℂ (Set.range (pauliWord (m := m)))
      ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ
          (Set.range (jwGamma (m := m)))) := by
    rw [Submodule.span_le]
    rintro Z ⟨w, rfl⟩
    exact pauliWord_mem_adjoin w
  have h2 : X ∈ Submodule.span ℂ
      (Set.range (pauliWord (m := m))) := by
    rw [pauliWord_span]
    exact Submodule.mem_top
  exact h1 h2

/-- **Irreducibility in every rank**: a matrix commuting with the
Jordan–Wigner system is scalar (it commutes with the generated
algebra, which is everything). -/
theorem jwGamma_commutant
    (X : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)
    (hX : ∀ x, Commute (jwGamma x) X) :
    ∃ c : ℂ, X = c • 1 := by
  classical
  have h1 : Algebra.adjoin ℂ (Set.range (jwGamma (m := m)))
      ≤ Subalgebra.centralizer ℂ {X} := by
    rw [Algebra.adjoin_le_iff]
    rintro Z ⟨x, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro Y hY
    rw [Set.mem_singleton_iff] at hY
    rw [hY]
    exact (hX x).symm
  rw [jwGamma_generates] at h1
  have h2 : ∀ i j : Fin m → Fin 2,
      Commute (Matrix.single i j (1 : ℂ)) X := by
    intro i j
    have h3 : Matrix.single i j (1 : ℂ)
        ∈ Subalgebra.centralizer ℂ {X} :=
      h1 (by trivial)
    rw [Subalgebra.mem_centralizer_iff] at h3
    have h4 := h3 X (Set.mem_singleton X)
    exact h4.symm
  obtain ⟨c, hc⟩ :=
    Matrix.mem_range_scalar_iff_commute_single'.mpr h2
  refine ⟨c, ?_⟩
  rw [← hc]
  ext f g
  rw [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hfg : f = g
  · rw [if_pos hfg, if_pos hfg, mul_one]
  · rw [if_neg hfg, if_neg hfg, mul_zero]

end NCG.CommonOrigin
