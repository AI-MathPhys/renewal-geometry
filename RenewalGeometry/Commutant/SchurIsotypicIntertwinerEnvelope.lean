/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Schur's lemma, isotypic intertwiner spaces and semi-intertwiner envelopes
(`prop:schur-incidence-envelope`, spacetime–gauge duality manuscript)

General infrastructure, valid for an **arbitrary group** `G` (no topology, no Haar measure):

* `SchurIsotypicEnvelope.IsIrreducible`, `IsIntertwiner`, `Equivalent` — irreducible complex
  representations, intertwiners, equivalence.
* `schur_bijective_or_eq_zero`, `schur_eq_zero_of_not_equivalent` — an intertwiner between
  irreducible representations is zero or bijective; between inequivalent ones it is zero.
* `schur_scalar` — an intertwiner of a finite-dimensional irreducible complex representation
  with itself is a scalar.
* `IsoSpace V m = Π λ, Fin (m λ) → V λ` with the action `isoRep` — the isotypic carrier
  `⊕_λ V_λ ⊗ ℂ^{m_λ}` (the factor `V_λ ⊗ ℂ^{m_λ}` is written in its canonical form
  `V_λ^{m_λ}`, `G` acting by `ρ_λ(g) ⊗ I`).
* `blockMap X` — the operator `⊕_λ I_{V_λ} ⊗ X_λ` for `X_λ ∈ M_{n_λ × m_λ}(ℂ)`;
  `isIntertwiner_iso_iff` — **Schur on isotypic carriers**: for pairwise inequivalent
  finite-dimensional irreducible `V_λ`, the intertwiners `⊕ V_λ ⊗ ℂ^{m_λ} → ⊕ V_λ ⊗ ℂ^{n_λ}`
  are exactly the `blockMap X`; `isoIntertwinerEquiv`, `finrank_isoIntertwiners`.

Application to the paper:

* `semiIntertwinerEnvelope Rs Rt χ = {K | R_t(g) K R_s(g)^* = χ(g) K}` for unitary
  representations on finite-dimensional Hilbert spaces and a character `χ`;
  `twistRep χ Rt = χ^{-1} R_t`.
* `schurEnvelopeEquiv` / `schur_incidence_envelope` (`prop:schur-incidence-envelope`): given
  the decompositions `H_s ≅ ⊕ V_λ ⊗ ℂ^{m_λ}` and `χ^{-1} H_t ≅ ⊕ V_λ ⊗ ℂ^{n_λ}` (equivariant
  linear isomorphisms; irreducible, pairwise inequivalent, finite-dimensional `V_λ`), the
  envelope is isomorphic to `⊕_λ I_{V_λ} ⊗ M_{n_λ × m_λ}(ℂ)` (explicitly: `E_t K E_s^{-1}` is
  `blockMap`), has dimension `Σ_λ m_λ n_λ`, every `K^* L` (`K, L ∈ S_χ`) lies in `R_s(G)'`,
  and `dim R_s(G)' = Σ_λ m_λ²`.
* `schur_normalization_screen` (`eq:schur-normalization-screen`): if the joint normalization
  map `(X_a)_a ↦ Σ_a Σ_{ij} (X_a)_{ij} K_{a,i}^* K_{a,j}` of several recorded envelopes (bases
  `K_{a,·}` of `S_{χ_a}`) is injective, then `Σ_a (Σ_λ m_λ n_{a,λ})² ≤ Σ_λ m_λ²`.
-/

open Module

namespace RenewalGeometry

namespace SchurIsotypicEnvelope

variable {G : Type*} [Group G]

/-! ## Schur's lemma for arbitrary groups -/

section Schur

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- `f` intertwines the representations `ρ` and `σ`: `f ∘ ρ(g) = σ(g) ∘ f` for all `g`. -/
def IsIntertwiner (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (f : V →ₗ[ℂ] W) :
    Prop :=
  ∀ g, f ∘ₗ ρ g = σ g ∘ₗ f

/-- An irreducible representation: nonzero, and its only invariant subspaces are `⊥` and `⊤`. -/
structure IsIrreducible (ρ : Representation ℂ G V) : Prop where
  nontrivial : Nontrivial V
  invariant_eq : ∀ U : Submodule ℂ V, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤

/-- Two representations are equivalent when an intertwining linear isomorphism exists. -/
def Equivalent (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, IsIntertwiner ρ σ e.toLinearMap

/-- The intertwiners `V → W` form a subspace. -/
def intertwiners (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Submodule ℂ (V →ₗ[ℂ] W) where
  carrier := {f | IsIntertwiner ρ σ f}
  add_mem' {f f'} hf hf' g := by
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, hf g, hf' g]
  zero_mem' g := by simp
  smul_mem' c f hf g := by
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hf g]

theorem mem_intertwiners {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {f : V →ₗ[ℂ] W} : f ∈ intertwiners ρ σ ↔ IsIntertwiner ρ σ f := Iff.rfl

/-- **Schur's lemma (first form).**  An intertwiner between irreducible representations is
either zero or bijective. -/
theorem schur_bijective_or_eq_zero {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hρ : IsIrreducible ρ) (hσ : IsIrreducible σ) {f : V →ₗ[ℂ] W}
    (hf : IsIntertwiner ρ σ f) : f = 0 ∨ Function.Bijective f := by
  by_cases h0 : f = 0
  · exact Or.inl h0
  right
  have hfg : ∀ g v, f (ρ g v) = σ g (f v) := fun g v => LinearMap.congr_fun (hf g) v
  constructor
  · rcases hρ.invariant_eq (LinearMap.ker f) (fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢; rw [hfg, hv, map_zero]) with hk | hk
    · exact LinearMap.ker_eq_bot.mp hk
    · exact absurd (LinearMap.ker_eq_top.mp hk) h0
  · rcases hσ.invariant_eq (LinearMap.range f) (fun g w hw => by
        obtain ⟨v, rfl⟩ := hw; exact ⟨ρ g v, hfg g v⟩) with hr | hr
    · exact absurd (LinearMap.range_eq_bot.mp hr) h0
    · exact LinearMap.range_eq_top.mp hr

/-- **Schur's lemma (inequivalent form).**  An intertwiner between inequivalent irreducible
representations vanishes. -/
theorem schur_eq_zero_of_not_equivalent {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hρ : IsIrreducible ρ) (hσ : IsIrreducible σ)
    (hne : ¬ Equivalent ρ σ) {f : V →ₗ[ℂ] W} (hf : IsIntertwiner ρ σ f) : f = 0 := by
  rcases schur_bijective_or_eq_zero hρ hσ hf with h | h
  · exact h
  · exact absurd ⟨LinearEquiv.ofBijective f h, hf⟩ hne

/-- **Schur's lemma (scalar form).**  A self-intertwiner of a finite-dimensional irreducible
complex representation is a scalar multiple of the identity. -/
theorem schur_scalar [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    (hρ : IsIrreducible ρ) {f : V →ₗ[ℂ] V} (hf : IsIntertwiner ρ ρ f) :
    ∃ c : ℂ, f = c • LinearMap.id := by
  have := hρ.nontrivial
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hint : IsIntertwiner ρ ρ (f - c • LinearMap.id) := by
    intro g
    rw [LinearMap.sub_comp, LinearMap.comp_sub, hf g, LinearMap.smul_comp, LinearMap.comp_smul,
      LinearMap.id_comp, LinearMap.comp_id]
  rcases schur_bijective_or_eq_zero hρ hρ hint with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hv0 : (f - c • LinearMap.id : V →ₗ[ℂ] V) v = 0 := by
      rw [LinearMap.sub_apply, hv.apply_eq_smul]; simp
    exact hv.2 (h.1 (by rw [hv0, map_zero]))

end Schur

/-! ## Isotypic carriers `⊕_λ V_λ ⊗ ℂ^{m_λ}` -/

section Isotypic

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {V : Λ → Type*}
  [∀ l, AddCommGroup (V l)] [∀ l, Module ℂ (V l)]

/-- The isotypic carrier `⊕_λ V_λ ⊗ ℂ^{m_λ}`, written in the canonical form `Π λ, V_λ^{m_λ}`. -/
abbrev IsoSpace (V : Λ → Type*) [∀ l, AddCommGroup (V l)] [∀ l, Module ℂ (V l)]
    (m : Λ → ℕ) : Type _ :=
  ∀ l, Fin (m l) → V l

/-- The action `⊕_λ ρ_λ(g) ⊗ I_{m_λ}` on the isotypic carrier. -/
def isoAct (ρ : ∀ l, Representation ℂ G (V l)) (m : Λ → ℕ) (g : G) :
    IsoSpace V m →ₗ[ℂ] IsoSpace V m where
  toFun f l i := ρ l g (f l i)
  map_add' f f' := by funext l i; simp
  map_smul' c f := by funext l i; simp

@[simp] theorem isoAct_apply (ρ : ∀ l, Representation ℂ G (V l)) (m : Λ → ℕ) (g : G)
    (f : IsoSpace V m) (l : Λ) (i : Fin (m l)) : isoAct ρ m g f l i = ρ l g (f l i) := rfl

/-- The representation `⊕_λ ρ_λ ⊗ I_{m_λ}` of `G` on `⊕_λ V_λ ⊗ ℂ^{m_λ}`. -/
def isoRep (ρ : ∀ l, Representation ℂ G (V l)) (m : Λ → ℕ) :
    Representation ℂ G (IsoSpace V m) where
  toFun := isoAct ρ m
  map_one' := by
    apply LinearMap.ext; intro f; funext l i; simp
  map_mul' g h := by
    apply LinearMap.ext; intro f; funext l i; simp [Module.End.mul_apply]

@[simp] theorem isoRep_apply (ρ : ∀ l, Representation ℂ G (V l)) (m : Λ → ℕ) (g : G)
    (f : IsoSpace V m) (l : Λ) (i : Fin (m l)) : isoRep ρ m g f l i = ρ l g (f l i) := rfl

/-- The operator `⊕_λ I_{V_λ} ⊗ X_λ : ⊕ V_λ ⊗ ℂ^{m_λ} → ⊕ V_λ ⊗ ℂ^{n_λ}` of a family of
rectangular coefficient matrices `X_λ ∈ M_{n_λ × m_λ}(ℂ)`, as a linear function of `X`. -/
def blockMap (V : Λ → Type*) [∀ l, AddCommGroup (V l)] [∀ l, Module ℂ (V l)]
    (m n : Λ → ℕ) :
    (∀ l, Matrix (Fin (n l)) (Fin (m l)) ℂ) →ₗ[ℂ] (IsoSpace V m →ₗ[ℂ] IsoSpace V n) where
  toFun X :=
    { toFun := fun f l i => ∑ j, X l i j • f l j
      map_add' := fun f f' => by funext l i; simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c f => by
        funext l i; simp [Finset.smul_sum, smul_comm c] }
  map_add' X Y := by
    apply LinearMap.ext; intro f; funext l i; simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by
    apply LinearMap.ext; intro f; funext l i; simp [Finset.smul_sum, smul_smul]

@[simp] theorem blockMap_apply (m n : Λ → ℕ) (X : ∀ l, Matrix (Fin (n l)) (Fin (m l)) ℂ)
    (f : IsoSpace V m) (l : Λ) (i : Fin (n l)) :
    blockMap V m n X f l i = ∑ j, X l i j • f l j := rfl

/-- The elementary vector `v` placed in sector `λ`, multiplicity coordinate `j`. -/
def isoSingle (m : Λ → ℕ) (l : Λ) (j : Fin (m l)) : V l →ₗ[ℂ] IsoSpace V m :=
  LinearMap.single ℂ (fun l => Fin (m l) → V l) l ∘ₗ LinearMap.single ℂ (fun _ => V l) j

theorem isoSingle_apply_self (m : Λ → ℕ) (l : Λ) (j : Fin (m l)) (v : V l) (j' : Fin (m l)) :
    isoSingle m l j v l j' = if j' = j then v else 0 := by
  simp only [isoSingle, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single,
    Pi.single_eq_same]
  by_cases h : j' = j
  · subst h; simp
  · simp [h, Pi.single_eq_of_ne h]

theorem isoSingle_apply_ne (m : Λ → ℕ) {l l' : Λ} (h : l' ≠ l) (j : Fin (m l)) (v : V l)
    (j' : Fin (m l')) : isoSingle m l j v l' j' = 0 := by
  simp [isoSingle, Pi.single_eq_of_ne h]

/-- Every vector of the isotypic carrier is the sum of its elementary components. -/
theorem sum_isoSingle (m : Λ → ℕ) (f : IsoSpace V m) :
    ∑ l, ∑ j, isoSingle m l j (f l j) = f := by
  funext l j
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single l, Finset.sum_eq_single j]
  · rw [isoSingle_apply_self, if_pos rfl]
  · intro b _ hb; rw [isoSingle_apply_self, if_neg (Ne.symm hb)]
  · simp
  · intro b _ hb
    exact Finset.sum_eq_zero fun j' _ => isoSingle_apply_ne m (Ne.symm hb) _ _ _
  · simp

/-- The `(λ,j) → (μ,i)` block of an operator between isotypic carriers. -/
def isoBlock (m n : Λ → ℕ) (T : IsoSpace V m →ₗ[ℂ] IsoSpace V n) (l : Λ) (j : Fin (m l))
    (l' : Λ) (i : Fin (n l')) : V l →ₗ[ℂ] V l' :=
  (LinearMap.proj i ∘ₗ LinearMap.proj (φ := fun l => Fin (n l) → V l) l') ∘ₗ T ∘ₗ
    isoSingle m l j

theorem isoBlock_apply (m n : Λ → ℕ) (T : IsoSpace V m →ₗ[ℂ] IsoSpace V n) (l : Λ)
    (j : Fin (m l)) (l' : Λ) (i : Fin (n l')) (v : V l) :
    isoBlock m n T l j l' i v = T (isoSingle m l j v) l' i := rfl

theorem isoAct_isoSingle (ρ : ∀ l, Representation ℂ G (V l)) (m : Λ → ℕ) (g : G) (l : Λ)
    (j : Fin (m l)) (v : V l) :
    isoAct ρ m g (isoSingle m l j v) = isoSingle m l j (ρ l g v) := by
  funext l' j'
  rw [isoAct_apply]
  by_cases h : l' = l
  · subst h
    rw [isoSingle_apply_self, isoSingle_apply_self]
    split_ifs <;> simp
  · rw [isoSingle_apply_ne m h, isoSingle_apply_ne m h, map_zero]

theorem isoBlock_isIntertwiner (ρ : ∀ l, Representation ℂ G (V l)) (m n : Λ → ℕ)
    {T : IsoSpace V m →ₗ[ℂ] IsoSpace V n} (hT : IsIntertwiner (isoRep ρ m) (isoRep ρ n) T)
    (l : Λ) (j : Fin (m l)) (l' : Λ) (i : Fin (n l')) :
    IsIntertwiner (ρ l) (ρ l') (isoBlock m n T l j l' i) := by
  intro g
  apply LinearMap.ext; intro v
  simp only [LinearMap.coe_comp, Function.comp_apply, isoBlock_apply]
  have h := LinearMap.congr_fun (hT g) (isoSingle m l j v)
  simp only [LinearMap.coe_comp, Function.comp_apply] at h
  change T (isoSingle m l j (ρ l g v)) l' i = _
  rw [← isoAct_isoSingle]
  change T (isoRep ρ m g (isoSingle m l j v)) l' i = _
  rw [h, isoRep_apply]

/-- `blockMap X` is an intertwiner. -/
theorem blockMap_isIntertwiner (ρ : ∀ l, Representation ℂ G (V l)) (m n : Λ → ℕ)
    (X : ∀ l, Matrix (Fin (n l)) (Fin (m l)) ℂ) :
    IsIntertwiner (isoRep ρ m) (isoRep ρ n) (blockMap V m n X) := by
  intro g
  apply LinearMap.ext; intro f; funext l i
  simp only [LinearMap.coe_comp, Function.comp_apply, blockMap_apply, isoRep_apply, map_sum,
    map_smul]

/-- `X ↦ ⊕ I ⊗ X_λ` is injective when every `V_λ` is nonzero. -/
theorem blockMap_injective (m n : Λ → ℕ) (hV : ∀ l, Nontrivial (V l)) :
    Function.Injective (blockMap V m n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  funext l i j
  obtain ⟨v, hv⟩ := exists_ne (0 : V l)
  have h := congrArg (fun T => T (isoSingle m l j v) l i) hX
  simp only [blockMap_apply, LinearMap.zero_apply, Pi.zero_apply] at h
  have hs : ∑ j', X l i j' • isoSingle m l j v l j' = X l i j • v := by
    rw [Finset.sum_eq_single j]
    · rw [isoSingle_apply_self, if_pos rfl]
    · intro b _ hb; rw [isoSingle_apply_self, if_neg hb, smul_zero]
    · simp
  rw [hs] at h
  exact (smul_eq_zero.mp h).resolve_right hv

variable [∀ l, FiniteDimensional ℂ (V l)]

/-- **Schur's lemma on isotypic carriers.**  For irreducible, pairwise inequivalent,
finite-dimensional `V_λ`, an operator `⊕ V_λ ⊗ ℂ^{m_λ} → ⊕ V_λ ⊗ ℂ^{n_λ}` is an intertwiner
exactly when it is `⊕_λ I_{V_λ} ⊗ X_λ` for rectangular matrices `X_λ ∈ M_{n_λ × m_λ}(ℂ)`. -/
theorem isIntertwiner_iso_iff (ρ : ∀ l, Representation ℂ G (V l))
    (hirr : ∀ l, IsIrreducible (ρ l)) (hineq : ∀ l l', l ≠ l' → ¬ Equivalent (ρ l) (ρ l'))
    (m n : Λ → ℕ) (T : IsoSpace V m →ₗ[ℂ] IsoSpace V n) :
    IsIntertwiner (isoRep ρ m) (isoRep ρ n) T ↔ ∃ X, T = blockMap V m n X := by
  constructor
  · intro hT
    have hsc : ∀ l (i : Fin (n l)) (j : Fin (m l)),
        ∃ c : ℂ, isoBlock m n T l j l i = c • LinearMap.id := fun l i j =>
      schur_scalar (hirr l) (isoBlock_isIntertwiner ρ m n hT l j l i)
    choose X hX using hsc
    refine ⟨X, ?_⟩
    apply LinearMap.ext; intro f; funext l' i
    conv_lhs => rw [← sum_isoSingle m f]
    simp only [map_sum, Finset.sum_apply, blockMap_apply]
    rw [Finset.sum_eq_single l']
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← isoBlock_apply, hX]
      rfl
    · intro l _ hl
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← isoBlock_apply, schur_eq_zero_of_not_equivalent (hirr l) (hirr l') (hineq l l' hl)
        (isoBlock_isIntertwiner ρ m n hT l j l' i)]
      rfl
    · simp
  · rintro ⟨X, rfl⟩
    exact blockMap_isIntertwiner ρ m n X

/-- **Isotypic intertwiner spaces.**  For irreducible, pairwise inequivalent,
finite-dimensional `V_λ`, the intertwiners `⊕ V_λ ⊗ ℂ^{m_λ} → ⊕ V_λ ⊗ ℂ^{n_λ}` form a space
isomorphic to `⊕_λ M_{n_λ × m_λ}(ℂ)`; the inverse is `X ↦ ⊕_λ I_{V_λ} ⊗ X_λ`. -/
noncomputable def isoIntertwinerEquiv (ρ : ∀ l, Representation ℂ G (V l))
    (hirr : ∀ l, IsIrreducible (ρ l)) (hineq : ∀ l l', l ≠ l' → ¬ Equivalent (ρ l) (ρ l'))
    (m n : Λ → ℕ) :
    intertwiners (isoRep ρ m) (isoRep ρ n) ≃ₗ[ℂ] (∀ l, Matrix (Fin (n l)) (Fin (m l)) ℂ) :=
  ((LinearEquiv.ofInjective (blockMap V m n)
      (blockMap_injective m n fun l => (hirr l).nontrivial)).trans
    (LinearEquiv.ofEq _ _ (by
      ext T
      rw [LinearMap.mem_range, mem_intertwiners, isIntertwiner_iso_iff ρ hirr hineq]
      constructor <;> rintro ⟨X, hX⟩ <;> exact ⟨X, hX.symm⟩))).symm

/-- The coefficient matrices of an isotypic intertwiner reproduce it: `T = ⊕ I ⊗ X_λ(T)`. -/
theorem blockMap_isoIntertwinerEquiv (ρ : ∀ l, Representation ℂ G (V l))
    (hirr : ∀ l, IsIrreducible (ρ l)) (hineq : ∀ l l', l ≠ l' → ¬ Equivalent (ρ l) (ρ l'))
    (m n : Λ → ℕ) (T : intertwiners (isoRep ρ m) (isoRep ρ n)) :
    blockMap V m n (isoIntertwinerEquiv ρ hirr hineq m n T) = T := by
  have h := (isoIntertwinerEquiv ρ hirr hineq m n).symm_apply_apply T
  conv_rhs => rw [← h]
  rfl

/-- `dim Hom_G(⊕ V_λ ⊗ ℂ^{m_λ}, ⊕ V_λ ⊗ ℂ^{n_λ}) = Σ_λ m_λ n_λ`. -/
theorem finrank_isoIntertwiners (ρ : ∀ l, Representation ℂ G (V l))
    (hirr : ∀ l, IsIrreducible (ρ l)) (hineq : ∀ l l', l ≠ l' → ¬ Equivalent (ρ l) (ρ l'))
    (m n : Λ → ℕ) :
    finrank ℂ (intertwiners (isoRep ρ m) (isoRep ρ n)) = ∑ l, m l * n l := by
  rw [LinearEquiv.finrank_eq (isoIntertwinerEquiv ρ hirr hineq m n), Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Module.finrank_matrix, Fintype.card_fin, Fintype.card_fin, Module.finrank_self, mul_one,
    mul_comm]

end Isotypic

/-! ## Transport of intertwiners along equivariant isomorphisms -/

section Transport

variable {V W V' W' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

theorem isIntertwiner_symm {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    {e : V ≃ₗ[ℂ] V'} (he : IsIntertwiner ρ ρ' e.toLinearMap) :
    IsIntertwiner ρ' ρ e.symm.toLinearMap := by
  intro g
  apply LinearMap.ext; intro v
  apply e.injective
  have h := LinearMap.congr_fun (he g) (e.symm v)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at h ⊢
  rw [h]

theorem isIntertwiner_conj {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'} {es : V ≃ₗ[ℂ] V'}
    {et : W ≃ₗ[ℂ] W'} (hes : IsIntertwiner ρ ρ' es.toLinearMap)
    (het : IsIntertwiner σ σ' et.toLinearMap) {K : V →ₗ[ℂ] W} (hK : IsIntertwiner ρ σ K) :
    IsIntertwiner ρ' σ' (et.toLinearMap ∘ₗ K ∘ₗ es.symm.toLinearMap) := by
  intro g
  apply LinearMap.ext; intro v
  have h1 := LinearMap.congr_fun (isIntertwiner_symm hes g) v
  have h2 := LinearMap.congr_fun (hK g) (es.symm v)
  have h3 := LinearMap.congr_fun (het g) (K (es.symm v))
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h1 h2 h3 ⊢
  rw [h1, h2, h3]

/-- Equivariant isomorphisms `V ≅ V'`, `W ≅ W'` identify the intertwiner spaces,
`K ↦ e_t K e_s^{-1}`. -/
noncomputable def intertwinersCongr {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'} (es : V ≃ₗ[ℂ] V')
    (et : W ≃ₗ[ℂ] W') (hes : IsIntertwiner ρ ρ' es.toLinearMap)
    (het : IsIntertwiner σ σ' et.toLinearMap) :
    intertwiners ρ σ ≃ₗ[ℂ] intertwiners ρ' σ' :=
  LinearEquiv.ofSubmodules (LinearEquiv.arrowCongr es et) _ _ (by
    ext T
    rw [Submodule.mem_map_equiv, mem_intertwiners, mem_intertwiners]
    constructor
    · intro h
      have := isIntertwiner_conj hes het h
      convert this using 1
      apply LinearMap.ext; intro v
      simp [LinearEquiv.arrowCongr_apply]
    · intro h
      exact isIntertwiner_conj (isIntertwiner_symm hes) (isIntertwiner_symm het) h)

theorem intertwinersCongr_apply {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'} (es : V ≃ₗ[ℂ] V')
    (et : W ≃ₗ[ℂ] W') (hes : IsIntertwiner ρ ρ' es.toLinearMap)
    (het : IsIntertwiner σ σ' et.toLinearMap) (K : intertwiners ρ σ) :
    (intertwinersCongr es et hes het K : V' →ₗ[ℂ] W')
      = et.toLinearMap ∘ₗ (K : V →ₗ[ℂ] W) ∘ₗ es.symm.toLinearMap := rfl

end Transport

/-! ## Semi-intertwiner envelopes (`prop:schur-incidence-envelope`) -/

section Envelope

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {V : Λ → Type*}
  [∀ l, AddCommGroup (V l)] [∀ l, Module ℂ (V l)]

/-- An isotypic decomposition `H ≅ ⊕_λ V_λ ⊗ ℂ^{m_λ}` of a representation `R` on `H`: an
equivariant linear isomorphism onto the isotypic carrier. -/
structure IsotypicDecomposition {H : Type*} [AddCommGroup H] [Module ℂ H]
    (ρ : ∀ l, Representation ℂ G (V l)) (R : Representation ℂ G H) (m : Λ → ℕ) where
  /-- the decomposing isomorphism -/
  equiv : H ≃ₗ[ℂ] IsoSpace V m
  /-- it carries `R` to `⊕_λ ρ_λ ⊗ I` -/
  intertwines : IsIntertwiner R (isoRep ρ m) equiv.toLinearMap

/-- A character never vanishes. -/
theorem character_ne_zero (χ : G →* ℂ) (g : G) : χ g ≠ 0 := by
  intro h
  have := map_mul χ g g⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at this
  exact one_ne_zero this

theorem rep_inv_comp {H : Type*} [AddCommGroup H] [Module ℂ H] (R : Representation ℂ G H)
    (g : G) : R g⁻¹ ∘ₗ R g = LinearMap.id := by
  rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem rep_comp_inv {H : Type*} [AddCommGroup H] [Module ℂ H] (R : Representation ℂ G H)
    (g : G) : R g ∘ₗ R g⁻¹ = LinearMap.id := by
  rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl

/-- The twisted representation `χ^{-1} R`. -/
noncomputable def twistRep {H : Type*} [AddCommGroup H] [Module ℂ H] (χ : G →* ℂ)
    (R : Representation ℂ G H) : Representation ℂ G H where
  toFun g := (χ g)⁻¹ • R g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, mul_inv, smul_mul_smul_comm]

theorem twistRep_apply {H : Type*} [AddCommGroup H] [Module ℂ H] (χ : G →* ℂ)
    (R : Representation ℂ G H) (g : G) : twistRep χ R g = (χ g)⁻¹ • R g := rfl

variable {Hs Ht : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  [FiniteDimensional ℂ Hs] [NormedAddCommGroup Ht] [InnerProductSpace ℂ Ht]
  [FiniteDimensional ℂ Ht]

/-- A unitary representation on a finite-dimensional Hilbert space: `R(g)^* = R(g⁻¹)`. -/
def IsUnitaryRep {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (R : Representation ℂ G H) : Prop :=
  ∀ g, LinearMap.adjoint (R g) = R g⁻¹

/-- A unitary character: `|χ(g)| = 1`. -/
def IsUnitaryCharacter (χ : G →* ℂ) : Prop :=
  ∀ g, star (χ g) * χ g = 1

/-- The amplitude envelope `S_χ = {K : R_t(g) K R_s(g)^* = χ(g) K for all g}`. -/
def semiIntertwinerEnvelope (Rs : Representation ℂ G Hs) (Rt : Representation ℂ G Ht)
    (χ : G →* ℂ) : Submodule ℂ (Hs →ₗ[ℂ] Ht) where
  carrier := {K | ∀ g, Rt g ∘ₗ K ∘ₗ LinearMap.adjoint (Rs g) = χ g • K}
  add_mem' {K L} hK hL g := by
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, hK g, hL g, smul_add]
  zero_mem' g := by simp
  smul_mem' c K hK g := by
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hK g, smul_comm]

/-- The source commutant `R_s(G)' = {A : A R_s(g) = R_s(g) A}`. -/
abbrev commutant (Rs : Representation ℂ G Hs) : Submodule ℂ (Hs →ₗ[ℂ] Hs) :=
  intertwiners Rs Rs

/-- **Twisting the target.**  For a unitary source, `K ∈ S_χ` iff `K` intertwines `R_s` with
`χ^{-1} R_t`. -/
theorem mem_semiIntertwinerEnvelope_iff {Rs : Representation ℂ G Hs}
    {Rt : Representation ℂ G Ht} {χ : G →* ℂ} (hRs : IsUnitaryRep Rs) (K : Hs →ₗ[ℂ] Ht) :
    K ∈ semiIntertwinerEnvelope Rs Rt χ ↔ IsIntertwiner Rs (twistRep χ Rt) K := by
  constructor
  · intro h g
    have hg := h g
    rw [hRs g] at hg
    rw [twistRep_apply, LinearMap.smul_comp]
    calc K ∘ₗ Rs g = (χ g)⁻¹ • ((χ g • K) ∘ₗ Rs g) := by
          rw [LinearMap.smul_comp, smul_smul, inv_mul_cancel₀ (character_ne_zero χ g),
            one_smul]
      _ = (χ g)⁻¹ • ((Rt g ∘ₗ K ∘ₗ Rs g⁻¹) ∘ₗ Rs g) := by rw [hg]
      _ = (χ g)⁻¹ • (Rt g ∘ₗ K) := by
          simp only [LinearMap.comp_assoc, rep_inv_comp, LinearMap.comp_id]
  · intro h g
    rw [hRs g]
    have hg := h g
    rw [twistRep_apply, LinearMap.smul_comp] at hg
    have h' : Rt g ∘ₗ K = χ g • (K ∘ₗ Rs g) := by
      rw [hg, smul_smul, mul_inv_cancel₀ (character_ne_zero χ g), one_smul]
    rw [← LinearMap.comp_assoc, h', LinearMap.smul_comp, LinearMap.comp_assoc, rep_comp_inv,
      LinearMap.comp_id]

theorem semiIntertwinerEnvelope_eq {Rs : Representation ℂ G Hs}
    {Rt : Representation ℂ G Ht} {χ : G →* ℂ} (hRs : IsUnitaryRep Rs) :
    semiIntertwinerEnvelope Rs Rt χ = intertwiners Rs (twistRep χ Rt) := by
  ext K
  exact mem_semiIntertwinerEnvelope_iff hRs K

/-- **`prop:schur-incidence-envelope`, isotypic form.**  The identification
`S_χ ≅ ⊕_λ I_{V_λ} ⊗ M_{n_λ × m_λ}(ℂ)` determined by the decompositions
`H_s ≅ ⊕ V_λ ⊗ ℂ^{m_λ}` and `χ^{-1} H_t ≅ ⊕ V_λ ⊗ ℂ^{n_λ}`. -/
noncomputable def schurEnvelopeEquiv (ρ : ∀ l, Representation ℂ G (V l))
    (hirr : ∀ l, IsIrreducible (ρ l)) (hineq : ∀ l l', l ≠ l' → ¬ Equivalent (ρ l) (ρ l'))
    [∀ l, FiniteDimensional ℂ (V l)]
    {Rs : Representation ℂ G Hs} {Rt : Representation ℂ G Ht} {χ : G →* ℂ}
    (hRs : IsUnitaryRep Rs) {m n : Λ → ℕ}
    (Ds : IsotypicDecomposition ρ Rs m) (Dt : IsotypicDecomposition ρ (twistRep χ Rt) n) :
    semiIntertwinerEnvelope Rs Rt χ ≃ₗ[ℂ] (∀ l, Matrix (Fin (n l)) (Fin (m l)) ℂ) :=
  (LinearEquiv.ofEq _ _ (semiIntertwinerEnvelope_eq hRs)).trans
    ((intertwinersCongr Ds.equiv Dt.equiv Ds.intertwines Dt.intertwines).trans
      (isoIntertwinerEquiv ρ hirr hineq m n))

/-- The envelope identification is `K ↦ (X_λ)` with `E_t K E_s^{-1} = ⊕_λ I_{V_λ} ⊗ X_λ`. -/
theorem blockMap_schurEnvelopeEquiv (ρ : ∀ l, Representation ℂ G (V l))
    (hirr : ∀ l, IsIrreducible (ρ l)) (hineq : ∀ l l', l ≠ l' → ¬ Equivalent (ρ l) (ρ l'))
    [∀ l, FiniteDimensional ℂ (V l)]
    {Rs : Representation ℂ G Hs} {Rt : Representation ℂ G Ht} {χ : G →* ℂ}
    (hRs : IsUnitaryRep Rs) {m n : Λ → ℕ}
    (Ds : IsotypicDecomposition ρ Rs m) (Dt : IsotypicDecomposition ρ (twistRep χ Rt) n)
    (K : semiIntertwinerEnvelope Rs Rt χ) :
    blockMap V m n (schurEnvelopeEquiv ρ hirr hineq hRs Ds Dt K)
      = Dt.equiv.toLinearMap ∘ₗ (K : Hs →ₗ[ℂ] Ht) ∘ₗ Ds.equiv.symm.toLinearMap := by
  unfold schurEnvelopeEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, blockMap_isoIntertwinerEquiv,
    intertwinersCongr_apply]
  rfl

/-- Every block-diagonal coefficient family is realized: `S_χ ∋ E_t^{-1} (⊕ I ⊗ X_λ) E_s`. -/
theorem schurEnvelopeEquiv_symm_apply (ρ : ∀ l, Representation ℂ G (V l))
    (hirr : ∀ l, IsIrreducible (ρ l)) (hineq : ∀ l l', l ≠ l' → ¬ Equivalent (ρ l) (ρ l'))
    [∀ l, FiniteDimensional ℂ (V l)]
    {Rs : Representation ℂ G Hs} {Rt : Representation ℂ G Ht} {χ : G →* ℂ}
    (hRs : IsUnitaryRep Rs) {m n : Λ → ℕ}
    (Ds : IsotypicDecomposition ρ Rs m) (Dt : IsotypicDecomposition ρ (twistRep χ Rt) n)
    (X : ∀ l, Matrix (Fin (n l)) (Fin (m l)) ℂ) :
    ((schurEnvelopeEquiv ρ hirr hineq hRs Ds Dt).symm X : Hs →ₗ[ℂ] Ht)
      = Dt.equiv.symm.toLinearMap ∘ₗ blockMap V m n X ∘ₗ Ds.equiv.toLinearMap := by
  have h := blockMap_schurEnvelopeEquiv ρ hirr hineq hRs Ds Dt
    ((schurEnvelopeEquiv ρ hirr hineq hRs Ds Dt).symm X)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h]
  apply LinearMap.ext; intro v
  simp

/-- `dim S_χ = Σ_λ m_λ n_λ`. -/
theorem finrank_semiIntertwinerEnvelope (ρ : ∀ l, Representation ℂ G (V l))
    (hirr : ∀ l, IsIrreducible (ρ l)) (hineq : ∀ l l', l ≠ l' → ¬ Equivalent (ρ l) (ρ l'))
    [∀ l, FiniteDimensional ℂ (V l)]
    {Rs : Representation ℂ G Hs} {Rt : Representation ℂ G Ht} {χ : G →* ℂ}
    (hRs : IsUnitaryRep Rs) {m n : Λ → ℕ}
    (Ds : IsotypicDecomposition ρ Rs m) (Dt : IsotypicDecomposition ρ (twistRep χ Rt) n) :
    finrank ℂ (semiIntertwinerEnvelope Rs Rt χ) = ∑ l, m l * n l := by
  rw [LinearEquiv.finrank_eq ((LinearEquiv.ofEq _ _ (semiIntertwinerEnvelope_eq hRs)).trans
      (intertwinersCongr Ds.equiv Dt.equiv Ds.intertwines Dt.intertwines)),
    finrank_isoIntertwiners ρ hirr hineq]

/-- `dim R_s(G)' = Σ_λ m_λ²`. -/
theorem finrank_commutant (ρ : ∀ l, Representation ℂ G (V l))
    (hirr : ∀ l, IsIrreducible (ρ l)) (hineq : ∀ l l', l ≠ l' → ¬ Equivalent (ρ l) (ρ l'))
    [∀ l, FiniteDimensional ℂ (V l)] {Rs : Representation ℂ G Hs} {m : Λ → ℕ}
    (Ds : IsotypicDecomposition ρ Rs m) :
    finrank ℂ (commutant Rs) = ∑ l, m l ^ 2 := by
  rw [LinearEquiv.finrank_eq
      (intertwinersCongr Ds.equiv Ds.equiv Ds.intertwines Ds.intertwines),
    finrank_isoIntertwiners ρ hirr hineq]
  simp [sq]

/-- **The character cancels in `K^* L`.**  For a unitary source and target and a unitary
character, `K^* L ∈ R_s(G)'` for all `K, L ∈ S_χ`. -/
theorem adjoint_comp_mem_commutant {Rs : Representation ℂ G Hs} {Rt : Representation ℂ G Ht}
    {χ : G →* ℂ} (hRs : IsUnitaryRep Rs) (hRt : IsUnitaryRep Rt) (hχ : IsUnitaryCharacter χ)
    {K L : Hs →ₗ[ℂ] Ht} (hK : K ∈ semiIntertwinerEnvelope Rs Rt χ)
    (hL : L ∈ semiIntertwinerEnvelope Rs Rt χ) :
    LinearMap.adjoint K ∘ₗ L ∈ commutant Rs := by
  rw [mem_semiIntertwinerEnvelope_iff hRs] at hK hL
  intro g
  have hLg := hL g
  rw [twistRep_apply, LinearMap.smul_comp] at hLg
  -- `K R_s(g⁻¹) = χ(g) R_t(g⁻¹) K`; take adjoints.
  have hKg := hK g⁻¹
  have hχinv : (χ g⁻¹)⁻¹ = χ g := by rw [map_inv, inv_inv]
  rw [twistRep_apply, LinearMap.smul_comp, hχinv] at hKg
  have hadj := congrArg LinearMap.adjoint hKg
  rw [LinearMap.adjoint_comp, map_smulₛₗ, LinearMap.adjoint_comp, hRs, hRt] at hadj
  simp only [inv_inv] at hadj
  have hstar : (starRingEnd ℂ) (χ g) = (χ g)⁻¹ :=
    eq_inv_of_mul_eq_one_left (hχ g)
  rw [hstar] at hadj
  -- hadj : R_s(g) K^* = χ(g)⁻¹ K^* R_t(g)
  rw [LinearMap.comp_assoc, hLg, LinearMap.comp_smul, ← LinearMap.comp_assoc,
    ← LinearMap.comp_assoc, hadj, LinearMap.smul_comp, LinearMap.comp_assoc]

/-- **`prop:schur-incidence-envelope`.**  Let `G` be any group (in particular a compact group)
acting unitarily on finite-dimensional Hilbert spaces `H_s`, `H_t`, let `χ` be a unitary
character, and let `H_s ≅ ⊕_λ V_λ ⊗ ℂ^{m_λ}`, `χ^{-1} H_t ≅ ⊕_λ V_λ ⊗ ℂ^{n_λ}` with
`V_λ` irreducible, pairwise inequivalent and finite-dimensional.  Then the envelope `S_χ` is
isomorphic to `⊕_λ I_{V_λ} ⊗ M_{n_λ × m_λ}(ℂ)` (the isomorphism sends `K` to the coefficient
family `X` with `E_t K E_s^{-1} = ⊕_λ I_{V_λ} ⊗ X_λ`), `dim S_χ = Σ_λ m_λ n_λ`, every
`K^* L` with `K, L ∈ S_χ` lies in `R_s(G)'`, and `dim R_s(G)' = Σ_λ m_λ²`. -/
theorem schur_incidence_envelope (ρ : ∀ l, Representation ℂ G (V l))
    (hirr : ∀ l, IsIrreducible (ρ l)) (hineq : ∀ l l', l ≠ l' → ¬ Equivalent (ρ l) (ρ l'))
    [∀ l, FiniteDimensional ℂ (V l)]
    {Rs : Representation ℂ G Hs} {Rt : Representation ℂ G Ht} {χ : G →* ℂ}
    (hRs : IsUnitaryRep Rs) (hRt : IsUnitaryRep Rt) (hχ : IsUnitaryCharacter χ)
    {m n : Λ → ℕ}
    (Ds : IsotypicDecomposition ρ Rs m) (Dt : IsotypicDecomposition ρ (twistRep χ Rt) n) :
    (∃ e : semiIntertwinerEnvelope Rs Rt χ ≃ₗ[ℂ] (∀ l, Matrix (Fin (n l)) (Fin (m l)) ℂ),
      ∀ K : semiIntertwinerEnvelope Rs Rt χ, Dt.equiv.toLinearMap ∘ₗ (K : Hs →ₗ[ℂ] Ht) ∘ₗ Ds.equiv.symm.toLinearMap
        = blockMap V m n (e K)) ∧
    finrank ℂ (semiIntertwinerEnvelope Rs Rt χ) = ∑ l, m l * n l ∧
    (∀ K ∈ semiIntertwinerEnvelope Rs Rt χ, ∀ L ∈ semiIntertwinerEnvelope Rs Rt χ,
      LinearMap.adjoint K ∘ₗ L ∈ commutant Rs) ∧
    finrank ℂ (commutant Rs) = ∑ l, m l ^ 2 :=
  ⟨⟨schurEnvelopeEquiv ρ hirr hineq hRs Ds Dt,
      fun K => (blockMap_schurEnvelopeEquiv ρ hirr hineq hRs Ds Dt K).symm⟩,
    finrank_semiIntertwinerEnvelope ρ hirr hineq hRs Ds Dt,
    fun _ hK _ hL => adjoint_comp_mem_commutant hRs hRt hχ hK hL,
    finrank_commutant ρ hirr hineq Ds⟩

/-! ### The normalization screen -/

variable {A : Type*} [Fintype A] {Ht' : A → Type*} [∀ a, NormedAddCommGroup (Ht' a)]
  [∀ a, InnerProductSpace ℂ (Ht' a)] [∀ a, FiniteDimensional ℂ (Ht' a)]

/-- The joint normalization map of several recorded amplitude families `K_{a,i}`:
`(X_a)_a ↦ Σ_a Σ_{i,j} (X_a)_{ij} K_{a,i}^* K_{a,j}` (a coefficient matrix unit goes to
`K_{a,i}^* K_{a,j}`). -/
noncomputable def jointNormalization {ι : A → Type*} [∀ a, Fintype (ι a)]
    (k : ∀ a, ι a → (Hs →ₗ[ℂ] Ht' a)) :
    (∀ a, Matrix (ι a) (ι a) ℂ) →ₗ[ℂ] (Hs →ₗ[ℂ] Hs) where
  toFun X := ∑ a, ∑ i, ∑ j, X a i j • (LinearMap.adjoint (k a i) ∘ₗ k a j)
  map_add' X Y := by
    simp only [Pi.add_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- The joint normalization of amplitudes in semi-intertwiner envelopes lands in the source
commutant; if it is injective, the coefficient domain is no larger than `R_s(G)'`. -/
theorem card_sq_le_of_jointNormalization_injective {Rs : Representation ℂ G Hs}
    {Rt : ∀ a, Representation ℂ G (Ht' a)} {χ : A → G →* ℂ} (hRs : IsUnitaryRep Rs)
    (hRt : ∀ a, IsUnitaryRep (Rt a)) (hχ : ∀ a, IsUnitaryCharacter (χ a))
    {ι : A → Type*} [∀ a, Fintype (ι a)] (k : ∀ a, ι a → (Hs →ₗ[ℂ] Ht' a))
    (hk : ∀ a i, k a i ∈ semiIntertwinerEnvelope Rs (Rt a) (χ a))
    (hinj : Function.Injective (jointNormalization k)) :
    ∑ a, Fintype.card (ι a) ^ 2 ≤ finrank ℂ (commutant Rs) := by
  have hmem : ∀ X, jointNormalization k X ∈ commutant Rs := fun X =>
    Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun i _ => Submodule.sum_mem _
      fun j _ => Submodule.smul_mem _ _
        (adjoint_comp_mem_commutant hRs (hRt a) (hχ a) (hk a i) (hk a j))
  let N := LinearMap.codRestrict (commutant Rs) (jointNormalization k) hmem
  have hN : Function.Injective N := fun X Y h => hinj (congrArg Subtype.val h)
  have := LinearMap.finrank_le_finrank_of_injective hN
  rw [Module.finrank_pi_fintype] at this
  simpa [Module.finrank_matrix, sq] using this

/-- **`eq:schur-normalization-screen`.**  For several recorded semi-intertwiner envelopes
`S_{χ_a}` on the same source (`χ_a^{-1} H_{t,a} ≅ ⊕ V_λ ⊗ ℂ^{n_{a,λ}}`), with amplitude bases
`K_{a,·}` of `S_{χ_a}`, injectivity of the joint normalization map forces
`Σ_a (Σ_λ m_λ n_{a,λ})² ≤ Σ_λ m_λ²`. -/
theorem schur_normalization_screen (ρ : ∀ l, Representation ℂ G (V l))
    (hirr : ∀ l, IsIrreducible (ρ l)) (hineq : ∀ l l', l ≠ l' → ¬ Equivalent (ρ l) (ρ l'))
    [∀ l, FiniteDimensional ℂ (V l)]
    {Rs : Representation ℂ G Hs} {Rt : ∀ a, Representation ℂ G (Ht' a)} {χ : A → G →* ℂ}
    (hRs : IsUnitaryRep Rs) (hRt : ∀ a, IsUnitaryRep (Rt a))
    (hχ : ∀ a, IsUnitaryCharacter (χ a)) {m : Λ → ℕ} {n : A → Λ → ℕ}
    (Ds : IsotypicDecomposition ρ Rs m)
    (Dt : ∀ a, IsotypicDecomposition ρ (twistRep (χ a) (Rt a)) (n a))
    {ι : A → Type*} [∀ a, Fintype (ι a)]
    (b : ∀ a, Basis (ι a) ℂ (semiIntertwinerEnvelope Rs (Rt a) (χ a)))
    (hinj : Function.Injective (jointNormalization fun a i => (b a i : Hs →ₗ[ℂ] Ht' a))) :
    ∑ a, (∑ l, m l * n a l) ^ 2 ≤ ∑ l, m l ^ 2 := by
  have h := card_sq_le_of_jointNormalization_injective hRs hRt hχ
    (fun a i => (b a i : Hs →ₗ[ℂ] Ht' a)) (fun a i => (b a i).2) hinj
  rw [finrank_commutant ρ hirr hineq Ds] at h
  convert h using 3 with a
  rw [← finrank_semiIntertwinerEnvelope ρ hirr hineq hRs Ds (Dt a),
    Module.finrank_eq_card_basis (b a)]

/-! ### Non-vacuity witness -/

/-- The trivial one-dimensional representation is irreducible. -/
theorem isIrreducible_trivial_complex : IsIrreducible (Representation.trivial ℂ G ℂ) :=
  ⟨inferInstance, fun U _ => Ideal.eq_bot_or_top U⟩

/-- The trivial representation on `ℂ` is unitary. -/
theorem isUnitaryRep_trivial_complex : IsUnitaryRep (Representation.trivial ℂ G ℂ) := by
  intro g
  simp [Representation.trivial]

/-- The trivial character is unitary. -/
theorem isUnitaryCharacter_one : IsUnitaryCharacter (1 : G →* ℂ) := by
  intro g; simp

/-- The decomposition `ℂ ≅ V ⊗ ℂ¹` of the trivial representation (one sector, multiplicity
one): the hypotheses of `schur_incidence_envelope` are jointly satisfiable. -/
noncomputable def trivialIsotypicDecomposition :
    IsotypicDecomposition (fun _ : Unit => Representation.trivial ℂ G ℂ)
      (twistRep 1 (Representation.trivial ℂ G ℂ)) (fun _ => 1) where
  equiv := (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.trans
    (LinearEquiv.funUnique Unit ℂ (Fin 1 → ℂ)).symm
  intertwines g := by
    apply LinearMap.ext; intro v; funext l i
    simp [twistRep_apply, Representation.trivial]

example : finrank ℂ (semiIntertwinerEnvelope (Representation.trivial ℂ G ℂ)
    (Representation.trivial ℂ G ℂ) 1) = 1 := by
  have Ds : IsotypicDecomposition (fun _ : Unit => Representation.trivial ℂ G ℂ)
      (Representation.trivial ℂ G ℂ) (fun _ => 1) :=
    ⟨(trivialIsotypicDecomposition (G := G)).equiv, by
      intro g; apply LinearMap.ext; intro v; funext l i
      simp [trivialIsotypicDecomposition, Representation.trivial]⟩
  rw [(schur_incidence_envelope (fun _ : Unit => Representation.trivial ℂ G ℂ)
    (fun _ => isIrreducible_trivial_complex) (fun l l' h => absurd (Subsingleton.elim l l') h)
    isUnitaryRep_trivial_complex isUnitaryRep_trivial_complex isUnitaryCharacter_one Ds
    trivialIsotypicDecomposition).2.1]
  simp

end Envelope

end SchurIsotypicEnvelope

end RenewalGeometry
