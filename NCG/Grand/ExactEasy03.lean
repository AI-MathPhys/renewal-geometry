/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MinimalReadAlgebra
import NCG.Grand.RecordRefinementBundle
import NCG.Grand.TypedHankelRealization

/-!
# Exact EASY batch 03: the generated minimal record

This file discharges the clause omitted by the original abstract
`minimal_record`: right congruence is now derived from the literal
all-future word signature of a deterministic record machine.  The
same construction packages descended primitive updates, unique
future-coordinate factorization, and the coarsest-quotient universal
property.
-/

namespace NCG

/-- A finite-word deterministic record machine.  The types need not
be finite for the quotient argument itself. -/
structure WordRecordMachine (A R D V : Type*) where
  step : A → R → R
  read : D → R → V

namespace WordRecordMachine

variable {A R D V : Type*} (M : WordRecordMachine A R D V)

/-- Execute a word from left to right. -/
def run : List A → R → R
  | [], r => r
  | a :: w, r => run w (M.step a r)

@[simp] theorem run_nil (r : R) : M.run [] r = r := rfl

@[simp] theorem run_cons (a : A) (w : List A) (r : R) :
    M.run (a :: w) r = M.run w (M.step a r) := rfl

/-- The complete admitted-future signature: every word followed by
every Read coordinate. -/
def futureSig (r : R) : List A × D → V :=
  fun wd => M.read wd.2 (M.run wd.1 r)

/-- Equality of complete future signatures is a right congruence for
each primitive update. -/
theorem futureSig_step (a : A) {r s : R}
    (h : M.futureSig r = M.futureSig s) :
    M.futureSig (M.step a r) = M.futureSig (M.step a s) := by
  funext wd
  have hw := congrFun h (a :: wd.1, wd.2)
  exact hw

/-- A future coordinate factors through the minimal quotient. -/
def quotientRead (wd : List A × D) :
    MinRec M.futureSig → V :=
  Quotient.lift (fun r => M.futureSig r wd)
    (fun _ _ h => congrFun h wd)

@[simp] theorem quotientRead_mk (wd : List A × D) (r : R) :
    M.quotientRead wd (Quotient.mk (minRecSetoid M.futureSig) r)
      = M.read wd.2 (M.run wd.1 r) := rfl

/-- Every primitive step descends to the all-future quotient. -/
def quotientStep (a : A) :
    MinRec M.futureSig → MinRec M.futureSig :=
  Quotient.lift
    (fun r => Quotient.mk (minRecSetoid M.futureSig) (M.step a r))
    (fun _ _ h => Quotient.sound (M.futureSig_step a h))

@[simp] theorem quotientStep_mk (a : A) (r : R) :
    M.quotientStep a (Quotient.mk (minRecSetoid M.futureSig) r)
      = Quotient.mk (minRecSetoid M.futureSig) (M.step a r) := rfl

/-- A map out of a quotient is unique once its values on quotient
classes are fixed. -/
theorem quotient_fun_unique {X : Type*} (f g : MinRec M.futureSig → X)
    (h : ∀ r, f (Quotient.mk (minRecSetoid M.futureSig) r)
      = g (Quotient.mk (minRecSetoid M.futureSig) r)) : f = g := by
  funext q
  induction q using Quotient.ind with
  | _ r => exact h r

/-- Literal version of `thm:minimal-record`, clauses M1--M4.

The sufficient quotient hypothesis says exactly that every generated
future coordinate factors through `c`; the theorem constructs the
unique surjection from that quotient to the minimal future quotient.
-/
def MinimalRecordExact : Prop :=
    -- M1: equivalence and right congruence
    (∀ r s : R,
      (Quotient.mk (minRecSetoid M.futureSig) r
          = Quotient.mk (minRecSetoid M.futureSig) s)
        ↔ M.futureSig r = M.futureSig s)
    ∧ (∀ a : A, ∀ r s : R, M.futureSig r = M.futureSig s →
        M.futureSig (M.step a r) = M.futureSig (M.step a s))
    -- M2: unique descended primitive updates
    ∧ (∀ a : A, ∃! u : MinRec M.futureSig → MinRec M.futureSig,
        ∀ r, u (Quotient.mk (minRecSetoid M.futureSig) r)
          = Quotient.mk (minRecSetoid M.futureSig) (M.step a r))
    -- M3: unique factorization of every pulled-back future Read
    ∧ (∀ wd : List A × D, ∃! f : MinRec M.futureSig → V,
        ∀ r, f (Quotient.mk (minRecSetoid M.futureSig) r)
          = M.read wd.2 (M.run wd.1 r))
    -- M4: every future-sufficient surjective quotient maps uniquely
    -- and surjectively onto the minimal quotient
    ∧ (∀ {S : Type*} (c : R → S), Function.Surjective c →
        (∀ wd : List A × D, ∃ f : S → V,
          ∀ r, f (c r) = M.read wd.2 (M.run wd.1 r)) →
        ∃! h : S → MinRec M.futureSig,
          Function.Surjective h ∧
          ∀ r, h (c r) = Quotient.mk (minRecSetoid M.futureSig) r)

theorem minimal_record_exact : M.MinimalRecordExact := by
  refine ⟨(minimal_record M.futureSig).1, ?_, ?_, ?_, ?_⟩
  · exact fun a r s h => M.futureSig_step a h
  · intro a
    refine ⟨M.quotientStep a, fun r => rfl, ?_⟩
    intro u hu
    exact M.quotient_fun_unique u (M.quotientStep a) fun r => by
      rw [hu r]
      rfl
  · intro wd
    refine ⟨M.quotientRead wd, fun r => rfl, ?_⟩
    intro f hf
    exact M.quotient_fun_unique f (M.quotientRead wd) fun r => by
      rw [hf r]
      rfl
  · intro S c hsurj hcoords
    choose f hf using hcoords
    let g : S → (List A × D → V) := fun s wd => f wd s
    have hfac : ∀ r, g (c r) = M.futureSig r := by
      intro r
      funext wd
      exact hf wd r
    obtain ⟨h, hh, huniq⟩ := minimal_record_universal
      M.futureSig c g hsurj hfac
    have hhsurj : Function.Surjective h := by
      intro q
      induction q using Quotient.ind with
      | _ r =>
          exact ⟨c r, hh r⟩
    refine ⟨h, ⟨hhsurj, hh⟩, ?_⟩
    intro h' hh'
    exact huniq h' hh'.2

/-- A signature-preserving record equivalence induces the canonical
equivalence of minimal records. -/
noncomputable def minimalEquiv {S Sig : Type*} (sigR : R → Sig) (sigS : S → Sig)
    (e : R ≃ S) (he : ∀ r, sigS (e r) = sigR r) :
    MinRec sigR ≃ MinRec sigS := by
  let f : MinRec sigR → MinRec sigS :=
    Quotient.lift
      (fun r => Quotient.mk (minRecSetoid sigS) (e r))
      (fun a b h => Quotient.sound ((he a).trans (h.trans (he b).symm)))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    induction x using Quotient.ind with
    | _ a =>
      induction y using Quotient.ind with
      | _ b =>
        apply Quotient.sound
        have hab : sigS (e a) = sigS (e b) := Quotient.exact hxy
        exact (he a).symm.trans (hab.trans (he b))
  · intro y
    induction y using Quotient.ind with
    | _ s =>
      refine ⟨Quotient.mk (minRecSetoid sigR) (e.symm s), ?_⟩
      apply Quotient.sound
      exact congrArg sigS (e.apply_symm_apply s)

/-- Applying minimal future separation twice changes nothing. -/
noncomputable def minimalRecordIdempotent {Sig : Type*} (sig : R → Sig) :
    MinRec (Quotient.lift sig (fun _ _ h => h) : MinRec sig → Sig)
      ≃ MinRec sig := by
  let sigbar : MinRec sig → Sig := Quotient.lift sig (fun _ _ h => h)
  have hinj : Function.Injective sigbar := by
    intro x y hxy
    induction x using Quotient.ind with
    | _ a =>
      induction y using Quotient.ind with
      | _ b => exact Quotient.sound hxy
  let flatten : MinRec sigbar → MinRec sig :=
    Quotient.lift id (fun _ _ h => hinj h)
  refine Equiv.ofBijective flatten ⟨?_, ?_⟩
  · intro x y hxy
    induction x using Quotient.ind with
    | _ a =>
      induction y using Quotient.ind with
      | _ b =>
        apply Quotient.sound
        exact congrArg sigbar hxy
  · intro q
    exact ⟨Quotient.mk (minRecSetoid sigbar) q, rfl⟩

/-- Full `thm:minimal-record`, including the canonicity and
idempotence clause M5. -/
theorem minimal_record_exact_full :
    M.MinimalRecordExact
    ∧ (∀ {S : Type*} (M' : WordRecordMachine A S D V) (e : R ≃ S),
        (∀ r, M'.futureSig (e r) = M.futureSig r) →
        Nonempty (MinRec M.futureSig ≃ MinRec M'.futureSig))
    ∧ Nonempty
        (MinRec
            (Quotient.lift M.futureSig (fun _ _ h => h) :
              MinRec M.futureSig → (List A × D → V))
          ≃ MinRec M.futureSig) := by
  refine ⟨M.minimal_record_exact, ?_, ?_⟩
  · intro S M' e he
    exact ⟨minimalEquiv M.futureSig M'.futureSig e he⟩
  · exact ⟨minimalRecordIdempotent M.futureSig⟩

/-! ## Exact minimal Read algebra -/

variable [Finite R]

/-- Functions constant on complete-future equivalence classes. -/
def fibreConstantAlgebra (M : WordRecordMachine A R D ℂ) :
    Subalgebra ℂ (R → ℂ) where
  carrier := {f | ∀ r s, M.futureSig r = M.futureSig s → f r = f s}
  mul_mem' hf hg r s hrs :=
    congrArg₂ (fun x y : ℂ => x * y) (hf r s hrs) (hg r s hrs)
  add_mem' hf hg r s hrs :=
    congrArg₂ (fun x y : ℂ => x + y) (hf r s hrs) (hg r s hrs)
  algebraMap_mem' c r s _ := rfl

/-- The unital algebra generated by every pulled-back future Read. -/
def generatedFutureAlgebra (M : WordRecordMachine A R D ℂ) :
    Subalgebra ℂ (R → ℂ) :=
  Algebra.adjoin ℂ (Set.range fun wd : List A × D =>
    fun r => M.read wd.2 (M.run wd.1 r))

/-- Quotient functions whose pullbacks belong to the generated
future algebra. -/
def quotientGeneratedAlgebra (M : WordRecordMachine A R D ℂ) :
    Subalgebra ℂ (MinRec M.futureSig → ℂ) where
  carrier := {g | (fun r => g
    (Quotient.mk (minRecSetoid M.futureSig) r)) ∈ M.generatedFutureAlgebra}
  mul_mem' hf hg := M.generatedFutureAlgebra.mul_mem hf hg
  add_mem' hf hg := M.generatedFutureAlgebra.add_mem hf hg
  algebraMap_mem' c := M.generatedFutureAlgebra.algebraMap_mem c

/-- Future coordinates separate distinct minimal-record classes. -/
theorem quotientRead_separates (M : WordRecordMachine A R D ℂ)
    (q q' : MinRec M.futureSig) (hqq : q ≠ q') :
    ∃ wd : List A × D, M.quotientRead wd q ≠ M.quotientRead wd q' := by
  classical
  induction q using Quotient.ind with
  | _ r =>
    induction q' using Quotient.ind with
    | _ s =>
      by_contra h
      push_neg at h
      apply hqq
      apply Quotient.sound
      funext wd
      exact h wd

/-- The quotient algebra generated by future Reads is the whole
finite function algebra. -/
theorem quotientGeneratedAlgebra_eq_top
    (M : WordRecordMachine A R D ℂ) :
    M.quotientGeneratedAlgebra = ⊤ := by
  classical
  apply separating_subalgebra_eq_top
  intro q q' hqq
  obtain ⟨wd, hwd⟩ := M.quotientRead_separates q q' hqq
  refine ⟨M.quotientRead wd, ?_, hwd⟩
  change (fun r => M.quotientRead wd
    (Quotient.mk (minRecSetoid M.futureSig) r))
      ∈ M.generatedFutureAlgebra
  apply Algebra.subset_adjoin
  exact ⟨wd, rfl⟩

/-- `thm:minimal-read-algebra`, boxed equality: the algebra
generated by all future Reads is exactly the pullback algebra of
functions on the minimal record. -/
theorem minimal_read_algebra_exact (M : WordRecordMachine A R D ℂ) :
    M.generatedFutureAlgebra = M.fibreConstantAlgebra := by
  classical
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro f ⟨wd, rfl⟩
    intro r s hrs
    exact congrFun hrs wd
  · intro f hf
    have hconst : ∀ r s, M.futureSig r = M.futureSig s → f r = f s := hf
    obtain ⟨g, hg⟩ :=
      ((minimal_read_algebra M.futureSig).1 f).mp hconst
    have htop := M.quotientGeneratedAlgebra_eq_top
    have hgm : g ∈ M.quotientGeneratedAlgebra := by
      rw [htop]
      trivial
    change (fun r => g (Quotient.mk (minRecSetoid M.futureSig) r))
      ∈ M.generatedFutureAlgebra at hgm
    have hfg : f = fun r => g
        (Quotient.mk (minRecSetoid M.futureSig) r) := by
      funext r
      exact (hg r).symm
    rwa [hfg]

/-- Primitive pullback preserves the minimal Read algebra. -/
theorem fibreConstantAlgebra_step
    (M : WordRecordMachine A R D ℂ) (a : A) {f : R → ℂ}
    (hf : f ∈ M.fibreConstantAlgebra) :
    f ∘ M.step a ∈ M.fibreConstantAlgebra := by
  intro r s hrs
  exact hf _ _ (M.futureSig_step a hrs)

end WordRecordMachine

/-! ## Exact unread-refinement bundle -/

namespace WordRecordMachine

/-- A morphism of deterministic record machines commutes with every
finite word. -/
theorem run_map {A R' R D V : Type*}
    (M' : WordRecordMachine A R' D V)
    (M : WordRecordMachine A R D V) (π : R' → R)
    (hstep : ∀ a r, π (M'.step a r) = M.step a (π r)) :
    ∀ w r, π (M'.run w r) = M.run w (π r) := by
  intro w
  induction w with
  | nil => intro r; rfl
  | cons a w ih =>
      intro r
      simp only [run_cons]
      rw [ih, hstep]

/-- Intertwining updates and Reads makes the complete fine future
signature exactly the pullback of the coarse signature. -/
theorem futureSig_map {A R' R D V : Type*}
    (M' : WordRecordMachine A R' D V)
    (M : WordRecordMachine A R D V) (π : R' → R)
    (hstep : ∀ a r, π (M'.step a r) = M.step a (π r))
    (hread : ∀ d r, M'.read d r = M.read d (π r)) (r : R') :
    M'.futureSig r = M.futureSig (π r) := by
  funext wd
  rcases wd with ⟨w, d⟩
  simp only [futureSig]
  rw [hread, run_map M' M π hstep]

/-- `thm:record-refinement-bundle` with the manuscript's actual
machine hypotheses and every algebraic/fibre clause. -/
theorem record_refinement_bundle_exact {A R' R D V : Type*}
    (M' : WordRecordMachine A R' D V)
    (M : WordRecordMachine A R D V) (π : R' → R)
    (hπ : Function.Surjective π)
    (hstep : ∀ a r, π (M'.step a r) = M.step a (π r))
    (hread : ∀ d r, M'.read d r = M.read d (π r)) :
    Nonempty (MinRec M'.futureSig ≃ MinRec M.futureSig)
    ∧ Nonempty ((Σ ρ : MinRec M.futureSig,
        {r : R // Quotient.mk (minRecSetoid M.futureSig) r = ρ}) ≃ R)
    ∧ (∀ f : R → ℂ,
        (∃ g : MinRec M.futureSig → ℂ,
          ∀ r, g (Quotient.mk (minRecSetoid M.futureSig) r) = f r)
        ↔ (∀ r r', M.futureSig r = M.futureSig r' → f r = f r'))
    ∧ (∀ (E : Type) [Finite E] [Finite R],
        ((∀ ρ : MinRec M.futureSig, Nonempty
          ({r : R // Quotient.mk (minRecSetoid M.futureSig) r = ρ} ≃ E))
        ↔ (∀ ρ : MinRec M.futureSig, Nat.card
            {r : R // Quotient.mk (minRecSetoid M.futureSig) r = ρ}
            = Nat.card E))) := by
  have hsig : M'.futureSig = M.futureSig ∘ π := by
    funext r
    exact futureSig_map M' M π hstep hread r
  rw [hsig]
  exact record_refinement_bundle π hπ M.futureSig

end WordRecordMachine

/-! ## Exact typed Hankel realization -/

/-- The response space is literally the span of the Hankel columns. -/
def HankelResponseSpace {P F : Type*} (tbl : F → P → ℂ) :
    Submodule ℂ (F → ℂ) :=
  Submodule.span ℂ (Set.range fun p : P => fun f : F => tbl f p)

/-- A past regarded as its reachable Hankel column. -/
def hankelColumn {P F : Type*} (tbl : F → P → ℂ) (p : P) :
    HankelResponseSpace tbl :=
  ⟨fun f => tbl f p, Submodule.subset_span (Set.mem_range_self p)⟩

@[simp] theorem hankelColumn_apply {P F : Type*} (tbl : F → P → ℂ)
    (p : P) (f : F) : (hankelColumn tbl p).1 f = tbl f p := rfl

/-- The canonical transition between response spaces, obtained by
precomposition of futures. -/
noncomputable def typedHankelTransition {P F P' F' : Type*}
    (tbl : F → P → ℂ) (tbl' : F' → P' → ℂ)
    (ca : P → P') (fa : F' → F)
    (hcompat : ∀ f' q, tbl' f' (ca q) = tbl (fa f') q) :
    HankelResponseSpace tbl →ₗ[ℂ] HankelResponseSpace tbl' where
  toFun m := ⟨fun f' => m.1 (fa f'), by
    have map_mem : ∀ g : F → ℂ, g ∈ HankelResponseSpace tbl →
        (fun f' => g (fa f')) ∈ HankelResponseSpace tbl' := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨q, rfl⟩ := hg
          have heq : (fun f' => tbl (fa f') q) =
              (fun f' => tbl' f' (ca q)) := by
            funext f'
            exact (hcompat f' q).symm
          rw [heq]
          exact Submodule.subset_span (Set.mem_range_self (ca q))
      | zero =>
          have hz := Submodule.zero_mem (HankelResponseSpace tbl')
          convert hz using 1
          funext f'
          simp
      | add x y _ _ hx hy =>
          have hxy := Submodule.add_mem (HankelResponseSpace tbl') hx hy
          convert hxy using 1
          funext f'
          rfl
      | smul c x _ hx =>
          have hcx := Submodule.smul_mem (HankelResponseSpace tbl') c hx
          convert hcx using 1
          funext f'
          rfl
    exact map_mem m.1 m.2⟩
  map_add' x y := by ext f'; rfl
  map_smul' c x := by ext f'; rfl

/-- `thm:typed-hankel-realization`, including both boxed evaluation
identities, uniqueness, reachability, and future separation. -/
theorem typed_hankel_realization_exact {P F P' F' : Type*}
    (tbl : F → P → ℂ) (tbl' : F' → P' → ℂ)
    (ca : P → P') (fa : F' → F)
    (hcompat : ∀ (f' : F') (q : P),
      tbl' f' (ca q) = tbl (fa f') q) :
    ∃ A : HankelResponseSpace tbl →ₗ[ℂ] HankelResponseSpace tbl',
      (∀ q, A (hankelColumn tbl q) = hankelColumn tbl' (ca q))
      ∧ (∀ m f', (A m).1 f' = m.1 (fa f'))
      ∧ (∀ A' : HankelResponseSpace tbl →ₗ[ℂ] HankelResponseSpace tbl',
          (∀ q, A' (hankelColumn tbl q) = hankelColumn tbl' (ca q)) →
          A' = A)
      ∧ Submodule.span ℂ (Set.range (hankelColumn tbl)) = ⊤
      ∧ (∀ m : HankelResponseSpace tbl,
          (∀ f, m.1 f = 0) → m = 0) := by
  let A := typedHankelTransition tbl tbl' ca fa hcompat
  refine ⟨A, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    ext f'
    exact (hcompat f' q).symm
  · intro m f'
    rfl
  · intro A' hA'
    apply LinearMap.ext
    intro m
    have agree : ∀ (g : F → ℂ) (hg : g ∈ HankelResponseSpace tbl),
        A' ⟨g, hg⟩ = A ⟨g, hg⟩ := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨q, rfl⟩ := hg
          change A' (hankelColumn tbl q) = A (hankelColumn tbl q)
          rw [hA' q]
          ext f'
          exact hcompat f' q
      | zero =>
          have hzero : (⟨(0 : F → ℂ), Submodule.zero_mem _⟩ :
              HankelResponseSpace tbl) = 0 := by
            apply Subtype.ext
            rfl
          rw [hzero, map_zero, map_zero]
      | add x y hxmem hymem hx hy =>
          have hxy : (⟨x + y, Submodule.add_mem _ hxmem hymem⟩ :
              HankelResponseSpace tbl) =
              (⟨x, hxmem⟩ : HankelResponseSpace tbl) + ⟨y, hymem⟩ := by
            apply Subtype.ext
            rfl
          rw [hxy, map_add, map_add, hx, hy]
      | smul c x hxmem hx =>
          have hcx : (⟨c • x, Submodule.smul_mem _ c hxmem⟩ :
              HankelResponseSpace tbl) =
              c • (⟨x, hxmem⟩ : HankelResponseSpace tbl) := by
            apply Subtype.ext
            rfl
          rw [hcx, map_smul, map_smul, hx]
    exact agree m.1 m.2
  · apply le_antisymm le_top
    intro m _
    have reachable : ∀ (g : F → ℂ) (hg : g ∈ HankelResponseSpace tbl),
        (⟨g, hg⟩ : HankelResponseSpace tbl) ∈
          Submodule.span ℂ (Set.range (hankelColumn tbl)) := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨q, rfl⟩ := hg
          exact Submodule.subset_span (Set.mem_range_self q)
      | zero => exact Submodule.zero_mem _
      | add x y hxmem hymem hx hy =>
          have hxy : (⟨x + y, Submodule.add_mem _ hxmem hymem⟩ :
              HankelResponseSpace tbl) =
              (⟨x, hxmem⟩ : HankelResponseSpace tbl) + ⟨y, hymem⟩ := by
            apply Subtype.ext
            rfl
          rw [hxy]
          exact Submodule.add_mem _ hx hy
      | smul c x hxmem hx =>
          have hcx : (⟨c • x, Submodule.smul_mem _ c hxmem⟩ :
              HankelResponseSpace tbl) =
              c • (⟨x, hxmem⟩ : HankelResponseSpace tbl) := by
            apply Subtype.ext
            rfl
          rw [hcx]
          exact Submodule.smul_mem _ c hx
    exact reachable m.1 m.2
  · intro m hm
    apply Subtype.ext
    funext f
    exact hm f

end NCG
