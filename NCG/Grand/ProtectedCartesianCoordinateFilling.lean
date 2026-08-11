/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.CochainExactness

/-!
# Protected Cartesian coordinate filling

This module supplies the Cartesian branch of protected coordinate integration:
an anchored injective coordinate writer with every deterministic nonterminal
unit successor fills the whole three-dimensional box.  Coordinate actions in
distinct directions commute by injectivity, and point writers span the full
finite endpoint algebra.
-/

namespace NCG
namespace ProtectedCartesianCoordinateFilling

/-- Integral one-chains on a finite oriented edge set. -/
abbrev IntegralChain (E : Type*) := E → ℤ

/-- The period of a protected three-component increment on an integral chain. -/
def chainPeriod {E : Type*} [Fintype E]
    (theta : E → Fin 3 → ℤ) : IntegralChain E →ₗ[ℤ] (Fin 3 → ℤ) where
  toFun c := ∑ e, c e • theta e
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    funext a
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.sum_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring

/-- The fundamental cycle obtained from anchored path chains and one oriented
edge. -/
def fundamentalCycle {V E : Type*} [DecidableEq E]
    (source target : E → V) (path : V → IntegralChain E) (e : E) :
    IntegralChain E :=
  path (source e) + Pi.single e 1 - path (target e)

/-- Face closure plus vanishing on one integral homology basis integrates an
antisymmetric edge increment.  The decomposition premise is precisely the
cellular statement that the face boundaries together with the chosen `H₁`
basis span every fundamental cycle over `ℤ`. -/
theorem faceAndHomologyPeriods_integrate {V E F B : Type*}
    [Fintype E] [DecidableEq E] [Fintype F] [Fintype B]
    (source target : E → V) (theta : E → Fin 3 → ℤ)
    (path : V → IntegralChain E)
    (face : F → IntegralChain E) (homology : B → IntegralChain E)
    (faceCoeff : E → F → ℤ) (homologyCoeff : E → B → ℤ)
    (hdecomp : ∀ e,
      fundamentalCycle source target path e =
        (∑ f, faceCoeff e f • face f) +
          ∑ b, homologyCoeff e b • homology b)
    (hface : ∀ f, chainPeriod theta (face f) = 0)
    (hhomology : ∀ b, chainPeriod theta (homology b) = 0) :
    ∃ X : V → Fin 3 → ℤ,
      ∀ e, theta e = X (target e) - X (source e) := by
  let P := chainPeriod theta
  have hfund : ∀ e, P (fundamentalCycle source target path e) = 0 := by
    intro e
    rw [hdecomp]
    simp only [map_add, map_sum, map_smul]
    have hfzero : ∑ f, faceCoeff e f • P (face f) = 0 := by
      apply Finset.sum_eq_zero
      intro f _
      rw [hface f, smul_zero]
    have hbzero : ∑ b, homologyCoeff e b • P (homology b) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      rw [hhomology b, smul_zero]
    rw [hfzero, hbzero, add_zero]
  refine ⟨fun v => P (path v), ?_⟩
  intro e
  have h := hfund e
  simp only [fundamentalCycle, map_sub, map_add, P, chainPeriod] at h
  have hsingle : chainPeriod theta (Pi.single e 1) = theta e := by
    ext a
    simp only [chainPeriod, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hbe
      simp [Pi.single, hbe]
    · simp
  change chainPeriod theta (path (source e)) +
      chainPeriod theta (Pi.single e 1) -
        chainPeriod theta (path (target e)) = 0 at h
  rw [hsingle] at h
  apply funext
  intro a
  have ha := congrFun h a
  simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at ha ⊢
  linarith

/-- Unit-successor closure from one anchored origin fills the entire finite
three-dimensional Cartesian box. -/
theorem cartesianBox_filled {V : Type*} {n₁ n₂ n₃ : ℕ}
    (X : V → Fin n₁ × Fin n₂ × Fin n₃) (o : V)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (horigin : X o = (⟨0, hn₁⟩, ⟨0, hn₂⟩, ⟨0, hn₃⟩))
    (hsucc₁ : ∀ (v : V) (h : (X v).1.val + 1 < n₁),
      ∃ w : V, X w = (⟨(X v).1.val + 1, h⟩, (X v).2.1, (X v).2.2))
    (hsucc₂ : ∀ (v : V) (h : (X v).2.1.val + 1 < n₂),
      ∃ w : V, X w = ((X v).1, ⟨(X v).2.1.val + 1, h⟩, (X v).2.2))
    (hsucc₃ : ∀ (v : V) (h : (X v).2.2.val + 1 < n₃),
      ∃ w : V, X w = ((X v).1, (X v).2.1, ⟨(X v).2.2.val + 1, h⟩)) :
    Function.Surjective X := by
  have reach₁ : ∀ a : ℕ, (ha : a < n₁) →
      ∃ v : V, X v = (⟨a, ha⟩, ⟨0, hn₂⟩, ⟨0, hn₃⟩) := by
    intro a
    induction a with
    | zero =>
        intro ha
        exact ⟨o, horigin⟩
    | succ a ih =>
        intro ha
        obtain ⟨v, hv⟩ := ih (Nat.lt_of_succ_lt ha)
        have hstep : (X v).1.val + 1 < n₁ := by simpa [hv] using ha
        obtain ⟨w, hw⟩ := hsucc₁ v hstep
        refine ⟨w, ?_⟩
        rw [hw]
        apply Prod.ext
        · apply Fin.ext
          simp [hv]
        · apply Prod.ext
          · apply Fin.ext
            simp [hv]
          · apply Fin.ext
            simp [hv]
  have reach₂ : ∀ (a b : ℕ) (ha : a < n₁) (hb : b < n₂),
      ∃ v : V, X v = (⟨a, ha⟩, ⟨b, hb⟩, ⟨0, hn₃⟩) := by
    intro a b ha
    induction b with
    | zero =>
        intro hb
        exact reach₁ a ha
    | succ b ih =>
        intro hb
        obtain ⟨v, hv⟩ := ih (Nat.lt_of_succ_lt hb)
        have hstep : (X v).2.1.val + 1 < n₂ := by simpa [hv] using hb
        obtain ⟨w, hw⟩ := hsucc₂ v hstep
        refine ⟨w, ?_⟩
        rw [hw]
        apply Prod.ext
        · apply Fin.ext
          simp [hv]
        · apply Prod.ext
          · apply Fin.ext
            simp [hv]
          · apply Fin.ext
            simp [hv]
  have reach₃ : ∀ (a b c : ℕ) (ha : a < n₁) (hb : b < n₂) (hc : c < n₃),
      ∃ v : V, X v = (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩) := by
    intro a b c ha hb
    induction c with
    | zero =>
        intro hc
        exact reach₂ a b ha hb
    | succ c ih =>
        intro hc
        obtain ⟨v, hv⟩ := ih (Nat.lt_of_succ_lt hc)
        have hstep : (X v).2.2.val + 1 < n₃ := by simpa [hv] using hc
        obtain ⟨w, hw⟩ := hsucc₃ v hstep
        refine ⟨w, ?_⟩
        rw [hw]
        apply Prod.ext
        · apply Fin.ext
          simp [hv]
        · apply Prod.ext
          · apply Fin.ext
            simp [hv]
          · apply Fin.ext
            simp [hv]
  intro q
  obtain ⟨v, hv⟩ := reach₃ q.1.val q.2.1.val q.2.2.val
    q.1.isLt q.2.1.isLt q.2.2.isLt
  refine ⟨v, ?_⟩
  simpa using hv

/-- With an injective writer, the filled endpoint carrier is canonically the
Cartesian box. -/
noncomputable def cartesianEndpointEquiv {V : Type*} {n₁ n₂ n₃ : ℕ}
    (X : V → Fin n₁ × Fin n₂ × Fin n₃) (hXinj : Function.Injective X)
    (hXsurj : Function.Surjective X) :
    V ≃ Fin n₁ × Fin n₂ × Fin n₃ :=
  Equiv.ofBijective X ⟨hXinj, hXsurj⟩

/-- Deterministic unit writers in distinct coordinate directions commute on
every common domain where both coordinate-action formulas hold. -/
theorem successorWriters_commute {V : Type*}
    (X : V → Fin 3 → ℤ) (hX : Function.Injective X)
    (S : Fin 3 → V → V)
    (hS : ∀ a v b, X (S a v) b = X v b + if b = a then 1 else 0) :
    ∀ a b v, S a (S b v) = S b (S a v) := by
  intro a b v
  apply hX
  funext c
  rw [hS, hS, hS, hS]
  by_cases hca : c = a <;> by_cases hcb : c = b <;> simp [hca, hcb]
  all_goals ring

/-- Point writers linearly generate every function on a finite endpoint
carrier, hence the complete protected endpoint algebra. -/
theorem pointWriters_generate_fullEndpointAlgebra {V R : Type*}
    [Fintype V] [DecidableEq V] [Semiring R] (f : V → R) :
    f = ∑ v : V, f v • (fun w : V => if w = v then 1 else 0) := by
  funext w
  simp

end ProtectedCartesianCoordinateFilling
end NCG
