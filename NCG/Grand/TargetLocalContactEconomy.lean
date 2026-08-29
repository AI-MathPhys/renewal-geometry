/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BrandNewEasy00

/-!
# Target-local contact economy

Exact collar-relative specialization of the finite counterterm target theorem,
closing `thm:GTLOC-target-local-contact`.
-/

namespace NCG
namespace TargetLocalContactEconomy

noncomputable section

variable {B Y : Type*} [AddCommGroup B] [Module ℂ B]
  [AddCommGroup Y] [Module ℂ Y]

/-- The common finite local-counterterm range. -/
abbrev CountertermRange {m : ℕ} (L : Fin m → B)
    (phi : Fin m → (B →ₗ[ℂ] ℂ)) :=
  LinearMap.range (ctProjector L phi)

/-- A bank of `k` scalar Reads identifies a target on the local counterterm
carrier exactly when its joint kernel is contained in the restricted target
kernel. -/
def ReadIdentifies {m k : ℕ} (L : Fin m → B)
    (phi : Fin m → (B →ₗ[ℂ] ℂ)) (T : B →ₗ[ℂ] Y)
    (read : Fin k → (CountertermRange L phi →ₗ[ℂ] ℂ)) : Prop :=
  LinearMap.ker (LinearMap.pi read) ≤
    LinearMap.ker (T.comp (CountertermRange L phi).subtype)

theorem readIdentifies_iff_kernel_condition {m k : ℕ} (L : Fin m → B)
    (phi : Fin m → (B →ₗ[ℂ] ℂ)) (T : B →ₗ[ℂ] Y)
    (read : Fin k → (CountertermRange L phi →ₗ[ℂ] ℂ)) :
    ReadIdentifies L phi T read ↔
      ∀ x : CountertermRange L phi,
        (∀ i, read i x = 0) →
          T.comp (CountertermRange L phi).subtype x = 0 := by
  constructor
  · intro h x hx
    apply LinearMap.mem_ker.mp (h ?_)
    rw [LinearMap.mem_ker]
    ext i
    simpa using hx i
  · intro h x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply h x
    intro i
    have hi := congrFun hx i
    simpa using hi

/-- **`thm:GTLOC-target-local-contact`**.  If the target factors through the
physical collar compression, then:

* representative independence is exactly annihilation of the local
  counterterm range;
* an arbitrary scalar Read bank identifies the target exactly by the displayed
  joint-kernel inclusion;
* the least number of Reads is the rank/finrank of the target restricted to
  that range;
* vectors killed by the collar compression are not charged to the target. -/
theorem target_local_contact_economy {m : ℕ}
    (PiR : B →ₗ[ℂ] B) (L : Fin m → B)
    (phi : Fin m → (B →ₗ[ℂ] ℂ)) (T : B →ₗ[ℂ] Y)
    (hfactor : T.comp PiR = T) :
    ((∀ C1 C2 : B,
        C1 - C2 ∈ CountertermRange L phi → T C1 = T C2) ↔
      ∀ u ∈ CountertermRange L phi, T u = 0) ∧
    (∀ (k : ℕ) (read : Fin k →
        (CountertermRange L phi →ₗ[ℂ] ℂ)),
      ReadIdentifies L phi T read ↔
        ∀ x : CountertermRange L phi,
          (∀ i, read i x = 0) →
            T.comp (CountertermRange L phi).subtype x = 0) ∧
    IsLeast {k : ℕ |
        ∃ read : Fin k → (CountertermRange L phi →ₗ[ℂ] ℂ),
          ReadIdentifies L phi T read}
      (Module.finrank ℂ ↥(LinearMap.range
        (T.comp (CountertermRange L phi).subtype))) ∧
    (∀ x : B, PiR x = 0 → T x = 0) := by
  refine ⟨ctTarget_independent_iff L phi T,
    fun k read => readIdentifies_iff_kernel_condition L phi T read,
    ?_, ?_⟩
  · have hleast := ctTarget_read_floor L phi T
    have hset : {k : ℕ |
          ∃ read : Fin k → (CountertermRange L phi →ₗ[ℂ] ℂ),
            ReadIdentifies L phi T read} =
        {k : ℕ |
          ∃ read : Fin k → (CountertermRange L phi →ₗ[ℂ] ℂ),
            ∀ x : CountertermRange L phi,
              (∀ i, read i x = 0) →
                T.comp (CountertermRange L phi).subtype x = 0} := by
      ext k
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨read, hread⟩
        exact ⟨read,
          (readIdentifies_iff_kernel_condition L phi T read).1 hread⟩
      · rintro ⟨read, hread⟩
        exact ⟨read,
          (readIdentifies_iff_kernel_condition L phi T read).2 hread⟩
    rw [hset]
    exact hleast
  · intro x hx
    have h := LinearMap.congr_fun hfactor x
    simp only [LinearMap.comp_apply, hx, map_zero] at h
    exact h.symm

end

end TargetLocalContactEconomy
end NCG
