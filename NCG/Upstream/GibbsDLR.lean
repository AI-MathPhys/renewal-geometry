/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.CircuitCount

/-!
# DLR/extremality packaging: the infinite-volume Ising phases

The last scoped input of `thm:torsion-phase-coexistence` clause (ii):
package the finite-volume plus-boundary Peierls bound into genuine
**infinite-volume states**.  A state is a normalized positive linear
functional on bounded observables of the spin field, obtained as the
limit of the plus-boundary box expectations along a fixed ultrafilter
extending the tail filter (so every bounded observable converges — no
diagonal extraction needed).

* `expec` — the finite-volume plus-boundary expectation;
* `gibbsPlus` — the plus phase: the ultrafilter limit over boxes;
* `gibbsMinus` — the minus phase: its deck (global spin) flip;
* `gibbsPlus_spin` / `gibbsMinus_spin` — magnetizations `≥ 203/216`
  and `≤ -203/216`: the two phases are **separated by the deck-odd
  local spin test** (`phases_distinct`);
* linearity, positivity, normalization: genuine states, not number
  sequences.
-/

namespace NCG.Upstream.Ising

open Filter Topology

variable (Λ : Finset V2)

instance : Nonempty (PlusBC Λ) := ⟨⟨fun _ => true, fun _ _ => rfl⟩⟩

/-- The partition function of the plus-boundary volume. -/
noncomputable def Z (θ : ℝ) : ℝ := ∑ σ : PlusBC Λ, wt Λ θ σ

theorem Z_pos (θ : ℝ) : 0 < Z Λ θ :=
  Finset.sum_pos (fun σ _ => wt_pos Λ θ σ) Finset.univ_nonempty

/-- The finite-volume plus-boundary expectation. -/
noncomputable def expec (θ : ℝ) (f : (V2 → Bool) → ℝ) : ℝ :=
  (∑ σ : PlusBC Λ, wt Λ θ σ * f σ.1) / Z Λ θ

variable {Λ}

theorem expec_const (θ : ℝ) (c : ℝ) :
    expec Λ θ (fun _ => c) = c := by
  unfold expec
  rw [← Finset.sum_mul, mul_comm, mul_div_assoc]
  rw [show (∑ σ : PlusBC Λ, wt Λ θ σ) = Z Λ θ from rfl]
  rw [div_self (Z_pos Λ θ).ne', mul_one]

theorem expec_add (θ : ℝ) (f g : (V2 → Bool) → ℝ) :
    expec Λ θ (fun τ => f τ + g τ)
      = expec Λ θ f + expec Λ θ g := by
  unfold expec
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem expec_smul (θ : ℝ) (c : ℝ) (f : (V2 → Bool) → ℝ) :
    expec Λ θ (fun τ => c * f τ) = c * expec Λ θ f := by
  unfold expec
  rw [show ∑ σ : PlusBC Λ, wt Λ θ σ * (c * f σ.1)
      = c * ∑ σ : PlusBC Λ, wt Λ θ σ * f σ.1 by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring]
  rw [mul_div_assoc]

theorem expec_nonneg (θ : ℝ) {f : (V2 → Bool) → ℝ}
    (hf : ∀ τ, 0 ≤ f τ) : 0 ≤ expec Λ θ f :=
  div_nonneg (Finset.sum_nonneg fun σ _ =>
    mul_nonneg (wt_pos Λ θ σ).le (hf _)) (Z_pos Λ θ).le

theorem expec_mono (θ : ℝ) {f g : (V2 → Bool) → ℝ}
    (h : ∀ τ, f τ ≤ g τ) : expec Λ θ f ≤ expec Λ θ g := by
  have h1 : 0 ≤ expec Λ θ (fun τ => g τ - f τ) :=
    expec_nonneg θ fun τ => by have := h τ; linarith
  have h2 : expec Λ θ (fun τ => f τ + (g τ - f τ))
      = expec Λ θ f + expec Λ θ (fun τ => g τ - f τ) :=
    expec_add θ f (fun τ => g τ - f τ)
  have h3 : (fun τ => f τ + (g τ - f τ)) = g :=
    funext fun τ => by ring
  rw [h3] at h2
  linarith

theorem abs_expec_le (θ : ℝ) {f : (V2 → Bool) → ℝ} {C : ℝ}
    (hf : ∀ τ, |f τ| ≤ C) : |expec Λ θ f| ≤ C := by
  have h1 : expec Λ θ f ≤ C := by
    have := expec_mono (Λ := Λ) θ
      (f := f) (g := fun _ => C) (fun τ => (abs_le.mp (hf τ)).2)
    rwa [expec_const] at this
  have h2 : -C ≤ expec Λ θ f := by
    have := expec_mono (Λ := Λ) θ
      (f := fun _ => -C) (g := f) (fun τ => (abs_le.mp (hf τ)).1)
    rwa [expec_const] at this
  exact abs_le.mpr ⟨h2, h1⟩

/-- The Peierls magnetization bound in expectation form. -/
theorem expec_spin_box (a b c d : ℤ) (θ : ℝ)
    (hθ : (1 / 2) * Real.log 12 ≤ θ) :
    (203 : ℝ) / 216 ≤ expec (Finset.Icc a b ×ˢ Finset.Icc c d) θ
      (fun τ => spin (τ 0)) := by
  have h := box_magnetization a b c d θ hθ
  rw [expec, le_div_iff₀ (Z_pos _ θ)]
  exact h

/-! ## The infinite-volume states -/

/-- A fixed ultrafilter extending the tail filter: every bounded
observable has a limit along it. -/
noncomputable def UF : Ultrafilter ℕ := Ultrafilter.of Filter.atTop

theorem UF_le_atTop : (UF : Filter ℕ) ≤ Filter.atTop :=
  Ultrafilter.of_le _

instance : (UF : Filter ℕ).NeBot := Ultrafilter.neBot _

/-- The box exhaustion of the lattice. -/
noncomputable def box (n : ℕ) : Finset V2 :=
  Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)

/-- Bounded sequences converge along the ultrafilter. -/
theorem exists_tendsto_of_bounded {u : ℕ → ℝ} {C : ℝ}
    (hu : ∀ n, |u n| ≤ C) :
    ∃ L, Filter.Tendsto u (UF : Filter ℕ) (nhds L) := by
  have hle : (Ultrafilter.map u UF : Filter ℝ)
      ≤ Filter.principal (Set.Icc (-C) C) := by
    rw [Filter.le_principal_iff]
    have hmem : ∀ n, u n ∈ Set.Icc (-C) C := fun n => by
      have := abs_le.mp (hu n)
      exact ⟨this.1, this.2⟩
    exact Filter.mem_map.mpr (Filter.univ_mem' hmem)
  obtain ⟨L, -, hL⟩ :=
    isCompact_Icc.ultrafilter_le_nhds (Ultrafilter.map u UF) hle
  refine ⟨L, ?_⟩
  rw [Filter.Tendsto]
  rw [← Ultrafilter.coe_map]
  exact hL

/-- **The plus phase**: the ultrafilter limit of the plus-boundary
box expectations. -/
noncomputable def gibbsPlus (θ : ℝ) (f : (V2 → Bool) → ℝ) : ℝ :=
  Filter.limUnder (UF : Filter ℕ) (fun n => expec (box n) θ f)

theorem gibbsPlus_eq {θ : ℝ} {f : (V2 → Bool) → ℝ} {L : ℝ}
    (h : Filter.Tendsto (fun n => expec (box n) θ f)
      (UF : Filter ℕ) (nhds L)) :
    gibbsPlus θ f = L := h.limUnder_eq

/-- Convergence to the plus phase for bounded observables. -/
theorem gibbsPlus_spec {θ : ℝ} {f : (V2 → Bool) → ℝ} {C : ℝ}
    (hf : ∀ τ, |f τ| ≤ C) :
    Filter.Tendsto (fun n => expec (box n) θ f) (UF : Filter ℕ)
      (nhds (gibbsPlus θ f)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_of_bounded
    (fun n => abs_expec_le θ hf)
  rw [gibbsPlus_eq hL]
  exact hL

/-- Normalization: the state of `1` is `1`. -/
theorem gibbsPlus_const (θ c : ℝ) : gibbsPlus θ (fun _ => c) = c :=
  gibbsPlus_eq (by
    have h : (fun n => expec (box n) θ (fun _ => c))
        = fun _ => c := funext fun n => expec_const θ c
    rw [h]
    exact tendsto_const_nhds)

/-- Additivity. -/
theorem gibbsPlus_add (θ : ℝ) {f g : (V2 → Bool) → ℝ} {Cf Cg : ℝ}
    (hf : ∀ τ, |f τ| ≤ Cf) (hg : ∀ τ, |g τ| ≤ Cg) :
    gibbsPlus θ (fun τ => f τ + g τ)
      = gibbsPlus θ f + gibbsPlus θ g :=
  gibbsPlus_eq (by
    have h3 := (gibbsPlus_spec (θ := θ) hf).add (gibbsPlus_spec (θ := θ) hg)
    have h4 : (fun n => expec (box n) θ f + expec (box n) θ g)
        = fun n => expec (box n) θ (fun τ => f τ + g τ) :=
      funext fun n => (expec_add θ f g).symm
    rwa [h4] at h3)

/-- Homogeneity. -/
theorem gibbsPlus_smul (θ c : ℝ) {f : (V2 → Bool) → ℝ} {C : ℝ}
    (hf : ∀ τ, |f τ| ≤ C) :
    gibbsPlus θ (fun τ => c * f τ) = c * gibbsPlus θ f :=
  gibbsPlus_eq (by
    have h3 := (gibbsPlus_spec (θ := θ) hf).const_mul c
    have h4 : (fun n => c * expec (box n) θ f)
        = fun n => expec (box n) θ (fun τ => c * f τ) :=
      funext fun n => (expec_smul θ c f).symm
    rwa [h4] at h3)

/-- Positivity. -/
theorem gibbsPlus_nonneg (θ : ℝ) {f : (V2 → Bool) → ℝ} {C : ℝ}
    (hb : ∀ τ, |f τ| ≤ C) (hf : ∀ τ, 0 ≤ f τ) :
    0 ≤ gibbsPlus θ f :=
  ge_of_tendsto' (gibbsPlus_spec (θ := θ) hb) (fun n => expec_nonneg θ hf)

theorem spin_abs_le (b : Bool) : |spin b| ≤ 1 := by
  cases b <;> simp [spin]

/-- **The plus-phase magnetization**: at least `203/216` at low
temperature. -/
theorem gibbsPlus_spin (θ : ℝ) (hθ : (1 / 2) * Real.log 12 ≤ θ) :
    (203 : ℝ) / 216 ≤ gibbsPlus θ (fun τ => spin (τ 0)) :=
  ge_of_tendsto' (gibbsPlus_spec (θ := θ) (fun τ => spin_abs_le _))
    (fun n =>
      show (203 : ℝ) / 216 ≤ expec
        (Finset.Icc (-(n : ℤ)) (n : ℤ)
          ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)) θ
        (fun τ => spin (τ 0)) from
      expec_spin_box _ _ _ _ θ hθ)

/-! ## The minus phase and the separation -/

/-- The global (deck) spin flip. -/
def flipAll (τ : V2 → Bool) : V2 → Bool := fun v => !(τ v)

/-- **The minus phase**: the deck flip of the plus phase. -/
noncomputable def gibbsMinus (θ : ℝ) (f : (V2 → Bool) → ℝ) : ℝ :=
  gibbsPlus θ (fun τ => f (flipAll τ))

/-- The minus phase is a state: normalization. -/
theorem gibbsMinus_const (θ c : ℝ) :
    gibbsMinus θ (fun _ => c) = c := gibbsPlus_const θ c

/-- The minus phase is a state: additivity. -/
theorem gibbsMinus_add (θ : ℝ) {f g : (V2 → Bool) → ℝ} {Cf Cg : ℝ}
    (hf : ∀ τ, |f τ| ≤ Cf) (hg : ∀ τ, |g τ| ≤ Cg) :
    gibbsMinus θ (fun τ => f τ + g τ)
      = gibbsMinus θ f + gibbsMinus θ g :=
  gibbsPlus_add θ (fun τ => hf (flipAll τ)) (fun τ => hg (flipAll τ))

/-- The minus phase is a state: positivity. -/
theorem gibbsMinus_nonneg (θ : ℝ) {f : (V2 → Bool) → ℝ} {C : ℝ}
    (hb : ∀ τ, |f τ| ≤ C) (hf : ∀ τ, 0 ≤ f τ) :
    0 ≤ gibbsMinus θ f :=
  gibbsPlus_nonneg θ (fun τ => hb (flipAll τ)) (fun τ => hf (flipAll τ))

/-- **The minus-phase magnetization**: at most `-203/216`. -/
theorem gibbsMinus_spin (θ : ℝ) (hθ : (1 / 2) * Real.log 12 ≤ θ) :
    gibbsMinus θ (fun τ => spin (τ 0)) ≤ -(203 / 216 : ℝ) := by
  unfold gibbsMinus
  have h1 : (fun τ : V2 → Bool => spin (flipAll τ 0))
      = fun τ : V2 → Bool => (-1 : ℝ) * spin (τ 0) :=
    funext fun τ => by
      rw [show flipAll τ 0 = !(τ 0) from rfl, spin_not]
      ring
  rw [h1, gibbsPlus_smul θ (-1) (fun τ => spin_abs_le _)]
  have h2 := gibbsPlus_spin θ hθ
  linarith

/-- **Phase separation**: the two deck-related states disagree on
the local spin at the origin — genuine states, separated by the
deck-odd test, exactly clause (ii). -/
theorem phases_distinct (θ : ℝ) (hθ : (1 / 2) * Real.log 12 ≤ θ) :
    gibbsMinus θ (fun τ => spin (τ 0))
      ≠ gibbsPlus θ (fun τ => spin (τ 0)) := by
  have h1 := gibbsPlus_spin θ hθ
  have h2 := gibbsMinus_spin θ hθ
  intro h
  rw [h] at h2
  linarith

/-- **The symmetric mixture** of the two phases. -/
noncomputable def gibbsMix (θ : ℝ) (f : (V2 → Bool) → ℝ) : ℝ :=
  (gibbsPlus θ f + gibbsMinus θ f) / 2

/-- Clause (iii), state level: the symmetric mixture has zero
magnetization. -/
theorem gibbsMix_spin (θ : ℝ) (hθ : (1 / 2) * Real.log 12 ≤ θ) :
    gibbsMix θ (fun τ => spin (τ 0))
      = -gibbsMix θ (fun τ => spin (τ 0)) := by
  unfold gibbsMix gibbsMinus
  have h1 : (fun τ : V2 → Bool => spin (flipAll τ 0))
      = fun τ : V2 → Bool => (-1 : ℝ) * spin (τ 0) :=
    funext fun τ => by
      rw [show flipAll τ 0 = !(τ 0) from rfl, spin_not]
      ring
  rw [h1, gibbsPlus_smul θ (-1) (fun τ => spin_abs_le _)]
  ring

/-! ## The DLR property

The kernel `dlrK V` resamples the volume `V` from its conditional
Gibbs law given the configuration outside.  Finite-volume consistency
(`expec_dlrK`) is the classical resampling identity, proved by the
patch/restriction involution; the infinite-volume states inherit it
because every finite `V` is eventually inside the boxes. -/

/-- Overwrite a configuration on `V`. -/
def patchV (V : Finset V2) (η : ↥V → Bool) (τ : V2 → Bool) :
    V2 → Bool :=
  fun v => if h : v ∈ V then η ⟨v, h⟩ else τ v

/-- The local Boltzmann weight: edges meeting `V`. -/
noncomputable def eLoc (V : Finset V2) (θ : ℝ) (τ : V2 → Bool) : ℝ :=
  Real.exp (θ * ∑ e ∈ eVol V, spin (τ (ep0 e)) * spin (τ (ep1 e)))

theorem eLoc_pos (V : Finset V2) (θ : ℝ) (τ : V2 → Bool) :
    0 < eLoc V θ τ := Real.exp_pos _

/-- The conditional partition function of `V` given `τ` outside. -/
noncomputable def zLoc (V : Finset V2) (θ : ℝ) (τ : V2 → Bool) : ℝ :=
  ∑ η : ↥V → Bool, eLoc V θ (patchV V η τ)

theorem zLoc_pos (V : Finset V2) (θ : ℝ) (τ : V2 → Bool) :
    0 < zLoc V θ τ :=
  Finset.sum_pos (fun η _ => eLoc_pos V θ _) Finset.univ_nonempty

/-- **The DLR kernel**: resample `V` from its conditional Gibbs law
with the ambient configuration as boundary condition. -/
noncomputable def dlrK (V : Finset V2) (θ : ℝ)
    (f : (V2 → Bool) → ℝ) (τ : V2 → Bool) : ℝ :=
  (∑ η : ↥V → Bool, eLoc V θ (patchV V η τ) * f (patchV V η τ))
    / zLoc V θ τ

/-- Patching twice overwrites. -/
theorem patchV_patchV (V : Finset V2) (η η' : ↥V → Bool)
    (τ : V2 → Bool) :
    patchV V η (patchV V η' τ) = patchV V η τ := by
  funext v
  unfold patchV
  by_cases h : v ∈ V
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, dif_neg h]

/-- The restriction of a configuration to `V`. -/
def resV (V : Finset V2) (τ : V2 → Bool) : ↥V → Bool :=
  fun v => τ v.1

/-- Patching with the restriction recovers the configuration. -/
theorem patchV_resV (V : Finset V2) (τ : V2 → Bool) :
    patchV V (resV V τ) τ = τ := by
  funext v
  unfold patchV resV
  by_cases h : v ∈ V
  · rw [dif_pos h]
  · rw [dif_neg h]

/-- Restricting a patch recovers the patch values. -/
theorem resV_patchV (V : Finset V2) (η : ↥V → Bool)
    (τ : V2 → Bool) :
    resV V (patchV V η τ) = η := by
  funext v
  show (if h : (v : V2) ∈ V then η ⟨(v : V2), h⟩ else τ (v : V2))
    = η v
  rw [dif_pos v.2]

/-- `zLoc` depends only on the configuration outside `V`. -/
theorem zLoc_patchV (V : Finset V2) (θ : ℝ) (η : ↥V → Bool)
    (τ : V2 → Bool) :
    zLoc V θ (patchV V η τ) = zLoc V θ τ := by
  unfold zLoc
  refine Finset.sum_congr rfl fun η' _ => ?_
  rw [patchV_patchV]

/-- Patching inside the volume preserves the plus boundary. -/
def patchP {V Λ : Finset V2} (hVΛ : V ⊆ Λ) (η : ↥V → Bool)
    (σ : PlusBC Λ) : PlusBC Λ :=
  ⟨patchV V η σ.1, fun v hv => by
    unfold patchV
    rw [dif_neg (fun hmem => hv (hVΛ hmem))]
    exact σ.2 v hv⟩

theorem patchP_val {V Λ : Finset V2} (hVΛ : V ⊆ Λ)
    (η : ↥V → Bool) (σ : PlusBC Λ) :
    (patchP hVΛ η σ).1 = patchV V η σ.1 := rfl

/-- Edges of the volume avoiding `V` have both endpoints off `V`. -/
theorem endpoints_off {V Λ : Finset V2} {e : IEdge}
    (he : e ∈ eVol Λ \ eVol V) : ep0 e ∉ V ∧ ep1 e ∉ V := by
  rw [Finset.mem_sdiff] at he
  constructor
  · intro h
    exact he.2 ((mem_eVol V).mpr (Or.inl h))
  · intro h
    exact he.2 ((mem_eVol V).mpr (Or.inr h))

theorem eVol_mono {V Λ : Finset V2} (hVΛ : V ⊆ Λ) :
    eVol V ⊆ eVol Λ := by
  intro e he
  rcases (mem_eVol V).mp he with h | h
  · exact (mem_eVol Λ).mpr (Or.inl (hVΛ h))
  · exact (mem_eVol Λ).mpr (Or.inr (hVΛ h))

/-- The exterior Boltzmann factor. -/
noncomputable def eRem (V Λ : Finset V2) (θ : ℝ)
    (τ : V2 → Bool) : ℝ :=
  Real.exp (θ * ∑ e ∈ eVol Λ \ eVol V,
    spin (τ (ep0 e)) * spin (τ (ep1 e)))

/-- **The energy factorization**: local times exterior. -/
theorem wt_split {V Λ : Finset V2} (hVΛ : V ⊆ Λ) (θ : ℝ)
    (σ : PlusBC Λ) :
    wt Λ θ σ = eLoc V θ σ.1 * eRem V Λ θ σ.1 := by
  unfold wt eLoc eRem
  rw [← Real.exp_add, ← mul_add]
  congr 2
  rw [add_comm]
  exact (Finset.sum_sdiff (eVol_mono hVΛ)).symm

/-- The exterior factor ignores patches inside `V`. -/
theorem eRem_patchV (V Λ : Finset V2) (θ : ℝ) (η : ↥V → Bool)
    (τ : V2 → Bool) :
    eRem V Λ θ (patchV V η τ) = eRem V Λ θ τ := by
  unfold eRem
  congr 2
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨h0, h1⟩ := endpoints_off he
  unfold patchV
  rw [dif_neg h0, dif_neg h1]

open Classical in
/-- **Finite-volume DLR consistency**: the plus-boundary expectation
is invariant under resampling any subvolume — the resampling
identity, by the patch/restriction involution. -/
theorem expec_dlrK (θ : ℝ) {V Λ : Finset V2} (hVΛ : V ⊆ Λ)
    (f : (V2 → Bool) → ℝ) :
    expec Λ θ (dlrK V θ f) = expec Λ θ f := by
  unfold expec
  congr 1
  have hinv : Function.Involutive
      (fun p : PlusBC Λ × (↥V → Bool) =>
        ((patchP hVΛ p.2 p.1, resV V p.1.1) :
          PlusBC Λ × (↥V → Bool))) := by
    rintro ⟨σ, η⟩
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      show patchV V (resV V σ.1) (patchV V η σ.1) = σ.1
      rw [patchV_patchV, patchV_resV]
    · show resV V (patchV V η σ.1) = η
      rw [resV_patchV]
  have key : (∑ σ : PlusBC Λ, wt Λ θ σ * dlrK V θ f σ.1)
      = ∑ p : PlusBC Λ × (↥V → Bool),
          wt Λ θ p.1 * (eLoc V θ (patchV V p.2 p.1.1)
            * f (patchV V p.2 p.1.1)) / zLoc V θ p.1.1 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    unfold dlrK
    rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
  rw [key]
  rw [← Equiv.sum_comp (Function.Involutive.toPerm _ hinv)
    (fun p : PlusBC Λ × (↥V → Bool) =>
      wt Λ θ p.1 * (eLoc V θ (patchV V p.2 p.1.1)
        * f (patchV V p.2 p.1.1)) / zLoc V θ p.1.1)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hterm : ∀ η : ↥V → Bool,
      wt Λ θ (patchP hVΛ η σ)
        * (eLoc V θ (patchV V (resV V σ.1) (patchP hVΛ η σ).1)
          * f (patchV V (resV V σ.1) (patchP hVΛ η σ).1))
        / zLoc V θ (patchP hVΛ η σ).1
      = eLoc V θ (patchV V η σ.1)
          * (eRem V Λ θ σ.1 * (eLoc V θ σ.1 * f σ.1))
          / zLoc V θ σ.1 := by
    intro η
    rw [patchP_val, patchV_patchV, patchV_resV]
    rw [wt_split hVΛ, patchP_val, eRem_patchV, zLoc_patchV]
    ring
  refine Eq.trans (Finset.sum_congr rfl fun η _ => hterm η) ?_
  rw [← Finset.sum_div, ← Finset.sum_mul]
  rw [show (∑ η : ↥V → Bool, eLoc V θ (patchV V η σ.1))
      = zLoc V θ σ.1 from rfl]
  rw [mul_comm (zLoc V θ σ.1), mul_div_assoc,
    div_self (zLoc_pos V θ σ.1).ne', mul_one]
  rw [wt_split hVΛ θ σ]
  ring

/-- The kernel is bounded by the bound of the observable. -/
theorem abs_dlrK_le (V : Finset V2) (θ : ℝ)
    {f : (V2 → Bool) → ℝ} {C : ℝ} (hf : ∀ τ, |f τ| ≤ C)
    (τ : V2 → Bool) : |dlrK V θ f τ| ≤ C := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf τ)
  unfold dlrK
  rw [abs_div, abs_of_pos (zLoc_pos V θ τ)]
  rw [div_le_iff₀ (zLoc_pos V θ τ)]
  calc |∑ η : ↥V → Bool, eLoc V θ (patchV V η τ)
        * f (patchV V η τ)|
      ≤ ∑ η : ↥V → Bool, |eLoc V θ (patchV V η τ)
        * f (patchV V η τ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ η : ↥V → Bool, eLoc V θ (patchV V η τ) * C := by
        refine Finset.sum_le_sum fun η _ => ?_
        rw [abs_mul, abs_of_pos (eLoc_pos V θ _)]
        exact mul_le_mul_of_nonneg_left (hf _)
          (eLoc_pos V θ _).le
    _ = C * zLoc V θ τ := by
        rw [← Finset.sum_mul]
        rw [show (∑ η : ↥V → Bool, eLoc V θ (patchV V η τ))
            = zLoc V θ τ from rfl]
        ring

/-- Every finite volume is eventually inside the boxes. -/
theorem eventually_subset_box (V : Finset V2) :
    ∀ᶠ n in Filter.atTop, V ⊆ box n := by
  rw [Filter.eventually_atTop]
  refine ⟨V.sup (fun v => v.1.natAbs ⊔ v.2.natAbs), fun n hn => ?_⟩
  intro v hv
  have hle : v.1.natAbs ⊔ v.2.natAbs ≤ n :=
    le_trans (Finset.le_sup
      (f := fun v : V2 => v.1.natAbs ⊔ v.2.natAbs) hv) hn
  unfold box
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  have h1 : v.1.natAbs ≤ n := le_trans le_sup_left hle
  have h2 : v.2.natAbs ≤ n := le_trans le_sup_right hle
  omega

/-- **The plus phase satisfies DLR**: resampling any finite volume
leaves it invariant. -/
theorem gibbsPlus_dlr (θ : ℝ) (V : Finset V2)
    {f : (V2 → Bool) → ℝ} {C : ℝ} (hf : ∀ τ, |f τ| ≤ C) :
    gibbsPlus θ (dlrK V θ f) = gibbsPlus θ f := by
  refine gibbsPlus_eq ?_
  have hev : (fun n => expec (box n) θ (dlrK V θ f))
      =ᶠ[(UF : Filter ℕ)] fun n => expec (box n) θ f := by
    refine Filter.EventuallyEq.filter_mono ?_ UF_le_atTop
    filter_upwards [eventually_subset_box V] with n hn
    exact expec_dlrK θ hn f
  exact (gibbsPlus_spec (θ := θ) hf).congr' hev.symm

/-! ## The flip symmetry and the minus phase DLR -/

/-- The flip of a `V`-assignment. -/
def flipEta {V : Finset V2} (η : ↥V → Bool) : ↥V → Bool :=
  fun v => !(η v)

theorem flipEta_involutive (V : Finset V2) :
    Function.Involutive (flipEta (V := V)) := by
  intro η
  funext v
  unfold flipEta
  rw [Bool.not_not]

/-- Patching commutes with the global flip. -/
theorem patchV_flipAll (V : Finset V2) (η : ↥V → Bool)
    (τ : V2 → Bool) :
    patchV V (flipEta η) (flipAll τ) = flipAll (patchV V η τ) := by
  funext v
  show (if h : v ∈ V then flipEta η ⟨v, h⟩ else flipAll τ v)
    = !(if h : v ∈ V then η ⟨v, h⟩ else τ v)
  by_cases h : v ∈ V
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]
    rfl

/-- The local energy is flip invariant. -/
theorem eLoc_flipAll (V : Finset V2) (θ : ℝ) (τ : V2 → Bool) :
    eLoc V θ (flipAll τ) = eLoc V θ τ := by
  unfold eLoc
  congr 2
  refine Finset.sum_congr rfl fun e _ => ?_
  show spin (!(τ (ep0 e))) * spin (!(τ (ep1 e))) = _
  rw [spin_not, spin_not]
  ring

/-- The conditional partition function is flip invariant. -/
theorem zLoc_flipAll (V : Finset V2) (θ : ℝ) (τ : V2 → Bool) :
    zLoc V θ (flipAll τ) = zLoc V θ τ := by
  unfold zLoc
  rw [← Equiv.sum_comp (Function.Involutive.toPerm _
    (flipEta_involutive V))
    (fun η => eLoc V θ (patchV V η (flipAll τ)))]
  refine Finset.sum_congr rfl fun η _ => ?_
  show eLoc V θ (patchV V (flipEta η) (flipAll τ)) = _
  rw [patchV_flipAll, eLoc_flipAll]

/-- **The kernel commutes with the deck flip.** -/
theorem dlrK_flipAll (V : Finset V2) (θ : ℝ)
    (f : (V2 → Bool) → ℝ) (τ : V2 → Bool) :
    dlrK V θ (fun τ' => f (flipAll τ')) τ
      = dlrK V θ f (flipAll τ) := by
  unfold dlrK
  rw [zLoc_flipAll]
  congr 1
  rw [← Equiv.sum_comp (Function.Involutive.toPerm _
    (flipEta_involutive V))
    (fun η => eLoc V θ (patchV V η (flipAll τ))
      * f (patchV V η (flipAll τ)))]
  refine Finset.sum_congr rfl fun η _ => ?_
  show eLoc V θ (patchV V η τ) * f (flipAll (patchV V η τ))
      = eLoc V θ (patchV V (flipEta η) (flipAll τ))
        * f (patchV V (flipEta η) (flipAll τ))
  rw [patchV_flipAll, eLoc_flipAll]

/-- **The minus phase satisfies DLR.** -/
theorem gibbsMinus_dlr (θ : ℝ) (V : Finset V2)
    {f : (V2 → Bool) → ℝ} {C : ℝ} (hf : ∀ τ, |f τ| ≤ C) :
    gibbsMinus θ (dlrK V θ f) = gibbsMinus θ f := by
  unfold gibbsMinus
  have h1 : (fun τ => dlrK V θ f (flipAll τ))
      = dlrK V θ (fun τ' => f (flipAll τ')) :=
    funext fun τ => (dlrK_flipAll V θ f τ).symm
  rw [h1]
  exact gibbsPlus_dlr θ V (fun τ => hf (flipAll τ))

/-- **The symmetric mixture satisfies DLR** — clause (iii) at state
level: same microscopic law, zero magnetization. -/
theorem gibbsMix_dlr (θ : ℝ) (V : Finset V2)
    {f : (V2 → Bool) → ℝ} {C : ℝ} (hf : ∀ τ, |f τ| ≤ C) :
    gibbsMix θ (dlrK V θ f) = gibbsMix θ f := by
  unfold gibbsMix
  rw [gibbsPlus_dlr θ V hf, gibbsMinus_dlr θ V hf]

end NCG.Upstream.Ising
