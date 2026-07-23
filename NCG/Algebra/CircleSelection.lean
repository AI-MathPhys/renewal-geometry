/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The two-path dimension selection: a transitive circle forces `m = 2`

The dimension-selection core of `thm:two-path-complex-face`
(`manuscripts/renewal_emergence/renewal_emergence.tex`): if the balanced pure states of a
nonclassical Peirce coherence space form the unit sphere of a real
inner product space `V` carrying an effective transitive continuous
action of the compact connected one-dimensional phase group by
isometries, then `dim V = 2`.

The proof is purely algebraic — no Lie theory and no invariance of
domain:

* `invariant_eq_bot_or_top_of_transitive` — **transitivity forces
  irreducibility**: an invariant subspace and its (also invariant)
  orthogonal complement would carry unit vectors in different
  orbits;
* `finrank_le_two_of_isometry_irreducible` — an isometry `M` with no
  proper invariant subspace forces `dim ≤ 2`: the symmetric operator
  `S = M + M⁻¹` commutes with `M`, so its eigenspace is invariant,
  hence everything; then `M² = λM − 1`, so every `span {x, Mx}` is
  invariant, hence everything;
* `invariant_of_generator` — a topological generator of a monothetic
  group (the circle) propagates invariance from one isometry to the
  whole action, by density and closedness of finite-dimensional
  subspaces;
* `circle_dimension_selection` — the assembly: `dim ≤ 2` from the
  above, `dim ≠ 1` because the connected circle cannot act
  transitively on the two-point sphere `S⁰` (an intermediate-value
  argument), and `dim ≠ 0` by nonclassicality.  Hence **`dim V = 2`**.
-/

namespace NCG.Jordan

open Module Submodule RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- **Transitivity forces irreducibility**: a subspace invariant
under a group of isometries acting transitively on the unit sphere
is trivial — its orthogonal complement is also invariant, and unit
vectors of the two cannot be in a common orbit. -/
theorem invariant_eq_bot_or_top_of_transitive
    {G : Type*} [Group G] (ρ : G →* (V ≃ₗᵢ[ℝ] V))
    (htrans : ∀ x y : V, ‖x‖ = 1 → ‖y‖ = 1 → ∃ g, ρ g x = y)
    (W : Submodule ℝ V) (hW : ∀ (g : G), ∀ w ∈ W, ρ g w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  by_contra htop
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have horthne : Wᗮ ≠ ⊥ := by
    intro hc
    exact htop (Submodule.orthogonal_eq_bot_iff.mp hc)
  obtain ⟨u, huW, hu0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot horthne
  -- normalized representatives
  set w' : V := ‖w‖⁻¹ • w with hw'
  set u' : V := ‖u‖⁻¹ • u with hu'
  have hw'norm : ‖w'‖ = 1 := by
    rw [hw', norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
  have hu'norm : ‖u'‖ = 1 := by
    rw [hu', norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0)]
  have hw'W : w' ∈ W := W.smul_mem _ hwW
  have hu'W : u' ∈ Wᗮ := Wᗮ.smul_mem _ huW
  obtain ⟨g, hg⟩ := htrans w' u' hw'norm hu'norm
  have hmem : u' ∈ W := by
    rw [← hg]
    exact hW g w' hw'W
  have hzero : u' = 0 :=
    (Submodule.mem_bot ℝ).mp
      ((Submodule.orthogonal_disjoint W).le_bot ⟨hmem, hu'W⟩)
  rw [hu'] at hzero
  rcases smul_eq_zero.mp hzero with h1 | h1
  · exact absurd (inv_eq_zero.mp h1)
      (norm_ne_zero_iff.mpr hu0)
  · exact hu0 h1

/-- **A single irreducible isometry forces `dim ≤ 2`**: the
symmetric operator `M + M⁻¹` commutes with `M`, so its eigenspace is
`M`-invariant, hence all of `V`; then `M² = λM − 1` and every
`span {x, Mx}` is `M`-invariant, hence all of `V`. -/
theorem finrank_le_two_of_isometry_irreducible (M : V ≃ₗᵢ[ℝ] V)
    (hirr : ∀ W : Submodule ℝ V, (∀ w ∈ W, M w ∈ W) → W = ⊥ ∨ W = ⊤) :
    finrank ℝ V ≤ 2 := by
  classical
  rcases Nat.lt_or_ge (finrank ℝ V) 1 with hn | hn
  · omega
  haveI : Nontrivial V := by
    have h1 : 0 < finrank ℝ V := hn
    exact Module.nontrivial_of_finrank_pos h1
  -- the symmetric operator S = M + M⁻¹
  set S : V →ₗ[ℝ] V :=
    (M.toLinearEquiv : V →ₗ[ℝ] V)
      + (M.symm.toLinearEquiv : V →ₗ[ℝ] V) with hSdef
  have hSapp : ∀ x : V, S x = M x + M.symm x := fun x => rfl
  have hSsymm : S.IsSymmetric := by
    intro x y
    rw [hSapp, hSapp, inner_add_left, inner_add_right]
    have h1 : ⟪M x, y⟫ = ⟪x, M.symm y⟫ := by
      conv_lhs => rw [show y = M (M.symm y) from
        (M.apply_symm_apply y).symm]
      exact M.inner_map_map x (M.symm y)
    have h2 : ⟪M.symm x, y⟫ = ⟪x, M y⟫ := by
      conv_lhs => rw [show y = M.symm (M y) from
        (M.symm_apply_apply y).symm]
      exact M.symm.inner_map_map x (M y)
    rw [h1, h2]
    ring
  -- an eigenvalue of S
  have hn' : finrank ℝ V = finrank ℝ V := rfl
  obtain ⟨i⟩ : Nonempty (Fin (finrank ℝ V)) := ⟨⟨0, hn⟩⟩
  set b := hSsymm.eigenvectorBasis hn'
  set lam := hSsymm.eigenvalues hn' i with hlam
  have hbev : S (b i) = (lam : ℝ) • b i :=
    hSsymm.apply_eigenvectorBasis hn' i
  -- the eigenspace is M-invariant, hence everything
  set E := Module.End.eigenspace S lam with hE
  have hEne : E ≠ ⊥ := by
    intro hc
    have h1 : b i ∈ E := by
      rw [hE, Module.End.mem_eigenspace_iff]
      exact hbev
    rw [hc, Submodule.mem_bot] at h1
    exact b.toBasis.ne_zero i (by simpa using h1)
  have hEinv : ∀ w ∈ E, M w ∈ E := by
    intro w hw
    rw [hE, Module.End.mem_eigenspace_iff] at hw ⊢
    have h1 : S (M w) = M (S w) := by
      rw [hSapp, hSapp, map_add, M.symm_apply_apply,
        M.apply_symm_apply]
    rw [h1, hw, map_smul]
  have hEtop : E = ⊤ := (hirr E hEinv).resolve_left hEne
  -- S = λ·id, so M² = λM − 1
  have hSid : ∀ x : V, M x + M.symm x = lam • x := by
    intro x
    have h1 : x ∈ E := hEtop ▸ Submodule.mem_top
    rw [hE, Module.End.mem_eigenspace_iff] at h1
    rw [← hSapp]
    exact h1
  have hMsq : ∀ x : V, M (M x) = lam • M x - x := by
    intro x
    have h1 := hSid (M x)
    have h2 : M.symm (M x) = x := M.symm_apply_apply x
    rw [h2] at h1
    linear_combination (norm := module) h1
  -- span {x, Mx} is M-invariant, hence everything
  obtain ⟨x, hx0⟩ := exists_ne (0 : V)
  set W := Submodule.span ℝ ({x, M x} : Set V) with hWdef
  have hxW : x ∈ W := Submodule.subset_span (by simp)
  have hMxW : M x ∈ W := Submodule.subset_span (by simp)
  have hWinv : ∀ w ∈ W, M w ∈ W := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact hMxW
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        rw [hMsq x]
        exact W.sub_mem (W.smul_mem _ hMxW) hxW
    | zero => simpa using W.zero_mem
    | add y z _ _ hy hz =>
      rw [map_add]
      exact W.add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul]
      exact W.smul_mem c hy
  have hWne : W ≠ ⊥ := by
    intro hc
    rw [hc, Submodule.mem_bot] at hxW
    exact hx0 hxW
  have hWtop : W = ⊤ := (hirr W hWinv).resolve_left hWne
  have h2 : finrank ℝ V = finrank ℝ W := by
    rw [hWtop]
    exact (finrank_top ℝ V).symm
  rw [h2, hWdef]
  refine le_trans (finrank_span_le_card ({x, M x} : Set V)) ?_
  rw [Set.toFinset_insert, Set.toFinset_singleton]
  exact (Finset.card_insert_le _ _).trans (by simp)

/-- **A topological generator propagates invariance**: if a subspace
is invariant under `ρ g₀` with `⟨g₀⟩` dense, it is invariant under
the whole continuous isometric action (finite-dimensional subspaces
are closed). -/
theorem invariant_of_generator {G : Type*} [Group G]
    [TopologicalSpace G]
    (ρ : G →* (V ≃ₗᵢ[ℝ] V)) (hcont : ∀ x : V, Continuous fun g => ρ g x)
    {g₀ : G}
    (hdense : Dense ((Subgroup.zpowers g₀ : Subgroup G) : Set G))
    (W : Submodule ℝ V) (hW : ∀ w ∈ W, ρ g₀ w ∈ W) :
    ∀ (g : G), ∀ w ∈ W, ρ g w ∈ W := by
  -- the generator maps W onto W, so its inverse preserves W as well
  have hmap : W.map (ρ g₀).toLinearEquiv.toLinearMap = W := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rintro y ⟨w, hwW, rfl⟩
      exact hW w hwW
    · rw [LinearEquiv.finrank_map_eq]
  have hWinv : ∀ w ∈ W, ρ g₀⁻¹ w ∈ W := by
    intro w hw
    rw [← hmap] at hw
    obtain ⟨w', hw'W, hw'⟩ := hw
    have h1 : ρ g₀⁻¹ w = w' := by
      have h2 : (ρ g₀) w' = w := hw'
      rw [← h2]
      have h3 : (ρ g₀⁻¹) ((ρ g₀) w') = ((ρ g₀⁻¹) * (ρ g₀)) w' := rfl
      rw [h3, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [h1]
    exact hw'W
  -- hence invariance under every integer power
  have hzpow : ∀ (n : ℤ), ∀ w ∈ W, ρ (g₀ ^ n) w ∈ W := by
    intro n
    induction n using Int.induction_on with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      have h1 : g₀ ^ ((k : ℤ) + 1) = g₀ * g₀ ^ (k : ℤ) := by
        rw [add_comm]
        exact zpow_one_add g₀ (k : ℤ)
      rw [h1, map_mul]
      exact hW _ (ih w hw)
    | pred k ih =>
      intro w hw
      have h1 : g₀ ^ (-(k : ℤ) - 1) = g₀⁻¹ * g₀ ^ (-(k : ℤ)) := by
        rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one]
      rw [h1, map_mul]
      exact hWinv _ (ih w hw)
  -- density + closedness of W transports invariance to all of G
  intro g w hw
  have hgcl : g ∈ closure ((Subgroup.zpowers g₀ : Subgroup G) : Set G) := by
    rw [hdense.closure_eq]
    trivial
  have himg : (fun h => ρ h w) ''
      ((Subgroup.zpowers g₀ : Subgroup G) : Set G) ⊆ (W : Set V) := by
    rintro y ⟨h, hh, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact hzpow n w hw
  have hclosed : IsClosed (W : Set V) := W.closed_of_finiteDimensional
  have h1 : ρ g w ∈ closure ((fun h => ρ h w) ''
      ((Subgroup.zpowers g₀ : Subgroup G) : Set G)) := by
    have h3 := image_closure_subset_closure_image (f := fun h => ρ h w)
      (s := ((Subgroup.zpowers g₀ : Subgroup G) : Set G)) (hcont w)
    exact h3 ⟨g, hgcl, rfl⟩
  exact closure_minimal himg hclosed h1

/-- **The two-path dimension selection**
(`thm:two-path-complex-face`, dimension clause): a monothetic
connected compact group — the circle — acting continuously,
isometrically, and transitively on the unit sphere of a nonzero
finite-dimensional real inner product space forces the dimension to
be exactly two.  `dim ≤ 2` is the irreducibility argument; `dim ≠ 1`
is connectedness (the circle cannot act transitively on `S⁰`, by the
intermediate value theorem); `dim ≠ 0` is nonclassicality. -/
theorem circle_dimension_selection {G : Type*} [Group G]
    [TopologicalSpace G] [PreconnectedSpace G]
    (ρ : G →* (V ≃ₗᵢ[ℝ] V))
    (hcont : ∀ x : V, Continuous fun g => ρ g x)
    (hmono : ∃ g₀ : G,
      Dense ((Subgroup.zpowers g₀ : Subgroup G) : Set G))
    (htrans : ∀ x y : V, ‖x‖ = 1 → ‖y‖ = 1 → ∃ g, ρ g x = y)
    (hpos : 0 < finrank ℝ V) :
    finrank ℝ V = 2 := by
  obtain ⟨g₀, hg₀⟩ := hmono
  have hle : finrank ℝ V ≤ 2 := by
    refine finrank_le_two_of_isometry_irreducible (ρ g₀) ?_
    intro W hW
    exact invariant_eq_bot_or_top_of_transitive ρ htrans W
      (invariant_of_generator ρ hcont hg₀ W hW)
  rcases (by omega : finrank ℝ V = 1 ∨ finrank ℝ V = 2) with h1 | h2
  · exfalso
    -- dimension one: the connected group cannot reach both poles
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨v, hv0⟩ := exists_ne (0 : V)
    set e : V := ‖v‖⁻¹ • v with he
    have henorm : ‖e‖ = 1 := by
      rw [he, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
    have hspan : Submodule.span ℝ ({e} : Set V) = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [finrank_span_singleton (by
        intro hc
        rw [hc, norm_zero] at henorm
        norm_num at henorm), h1]
    -- every group element sends e to ±e
    have hpm : ∀ g : G, ⟪ρ g e, e⟫ = 1 ∨ ⟪ρ g e, e⟫ = -1 := by
      intro g
      have hmem : ρ g e ∈ Submodule.span ℝ ({e} : Set V) := by
        rw [hspan]
        trivial
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hnorm : ‖ρ g e‖ = 1 := by
        rw [(ρ g).norm_map, henorm]
      rw [← hc, norm_smul, henorm, mul_one] at hnorm
      have hinner : ⟪ρ g e, e⟫ = c := by
        rw [← hc, real_inner_smul_left,
          real_inner_self_eq_norm_sq, henorm]
        norm_num
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp
        (by simpa [Real.norm_eq_abs] using hnorm) with h | h
      · left; rw [hinner, h]
      · right; rw [hinner, h]
    -- but the inner product takes both values ±1 on a connected group
    obtain ⟨g₁, hg₁⟩ := htrans e (-e) henorm (by
      rw [norm_neg, henorm])
    set f : G → ℝ := fun g => ⟪ρ g e, e⟫ with hf
    have hfcont : Continuous f := by
      refine Continuous.inner (hcont e) continuous_const
    have hf1 : f 1 = 1 := by
      rw [hf]
      simp only [map_one]
      have h2 : (1 : V ≃ₗᵢ[ℝ] V) e = e := rfl
      rw [h2, real_inner_self_eq_norm_sq, henorm]
      norm_num
    have hfg₁ : f g₁ = -1 := by
      rw [hf]
      simp only [hg₁, inner_neg_left, real_inner_self_eq_norm_sq,
        henorm]
      norm_num
    -- intermediate value on the preconnected group
    have hiv := intermediate_value_univ (a := g₁) (b := (1 : G))
      (f := f) hfcont
    have h0mem : (0 : ℝ) ∈ Set.Icc (f g₁) (f 1) := by
      rw [hf1, hfg₁]
      norm_num
    obtain ⟨g₂, hg₂⟩ := hiv h0mem
    rcases hpm g₂ with h | h
    · have h' : f g₂ = 1 := h
      rw [hg₂] at h'
      norm_num at h'
    · have h' : f g₂ = -1 := h
      rw [hg₂] at h'
      norm_num at h' 
  · exact h2

end NCG.Jordan
