/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.BettiNumber

/-!
# Graph cohomology with `ℤ/4` coefficients and the amplitude reduction

**Lemma `lem:z4-lift-surjects`** at the actual graph level (repairing
the earlier abstract-tuple stand-in): for a multigraph `G` we construct

* `coboundaryMap4` — the oriented coboundary
  `δ : C⁰(G,ℤ/4) → C¹(G,ℤ/4)`, `(δg)(e) = g(tgt e) − g(src e)`;
* `H1Z4 G` — the genuine first cohomology
  `C¹(G,ℤ/4) ⧸ im δ` of the graph with `ℤ/4` coefficients;
* `H1Z4.reduce` — the map `H¹(G,ℤ/4) → H¹(G,ℤ/2)` induced on
  cohomology by the coefficient reduction `ℤ/4 → ℤ/2` (well defined
  because reduction intertwines the two coboundaries);
* `H1Z4.reduce_surjective` — **surjectivity**: every `ℤ/2` class lifts,
  by lifting a representative cochain through the set-theoretic
  section `0 ↦ 0, 1 ↦ 1` (`NCG.Multigraph.z4Section`);
* `ker_coboundaryMap4` and `card_H1Z4_of_connected` — on a finite
  connected graph the `ℤ/4` kernel is again the constants (the walk
  argument needs no characteristic assumption), and pure group-order
  counting (no field structure, since `ℤ/4` is not a field) gives
  `|H¹(G,ℤ/4)| = 4^{b₁}`;
* `card_fibre_reduce` — combined with `|H¹(G,ℤ/2)| = 2^{b₁}` this
  makes every fibre of the reduction a coset of size exactly
  `4^{b₁}/2^{b₁} = 2^{b₁}` — the manuscript's "every signed class has
  exactly `2^{b₁}` amplitude lifts".
-/

namespace NCG.Multigraph

variable (G : Multigraph)

/-- The oriented **coboundary map** `δ : C⁰(G,ℤ/4) → C¹(G,ℤ/4)`,
`(δg)(e) = g(tgt e) − g(src e)`.  (Over `ℤ/2` orientation is invisible;
over `ℤ/4` the oriented difference is the correct cochain map.) -/
def coboundaryMap4 : (G.V → ZMod 4) →ₗ[ZMod 4] (G.E → ZMod 4) where
  toFun g := fun e => g (G.tgt e) - g (G.src e)
  map_add' g₁ g₂ := by
    funext e
    simp only [Pi.add_apply]
    ring
  map_smul' c g := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- **First cohomology with `ℤ/4` coefficients**: since a graph has no
2-cells every 1-cochain is a cocycle, so `H¹(G,ℤ/4) = C¹ ⧸ im δ`. -/
def H1Z4 :=
  (G.E → ZMod 4) ⧸ LinearMap.range (coboundaryMap4 G)

instance : AddCommGroup (H1Z4 G) :=
  inferInstanceAs (AddCommGroup
    ((G.E → ZMod 4) ⧸ LinearMap.range (coboundaryMap4 G)))

/-- The class of a `ℤ/4` cochain. -/
def H1Z4.mk (c : G.E → ZMod 4) : H1Z4 G :=
  Submodule.Quotient.mk c

/-- Coefficient reduction `ℤ/4 → ℤ/2` (the ring homomorphism). -/
def z4ToZ2 : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by norm_num) (ZMod 2)

/-- The set-theoretic section `ℤ/2 → ℤ/4`, `0 ↦ 0, 1 ↦ 1`. -/
def z4Section (x : ZMod 2) : ZMod 4 :=
  if x = 0 then 0 else 1

@[simp] theorem z4ToZ2_z4Section (x : ZMod 2) :
    z4ToZ2 (z4Section x) = x := by
  fin_cases x
  · show z4ToZ2 (z4Section 0) = 0
    rw [z4Section, if_pos rfl, map_zero]
  · show z4ToZ2 (z4Section 1) = 1
    rw [z4Section, if_neg (by decide), map_one]

variable {G}

/-- Reduction intertwines the coboundaries: the mod-2 reduction of a
`ℤ/4` coboundary is a `ℤ/2` coboundary (of the reduced 0-cochain) —
the well-definedness input for the induced map on cohomology. -/
theorem z4ToZ2_coboundary (g : G.V → ZMod 4) :
    (fun e => z4ToZ2 (coboundaryMap4 G g e))
      = coboundaryMap G (fun v => z4ToZ2 (g v)) := by
  funext e
  show z4ToZ2 (g (G.tgt e) - g (G.src e))
    = z4ToZ2 (g (G.src e)) + z4ToZ2 (g (G.tgt e))
  rw [map_sub]
  have h2 : ∀ a b : ZMod 2, a - b = b + a := by decide
  exact h2 _ _

variable (G)

/-- **The induced reduction on cohomology**
`ρ : H¹(G,ℤ/4) → H¹(G,ℤ/2)` — well defined because reduction carries
`ℤ/4` coboundaries to `ℤ/2` coboundaries. -/
def H1Z4.reduce : H1Z4 G → H1 G :=
  Quotient.lift (fun c => H1.mk G (fun e => z4ToZ2 (c e)))
    (by
      intro c₁ c₂ hrel
      have hmem : c₁ - c₂ ∈ LinearMap.range (coboundaryMap4 G) :=
        (Submodule.quotientRel_def _).mp hrel
      obtain ⟨g, hg⟩ := hmem
      have hdiff : (fun e => z4ToZ2 (c₁ e)) - (fun e => z4ToZ2 (c₂ e))
          ∈ LinearMap.range (coboundaryMap G) := by
        refine ⟨fun v => z4ToZ2 (g v), ?_⟩
        funext e
        calc (coboundaryMap G fun v => z4ToZ2 (g v)) e
            = z4ToZ2 (coboundaryMap4 G g e) :=
              (congrFun (z4ToZ2_coboundary g) e).symm
          _ = z4ToZ2 ((c₁ - c₂) e) := by rw [hg]
          _ = z4ToZ2 (c₁ e) - z4ToZ2 (c₂ e) := by
              rw [Pi.sub_apply, map_sub]
          _ = ((fun e => z4ToZ2 (c₁ e))
              - fun e => z4ToZ2 (c₂ e)) e := rfl
      exact (Submodule.Quotient.eq _).mpr hdiff)

@[simp] theorem H1Z4.reduce_mk (c : G.E → ZMod 4) :
    H1Z4.reduce G (H1Z4.mk G c) = H1.mk G (fun e => z4ToZ2 (c e)) :=
  rfl

/-- **Lemma `lem:z4-lift-surjects` (surjectivity, at the graph
level)**: reduction modulo two is surjective
`H¹(G,ℤ/4) ↠ H¹(G,ℤ/2)` — every signed class admits an amplitude
lift, obtained by lifting a representative cochain through the
section `0 ↦ 0, 1 ↦ 1`. -/
theorem H1Z4.reduce_surjective :
    Function.Surjective (H1Z4.reduce G) := by
  intro y
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine ⟨H1Z4.mk G (fun e => z4Section (c e)), ?_⟩
  rw [H1Z4.reduce_mk]
  show Submodule.Quotient.mk (fun e => z4ToZ2 (z4Section (c e)))
    = Submodule.Quotient.mk c
  congr 1
  funext e
  exact z4ToZ2_z4Section (c e)

/-- The reduction is additive — it is the map on quotients induced by
an additive cochain map, so fibres are cosets of its kernel. -/
def H1Z4.reduceHom : H1Z4 G →+ H1 G where
  toFun := H1Z4.reduce G
  map_zero' := by
    show H1Z4.reduce G (H1Z4.mk G 0) = _
    rw [H1Z4.reduce_mk]
    have h0 : (fun e => z4ToZ2 ((0 : G.E → ZMod 4) e))
        = (0 : G.E → ZMod 2) := by
      funext e
      exact map_zero _
    rw [h0]
    rfl
  map_add' x y := by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    show H1Z4.reduce G (H1Z4.mk G (c + d)) = _
    rw [H1Z4.reduce_mk]
    have hsum : (fun e => z4ToZ2 ((c + d) e))
        = (fun e => z4ToZ2 (c e)) + fun e => z4ToZ2 (d e) := by
      funext e
      exact map_add _ _ _
    rw [hsum]
    rfl

variable {G}

/-- A `ℤ/4` kernel cochain is walk-invariant — the oriented edge
relation `g(tgt e) = g(src e)` propagates along walks (no
characteristic assumption needed). -/
theorem eq_of_walk_of_coboundary4_eq_zero {g : G.V → ZMod 4}
    (hg : coboundaryMap4 G g = 0) :
    ∀ {u v : G.V}, G.Walk u v → g u = g v := by
  have hz : ∀ e, g (G.tgt e) = g (G.src e) := by
    intro e
    exact sub_eq_zero.mp (congrFun hg e)
  intro u v p
  induction p with
  | nil w => rfl
  | fwd e p ih =>
      rw [← hz e]
      exact ih
  | bwd e p ih =>
      rw [hz e]
      exact ih

variable (G)

/-- The constant `0`-cochains over `ℤ/4`. -/
def constMap4 : ZMod 4 →ₗ[ZMod 4] (G.V → ZMod 4) where
  toFun c := fun _ => c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {G}

/-- **The `ℤ/4` kernel of the coboundary on a connected graph is the
constants** — the walk argument, valid over any coefficient group. -/
theorem ker_coboundaryMap4 {v₀ : G.V} (hconn : G.ConnectedTo v₀) :
    LinearMap.ker (coboundaryMap4 G) = LinearMap.range (constMap4 G) := by
  ext g
  constructor
  · intro hg
    exact ⟨g v₀, funext fun v =>
      eq_of_walk_of_coboundary4_eq_zero
        (LinearMap.mem_ker.mp hg) (hconn v).some⟩
  · rintro ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    funext e
    show c - c = 0
    exact sub_self c

/-- **`|H¹(G, ℤ/4)| = 4^{b₁}` on every finite connected multigraph** —
by pure group-order counting through the two quotient exact sequences
(`ℤ/4` is not a field, so no rank–nullity is available; none is
needed). -/
theorem card_H1Z4_of_connected [Fintype G.V] [Fintype G.E]
    {v₀ : G.V} (hconn : G.ConnectedTo v₀) :
    Nat.card (H1Z4 G)
      = 4 ^ (Fintype.card G.E + 1 - Fintype.card G.V) := by
  classical
  -- |V| ≤ |E| + 1 from the ℤ/2 Betti formula
  have hVE : Fintype.card G.V ≤ Fintype.card G.E + 1 := by
    have := finrank_H1_add_card_vertices hconn
    omega
  -- |ker δ₄| = 4 (constants, injectively parametrised by ℤ/4)
  have hconstinj : Function.Injective (constMap4 G) := by
    intro a b hab
    exact congrFun hab v₀
  have hker : Nat.card (LinearMap.ker (coboundaryMap4 G)) = 4 := by
    rw [ker_coboundaryMap4 hconn]
    rw [Nat.card_congr
      (LinearEquiv.ofInjective (constMap4 G) hconstinj).toEquiv.symm,
      Nat.card_eq_fintype_card, ZMod.card]
  -- |C⁰| = |range δ₄| · |ker δ₄|  (first isomorphism + quotient count)
  have hC0 : Nat.card (G.V → ZMod 4)
      = Nat.card (LinearMap.ker (coboundaryMap4 G))
        * Nat.card (LinearMap.range (coboundaryMap4 G)) := by
    have hq := Submodule.card_eq_card_quotient_mul_card
      (LinearMap.ker (coboundaryMap4 G))
    rw [Nat.card_congr
      (LinearMap.quotKerEquivRange (coboundaryMap4 G)).toEquiv] at hq
    exact hq
  -- |C¹| = |H¹| · |range δ₄|  (quotient count for H¹)
  have hC1 : Nat.card (G.E → ZMod 4)
      = Nat.card (H1Z4 G)
        * Nat.card (LinearMap.range (coboundaryMap4 G)) := by
    have hq := Submodule.card_eq_card_quotient_mul_card
      (LinearMap.range (coboundaryMap4 G))
    first
    | exact hq
    | exact hq.trans (Nat.mul_comm _ _)
  -- assemble: |H¹| · 4^{|V|} = 4^{|E|+1}
  have hpowV : Nat.card (G.V → ZMod 4) = 4 ^ Fintype.card G.V := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  have hpowE : Nat.card (G.E → ZMod 4) = 4 ^ Fintype.card G.E := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  have hkey : Nat.card (H1Z4 G) * 4 ^ Fintype.card G.V
      = 4 ^ (Fintype.card G.E + 1) := by
    calc Nat.card (H1Z4 G) * 4 ^ Fintype.card G.V
        = Nat.card (H1Z4 G) * Nat.card (G.V → ZMod 4) := by
          rw [hpowV]
      _ = Nat.card (H1Z4 G)
            * (Nat.card (LinearMap.ker (coboundaryMap4 G))
              * Nat.card (LinearMap.range (coboundaryMap4 G))) := by
          rw [hC0]
      _ = (Nat.card (H1Z4 G)
            * Nat.card (LinearMap.range (coboundaryMap4 G))) * 4 := by
          rw [hker]
          ring
      _ = Nat.card (G.E → ZMod 4) * 4 := by rw [← hC1]
      _ = 4 ^ (Fintype.card G.E + 1) := by
          rw [hpowE, pow_succ]
  have hsplit : (4:ℕ) ^ (Fintype.card G.E + 1)
      = 4 ^ (Fintype.card G.E + 1 - Fintype.card G.V)
        * 4 ^ Fintype.card G.V := by
    rw [← pow_add]
    congr 1
    omega
  have hpos : 0 < (4:ℕ) ^ Fintype.card G.V := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [hkey, hsplit])

/-- **Lemma `lem:z4-lift-surjects` (fibre count)**: on a finite
connected multigraph every signed class has exactly `2^{b₁}` amplitude
lifts — each fibre of the reduction is a coset of the kernel, and the
orders `|H¹(ℤ/4)| = 4^{b₁}`, `|H¹(ℤ/2)| = 2^{b₁}` force
`|ker| = 2^{b₁}`. -/
theorem card_fibre_reduce [Fintype G.V] [Fintype G.E]
    {v₀ : G.V} (hconn : G.ConnectedTo v₀) (y : H1 G) :
    Nat.card {x : H1Z4 G // H1Z4.reduce G x = y}
      = 2 ^ (Fintype.card G.E + 1 - Fintype.card G.V) := by
  classical
  obtain ⟨x₀, hx₀⟩ := H1Z4.reduce_surjective G y
  -- the fibre over y is a coset of the kernel of the additive hom
  have hfib : Nat.card {x : H1Z4 G // H1Z4.reduce G x = y}
      = Nat.card {k : H1Z4 G // H1Z4.reduce G k = 0} := by
    refine Nat.card_congr ⟨fun x => ⟨x.1 - x₀, ?_⟩,
      fun k => ⟨k.1 + x₀, ?_⟩, fun x => ?_, fun k => ?_⟩
    · show H1Z4.reduce G (x.1 - x₀) = 0
      have h := (H1Z4.reduceHom G).map_sub x.1 x₀
      rw [show H1Z4.reduce G (x.1 - x₀)
          = H1Z4.reduceHom G (x.1 - x₀) from rfl, h,
        show H1Z4.reduceHom G x.1 = H1Z4.reduce G x.1 from rfl,
        show H1Z4.reduceHom G x₀ = H1Z4.reduce G x₀ from rfl,
        x.2, hx₀, sub_self]
    · show H1Z4.reduce G (k.1 + x₀) = y
      have h := (H1Z4.reduceHom G).map_add k.1 x₀
      rw [show H1Z4.reduce G (k.1 + x₀)
          = H1Z4.reduceHom G (k.1 + x₀) from rfl, h,
        show H1Z4.reduceHom G k.1 = H1Z4.reduce G k.1 from rfl,
        show H1Z4.reduceHom G x₀ = H1Z4.reduce G x₀ from rfl,
        k.2, hx₀, zero_add]
    · apply Subtype.ext
      show x.1 - x₀ + x₀ = x.1
      abel
    · apply Subtype.ext
      show k.1 + x₀ - x₀ = k.1
      abel
  rw [hfib]
  -- |ker| from the order equation 4^{b₁} = 2^{b₁}·|ker|
  have hkerfib : Nat.card {k : H1Z4 G // H1Z4.reduce G k = 0}
      = Nat.card (H1Z4.reduceHom G).ker := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun k => Iff.rfl
  rw [hkerfib]
  have hcard4 := card_H1Z4_of_connected hconn
  have hcard2 := card_H1_of_connected hconn
  have hquot : Nat.card (H1Z4 G)
      = Nat.card (H1 G) * Nat.card (H1Z4.reduceHom G).ker := by
    have hq := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (H1Z4.reduceHom G).ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
      (H1Z4.reduceHom G) (H1Z4.reduce_surjective G)).toEquiv] at hq
    first
    | exact hq
    | exact hq.trans (Nat.mul_comm _ _)
  set b := Fintype.card G.E + 1 - Fintype.card G.V
  have h4 : (4:ℕ) ^ b = 2 ^ b * 2 ^ b := by
    rw [← pow_add, ← two_mul]
    norm_num [pow_mul]
  have hpos : 0 < (2:ℕ) ^ b := by positivity
  have : 2 ^ b * 2 ^ b = 2 ^ b * Nat.card (H1Z4.reduceHom G).ker := by
    rw [← h4, ← hcard4, hquot, hcard2]
  exact (Nat.eq_of_mul_eq_mul_left hpos this).symm

end NCG.Multigraph
