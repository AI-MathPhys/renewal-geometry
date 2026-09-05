import NCG.Grand.SmithGale

/-!
# Smith-coordinate Gale completeness

The Smith–Gale exact sequence already proves the intrinsic torsion criteria.
This file supplies the manuscript's explicit `gcd(dᵢ,q)=1` reformulation and
its all-moduli (torsion-free) specialization.
-/

namespace NCG

private lemma zmod_torsion_zero_iff_coprime (d q : ℕ) (hd : 0 < d) :
    (∀ x : ZMod d, q • x = 0 → x = 0) ↔ Nat.Coprime d q := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  constructor
  · intro ht
    have hinj : Function.Injective (fun x : ZMod d => (q : ZMod d) * x) := by
      intro x y hxy
      apply sub_eq_zero.mp
      apply ht (x - y)
      simpa [nsmul_eq_mul, mul_sub, hxy]
    have hsurj : Function.Surjective (fun x : ZMod d => (q : ZMod d) * x) :=
      Finite.surjective_of_injective hinj
    obtain ⟨x, hx⟩ := hsurj 1
    have hu : IsUnit (q : ZMod d) := IsUnit.of_mul_eq_one x hx
    exact (ZMod.isUnit_iff_coprime q d).mp hu |>.symm
  · intro hcop x hx
    have hu : IsUnit (q : ZMod d) :=
      (ZMod.isUnit_iff_coprime q d).mpr hcop.symm
    obtain ⟨u, huq⟩ := hu
    have hux : (u : ZMod d) * x = 0 := by
      simpa [nsmul_eq_mul, huq] using hx
    exact (Units.mul_right_eq_zero u).mp hux

/-- `cor:Gale-completeness`, Smith-coordinate fixed-modulus clause: the
`q`-torsion of the product of cyclic Smith factors vanishes exactly when every
Smith invariant is coprime to `q` (equivalently has gcd one with `q`). -/
theorem gale_smith_coprime_criterion {ι : Type*} [Fintype ι]
    [DecidableEq ι] (d : ι → ℕ) (hd : ∀ i, 0 < d i) (q : ℕ) :
    (∀ x : ∀ i, ZMod (d i), q • x = 0 → x = 0)
      ↔ ∀ i, Nat.Coprime (d i) q := by
  constructor
  · intro ht i
    rw [← zmod_torsion_zero_iff_coprime (d i) q (hd i)]
    intro y hy
    let x : ∀ j, ZMod (d j) := Pi.single i y
    have hx : q • x = 0 := by
      funext j
      by_cases hji : j = i
      · subst j
        simpa [x] using hy
      · simp [x, Pi.single_apply, hji]
    have hzero := ht x hx
    have hi := congrFun hzero i
    simpa [x] using hi
  · intro hcop x hx
    funext i
    have hi := congrFun hx i
    exact (zmod_torsion_zero_iff_coprime (d i) q (hd i)).mpr (hcop i)
      (x i) (by simpa using hi)

/-- `cor:Gale-completeness`, all-moduli Smith clause: for positive Smith
invariants, coprimality for every nonzero modulus is equivalent to every
torsion invariant being one, i.e. to a torsion-free cokernel. -/
theorem gale_smith_all_moduli_criterion {ι : Type*}
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) :
    (∀ q : ℕ, 0 < q → ∀ i, Nat.Coprime (d i) q)
      ↔ ∀ i, d i = 1 := by
  constructor
  · intro h i
    have hc := h (d i) (hd i) i
    simpa using hc
  · intro h q hq i
    simp [h i]

end NCG
