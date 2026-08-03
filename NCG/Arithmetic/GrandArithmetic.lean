/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.MassFlux
import NCG.Arithmetic.ScalingChain
import NCG.Arithmetic.ArithParity
import NCG.Arithmetic.SignedSeparator

/-!
# Grand arithmetic closure theorem
  (`thm:grand-arithmetic`, arithmetic manuscript)

`grand_arithmetic_closure`: the multiport assembly — one theorem
consuming the entry data of the constituent proved records and
returning, in a single conjunction:

* the multiport endpoint estimate (the common logarithmic cell
  packet controls every selected port at once,
  `thm:multiport-prefix`);
* (i)–(ii) the spectral conclusion: subpower residue variance at
  every positive line forces each nonprincipal displacement to
  vanish (`cor:fixed-mod-grh` through the Gaussian–Hardy
  criterion);
* (iii) the twin conclusion: a positive `P₁ ∪ P₂` carrier with
  selector-stable parity cancellation contains a twin pair
  (`thm:twin-chain`);
* (iv) the Goldbach conclusion: a positive fixed-sum carrier with
  uniform parity cancellation yields a Goldbach representation
  (`thm:gold-chain`);
* (v) the signed route: positivity of the signed degree-separator
  correlation gives a twin pair directly
  (`cor:v003-signed-additive-closure` / `twin_closure`).

Rendering disclosed: the discrepancy factorization through one
predetermined logarithmic cell packet and the two `o(A_X)` ledger
estimates are the displayed entry hypotheses (the manuscript's
warning: the theorem does not derive the packet, its mass
balance, or its prefix-current estimate — it states that one
source controls all preassigned ports); the per-port
normalizations are the cited sector records.
-/

namespace NCG

/-- `thm:grand-arithmetic`: the multiport closure assembly. -/
theorem grand_arithmetic_closure
    -- common cell packet: multiport data (a = mass ledger,
    -- b = prefix-current ledger, x = port discrepancies)
    {R : ℕ} (lam x a b : Fin R → ℝ)
    (hlam : ∀ r, 0 ≤ lam r) (ha : ∀ r, 0 ≤ a r)
    (hb : ∀ r, 0 ≤ b r) (hx0 : ∀ r, 0 ≤ x r)
    (hx : ∀ r, x r ≤ a r + b r)
    -- (i)-(ii) spectral entry: per-character indicator at every
    -- positive line
    (dis : ℝ) (hind : ∀ σ : ℝ, 0 < σ → dis ≤ σ ∧ -dis ≤ σ)
    -- (iii) twin carrier entry
    {C : Type*} [Fintype C] (w : C → ℝ) (p : C → ℕ)
    (m0 delta : ℝ) (hw : ∀ c, 0 ≤ w c) (hm0 : 0 < m0)
    (hdelta : 0 < delta) (hp : ∀ c, Nat.Prime (p c))
    (hM : m0 ≤ ∑ c, w c)
    (hJtwin : ∑ c, w c
        * (if Nat.Prime (p c + 2) then (-1 : ℝ) else 1)
      ≤ (1 - 2 * delta) * ∑ c, w c)
    -- (iv) Goldbach carrier entry
    {C' : Type*} [Fintype C'] (w' : C' → ℝ) (p' : C' → ℕ)
    (N : ℕ) (m0' delta' : ℝ) (hw' : ∀ c, 0 ≤ w' c)
    (hm0' : 0 < m0') (hdelta' : 0 < delta')
    (hp' : ∀ c, Nat.Prime (p' c)) (hsum' : ∀ c, p' c ≤ N)
    (hM' : m0' ≤ ∑ c, w' c)
    (hJgold : ∑ c, w' c
        * (if Nat.Prime (N - p' c) then (-1 : ℝ) else 1)
      ≤ (1 - 2 * delta') * ∑ c, w' c)
    -- (v) signed degree-separator entry
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (Jsep : ℕ → ℝ)
    (hminor : ∀ q ∈ S,
      Jsep (q + 2) ≤ if (q + 2).Prime then 1 else 0)
    (hpos : 0 < ∑ q ∈ S, Real.log q * Jsep (q + 2)) :
    -- multiport endpoint estimate
    Real.sqrt (∑ r, lam r * x r ^ 2)
      ≤ Real.sqrt (∑ r, lam r * a r ^ 2)
        + Real.sqrt (∑ r, lam r * b r ^ 2)
    -- (i)-(ii) spectral conclusion
    ∧ dis = 0
    -- (iii) twin conclusion
    ∧ (∃ c, 0 < w c ∧ Nat.Prime (p c) ∧ Nat.Prime (p c + 2))
    -- (iv) Goldbach conclusion
    ∧ (∃ u v : ℕ, Nat.Prime u ∧ Nat.Prime v ∧ u + v = N)
    -- (v) signed-separator conclusion
    ∧ ∃ q ∈ S, q.Prime ∧ (q + 2).Prime :=
  ⟨multiport_prefix lam x a b hlam ha hb hx0 hx,
    fixed_mod_grh dis hind,
    twin_chain w p m0 delta hw hm0 hdelta hp hM hJtwin,
    gold_chain w' p' N m0' delta' hw' hm0' hdelta' hp' hsum'
      hM' hJgold,
    twin_closure hS Jsep hminor hpos⟩

end NCG
