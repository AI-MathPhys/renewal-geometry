import NCG.Grand.FluctuationObservability

/-! # Exact EASY batch 35: finite regenerative complete observability -/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma psd_finset_sum {s : Finset ℕ}
    {A : ℕ → Matrix n n ℂ} (hA : ∀ k ∈ s, (A k).PosSemidef) :
    (∑ k ∈ s, A k).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix n n ℂ).PosSemidef)
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact (hA k (Finset.mem_insert_self k s)).add
        (ih fun j hj => hA j (Finset.mem_insert_of_mem hj))

/-- `thm:renewal-complete-observability`, including the source-frame
comparison and the finite form of the total observed-energy estimate.

The first Loewner conclusion says
`a ‖R^k x‖_G² ≤ b(1-δ)^k ‖x‖_G²` for every `x`, which is precisely the
squared manuscript norm bound.  The second says every partial observed-energy
sum is bounded by `δ⁻¹ O`; hence it is the exact finite certificate underlying
the infinite-series statement. -/
theorem renewal_complete_observability_exact
    (R O Q G : Matrix n n ℂ) (m : ℕ) (a b δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hO : O.PosSemidef)
    (hObs : O = ∑ j ∈ Finset.range m, Rᴴ ^ j * Q * R ^ j)
    (hmargin : ((O - Rᴴ * O * R) - (δ : ℂ) • O).PosSemidef)
    (hframeLow : (O - (a : ℂ) • G).PosSemidef)
    (hframeHigh : ((b : ℂ) • G - O).PosSemidef)
    (hQleO : (O - Q).PosSemidef) :
    (O - Rᴴ * O * R = Q - Rᴴ ^ m * Q * R ^ m)
      ∧ (∀ k : ℕ,
        ((((b * (1 - δ) ^ k : ℝ) : ℂ) • G)
          - (a : ℂ) • (Rᴴ ^ k * G * R ^ k)).PosSemidef)
      ∧ (∀ K : ℕ,
        (O - (δ : ℂ) • (∑ k ∈ Finset.range K,
          Rᴴ ^ k * Q * R ^ k)).PosSemidef) := by
  have hcore := renewal_complete_observability R O Q δ hδ0 hδ1 hO hmargin
  refine ⟨?_, ?_, ?_⟩
  · calc
      O - Rᴴ * O * R
          = (∑ j ∈ Finset.range m, Rᴴ ^ j * Q * R ^ j)
              - Rᴴ * (∑ j ∈ Finset.range m,
                Rᴴ ^ j * Q * R ^ j) * R := by rw [← hObs]
      _ = Q - Rᴴ ^ m * Q * R ^ m := hcore.1 m
  · intro k
    have hc0 : 0 ≤ (1 - δ) ^ k := by positivity
    have hhigh := hframeHigh.smul hc0
    have hdec := hcore.2.1 k
    have hlow := hframeLow.conjTranspose_mul_mul_same (R ^ k)
    have hsum := (hhigh.add hdec).add hlow
    have hpow : (R ^ k)ᴴ = Rᴴ ^ k := Matrix.conjTranspose_pow R k
    rw [hpow] at hlow hsum
    convert hsum using 1 <;>
      simp only [smul_sub, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul, smul_smul] <;>
      push_cast <;> module
  · intro K
    let D := O - Rᴴ * O * R
    have hDO : (D - (δ : ℂ) • O).PosSemidef := hmargin
    have hsumDO : ((∑ k ∈ Finset.range K, Rᴴ ^ k * D * R ^ k)
        - (δ : ℂ) • (∑ k ∈ Finset.range K,
          Rᴴ ^ k * O * R ^ k)).PosSemidef := by
      have hs := psd_finset_sum (s := Finset.range K)
        (A := fun k => Rᴴ ^ k * (D - (δ : ℂ) • O) * R ^ k)
        (fun k _ => by
          simpa [Matrix.conjTranspose_pow] using
            hDO.conjTranspose_mul_mul_same (R ^ k))
      convert hs using 1 <;>
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
          Matrix.smul_mul, Finset.sum_sub_distrib, Finset.smul_sum]
    have hsumOQ : ((∑ k ∈ Finset.range K, Rᴴ ^ k * O * R ^ k)
        - (∑ k ∈ Finset.range K, Rᴴ ^ k * Q * R ^ k)).PosSemidef := by
      have hs := psd_finset_sum (s := Finset.range K)
        (A := fun k => Rᴴ ^ k * (O - Q) * R ^ k)
        (fun k _ => by
          simpa [Matrix.conjTranspose_pow] using
            hQleO.conjTranspose_mul_mul_same (R ^ k))
      convert hs using 1 <;>
        simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
    have htail : (O - ∑ k ∈ Finset.range K,
        Rᴴ ^ k * D * R ^ k).PosSemidef := hcore.2.2 K |>.2
    have hscaledOQ := hsumOQ.smul hδ0
    have hsum := (htail.add hsumDO).add hscaledOQ
    convert hsum using 1 <;>
      simp only [smul_sub, Finset.smul_sum] <;> module

end NCG
