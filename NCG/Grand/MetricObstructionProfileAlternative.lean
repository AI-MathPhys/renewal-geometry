import NCG.Grand.MetricProfile
import NCG.Grand.RenormalizationCocycle

/-!
# The complete metric-obstruction profile alternative

This file supplies the finite-dimensional compactness and witness layers of
`thm:metric-profile-alternative`.  The earlier theorem
`NCG.metric_profile_alternative` is the scalar extraction engine.  Here it is
iterated for the trace scale, the least positive normalized eigenvalue, the
old/new-support residual, and the diamond/affine residual.  Compactness of the
declared gauge then gives the remaining modulus alternative.

Every negative constructor contains the subsequence on which it occurs and
the corresponding normalized eigenvector, source direction, diamond vector,
affine-anchor vector, or unresolved compact modulus.
-/

open Filter Matrix Topology

noncomputable section

namespace NCG

universe u

/-- Squared Euclidean norm in the fixed finite coordinate model. -/
def profileNormSq {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- The data recorded by the manuscript's metric-obstruction profile.

`metric` is the unnormalised Gram matrix, `normalizedMetric` is its trace-one
normalisation, and `shapeVector` certifies the displayed least positive
eigenvalue.  The remaining vector fields are the displayed source, diamond,
and affine-anchor witnesses. -/
structure MetricObstructionProfile (d : ℕ) (K : Type*) where
  metric : ℕ → Matrix (Fin d) (Fin d) ℝ
  normalizedMetric : ℕ → Matrix (Fin d) (Fin d) ℝ
  scale : ℕ → ℝ
  shape : ℕ → ℝ
  shapeVector : ℕ → Fin d → ℝ
  oldLoss : ℕ → ℝ
  oldSource : ℕ → Fin d → ℝ
  newInnovation : ℕ → ℝ
  newSource : ℕ → Fin d → ℝ
  diamondResidual : ℕ → ℝ
  diamondVector : ℕ → Fin d → ℝ
  anchorResidual : ℕ → ℝ
  anchorVector : ℕ → Fin d → ℝ
  modulus : ℕ → K
  anchorResolves : K → Prop

/-- The old-support loss plus new-support innovation. -/
def MetricObstructionProfile.supportResidual {d : ℕ} {K : Type*}
    (P : MetricObstructionProfile d K) (n : ℕ) : ℝ :=
  P.oldLoss n + P.newInnovation n

/-- The cocycle-diamond plus affine-anchor residual. -/
def MetricObstructionProfile.coherenceResidual {d : ℕ} {K : Type*}
    (P : MetricObstructionProfile d K) (n : ℕ) : ℝ :=
  P.diamondResidual n + P.anchorResidual n

/-- Certification that the profile fields really are the stated metric,
spectral, source, diamond, and affine witnesses. -/
structure CertifiedMetricObstructionProfile (d : ℕ) (K : Type*)
    extends MetricObstructionProfile d K where
  scale_pos : ∀ n, 0 < scale n
  scale_eq_trace : ∀ n, scale n = Matrix.trace (metric n)
  normalization : ∀ n i j,
    scale n * normalizedMetric n i j = metric n i j
  normalized_psd : ∀ n v,
    0 ≤ dotProduct v (normalizedMetric n *ᵥ v)
  shape_pos : ∀ n, 0 < shape n
  shape_vector_normalized : ∀ n, profileNormSq (shapeVector n) = 1
  shape_eigenvector : ∀ n,
    normalizedMetric n *ᵥ shapeVector n = shape n • shapeVector n
  shape_is_least_positive : ∀ n v,
    profileNormSq v = 1 →
    0 < dotProduct v (normalizedMetric n *ᵥ v) →
    shape n ≤ dotProduct v (normalizedMetric n *ᵥ v)
  old_loss_nonneg : ∀ n, 0 ≤ oldLoss n
  old_source_normalized : ∀ n, profileNormSq (oldSource n) = 1
  new_innovation_nonneg : ∀ n, 0 ≤ newInnovation n
  new_source_normalized : ∀ n, profileNormSq (newSource n) = 1
  diamond_nonneg : ∀ n, 0 ≤ diamondResidual n
  diamond_vector_normalized : ∀ n, profileNormSq (diamondVector n) = 1
  anchor_nonneg : ∀ n, 0 ≤ anchorResidual n
  anchor_vector_normalized : ∀ n, profileNormSq (anchorVector n) = 1

/-- A complete, witness-bearing version of branches (R1)--(R6). -/
inductive MetricProfileBranch {d : ℕ} {K : Type u}
    [TopologicalSpace K] (P : CertifiedMetricObstructionProfile d K) : Type u
  | stable
      (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (αminus αplus sstar : ℝ) (k : K)
      (hαminus : 0 < αminus) (hαplus : αminus ≤ αplus)
      (hsstar : 0 < sstar)
      (hscale : ∀ᶠ n in atTop,
        αminus ≤ P.scale (φ n) ∧ P.scale (φ n) ≤ αplus)
      (hshape : ∀ᶠ n in atTop, sstar ≤ P.shape (φ n))
      (hold : Tendsto (fun n => P.oldLoss (φ n)) atTop (nhds 0))
      (hnew : Tendsto (fun n => P.newInnovation (φ n)) atTop (nhds 0))
      (hdiamond : Tendsto (fun n => P.diamondResidual (φ n)) atTop (nhds 0))
      (hanchor : Tendsto (fun n => P.anchorResidual (φ n)) atTop (nhds 0))
      (hmodulus : Tendsto (fun n => P.modulus (φ n)) atTop (nhds k))
      (hresolved : P.anchorResolves k)
  | scaleCollapse
      (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (hscale : Tendsto (fun n => P.scale (φ n)) atTop (nhds 0))
  | scaleBlowup
      (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (hscale : Tendsto (fun n => P.scale (φ n)) atTop atTop)
  | shapeCollapse
      (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (αminus αplus : ℝ) (hαminus : 0 < αminus)
      (hscale : ∀ᶠ n in atTop,
        αminus ≤ P.scale (φ n) ∧ P.scale (φ n) ≤ αplus)
      (hshape : Tendsto (fun n => P.shape (φ n)) atTop (nhds 0))
      (hnormalized : ∀ n, profileNormSq (P.shapeVector (φ n)) = 1)
      (heigen : ∀ n, P.normalizedMetric (φ n) *ᵥ P.shapeVector (φ n) =
        P.shape (φ n) • P.shapeVector (φ n))
  | supportChange
      (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (αminus αplus sstar ε : ℝ)
      (hαminus : 0 < αminus) (hsstar : 0 < sstar) (hε : 0 < ε)
      (hscale : ∀ᶠ n in atTop,
        αminus ≤ P.scale (φ n) ∧ P.scale (φ n) ≤ αplus)
      (hshape : ∀ᶠ n in atTop, sstar ≤ P.shape (φ n))
      (haway : ∀ᶠ n in atTop, ε ≤ P.supportResidual (φ n))
      (hwitness : ∀ n,
        profileNormSq (P.oldSource (φ n)) = 1 ∧
        profileNormSq (P.newSource (φ n)) = 1)
  | coherenceFailure
      (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (αminus αplus sstar ε : ℝ)
      (hαminus : 0 < αminus) (hsstar : 0 < sstar) (hε : 0 < ε)
      (hscale : ∀ᶠ n in atTop,
        αminus ≤ P.scale (φ n) ∧ P.scale (φ n) ≤ αplus)
      (hshape : ∀ᶠ n in atTop, sstar ≤ P.shape (φ n))
      (hsupport : Tendsto (fun n => P.supportResidual (φ n)) atTop (nhds 0))
      (haway : ∀ᶠ n in atTop, ε ≤ P.coherenceResidual (φ n))
      (hwitness : ∀ n,
        profileNormSq (P.diamondVector (φ n)) = 1 ∧
        profileNormSq (P.anchorVector (φ n)) = 1)
  | unresolvedModulus
      (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (αminus αplus sstar : ℝ) (k : K)
      (hαminus : 0 < αminus) (hsstar : 0 < sstar)
      (hscale : ∀ᶠ n in atTop,
        αminus ≤ P.scale (φ n) ∧ P.scale (φ n) ≤ αplus)
      (hshape : ∀ᶠ n in atTop, sstar ≤ P.shape (φ n))
      (hold : Tendsto (fun n => P.oldLoss (φ n)) atTop (nhds 0))
      (hnew : Tendsto (fun n => P.newInnovation (φ n)) atTop (nhds 0))
      (hdiamond : Tendsto (fun n => P.diamondResidual (φ n)) atTop (nhds 0))
      (hanchor : Tendsto (fun n => P.anchorResidual (φ n)) atTop (nhds 0))
      (hmodulus : Tendsto (fun n => P.modulus (φ n)) atTop (nhds k))
      (hunresolved : ¬ P.anchorResolves k)

/-- A nonnegative scalar sequence has a subsequence which vanishes or stays
uniformly away from zero. -/
theorem nonnegative_subsequence_zero_or_away (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (Tendsto (fun n => a (φ n)) atTop (nhds 0) ∨
        ∃ ε > 0, ∀ᶠ n in atTop, ε ≤ a (φ n)) := by
  obtain ⟨φ, hφ, hinf | hzero | ⟨l, hl, hlim⟩⟩ :=
    metric_profile_alternative a ha
  · refine ⟨φ, hφ, Or.inr ⟨1, by norm_num, ?_⟩⟩
    exact hinf.eventually (eventually_ge_atTop (1 : ℝ))
  · exact ⟨φ, hφ, Or.inl hzero⟩
  · refine ⟨φ, hφ, Or.inr ⟨l / 2, by linarith, ?_⟩⟩
    obtain ⟨N, hball⟩ :=
      (Metric.tendsto_atTop.1 hlim) (l / 2) (by linarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn := hball n hn
    rw [Real.dist_eq] at hn
    linarith [abs_lt.mp hn]

/-- A positive scalar limit supplies uniform lower and upper scale bounds. -/
theorem positive_limit_eventually_bounded {a : ℕ → ℝ} {l : ℝ}
    (hl : 0 < l) (hlim : Tendsto a atTop (nhds l)) :
    ∀ᶠ n in atTop, l / 2 ≤ a n ∧ a n ≤ 2 * l := by
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hlim) (l / 2) (by linarith)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hd := hN n hn
  rw [Real.dist_eq] at hd
  rcases abs_lt.mp hd with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- A nonnegative summand of a sequence converging to zero also converges to
zero.  This is the analytic form of the source/diamond Pythagoras splitting
used in the profile proof. -/
theorem tendsto_zero_of_nonneg_of_le {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n ≤ b n)
    (hb : Tendsto b atTop (nhds 0)) :
    Tendsto a atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hb ha hab

/-- Pull an eventual assertion through a strictly increasing subsequence. -/
theorem eventually_subsequence {p : ℕ → Prop} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hp : ∀ᶠ n in atTop, p n) :
    ∀ᶠ n in atTop, p (φ n) :=
  hφ.tendsto_atTop.eventually hp

/-- `thm:metric-profile-alternative`, complete witness-bearing form.

Every certified cofinal metric family has a cofinal subsequence in precisely
one of the manuscript's positive/stable or negative obstruction classes.
The constructors retain all displayed witnesses, so no obstruction is hidden
behind a bare disjunction. -/
theorem metric_obstruction_profile_alternative
    {d : ℕ} {K : Type u} [MetricSpace K] [CompactSpace K]
    (P : CertifiedMetricObstructionProfile d K) :
    Nonempty (MetricProfileBranch P) := by
  obtain ⟨φ, hφ, hscaleInf | hscaleZero | ⟨l, hl, hscaleLim⟩⟩ :=
    metric_profile_alternative P.scale (fun n => (P.scale_pos n).le)
  · exact ⟨MetricProfileBranch.scaleBlowup φ hφ hscaleInf⟩
  · exact ⟨MetricProfileBranch.scaleCollapse φ hφ hscaleZero⟩
  · have hscaleBounds : ∀ᶠ n in atTop,
        l / 2 ≤ P.scale (φ n) ∧ P.scale (φ n) ≤ 2 * l :=
      positive_limit_eventually_bounded hl hscaleLim
    obtain ⟨ψ, hψ, hshapeZero | ⟨sstar, hsstar, hshapeAway⟩⟩ :=
      nonnegative_subsequence_zero_or_away
        (fun n => P.shape (φ n)) (fun n => (P.shape_pos (φ n)).le)
    · let ξ : ℕ → ℕ := φ ∘ ψ
      have hξ : StrictMono ξ := hφ.comp hψ
      have hscaleξ : ∀ᶠ n in atTop,
          l / 2 ≤ P.scale (ξ n) ∧ P.scale (ξ n) ≤ 2 * l := by
        simpa [ξ, Function.comp_def] using
          eventually_subsequence hψ hscaleBounds
      have hshapeξ : Tendsto (fun n => P.shape (ξ n)) atTop (nhds 0) := by
        simpa [ξ, Function.comp_def] using hshapeZero
      exact ⟨MetricProfileBranch.shapeCollapse ξ hξ (l / 2) (2 * l)
        (by linarith) hscaleξ hshapeξ
        (fun n => P.shape_vector_normalized (ξ n))
        (fun n => P.shape_eigenvector (ξ n))⟩
    · let ξ : ℕ → ℕ := φ ∘ ψ
      have hξ : StrictMono ξ := hφ.comp hψ
      have hscaleξ : ∀ᶠ n in atTop,
          l / 2 ≤ P.scale (ξ n) ∧ P.scale (ξ n) ≤ 2 * l := by
        simpa [ξ, Function.comp_def] using
          eventually_subsequence hψ hscaleBounds
      have hshapeξ : ∀ᶠ n in atTop, sstar ≤ P.shape (ξ n) := by
        simpa [ξ, Function.comp_def] using hshapeAway
      obtain ⟨θ, hθ, hsupportZero | ⟨εs, hεs, hsupportAway⟩⟩ :=
        nonnegative_subsequence_zero_or_away
          (fun n => P.supportResidual (ξ n))
          (fun n => add_nonneg (P.old_loss_nonneg (ξ n))
            (P.new_innovation_nonneg (ξ n)))
      · let ζ : ℕ → ℕ := ξ ∘ θ
        have hζ : StrictMono ζ := hξ.comp hθ
        have hscaleζ : ∀ᶠ n in atTop,
            l / 2 ≤ P.scale (ζ n) ∧ P.scale (ζ n) ≤ 2 * l := by
          simpa [ζ, Function.comp_def] using
            eventually_subsequence hθ hscaleξ
        have hshapeζ : ∀ᶠ n in atTop, sstar ≤ P.shape (ζ n) := by
          simpa [ζ, Function.comp_def] using
            eventually_subsequence hθ hshapeξ
        have hsupportζ :
            Tendsto (fun n => P.supportResidual (ζ n)) atTop (nhds 0) := by
          simpa [ζ, Function.comp_def] using hsupportZero
        obtain ⟨χ, hχ, hcoherenceZero | ⟨εc, hεc, hcoherenceAway⟩⟩ :=
          nonnegative_subsequence_zero_or_away
            (fun n => P.coherenceResidual (ζ n))
            (fun n => add_nonneg (P.diamond_nonneg (ζ n))
              (P.anchor_nonneg (ζ n)))
        · let η : ℕ → ℕ := ζ ∘ χ
          have hη : StrictMono η := hζ.comp hχ
          have hscaleη : ∀ᶠ n in atTop,
              l / 2 ≤ P.scale (η n) ∧ P.scale (η n) ≤ 2 * l := by
            simpa [η, Function.comp_def] using
              eventually_subsequence hχ hscaleζ
          have hshapeη : ∀ᶠ n in atTop, sstar ≤ P.shape (η n) := by
            simpa [η, Function.comp_def] using
              eventually_subsequence hχ hshapeζ
          have hsupportη :
              Tendsto (fun n => P.supportResidual (η n)) atTop (nhds 0) := by
            simpa [η, Function.comp_def] using
              hsupportζ.comp hχ.tendsto_atTop
          have hcoherenceη :
              Tendsto (fun n => P.coherenceResidual (η n)) atTop (nhds 0) := by
            simpa [η, Function.comp_def] using hcoherenceZero
          have holdη : Tendsto (fun n => P.oldLoss (η n)) atTop (nhds 0) :=
            tendsto_zero_of_nonneg_of_le
              (fun n => P.old_loss_nonneg (η n))
              (fun n => by
                unfold MetricObstructionProfile.supportResidual
                exact le_add_of_nonneg_right (P.new_innovation_nonneg (η n))) hsupportη
          have hnewη : Tendsto (fun n => P.newInnovation (η n)) atTop (nhds 0) :=
            tendsto_zero_of_nonneg_of_le
              (fun n => P.new_innovation_nonneg (η n))
              (fun n => by
                unfold MetricObstructionProfile.supportResidual
                exact le_add_of_nonneg_left (P.old_loss_nonneg (η n))) hsupportη
          have hdiamondη : Tendsto (fun n => P.diamondResidual (η n)) atTop (nhds 0) :=
            tendsto_zero_of_nonneg_of_le
              (fun n => P.diamond_nonneg (η n))
              (fun n => by
                unfold MetricObstructionProfile.coherenceResidual
                exact le_add_of_nonneg_right (P.anchor_nonneg (η n))) hcoherenceη
          have hanchorη : Tendsto (fun n => P.anchorResidual (η n)) atTop (nhds 0) :=
            tendsto_zero_of_nonneg_of_le
              (fun n => P.anchor_nonneg (η n))
              (fun n => by
                unfold MetricObstructionProfile.coherenceResidual
                exact le_add_of_nonneg_left (P.diamond_nonneg (η n))) hcoherenceη
          obtain ⟨k, ω, hω, hmodulus⟩ :=
            CompactSpace.tendsto_subseq (fun n => P.modulus (η n))
          let ρ : ℕ → ℕ := η ∘ ω
          have hρ : StrictMono ρ := hη.comp hω
          have hscaleρ : ∀ᶠ n in atTop,
              l / 2 ≤ P.scale (ρ n) ∧ P.scale (ρ n) ≤ 2 * l := by
            simpa [ρ, Function.comp_def] using
              eventually_subsequence hω hscaleη
          have hshapeρ : ∀ᶠ n in atTop, sstar ≤ P.shape (ρ n) := by
            simpa [ρ, Function.comp_def] using
              eventually_subsequence hω hshapeη
          have holdρ : Tendsto (fun n => P.oldLoss (ρ n)) atTop (nhds 0) := by
            simpa [ρ, Function.comp_def] using holdη.comp hω.tendsto_atTop
          have hnewρ : Tendsto (fun n => P.newInnovation (ρ n)) atTop (nhds 0) := by
            simpa [ρ, Function.comp_def] using hnewη.comp hω.tendsto_atTop
          have hdiamondρ : Tendsto (fun n => P.diamondResidual (ρ n)) atTop (nhds 0) := by
            simpa [ρ, Function.comp_def] using hdiamondη.comp hω.tendsto_atTop
          have hanchorρ : Tendsto (fun n => P.anchorResidual (ρ n)) atTop (nhds 0) := by
            simpa [ρ, Function.comp_def] using hanchorη.comp hω.tendsto_atTop
          have hmodulusρ : Tendsto (fun n => P.modulus (ρ n)) atTop (nhds k) := by
            simpa [ρ, Function.comp_def] using hmodulus
          by_cases hk : P.anchorResolves k
          · exact ⟨MetricProfileBranch.stable ρ hρ (l / 2) (2 * l) sstar k
              (by linarith) (by linarith) hsstar hscaleρ hshapeρ
              holdρ hnewρ hdiamondρ hanchorρ hmodulusρ hk⟩
          · exact ⟨MetricProfileBranch.unresolvedModulus ρ hρ
              (l / 2) (2 * l) sstar k (by linarith) hsstar
              hscaleρ hshapeρ holdρ hnewρ hdiamondρ hanchorρ hmodulusρ hk⟩
        · let η : ℕ → ℕ := ζ ∘ χ
          have hη : StrictMono η := hζ.comp hχ
          have hscaleη : ∀ᶠ n in atTop,
              l / 2 ≤ P.scale (η n) ∧ P.scale (η n) ≤ 2 * l := by
            simpa [η, Function.comp_def] using
              eventually_subsequence hχ hscaleζ
          have hshapeη : ∀ᶠ n in atTop, sstar ≤ P.shape (η n) := by
            simpa [η, Function.comp_def] using
              eventually_subsequence hχ hshapeζ
          have hsupportη :
              Tendsto (fun n => P.supportResidual (η n)) atTop (nhds 0) := by
            simpa [η, Function.comp_def] using
              hsupportζ.comp hχ.tendsto_atTop
          have hawayη : ∀ᶠ n in atTop,
              εc ≤ P.coherenceResidual (η n) := by
            simpa [η, Function.comp_def] using hcoherenceAway
          exact ⟨MetricProfileBranch.coherenceFailure η hη
            (l / 2) (2 * l) sstar εc (by linarith) hsstar hεc
            hscaleη hshapeη hsupportη hawayη
            (fun n => ⟨P.diamond_vector_normalized (η n),
              P.anchor_vector_normalized (η n)⟩)⟩
      · let ζ : ℕ → ℕ := ξ ∘ θ
        have hζ : StrictMono ζ := hξ.comp hθ
        have hscaleζ : ∀ᶠ n in atTop,
            l / 2 ≤ P.scale (ζ n) ∧ P.scale (ζ n) ≤ 2 * l := by
          simpa [ζ, Function.comp_def] using
            eventually_subsequence hθ hscaleξ
        have hshapeζ : ∀ᶠ n in atTop, sstar ≤ P.shape (ζ n) := by
          simpa [ζ, Function.comp_def] using
            eventually_subsequence hθ hshapeξ
        have hawayζ : ∀ᶠ n in atTop,
            εs ≤ P.supportResidual (ζ n) := by
          simpa [ζ, Function.comp_def] using hsupportAway
        exact ⟨MetricProfileBranch.supportChange ζ hζ
          (l / 2) (2 * l) sstar εs (by linarith) hsstar hεs
          hscaleζ hshapeζ hawayζ
          (fun n => ⟨P.old_source_normalized (ζ n),
            P.new_source_normalized (ζ n)⟩)⟩

end NCG
