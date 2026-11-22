module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Process.Filtration

public import SecondMomentSA.Deterministic
public import SecondMomentSA.NoiseConvergence
public import SecondMomentSA.NoiseMoments
import Mathlib.Tactic.Module

public section

open Filter MeasureTheory

namespace SecondMomentSA

/-- Real (m × n) matrices with the Frobenius norm and inner product. -/
abbrev FrobeniusMatrix (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n)

variable {Ω : Type*} [ambient : MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}

/-- Theorem 3.4 (Convergence of practical algorithms), Jiang and Xiao, arXiv:2609.36600v1.

`D x` denotes the conceptual update direction φ(M(x), W(x)).
`Z t ω` denotes the practical update direction φ(M̂ₜ(ω), Ŵₜ(ω)).
`F` is the filtration, `decay` is the weight decay, and `εbar` bounds the asymptotic
conditional bias. Conditional expectations use Mathlib's integrable domain. -/
theorem theorem_3_4 [IsProbabilityMeasure P]
    (F : Filtration ℕ ambient)
    (X Z : ℕ → Ω → FrobeniusMatrix m n)
    (D : FrobeniusMatrix m n → FrobeniusMatrix m n)
    (target : FrobeniusMatrix m n)
    (decay μ L C εbar b : ℝ) (α : ℕ → ℝ)
    (hDecay : 0 ≤ decay)
    (_hX : ∀ t, StronglyMeasurable[F t] (X t))
    (hZ : ∀ t, StronglyMeasurable[F (t + 1)] (Z t))
    (hIntegrable : ∀ t, Integrable (Z t) P)
    (hUpdate : ∀ t, X (t + 1) =ᵐ[P] fun ω =>
      (1 - α t * decay) • X t ω - α t • Z t ω)
    -- Assumption A
    (hμ : 0 < μ) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hAim : ∀ x, μ * ‖x - target‖ ^ 2 ≤ inner ℝ (D x + decay • x) (x - target))
    (hGrowth : ∀ x, ‖D x‖ ≤ L * ‖x - target‖ + C)
    -- Assumption B
    (hεbar : 0 ≤ εbar)
    (hBias : ∀ᵐ ω ∂P,
      limsup (fun t => (‖P[Z t | F t] ω - D (X t ω)‖ : EReal)) atTop ≤ εbar)
    (_hInitial : MemLp (X 0) 2 P)
    -- Condition (a), including integrability of the squared residual.
    (hVariance : ∀ t,
      let residualSq := fun ω => ‖Z t ω - P[Z t | F t] ω‖ ^ 2
      Integrable residualSq P ∧ ∀ᵐ ω ∂P, P[residualSq | F t] ω ≤ b)
    -- Condition (b)
    (hStepNonneg : ∀ t, 0 ≤ α t)
    (hStepDiverges : ¬ Summable α)
    (hStepSquareSummable : Summable (fun t => α t ^ 2)) :
    ∀ᵐ ω ∂P, limsup (fun t => (‖X t ω - target‖ : EReal)) atTop ≤
      ((εbar / μ : ℝ) : EReal) := by
  let noise : ℕ → Ω → FrobeniusMatrix m n :=
    fun t ω => α t • (P[Z t | F t] ω - Z t ω)
  obtain ⟨hNoiseMeas, hNoiseSq, hNoiseZero, hNoiseSummable⟩ :=
    noise_moments F Z α b hZ hIntegrable hVariance hStepSquareSummable
  have hNoise := ae_tendsto_noise_sum F noise
    hNoiseMeas hNoiseSq hNoiseZero hNoiseSummable
  filter_upwards [ae_all_iff.mpr hUpdate, hBias, hNoise] with ω hUpdateω hBiasω hNoiseω
  let bias : ℕ → FrobeniusMatrix m n := fun t => P[Z t | F t] ω - D (X t ω)
  refine pathwise_convergence (fun t => X t ω) (fun t => noise t ω) D target
    decay μ L C εbar α hDecay hμ hL hC hεbar hAim hGrowth bias hBiasω
    hStepNonneg hStepDiverges hStepSquareSummable ?_ hNoiseω
  intro t
  rw [hUpdateω t]
  dsimp [bias, noise]
  module

end SecondMomentSA
