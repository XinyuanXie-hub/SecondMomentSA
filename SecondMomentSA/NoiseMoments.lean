module

public import Mathlib.Probability.Process.Filtration
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

open MeasureTheory

namespace SecondMomentSA

variable {Ω E : Type*} [ambient : MeasurableSpace Ω] {P : Measure Ω}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Scaling the centered update by square-summable steps gives martingale differences
with summable second moments whenever the conditional variance is uniformly bounded. -/
theorem noise_moments [IsProbabilityMeasure P]
    (F : Filtration ℕ ambient) (Z : ℕ → Ω → E) (α : ℕ → ℝ) (b : ℝ)
    (hZ : ∀ t, StronglyMeasurable[F (t + 1)] (Z t))
    (hIntegrable : ∀ t, Integrable (Z t) P)
    (hVariance : ∀ t,
      let residualSq := fun ω => ‖Z t ω - P[Z t | F t] ω‖ ^ 2
      Integrable residualSq P ∧ ∀ᵐ ω ∂P, P[residualSq | F t] ω ≤ b)
    (hStepSquareSummable : Summable (fun t => α t ^ 2)) :
    let noise := fun t ω => α t • (P[Z t | F t] ω - Z t ω)
    (∀ t, StronglyMeasurable[F (t + 1)] (noise t)) ∧
    (∀ t, Integrable (fun ω => ‖noise t ω‖ ^ 2) P) ∧
    (∀ t, P[noise t | F t] =ᵐ[P] 0) ∧
    Summable (fun t => ∫ ω, ‖noise t ω‖ ^ 2 ∂P) := by
  intro noise
  let residualSq := fun t ω => ‖Z t ω - P[Z t | F t] ω‖ ^ 2
  have noiseNormSq (t : ℕ) (ω : Ω) : ‖noise t ω‖ ^ 2 = α t ^ 2 * residualSq t ω := by
    simp [noise, residualSq, norm_smul, ← norm_sub_rev (Z t ω), mul_pow, Real.norm_eq_abs,
      sq_abs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    have hCond : StronglyMeasurable[F (t + 1)] (P[Z t | F t]) :=
      stronglyMeasurable_condExp.mono (F.mono (Nat.le_succ t))
    exact (hCond.sub (hZ t)).const_smul (α t)
  · intro t
    simpa only [noiseNormSq] using ((hVariance t).1.const_mul (α t ^ 2))
  · intro t
    have hMean : P[(P[Z t | F t] - Z t) | F t] =ᵐ[P] 0 := by
      calc
        P[(P[Z t | F t] - Z t) | F t] =ᵐ[P]
            P[P[Z t | F t] | F t] - P[Z t | F t] :=
          condExp_sub integrable_condExp (hIntegrable t) (F t)
        _ =ᵐ[P] 0 := by
          rw [condExp_of_stronglyMeasurable (F.le t) stronglyMeasurable_condExp
            integrable_condExp, sub_self]
    calc
      P[noise t | F t] =ᵐ[P] α t • P[(P[Z t | F t] - Z t) | F t] :=
        condExp_smul (α t) (P[Z t | F t] - Z t) (F t)
      _ =ᵐ[P] 0 := by
        filter_upwards [hMean] with ω hω
        simp [Pi.smul_apply, hω]
  · refine Summable.of_nonneg_of_le
      (fun t => integral_nonneg (fun ω => sq_nonneg ‖noise t ω‖)) ?_
      (hStepSquareSummable.mul_right b)
    intro t
    have hResidualBound : (∫ ω, residualSq t ω ∂P) ≤ b := by
      rw [← integral_condExp (F.le t)]
      simpa using integral_mono_ae integrable_condExp (integrable_const b) (hVariance t).2
    simp_rw [noiseNormSq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hResidualBound (sq_nonneg _)

end SecondMomentSA
