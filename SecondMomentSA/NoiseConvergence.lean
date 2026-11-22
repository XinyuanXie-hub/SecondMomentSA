module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Martingale.Convergence

public section

open Filter MeasureTheory
open scoped BigOperators Topology

namespace SecondMomentSA

variable {Ω : Type*} [ambient : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private theorem ae_tendsto_scalar_noise_sum (F : Filtration ℕ ambient)
    (noise : ℕ → Ω → ℝ)
    (hmeas : ∀ t, StronglyMeasurable[F (t + 1)] (noise t))
    (hlp : ∀ t, MemLp (noise t) 2 P)
    (hzero : ∀ t, P[noise t | F t] =ᵐ[P] 0)
    (R : ℝ) (hbound : ∀ t, ∑ s ∈ Finset.range t, (∫ ω, (noise s ω) ^ 2 ∂P) ≤ R) :
    ∀ᵐ ω ∂P, ∃ z, Tendsto (fun t => ∑ s ∈ Finset.range t, noise s ω) atTop (𝓝 z) := by
  let sums : ℕ → Ω → ℝ := fun t ω => ∑ s ∈ Finset.range t, noise s ω
  have hrec (t : ℕ) : sums (t + 1) = sums t + noise t := by
    funext ω
    exact Finset.sum_range_succ _ _
  have hadapt : StronglyAdapted F sums := by
    intro t
    induction t with
    | zero =>
      simp only [sums, Finset.range_zero, Finset.sum_empty]
      exact stronglyMeasurable_const
    | succ t ih =>
      rw [hrec]
      exact (ih.mono (F.mono (Nat.le_succ t))).add (hmeas t)
  have hsumlp (t : ℕ) : MemLp (sums t) 2 P := by
    induction t with
    | zero => simp [sums]
    | succ t ih =>
      rw [hrec]
      exact ih.add (hlp t)
  have hsumInt (t : ℕ) : Integrable (sums t) P :=
    (hsumlp t).integrable (by norm_num)
  have hmart : Martingale sums F P := by
    apply martingale_of_condExp_sub_eq_zero_nat hadapt hsumInt
    intro t
    rw [hrec, add_sub_cancel_left]
    exact hzero t
  have hcross (t : ℕ) : (∫ ω, sums t ω * noise t ω ∂P) = 0 := by
    have hprod : Integrable (sums t * noise t) P := (hsumlp t).integrable_mul (hlp t)
    have hpull : P[sums t * noise t | F t] =ᵐ[P] sums t * P[noise t | F t] :=
      condExp_mul_of_stronglyMeasurable_left (hadapt t) hprod ((hlp t).integrable (by norm_num))
    have hcond : P[sums t * noise t | F t] =ᵐ[P] 0 := by
      filter_upwards [hpull, hzero t] with ω h₁ h₂
      simp [h₁, h₂]
    calc
      (∫ ω, sums t ω * noise t ω ∂P) = ∫ ω, P[sums t * noise t | F t] ω ∂P :=
        (integral_condExp (F.le t)).symm
      _ = 0 := by rw [integral_congr_ae hcond]; simp
  have henergy (t : ℕ) :
      (∫ ω, (sums t ω) ^ 2 ∂P) = ∑ s ∈ Finset.range t, (∫ ω, (noise s ω) ^ 2 ∂P) := by
    induction t with
    | zero => simp [sums]
    | succ t ih =>
      have hs := (hsumlp t).integrable_sq
      have hn := (hlp t).integrable_sq
      have hp : Integrable (fun ω => sums t ω * noise t ω) P :=
        (hsumlp t).integrable_mul (hlp t)
      have heq : (fun ω => (sums (t + 1) ω) ^ 2) =
          fun ω => ((sums t ω) ^ 2 + 2 * (sums t ω * noise t ω)) + (noise t ω) ^ 2 := by
        funext ω
        rw [hrec, Pi.add_apply]
        ring
      have hadd :
          (∫ ω, ((sums t ω) ^ 2 + 2 * (sums t ω * noise t ω)) + (noise t ω) ^ 2 ∂P) =
          (∫ ω, (sums t ω) ^ 2 + 2 * (sums t ω * noise t ω) ∂P) +
            (∫ ω, (noise t ω) ^ 2 ∂P) := by
        simpa only [Pi.add_apply] using integral_add (hs.add (hp.const_mul 2)) hn
      rw [heq, hadd, integral_add hs (hp.const_mul 2), integral_const_mul, hcross, mul_zero,
        add_zero, ih, Finset.sum_range_succ]
  apply hmart.submartingale.exists_ae_tendsto_of_bdd (R := Real.toNNReal (1 + R))
  intro t
  rw [eLpNorm_one_eq_lintegral_enorm (hsumInt t).aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm (hsumInt t)]
  change ENNReal.ofReal _ ≤ ENNReal.ofReal (1 + R)
  apply ENNReal.ofReal_le_ofReal
  have hpoint (ω : Ω) : ‖sums t ω‖ ≤ 1 + (sums t ω) ^ 2 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (sums t ω - 1), sq_nonneg (sums t ω + 1)]
  calc
    (∫ ω, ‖sums t ω‖ ∂P) ≤ ∫ ω, 1 + (sums t ω) ^ 2 ∂P :=
      integral_mono (hsumInt t).norm ((integrable_const 1).add (hsumlp t).integrable_sq) hpoint
    _ = 1 + ∫ ω, (sums t ω) ^ 2 ∂P := by
      rw [integral_add (integrable_const 1) (hsumlp t).integrable_sq]
      simp
    _ ≤ 1 + R := by
      rw [henergy]
      linarith only [hbound t]

/-- A Euclidean-valued martingale difference sequence with summable second moments
has almost surely convergent partial sums. -/
theorem ae_tendsto_noise_sum {ι : Type*} [Fintype ι]
    (F : Filtration ℕ ambient) (noise : ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ t, StronglyMeasurable[F (t + 1)] (noise t))
    (hsqInt : ∀ t, Integrable (fun ω => ‖noise t ω‖ ^ 2) P)
    (hzero : ∀ t, P[noise t | F t] =ᵐ[P] 0)
    (hsummable : Summable (fun t => ∫ ω, ‖noise t ω‖ ^ 2 ∂P)) :
    ∀ᵐ ω ∂P, ∃ z, Tendsto (fun t => ∑ s ∈ Finset.range t, noise s ω) atTop (𝓝 z) := by
  classical
  have hcoord (i : ι) : ∀ᵐ ω ∂P, ∃ z : ℝ,
      Tendsto (fun t => ∑ s ∈ Finset.range t, noise s ω i) atTop (𝓝 z) := by
    let π : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj _ _ i
    have hproj (t : ℕ) : StronglyMeasurable[F (t + 1)] (fun ω => noise t ω i) :=
      π.continuous.comp_stronglyMeasurable (hmeas t)
    have hle (t : ℕ) (ω : Ω) : (noise t ω i) ^ 2 ≤ ‖noise t ω‖ ^ 2 := by
      rw [← sq_abs (noise t ω i)]
      exact pow_le_pow_left₀ (abs_nonneg _) (PiLp.norm_apply_le (noise t ω) i) 2
    have hint (t : ℕ) : Integrable (fun ω => (noise t ω i) ^ 2) P := by
      refine (hsqInt t).mono' (((hproj t).mono (F.le (t + 1))).aestronglyMeasurable.pow 2) ?_
      exact ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle t ω
    apply ae_tendsto_scalar_noise_sum F (fun t ω => noise t ω i) hproj ?_ ?_
      (∑' t, ∫ ω, ‖noise t ω‖ ^ 2 ∂P) ?_
    · intro t
      exact (memLp_two_iff_integrable_sq (((hproj t).mono (F.le (t + 1))).aestronglyMeasurable)).2
        (hint t)
    · intro t
      have hv : MemLp (noise t) 2 P :=
        (memLp_two_iff_integrable_sq_norm (((hmeas t).mono (F.le (t + 1))).aestronglyMeasurable)).2
          (hsqInt t)
      filter_upwards [π.comp_condExp_comm (m := F t) (hv.integrable (by norm_num)), hzero t]
        with ω heq hz
      change P[π ∘ noise t | F t] ω = 0
      rw [← heq, Function.comp_apply, hz, Pi.zero_apply, map_zero]
    · intro t
      calc
        ∑ s ∈ Finset.range t, (∫ ω, (noise s ω i) ^ 2 ∂P) ≤
            ∑ s ∈ Finset.range t, (∫ ω, ‖noise s ω‖ ^ 2 ∂P) :=
          Finset.sum_le_sum fun s _ => integral_mono (hint s) (hsqInt s) (hle s)
        _ ≤ ∑' s, ∫ ω, ‖noise s ω‖ ^ 2 ∂P :=
          hsummable.sum_le_tsum _ fun s _ => integral_nonneg fun ω => sq_nonneg _
  filter_upwards [ae_all_iff.2 hcoord] with ω hω
  choose z hz using hω
  refine ⟨WithLp.toLp 2 z, ?_⟩
  have hc : Tendsto (fun t => WithLp.ofLp (∑ s ∈ Finset.range t, noise s ω)) atTop (𝓝 z) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa using hz i
  exact (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).continuousAt.tendsto.comp hc

end SecondMomentSA
