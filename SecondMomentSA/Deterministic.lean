module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import SecondMomentSA.Barrier

public section

open Filter
open scoped BigOperators Topology

namespace SecondMomentSA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma inner_lower (u v : E) : -(‖u‖ * ‖v‖) ≤ inner ℝ u v :=
  (neg_le_neg (abs_real_inner_le_norm u v)).trans (neg_abs_le _)

/-- Removing a convergent series of additive errors does not change the asymptotic radius. -/
theorem pathwise_convergence (x noise : ℕ → E) (D : E → E) (target : E)
    (decay μ L C εbar : ℝ) (α : ℕ → ℝ)
    (hDecay : 0 ≤ decay) (hμ : 0 < μ) (hL : 0 ≤ L) (hC : 0 ≤ C) (hε : 0 ≤ εbar)
    (hAim : ∀ x, μ * ‖x - target‖ ^ 2 ≤ inner ℝ (D x + decay • x) (x - target))
    (hGrowth : ∀ x, ‖D x‖ ≤ L * ‖x - target‖ + C)
    (bias : ℕ → E)
    (hBias : limsup (fun t => (‖bias t‖ : EReal)) atTop ≤ εbar)
    (hα : ∀ t, 0 ≤ α t) (hdiv : ¬ Summable α) (hsq : Summable (fun t => α t ^ 2))
    (hrec : ∀ t, x (t + 1) = x t - α t • (D (x t) + decay • x t + bias t) + noise t)
    (hnoise : ∃ z, Tendsto (fun t => ∑ s ∈ Finset.range t, noise s) atTop (𝓝 z)) :
    limsup (fun t => (‖x t - target‖ : EReal)) atTop ≤ ((εbar / μ : ℝ) : EReal) := by
  obtain ⟨z, hz⟩ := hnoise
  let tail (t : ℕ) := z - ∑ s ∈ Finset.range t, noise s
  let u (t : ℕ) := x t - target
  let v (t : ℕ) := u t + tail t
  let drift (t : ℕ) := D (x t) + decay • x t + bias t
  have hTail : Tendsto tail atTop (𝓝 0) := by
    simpa [tail] using (tendsto_const_nhds (x := z)).sub hz
  have hTailNorm : Tendsto (fun t => ‖tail t‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hTail.norm
  have hV (t : ℕ) : v (t + 1) = v t - α t • drift t := by
    dsimp [v, u, tail, drift]
    rw [hrec t, Finset.sum_range_succ]
    abel
  have hUV (t : ℕ) : ‖u t‖ ≤ ‖v t‖ + ‖tail t‖ := by
    simpa [v, norm_neg] using norm_add_le (v t) (-tail t)
  have hαzero : Tendsto α atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp hsq.tendsto_atTop_zero
    simpa [Function.comp_def, Real.sqrt_sq (hα _)] using h
  have eventual_radius (r : ℝ) (hr : εbar / μ < r) : ∀ᶠ t in atTop, ‖u t‖ < r := by
    obtain ⟨r₀, hr₀, hr₀r⟩ := exists_between hr
    obtain ⟨r₁, hr₀r₁, hr₁r⟩ := exists_between hr₀r
    obtain ⟨r₂, hr₁r₂, hr₂r⟩ := exists_between hr₁r
    have hr₀pos : 0 < r₀ := (div_nonneg hε hμ.le).trans_lt hr₀
    have hr₁pos : 0 < r₁ := hr₀pos.trans hr₀r₁
    have hr₂pos : 0 < r₂ := hr₁pos.trans hr₁r₂
    have hεμ : εbar < μ * r₀ := by
      rw [mul_comm]
      exact (div_lt_iff₀ hμ).mp hr₀
    obtain ⟨B, hεB, hBr₀⟩ := exists_between hεμ
    have hBpos : 0 < B := hε.trans_lt hεB
    let A := L + decay
    let G := C + decay * ‖target‖ + B
    let K := A + G / r₀ + 1
    let k := μ - B / r₀
    let I := A * (r₁ + 1) + G
    have hA : 0 ≤ A := add_nonneg hL hDecay
    have hG : 0 ≤ G := by dsimp [G]; positivity
    have hK : 0 < K := by dsimp [K]; positivity
    have hk : 0 < k := by
      dsimp [k]
      apply sub_pos.mpr
      exact (div_lt_iff₀ hr₀pos).mpr hBr₀
    have hI : 0 ≤ I := by dsimp [I]; positivity
    have hBiasEventually : ∀ᶠ t in atTop, ‖bias t‖ < B := by
      have h := eventually_lt_of_limsup_lt (hBias.trans_lt (EReal.coe_lt_coe hεB))
      exact h.mono fun t ht => EReal.coe_lt_coe_iff.mp ht
    have hDriftBound (t : ℕ) (ht : ‖bias t‖ ≤ B) :
        ‖drift t‖ ≤ A * ‖u t‖ + G := by
      have hx : ‖x t‖ ≤ ‖u t‖ + ‖target‖ := by
        simpa [u] using norm_add_le (u t) target
      have hxd := mul_le_mul_of_nonneg_left hx hDecay
      calc
        ‖drift t‖ ≤ ‖D (x t) + decay • x t‖ + ‖bias t‖ := norm_add_le _ _
        _ ≤ ‖D (x t)‖ + ‖decay • x t‖ + ‖bias t‖ :=
          add_le_add (norm_add_le _ _) le_rfl
        _ ≤ A * ‖u t‖ + G := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hDecay]
          have hg : ‖D (x t)‖ ≤ L * ‖u t‖ + C := hGrowth (x t)
          dsimp [A, G]
          nlinarith only [hg, ht, hxd]
    have hdown : ∀ᶠ t in atTop, r₁ ^ 2 ≤ ‖v t‖ ^ 2 →
        ‖v (t + 1)‖ ^ 2 ≤ ‖v t‖ ^ 2 - (k * r₀ ^ 2 / 2) * α t := by
      have hsmallTail := hTailNorm.eventually_lt_const (show 0 < r₁ - r₀ by linarith)
      have hsmallTailK : ∀ᶠ t in atTop, ‖tail t‖ * K < k * r₀ / 2 := by
        have ht : Tendsto (fun t => ‖tail t‖ * K) atTop (𝓝 0) := by
          simpa only [zero_mul] using hTailNorm.mul_const K
        exact ht.eventually_lt_const (by positivity)
      have hsmallAlpha : ∀ᶠ t in atTop, α t * K ^ 2 < k / 2 := by
        have ht : Tendsto (fun t => α t * K ^ 2) atTop (𝓝 0) := by
          simpa only [zero_mul] using hαzero.mul_const (K ^ 2)
        exact ht.eventually_lt_const (by positivity)
      filter_upwards [hBiasEventually, hsmallTail, hsmallTailK, hsmallAlpha] with t hb ht htK ha
      intro hv
      have hv' : r₁ ≤ ‖v t‖ := by
        by_contra! hn
        exact (not_lt_of_ge hv) (pow_lt_pow_left₀ hn (norm_nonneg _) (by decide))
      have hvt : ‖v t‖ ≤ ‖u t‖ + ‖tail t‖ := norm_add_le _ _
      have hu : r₀ ≤ ‖u t‖ := by linarith
      have hUpos := hr₀pos.trans_le hu
      have hGle : G ≤ G / r₀ * ‖u t‖ := by
        calc
          G = G / r₀ * r₀ := by field_simp
          _ ≤ G / r₀ * ‖u t‖ := mul_le_mul_of_nonneg_left hu (div_nonneg hG hr₀pos.le)
      have hDrift := hDriftBound t hb.le
      have hDriftK : ‖drift t‖ ≤ K * ‖u t‖ := by
        dsimp [K]
        nlinarith only [hDrift, hGle, hUpos]
      have hBiasInner : -(B * ‖u t‖) ≤ inner ℝ (bias t) (u t) :=
        (neg_le_neg (mul_le_mul_of_nonneg_right hb.le (norm_nonneg _))).trans
          (inner_lower _ _)
      have hBu : B * ‖u t‖ ≤ (B / r₀) * ‖u t‖ ^ 2 := by
        have h : B = (B / r₀) * r₀ := by field_simp
        calc
          B * ‖u t‖ = ((B / r₀) * r₀) * ‖u t‖ := congrArg (· * ‖u t‖) h
          _ ≤ ((B / r₀) * ‖u t‖) * ‖u t‖ := by gcongr
          _ = _ := by ring
      have hDriftU : k * ‖u t‖ ^ 2 ≤ inner ℝ (drift t) (u t) := by
        rw [show drift t = D (x t) + decay • x t + bias t from rfl, inner_add_left]
        have him : μ * ‖u t‖ ^ 2 ≤ inner ℝ (D (x t) + decay • x t) (u t) := hAim (x t)
        dsimp [k]
        nlinarith only [him, hBiasInner, hBu]
      have hErr : ‖drift t‖ * ‖tail t‖ ≤ k / 2 * ‖u t‖ ^ 2 := by
        calc
          ‖drift t‖ * ‖tail t‖ ≤ (K * ‖u t‖) * ‖tail t‖ :=
            mul_le_mul_of_nonneg_right hDriftK (norm_nonneg _)
          _ = (‖tail t‖ * K) * ‖u t‖ := by ring
          _ ≤ (k * r₀ / 2) * ‖u t‖ := mul_le_mul_of_nonneg_right htK.le hUpos.le
          _ ≤ k / 2 * ‖u t‖ ^ 2 := by
            have h := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hu (show 0 ≤ k / 2 by positivity)) hUpos.le
            nlinarith only [h]
      have hDriftV : k / 2 * ‖u t‖ ^ 2 ≤ inner ℝ (drift t) (v t) := by
        rw [show v t = u t + tail t from rfl, inner_add_right]
        have ht' := inner_lower (drift t) (tail t)
        linarith only [hDriftU, hErr, ht']
      have hαt := hα t
      have hDriftSq : ‖drift t‖ ^ 2 ≤ (K * ‖u t‖) ^ 2 := by
        gcongr
      have hInnerStep := mul_le_mul_of_nonneg_left hDriftV (hα t)
      have hSqStep : α t ^ 2 * ‖drift t‖ ^ 2 ≤ α t * (k / 2 * ‖u t‖ ^ 2) := by
        calc
          α t ^ 2 * ‖drift t‖ ^ 2 ≤ α t ^ 2 * (K * ‖u t‖) ^ 2 := by gcongr
          _ = α t * ((α t * K ^ 2) * ‖u t‖ ^ 2) := by ring
          _ ≤ α t * (k / 2 * ‖u t‖ ^ 2) := by gcongr
      have hFinalStep : (k * r₀ ^ 2 / 2) * α t ≤ α t * (k / 2 * ‖u t‖ ^ 2) := by
        calc
          _ = α t * (k / 2 * r₀ ^ 2) := by ring
          _ ≤ _ := by gcongr
      rw [hV, norm_sub_sq_real, real_inner_smul_right, ← real_inner_comm (v t) (drift t),
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα t), mul_pow]
      nlinarith only [hInnerStep, hSqStep, hFinalStep]
    have hup : ∀ᶠ t in atTop, ‖v t‖ ^ 2 < r₁ ^ 2 → ‖v (t + 1)‖ ^ 2 < r₂ ^ 2 := by
      have hsmallTail := hTailNorm.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
      have hsmallAlpha : ∀ᶠ t in atTop, α t * I < r₂ - r₁ := by
        have ht : Tendsto (fun t => α t * I) atTop (𝓝 0) := by
          simpa only [zero_mul] using hαzero.mul_const I
        exact ht.eventually_lt_const (sub_pos.mpr hr₁r₂)
      filter_upwards [hBiasEventually, hsmallTail, hsmallAlpha] with t hb ht ha
      intro hv
      have hv' : ‖v t‖ < r₁ := by
        by_contra! hn
        exact (not_le_of_gt hv) (pow_le_pow_left₀ hr₁pos.le hn 2)
      have hu : ‖u t‖ ≤ r₁ + 1 := by linarith [hUV t]
      have hbound := (hDriftBound t hb.le).trans
        (add_le_add (mul_le_mul_of_nonneg_left hu hA) le_rfl)
      have hnorm : ‖v (t + 1)‖ < r₂ := by
        rw [hV]
        have hsub := norm_sub_le (v t) (α t • drift t)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα t)] at hsub
        linarith only [hsub, hv', ha, mul_le_mul_of_nonneg_left hbound (hα t)]
      exact pow_lt_pow_left₀ hnorm (norm_nonneg _) (by decide)
    have hBarrier : ∀ᶠ t in atTop, ‖v t‖ ^ 2 < r₂ ^ 2 :=
      eventually_lt_of_drift (fun t => ‖v t‖ ^ 2) α (r₁ ^ 2) (r₂ ^ 2) (k * r₀ ^ 2 / 2)
        (by positivity) hα hdiv hdown hup (pow_lt_pow_left₀ hr₁r₂ hr₁pos.le (by decide))
        (fun _ => sq_nonneg _)
    have hsmallTail := hTailNorm.eventually_lt_const (sub_pos.mpr hr₂r)
    filter_upwards [hBarrier, hsmallTail] with t hv ht
    have hv' : ‖v t‖ < r₂ := by
      by_contra! hn
      exact (not_le_of_gt hv) (pow_le_pow_left₀ hr₂pos.le hn 2)
    linarith only [hUV t, hv', ht]
  by_contra! h
  obtain ⟨r, hr, hrlim⟩ := EReal.exists_between_coe_real h
  have hEvent := (eventual_radius r (EReal.coe_lt_coe_iff.mp hr)).mono
    (fun _ ht => EReal.coe_le_coe ht.le)
  exact (not_le_of_gt hrlim) (limsup_le_of_le (by isBoundedDefault) hEvent)

end SecondMomentSA
