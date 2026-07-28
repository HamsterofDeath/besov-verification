import BesovVerification.Definitions

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/-- The elementary three-point estimate used by the anchor-set argument. -/
theorem differenceSq_triangle {X : Type*} (u : X → ℝ) (x y z : X) :
    differenceSq u x y ≤
      2 * differenceSq u x z + 2 * differenceSq u z y := by
  have hreal :
      (u x - u y) ^ 2 ≤
        2 * (u x - u z) ^ 2 + 2 * (u z - u y) ^ 2 := by
    nlinarith [sq_nonneg (u x - 2 * u z + u y)]
  have henn := ENNReal.ofReal_le_ofReal hreal
  have hnonneg : 0 ≤ 2 * (u x - u z) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hnonneg' : 0 ≤ 2 * (u z - u y) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  simpa only [differenceSq, ENNReal.ofReal_add hnonneg hnonneg',
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using henn

/-- Open metric balls are monotone in their radius. -/
theorem localEnergy_mono {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (u : X → ℝ) :
    Monotone (localEnergy ν u) := by
  intro r t hrt
  apply lintegral_mono
  intro x
  exact lintegral_mono' (Measure.restrict_mono_set ν (Metric.ball_subset_ball hrt)) le_rfl

end BesovVerification
