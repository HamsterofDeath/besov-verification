import BesovVerification.Measurability
import BesovVerification.ScaleIntegral

/-!
# Tonelli kernel for the scale energy

This file isolates the extended-nonnegative scalar kernel, including the
diagonal convention needed when the distance is zero.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/--
The kernel obtained by integrating scales from a positive distance `t` up to
`R`.  It is explicitly zero outside `0 < t ≤ R`.
-/
def truncatedScaleKernel (p R t : ℝ) : ℝ≥0∞ :=
  if 0 < t ∧ t ≤ R then
    ENNReal.ofReal ((t ^ (-p) - R ^ (-p)) / p)
  else 0

/-- The scale energy written with the combined exponent `p = α + 2s`. -/
def pScaleEnergy {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (p R : ℝ) (u : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioc 0 R,
    (ENNReal.ofReal r).rpow (-1 - p) * localEnergy ν u r

/-- The double integral with the exact truncated scale kernel. -/
def truncatedEnergy {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (p R : ℝ) (u : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y,
    truncatedScaleKernel p R (dist x y) * differenceSq u x y ∂ν ∂ν

/-- Joint scale-center-point integrand used in the Tonelli calculation. -/
def scaleTripleKernel {X : Type*} [PseudoMetricSpace X]
    (p : ℝ) (u : X → ℝ) (q : (ℝ × X) × X) : ℝ≥0∞ :=
  if dist q.2 q.1.2 < q.1.1 then
    (ENNReal.ofReal q.1.1).rpow (-1 - p) *
      differenceSq u q.1.2 q.2
  else 0

theorem measurable_scaleTripleKernel
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    {p : ℝ} {u : X → ℝ} (hu : Measurable u) :
    Measurable (scaleTripleKernel p u) := by
  unfold scaleTripleKernel
  apply Measurable.ite
  · exact measurableSet_lt (by fun_prop) (by fun_prop)
  · have hw :
        Measurable
          (fun q : (ℝ × X) × X =>
            (ENNReal.ofReal q.1.1).rpow (-1 - p)) :=
      (ENNReal.continuous_rpow_const (y := -1 - p)).measurable.comp
        (ENNReal.measurable_ofReal.comp (by fun_prop))
    have hd :
        Measurable
          (fun q : (ℝ × X) × X =>
            differenceSq u q.1.2 q.2) := by
      unfold differenceSq
      fun_prop
    exact hw.mul hd
  · exact measurable_const

/--
Scalar Tonelli kernel with an arbitrary nonnegative multiplier.  At `t = 0`
the multiplier must vanish; this is precisely the diagonal situation for the
squared difference in a metric space.
-/
theorem lintegral_scale_indicator_mul
    {p R t : ℝ} {a : ℝ≥0∞}
    (hp : 0 < p) (ht0 : 0 ≤ t) (hdiag : t = 0 → a = 0) :
    (∫⁻ r in Set.Ioc 0 R,
      (Set.Ioi t).indicator
        (fun r : ℝ =>
          (ENNReal.ofReal r).rpow (-1 - p) * a) r) =
      truncatedScaleKernel p R t * a := by
  have hweight :
      Measurable
        (fun r : ℝ => (ENNReal.ofReal r).rpow (-1 - p)) :=
    (ENNReal.continuous_rpow_const (y := -1 - p)).measurable.comp
      ENNReal.measurable_ofReal
  by_cases htzero : t = 0
  · subst t
    have ha : a = 0 := hdiag rfl
    subst a
    simp [truncatedScaleKernel]
  have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
  by_cases htR : t ≤ R
  · have hfun :
        (Set.Ioi t).indicator
            (fun r : ℝ =>
              (ENNReal.ofReal r).rpow (-1 - p) * a) =
          fun r =>
            (Set.Ioi t).indicator
              (fun q : ℝ => (ENNReal.ofReal q).rpow (-1 - p)) r * a := by
        funext r
        by_cases hr : r ∈ Set.Ioi t <;> simp [Set.indicator, hr]
    rw [hfun, lintegral_mul_const a (hweight.indicator measurableSet_Ioi),
      lintegral_scale_indicator hp ht htR]
    simp [truncatedScaleKernel, ht, htR]
  · have hzero_ae :
        (Set.Ioi t).indicator
            (fun r : ℝ =>
              (ENNReal.ofReal r).rpow (-1 - p) * a) =ᵐ[
                volume.restrict (Set.Ioc 0 R)] 0 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        have hnlt : ¬t < r :=
          not_lt_of_ge (le_trans hr.2 (lt_of_not_ge htR).le)
        simp [Set.indicator, hnlt]
    rw [lintegral_congr_ae hzero_ae]
    simp [truncatedScaleKernel, ht, htR]

/-- The scalar kernel specialized to a squared difference and a metric distance. -/
theorem lintegral_scale_difference
    {X : Type*} [MetricSpace X]
    {p R : ℝ} (hp : 0 < p) (u : X → ℝ) (x y : X) :
    (∫⁻ r in Set.Ioc 0 R,
      (Set.Ioi (dist x y)).indicator
        (fun r : ℝ =>
          (ENNReal.ofReal r).rpow (-1 - p) *
            differenceSq u x y) r) =
      truncatedScaleKernel p R (dist x y) *
        differenceSq u x y := by
  apply lintegral_scale_indicator_mul hp dist_nonneg
  intro hdist
  have hxy : x = y := dist_eq_zero.mp hdist
  subst y
  simp [differenceSq]

/-- Expanding `localEnergy` turns `pScaleEnergy` into a nonnegative triple integral. -/
theorem pScaleEnergy_eq_triple
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {p R : ℝ} {u : X → ℝ} (hu : Measurable u) :
    pScaleEnergy ν p R u =
      ∫⁻ r in Set.Ioc 0 R, ∫⁻ x, ∫⁻ y,
        scaleTripleKernel p u ((r, x), y) ∂ν ∂ν := by
  unfold pScaleEnergy localEnergy
  apply lintegral_congr
  intro r
  have hball : Measurable (ballEnergy ν u r) := by
    change Measurable
      (fun x => ∫⁻ y in Metric.ball x r, differenceSq u x y ∂ν)
    exact measurable_ballEnergy ν hu r
  rw [← lintegral_const_mul _ hball]
  apply lintegral_congr
  intro x
  have hdiff : Measurable (fun y => differenceSq u x y) := by
    unfold differenceSq
    fun_prop
  rw [ballEnergy, ← lintegral_const_mul _ hdiff,
    ← MeasureTheory.lintegral_indicator measurableSet_ball]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ Metric.ball x r
  · have hdist : dist y x < r := Metric.mem_ball.mp hy
    simp [scaleTripleKernel, Set.indicator, hy, hdist]
  · have hdist : ¬dist y x < r := by
      simpa only [Metric.mem_ball] using hy
    simp [scaleTripleKernel, Set.indicator, hy, hdist]

/-- Tonelli followed by the scalar identity gives the exact truncated kernel. -/
theorem triple_eq_truncatedEnergy
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {p R : ℝ} (hp : 0 < p) {u : X → ℝ} (hu : Measurable u) :
    (∫⁻ r in Set.Ioc 0 R, ∫⁻ x, ∫⁻ y,
        scaleTripleKernel p u ((r, x), y) ∂ν ∂ν) =
      truncatedEnergy ν p R u := by
  have hF : Measurable (scaleTripleKernel p u) :=
    measurable_scaleTripleKernel hu
  have hinner :
      Measurable
        (fun q : ℝ × X =>
          ∫⁻ y, scaleTripleKernel p u (q, y) ∂ν) :=
    hF.lintegral_prod_right'
  calc
    (∫⁻ r in Set.Ioc 0 R, ∫⁻ x, ∫⁻ y,
        scaleTripleKernel p u ((r, x), y) ∂ν ∂ν) =
        ∫⁻ x, (∫⁻ r in Set.Ioc 0 R, ∫⁻ y,
          scaleTripleKernel p u ((r, x), y) ∂ν) ∂ν :=
      lintegral_lintegral_swap hinner.aemeasurable
    _ = ∫⁻ x, ∫⁻ y, (∫⁻ r in Set.Ioc 0 R,
          scaleTripleKernel p u ((r, x), y)) ∂ν ∂ν := by
      apply lintegral_congr
      intro x
      have hxmeas :
          Measurable
            (fun q : ℝ × X =>
              scaleTripleKernel p u ((q.1, x), q.2)) :=
        hF.comp (by fun_prop)
      exact lintegral_lintegral_swap hxmeas.aemeasurable
    _ = truncatedEnergy ν p R u := by
      unfold truncatedEnergy
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro y
      have hfun :
          (fun r : ℝ => scaleTripleKernel p u ((r, x), y)) =
            fun r =>
              (Set.Ioi (dist x y)).indicator
                (fun q : ℝ =>
                  (ENNReal.ofReal q).rpow (-1 - p) *
                    differenceSq u x y) r := by
        funext r
        by_cases hxy : dist x y < r
        · have hyx : dist y x < r := by simpa [dist_comm] using hxy
          simp [scaleTripleKernel, Set.indicator, hxy, hyx]
        · have hyx : ¬dist y x < r := by simpa [dist_comm] using hxy
          simp [scaleTripleKernel, Set.indicator, hxy, hyx]
      rw [hfun, lintegral_scale_difference hp u x y]

/-- The complete Tonelli identity for the combined exponent `p`. -/
theorem pScaleEnergy_eq_truncatedEnergy
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {p R : ℝ} (hp : 0 < p) {u : X → ℝ} (hu : Measurable u) :
    pScaleEnergy ν p R u = truncatedEnergy ν p R u :=
  (pScaleEnergy_eq_triple ν hu).trans
    (triple_eq_truncatedEnergy ν hp hu)

/-- Repackaging the two exponents of `scaleEnergy` into `p = α + 2s`. -/
theorem scaleEnergy_eq_pScaleEnergy
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (α s R : ℝ) (u : X → ℝ) :
    scaleEnergy ν α s R u = pScaleEnergy ν (α + 2 * s) R u := by
  unfold scaleEnergy pScaleEnergy
  apply lintegral_congr
  intro r
  congr 2
  ring

/--
The requested Tonelli calculation for the actual scale energy.  No subtraction
in `ℝ≥0∞` occurs: the real subtraction is evaluated first and embedded with
`ENNReal.ofReal`.
-/
theorem scaleEnergy_eq_truncatedEnergy
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν]
    {α s R : ℝ} (hp : 0 < α + 2 * s)
    {u : X → ℝ} (hu : Measurable u) :
    scaleEnergy ν α s R u =
      truncatedEnergy ν (α + 2 * s) R u :=
  (scaleEnergy_eq_pScaleEnergy ν α s R u).trans
    (pScaleEnergy_eq_truncatedEnergy ν hp hu)

end BesovVerification
