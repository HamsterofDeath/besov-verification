import BesovVerification.Definitions

/-!
# Measurability of the energy kernels

These lemmas make the varying-ball inner integral available to Tonelli and to
the constant-multiple rules for `lintegral`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

theorem measurable_differenceSq_uncurry
    {X : Type*} [MeasurableSpace X]
    {u : X → ℝ} (hu : Measurable u) :
    Measurable (fun p : X × X => differenceSq u p.1 p.2) := by
  unfold differenceSq
  fun_prop

/--
For a measurable `u`, the local energy inside the ball centered at `x` is a
measurable function of `x`.
-/
theorem measurable_ballEnergy
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν] {u : X → ℝ} (hu : Measurable u) (r : ℝ) :
    Measurable
      (fun x => ∫⁻ y in Metric.ball x r, differenceSq u x y ∂ν) := by
  let D : Set (X × X) := {p | dist p.2 p.1 < r}
  have hD : MeasurableSet D := by
    exact measurableSet_lt (measurable_dist.comp measurable_swap) measurable_const
  have hkernel :
      Measurable
        (D.indicator (fun p : X × X => differenceSq u p.1 p.2)) :=
    (measurable_differenceSq_uncurry hu).indicator hD
  have hintegral :
      Measurable
        (fun x : X =>
          ∫⁻ y : X,
            D.indicator (fun p : X × X => differenceSq u p.1 p.2) (x, y) ∂ν) :=
    hkernel.lintegral_prod_right'
  convert hintegral using 1
  funext x
  rw [← MeasureTheory.lintegral_indicator measurableSet_ball]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ Metric.ball x r
  · simp [D, hy, Metric.mem_ball.mp hy]
  · have hdist : ¬ dist y x < r := by
      simpa only [Metric.mem_ball] using hy
    simp [D, hy, hdist]

/-- The unnormalised local energy is measurable as a function of the radius-free outer variable. -/
theorem measurable_localEnergy_integrand
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν] {u : X → ℝ} (hu : Measurable u) (r : ℝ) :
    Measurable
      (fun x => ∫⁻ y in Metric.ball x r, differenceSq u x y ∂ν) :=
  measurable_ballEnergy ν hu r

/--
Joint measurability in the radius and center of the local ball energy.
-/
theorem measurable_ballEnergy_radiusCenter
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν] {u : X → ℝ} (hu : Measurable u) :
    Measurable
      (fun q : ℝ × X => ballEnergy ν u q.1 q.2) := by
  let D : Set ((ℝ × X) × X) :=
    {q | dist q.2 q.1.2 < q.1.1}
  have hD : MeasurableSet D := by
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hkernel :
      Measurable
        (D.indicator
          (fun q : (ℝ × X) × X => differenceSq u q.1.2 q.2)) := by
    apply Measurable.indicator
    · unfold differenceSq
      fun_prop
    · exact hD
  have hintegral :
      Measurable
        (fun q : ℝ × X =>
          ∫⁻ y : X,
            D.indicator
              (fun z : (ℝ × X) × X => differenceSq u z.1.2 z.2)
              (q, y) ∂ν) :=
    hkernel.lintegral_prod_right'
  convert hintegral using 1
  funext q
  rw [ballEnergy, ← MeasureTheory.lintegral_indicator measurableSet_ball]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ Metric.ball q.2 q.1
  · simp [D, hy, Metric.mem_ball.mp hy]
  · have hdist : ¬ dist y q.2 < q.1 := by
      simpa only [Metric.mem_ball] using hy
    simp [D, hy, hdist]

/-- The local energy is measurable as a function of the radius. -/
theorem measurable_localEnergy_radius
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν] {u : X → ℝ} (hu : Measurable u) :
    Measurable (localEnergy ν u) := by
  have h :=
    (measurable_ballEnergy_radiusCenter ν hu).lintegral_prod_right'
      (ν := ν)
  change Measurable (fun r => ∫⁻ x, ballEnergy ν u r x ∂ν)
  exact h

/-- Joint measurability of the mass of a moving open ball. -/
theorem measurable_ballMeasure_radiusCenter
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν] :
    Measurable (fun q : ℝ × X => ν (Metric.ball q.2 q.1)) := by
  let D : Set ((ℝ × X) × X) :=
    {q | dist q.2 q.1.2 < q.1.1}
  have hD : MeasurableSet D :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have hkernel :
      Measurable
        (D.indicator (fun _ : (ℝ × X) × X => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hD
  have hintegral :
      Measurable
        (fun q : ℝ × X =>
          ∫⁻ y : X,
            D.indicator (fun _ : (ℝ × X) × X => (1 : ℝ≥0∞))
              (q, y) ∂ν) :=
    hkernel.lintegral_prod_right'
  convert hintegral using 1
  funext q
  symm
  calc
    (∫⁻ y : X,
        D.indicator (fun _ : (ℝ × X) × X => (1 : ℝ≥0∞))
          (q, y) ∂ν) =
        ∫⁻ y : X in Metric.ball q.2 q.1, (1 : ℝ≥0∞) ∂ν := by
      rw [← MeasureTheory.lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ Metric.ball q.2 q.1
      · simp [D, hy, Metric.mem_ball.mp hy]
      · have hdist : ¬ dist y q.2 < q.1 := by
          simpa only [Metric.mem_ball] using hy
        simp [D, hy, hdist]
    _ = ν (Metric.ball q.2 q.1) := MeasureTheory.setLIntegral_one _

/-- The normalized local energy is measurable as a function of the radius. -/
theorem measurable_normalizedLocalEnergy_radius
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [SFinite ν] {u : X → ℝ} (hu : Measurable u) :
    Measurable (normalizedLocalEnergy ν u) := by
  have hpair :
      Measurable
        (fun q : ℝ × X =>
          (ν (Metric.ball q.2 q.1))⁻¹ * ballEnergy ν u q.1 q.2) :=
    (measurable_ballMeasure_radiusCenter ν).inv.mul
      (measurable_ballEnergy_radiusCenter ν hu)
  have h := hpair.lintegral_prod_right' (ν := ν)
  change Measurable
    (fun r =>
      ∫⁻ x, (ν (Metric.ball x r))⁻¹ * ballEnergy ν u r x ∂ν)
  exact h

end BesovVerification
