import BesovVerification.CubeGeometry
import BesovVerification.TailEstimate

/-!
# Complete tail control with a cutoff wider than the cube

If the scale cutoff is strictly larger than the cube diameter, choose an
intermediate radius between `sqrt d` and the cutoff.  At that radius every
pair of supported points is already visible to the local energy, while a
positive interval of larger scales remains available to control it.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/-- The midpoint between the cube diameter and a wider scale cutoff. -/
def wideCutoffAnchorRadius (d : ℕ) (R : ℝ) : ℝ :=
  (Real.sqrt d + R) / 2

theorem sqrt_nat_lt_wideCutoffAnchorRadius
    {d : ℕ} {R : ℝ} (hR : Real.sqrt d < R) :
    Real.sqrt d < wideCutoffAnchorRadius d R := by
  unfold wideCutoffAnchorRadius
  linarith

theorem wideCutoffAnchorRadius_lt
    {d : ℕ} {R : ℝ} (hR : Real.sqrt d < R) :
    wideCutoffAnchorRadius d R < R := by
  unfold wideCutoffAnchorRadius
  linarith

theorem wideCutoffAnchorRadius_pos
    {d : ℕ} {R : ℝ} (hR : Real.sqrt d < R) :
    0 < wideCutoffAnchorRadius d R :=
  (Real.sqrt_nonneg d).trans_lt
    (sqrt_nat_lt_wideCutoffAnchorRadius hR)

/--
With a cutoff wider than `sqrt d`, the global oscillation is controlled by the
scale energy with an explicit coefficient.
-/
theorem globalVariation_le_scaleEnergy_of_unitCube_wideCutoff
    {d : ℕ} (ν : Measure (Ambient d))
    {u : Ambient d → ℝ}
    {α s R : ℝ}
    (hsupport : Measure.support ν ⊆ unitCube d)
    (hR : Real.sqrt d < R)
    (hp : 0 < α + 2 * s) :
    globalVariation ν u ≤
      (ENNReal.ofReal
        (((wideCutoffAnchorRadius d R) ^ (-(α + 2 * s)) -
            R ^ (-(α + 2 * s))) / (α + 2 * s)))⁻¹ *
        scaleEnergy ν α s R u := by
  let ρ := wideCutoffAnchorRadius d R
  have hdiamρ : Real.sqrt d < ρ :=
    sqrt_nat_lt_wideCutoffAnchorRadius hR
  have hρpos : 0 < ρ := (Real.sqrt_nonneg d).trans_lt hdiamρ
  have hρR : ρ < R := wideCutoffAnchorRadius_lt hR
  have hcover :
      ∀ᵐ x ∂ν, ∀ᵐ y ∂ν, y ∈ Metric.ball x ρ :=
    ae_pair_mem_ball_of_unitCube_support ν hsupport hdiamρ
  calc
    globalVariation ν u = localEnergy ν u ρ :=
      (localEnergy_eq_globalVariation_of_ae_mem_ball
        ν u hcover).symm
    _ ≤
        (ENNReal.ofReal
          ((ρ ^ (-(α + 2 * s)) - R ^ (-(α + 2 * s))) /
            (α + 2 * s)))⁻¹ *
          scaleEnergy ν α s R u :=
      localEnergy_le_inv_scaleTailMass_mul_scaleEnergy
        ν hp hρpos hρR

/--
The explicit tail coefficient in the preceding theorem is positive and
finite.
-/
theorem wideCutoff_tailCoefficient_pos_finite
    {d : ℕ} {α s R : ℝ}
    (hR : Real.sqrt d < R)
    (hp : 0 < α + 2 * s) :
    let K : ℝ≥0∞ :=
      (ENNReal.ofReal
        (((wideCutoffAnchorRadius d R) ^ (-(α + 2 * s)) -
            R ^ (-(α + 2 * s))) / (α + 2 * s)))⁻¹
    0 < K ∧ K < ∞ := by
  let ρ := wideCutoffAnchorRadius d R
  let p := α + 2 * s
  have hρpos : 0 < ρ := wideCutoffAnchorRadius_pos hR
  have hρR : ρ < R := wideCutoffAnchorRadius_lt hR
  have hpow : R ^ (-p) < ρ ^ (-p) :=
    Real.rpow_lt_rpow_of_neg hρpos hρR (neg_neg_of_pos hp)
  have hreal : 0 < (ρ ^ (-p) - R ^ (-p)) / p :=
    div_pos (sub_pos.2 hpow) hp
  dsimp only
  constructor
  · exact ENNReal.inv_pos.2 ENNReal.ofReal_ne_top
  · exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.2 hreal)

end BesovVerification
