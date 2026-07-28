import BesovVerification.CubeAnchor

/-!
# Anchor sets at a fixed structural corner scale

This file packages the cube-anchor construction with `δ` as an external
input.  Therefore `δ`, `ε`, and `lam` can all be quantified before the
measure; only the location of the anchor set depends on the measure.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/--
Construct a cube anchor set at an externally fixed corner scale `δ`.

The hypotheses on `δ` are entirely structural.  For every nonzero measure
with the stated Ahlfors constants and cube support, only `S` is selected
after the measure is known.  The returned scale and contraction factor are
the exact formulas

* `ε = (√d - √(d - δ²)) / 2`,
* `lam = (√d + √(d - δ²)) / (2√d)`.
-/
theorem exists_fixedCornerScale_unitCube_anchor_ball
    {d : ℕ} {α cA CA δ : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hcA : 0 < cA)
    (hδ : 0 < δ) (h2δR : 2 * δ ≤ Real.sqrt d)
    (hsmall :
      (∑ _v : Fin d → Bool,
        ENNReal.ofReal (CA * (2 * δ) ^ α)) <
          ENNReal.ofReal (cA * (Real.sqrt d) ^ α))
    (ν : Measure (Ambient d))
    (hreg : AhlforsRegular ν α cA CA (Real.sqrt d))
    (hν : ν ≠ 0)
    (hsupport : Measure.support ν ⊆ unitCube d) :
    ∃ (S : Set (Ambient d)) (ε lam : ℝ),
      ε =
        (Real.sqrt d - Real.sqrt ((d : ℝ) - δ ^ 2)) / 2 ∧
      lam =
        (Real.sqrt d + Real.sqrt ((d : ℝ) - δ ^ 2)) /
          (2 * Real.sqrt d) ∧
      MeasurableSet S ∧
      S ⊆ Measure.support ν ∧
      0 < ε ∧ ε ≤ Real.sqrt d ∧
      ENNReal.ofReal (cA * ε ^ α) ≤ ν S ∧
      0 < ν S ∧
      0 < lam ∧ lam < 1 ∧
      ∀ x ∈ Measure.support ν, ∀ z ∈ S,
        dist x z < lam * Real.sqrt d := by
  have hR : 0 < Real.sqrt d :=
    Real.sqrt_pos.2 (by exact_mod_cast hd)
  obtain ⟨q, hqSupport, hqAway⟩ :=
    exists_support_away_from_cubeCorners
      hreg hR hδ h2δR hν hsmall
  have hqCube : q ∈ unitCube d := hsupport hqSupport
  obtain ⟨hρ, hρR, hcubeρ⟩ :=
    subdiametral_radius_of_away_from_cubeCorners
      hqCube hδ hqAway
  exact
    exists_quantitative_anchor_ball_of_subdiametral_point
      hreg hα hcA hR hqSupport hρ hρR
        (fun x hx => hcubeρ x (hsupport hx))

end BesovVerification
