import BesovVerification.AnchorTailComparison
import BesovVerification.ExactCubeConstants
import BesovVerification.FixedCornerScaleAnchor
import BesovVerification.FullEnergyDecomposition
import BesovVerification.MainTheorem
import BesovVerification.StructuralAnchorEstimate

/-!
# Full equivalence at the exact cube diameter

The constants in the final theorem are quantified before the measure and the
function.  This makes their structural dependence explicit in Lean: they can
depend on `d`, `α`, `s`, `cA`, and `CA`, but not on `ν` or `u`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BesovVerification

/--
An anchor set whose anchor scale is strictly below `R` also gives the
structural total-mass upper bound `CA * R^α`.
-/
theorem measure_univ_le_upperAhlfors_of_anchor
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X)
    {α cA CA R ρ : ℝ}
    (hreg : AhlforsRegular ν α cA CA R)
    (hR : 0 < R) (hρR : ρ < R)
    (S : Set X) (hSsubset : S ⊆ Measure.support ν)
    (hSpos : 0 < ν S)
    (hanchor :
      ∀ x ∈ Measure.support ν, ∀ z ∈ S, dist x z < ρ) :
    ν Set.univ ≤ ENNReal.ofReal (CA * R ^ α) := by
  have hSne : S.Nonempty := by
    by_contra h
    have hSempty : S = ∅ := not_nonempty_iff_eq_empty.mp h
    rw [hSempty] at hSpos
    simp at hSpos
  obtain ⟨z, hzS⟩ := hSne
  have hzSupport : z ∈ Measure.support ν := hSsubset hzS
  have hball : ∀ᵐ x ∂ν, x ∈ Metric.ball z R := by
    filter_upwards [Measure.support_mem_ae] with x hx
    exact Metric.mem_ball.mpr
      ((hanchor x hx z hzS).trans hρR)
  calc
    ν Set.univ ≤ ν (Metric.ball z R) := by
      apply measure_mono_ae
      filter_upwards [hball] with x hx
      exact fun _hxuniv => hx
    _ ≤ ENNReal.ofReal (CA * R ^ α) :=
      hreg.upper z hzSupport R hR le_rfl

/--
The exact two-sided comparison for one structural corner scale.  All numeric
constants are fixed before `ν` and `u`.
-/
theorem exactCube_besovEnergy_equivalence_of_cornerScale
    {d : ℕ} {α s cA CA δ : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hs : 0 < s)
    (hcA : 0 < cA) (hcACA : cA ≤ CA)
    (hδ : 0 < δ) (h2δR : 2 * δ ≤ Real.sqrt d)
    (hsmall :
      (∑ _v : Fin d → Bool,
        ENNReal.ofReal (CA * (2 * δ) ^ α)) <
          ENNReal.ofReal (cA * (Real.sqrt d) ^ α))
    (ν : Measure (Ambient d))
    {u : Ambient d → ℝ} (hu : Measurable u)
    (hreg : AhlforsRegular ν α cA CA (Real.sqrt d))
    (hsupport : Measure.support ν ⊆ unitCube d) :
    exactCubeLowerConstant d α (α + 2 * s) cA CA δ *
        besovEnergy ν α s u ≤
        averagedEnergy ν s (Real.sqrt d) u ∧
      averagedEnergy ν s (Real.sqrt d) u ≤
        exactCubeUpperConstant (α + 2 * s) cA *
          besovEnergy ν α s u := by
  have hR : 0 < Real.sqrt d :=
    Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hCA : 0 < CA := hcA.trans_le hcACA
  have hp : 0 < α + 2 * s := add_pos hα (mul_pos (by norm_num) hs)
  letI : IsFiniteMeasure ν :=
    hreg.isFiniteMeasure_of_unitCube_support hR hsupport
  have hconstants :=
    exactCube_constants_pos_and_lt_top
      hd hα hp hcA hCA hδ h2δR
  constructor
  · by_cases hν : ν = 0
    · subst ν
      simp [averagedEnergy, normalizedLocalEnergy, ballEnergy,
        besovEnergy]
    obtain ⟨S, ε, lam, hεeq, hlameq, hSmeas, hSsubset,
        hεpos, hεR, hSlower, hSpos, hlamPos, hlamOne,
        hanchor⟩ :=
      exists_fixedCornerScale_unitCube_anchor_ball
        hd hα hcA hδ h2δR hsmall ν hreg hν hsupport
    have hεdef :
        ε = exactCubeAnchorBallRadius d δ := by
      simpa [exactCubeAnchorBallRadius,
        exactCubeSubdiametralRadius] using hεeq
    have hlamdef :
        lam = exactCubeLambda d δ := by
      simpa [exactCubeLambda,
        exactCubeSubdiametralRadius] using hlameq
    have hradii := exactCube_structural_radii hd hδ h2δR
    have hanchor' :
        ∀ x ∈ Measure.support ν, ∀ z ∈ S,
          dist x z < exactCubeAnchorScale d δ := by
      simpa [exactCubeAnchorScale, ← hlamdef] using hanchor
    have hL :
        exactCubeAnchorMassLower d α cA δ ≤ ν S := by
      simpa [exactCubeAnchorMassLower, ← hεdef] using hSlower
    have hLpos :
        0 < exactCubeAnchorMassLower d α cA δ := by
      unfold exactCubeAnchorMassLower
      exact ENNReal.ofReal_pos.2
        (mul_pos hcA
          (Real.rpow_pos_of_pos hradii.2.2.1 α))
    have hU :
        ν Set.univ ≤ exactCubeTotalMassUpper d α CA := by
      unfold exactCubeTotalMassUpper
      exact measure_univ_le_upperAhlfors_of_anchor
        ν hreg hR hradii.2.2.2.2.2.2 S hSsubset hSpos hanchor'
    have hUfin :
        exactCubeTotalMassUpper d α CA < ∞ := by
      unfold exactCubeTotalMassUpper
      exact ENNReal.ofReal_ne_top.lt_top
    have hglobalLocal :
        globalVariation ν u ≤
          (4 * exactCubeTotalMassUpper d α CA /
            exactCubeAnchorMassLower d α cA δ) *
              localEnergy ν u (exactCubeAnchorScale d δ) :=
      globalVariation_le_structural_anchor_localEnergy
        ν hu S hanchor' hL hLpos hU hUfin
    have hlocalScale :
        localEnergy ν u (exactCubeAnchorScale d δ) ≤
          exactCubeTailConstant d (α + 2 * s) δ *
            scaleEnergy ν α s (Real.sqrt d) u := by
      simpa [exactCubeTailConstant] using
        (localEnergy_le_inv_scaleTailMass_mul_scaleEnergy
          ν hp hradii.2.2.2.2.2.1 hradii.2.2.2.2.2.2)
    have hglobalScale :
        globalVariation ν u ≤
          exactCubeGlobalScaleConstant d α (α + 2 * s) cA CA δ *
            scaleEnergy ν α s (Real.sqrt d) u := by
      calc
        globalVariation ν u ≤
            (4 * exactCubeTotalMassUpper d α CA /
              exactCubeAnchorMassLower d α cA δ) *
                localEnergy ν u (exactCubeAnchorScale d δ) :=
          hglobalLocal
        _ ≤ (4 * exactCubeTotalMassUpper d α CA /
              exactCubeAnchorMassLower d α cA δ) *
                (exactCubeTailConstant d (α + 2 * s) δ *
                  scaleEnergy ν α s (Real.sqrt d) u) :=
          mul_le_mul_right hlocalScale _
        _ = exactCubeGlobalScaleConstant
              d α (α + 2 * s) cA CA δ *
                scaleEnergy ν α s (Real.sqrt d) u := by
          unfold exactCubeGlobalScaleConstant
          rw [mul_assoc]
    have hglobalTruncated :
        globalVariation ν u ≤
          exactCubeGlobalScaleConstant d α (α + 2 * s) cA CA δ *
            truncatedEnergy ν (α + 2 * s) (Real.sqrt d) u := by
      simpa only [scaleEnergy_eq_truncatedEnergy ν hp hu] using
        hglobalScale
    have hfull :
        besovEnergy ν (α + 2 * s) 0 u ≤
          (ENNReal.ofReal (α + 2 * s) +
              (ENNReal.ofReal (Real.sqrt d)).rpow (-(α + 2 * s)) *
                exactCubeGlobalScaleConstant
                  d α (α + 2 * s) cA CA δ) *
            truncatedEnergy ν (α + 2 * s) (Real.sqrt d) u :=
      besovEnergy_le_truncated_of_globalVariation_le
        ν hu hp hR hglobalTruncated
    have hscale :
        scaleEnergy ν α s (Real.sqrt d) u ≤
          ENNReal.ofReal CA *
            averagedEnergy ν s (Real.sqrt d) u :=
      scaleEnergy_le_upperAhlfors_mul_averagedEnergy
        ν hu hreg hCA
    have hreverse :
        besovEnergy ν α s u ≤
          exactCubeReverseConstant d α (α + 2 * s) cA CA δ *
            averagedEnergy ν s (Real.sqrt d) u := by
      calc
        besovEnergy ν α s u =
            besovEnergy ν (α + 2 * s) 0 u := by
          symm
          exact besovEnergy_repackage ν α s u
        _ ≤ (ENNReal.ofReal (α + 2 * s) +
              (ENNReal.ofReal (Real.sqrt d)).rpow (-(α + 2 * s)) *
                exactCubeGlobalScaleConstant
                  d α (α + 2 * s) cA CA δ) *
              truncatedEnergy ν (α + 2 * s) (Real.sqrt d) u :=
          hfull
        _ = (ENNReal.ofReal (α + 2 * s) +
              (ENNReal.ofReal (Real.sqrt d)).rpow (-(α + 2 * s)) *
                exactCubeGlobalScaleConstant
                  d α (α + 2 * s) cA CA δ) *
              scaleEnergy ν α s (Real.sqrt d) u := by
          rw [scaleEnergy_eq_truncatedEnergy ν hp hu]
        _ ≤ (ENNReal.ofReal (α + 2 * s) +
              (ENNReal.ofReal (Real.sqrt d)).rpow (-(α + 2 * s)) *
                exactCubeGlobalScaleConstant
                  d α (α + 2 * s) cA CA δ) *
              (ENNReal.ofReal CA *
                averagedEnergy ν s (Real.sqrt d) u) :=
          mul_le_mul_right hscale _
        _ = exactCubeReverseConstant d α (α + 2 * s) cA CA δ *
              averagedEnergy ν s (Real.sqrt d) u := by
          unfold exactCubeReverseConstant
          rw [mul_assoc]
    have hD0 :
        exactCubeReverseConstant d α (α + 2 * s) cA CA δ ≠ 0 :=
      (ENNReal.inv_lt_top.mp hconstants.2.1).ne'
    have hDtop :
        exactCubeReverseConstant d α (α + 2 * s) cA CA δ ≠ ∞ :=
      ENNReal.inv_pos.mp hconstants.1
    unfold exactCubeLowerConstant
    exact (ENNReal.inv_mul_le_iff hD0 hDtop).2 hreverse
  · simpa [exactCubeUpperConstant] using
      (averagedEnergy_le_besovEnergy
        ν hu hreg hcA hCA hp)

/--
The complete theorem at `R = sqrt d`, with constants quantified before the
measure and function.  The original restriction `s < α/2` is retained in the
statement for fidelity, although the proof only uses `α > 0` and `s > 0`.
-/
theorem exists_exactCube_besovEnergy_equivalence_constants
    (d : ℕ) (α s cA CA : ℝ)
    (hd : 0 < d) (hα : 0 < α) (hs : 0 < s)
    (_hsα : s < α / 2)
    (hcA : 0 < cA) (hcACA : cA ≤ CA) :
    ∃ c C : ℝ≥0∞,
      0 < c ∧ c < ∞ ∧ 0 < C ∧ C < ∞ ∧
      ∀ (ν : Measure (Ambient d)) (u : Ambient d → ℝ),
        Measurable u →
        AhlforsRegular ν α cA CA (Real.sqrt d) →
        Measure.support ν ⊆ unitCube d →
        c * besovEnergy ν α s u ≤
            averagedEnergy ν s (Real.sqrt d) u ∧
          averagedEnergy ν s (Real.sqrt d) u ≤
            C * besovEnergy ν α s u := by
  have hR : 0 < Real.sqrt d :=
    Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hCA : 0 < CA := hcA.trans_le hcACA
  have hp : 0 < α + 2 * s := add_pos hα (mul_pos (by norm_num) hs)
  obtain ⟨δ, hδ, h2δR, hsmall⟩ :=
    exists_cornerScale d hα hcA hCA.le hR
  let c := exactCubeLowerConstant d α (α + 2 * s) cA CA δ
  let C := exactCubeUpperConstant (α + 2 * s) cA
  have hconstants :=
    exactCube_constants_pos_and_lt_top
      hd hα hp hcA hCA hδ h2δR
  refine ⟨c, C, hconstants.1, hconstants.2.1,
    hconstants.2.2.1, hconstants.2.2.2, ?_⟩
  intro ν u hu hreg hsupport
  exact exactCube_besovEnergy_equivalence_of_cornerScale
    hd hα hs hcA hcACA hδ h2δR hsmall
      ν hu hreg hsupport

end BesovVerification
