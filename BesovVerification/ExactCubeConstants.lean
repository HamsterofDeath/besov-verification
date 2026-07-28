import BesovVerification.CubeAnchor

/-!
# Structural constants for the exact cube cutoff

All definitions in this file depend only on the displayed numerical
parameters.  In particular, they do not mention the measure or the function.
-/

open scoped ENNReal

noncomputable section

namespace BesovVerification

def exactCubeSubdiametralRadius (d : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt ((d : ℝ) - δ ^ 2)

def exactCubeAnchorBallRadius (d : ℕ) (δ : ℝ) : ℝ :=
  (Real.sqrt d - exactCubeSubdiametralRadius d δ) / 2

def exactCubeLambda (d : ℕ) (δ : ℝ) : ℝ :=
  (Real.sqrt d + exactCubeSubdiametralRadius d δ) /
    (2 * Real.sqrt d)

def exactCubeAnchorScale (d : ℕ) (δ : ℝ) : ℝ :=
  exactCubeLambda d δ * Real.sqrt d

def exactCubeAnchorMassLower
    (d : ℕ) (α cA δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (cA * (exactCubeAnchorBallRadius d δ) ^ α)

def exactCubeTotalMassUpper
    (d : ℕ) (α CA : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (CA * (Real.sqrt d) ^ α)

def exactCubeTailConstant
    (d : ℕ) (p δ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal
    (((exactCubeAnchorScale d δ) ^ (-p) -
        (Real.sqrt d) ^ (-p)) / p))⁻¹

def exactCubeGlobalScaleConstant
    (d : ℕ) (α p cA CA δ : ℝ) : ℝ≥0∞ :=
  (4 * exactCubeTotalMassUpper d α CA /
      exactCubeAnchorMassLower d α cA δ) *
    exactCubeTailConstant d p δ

def exactCubeReverseConstant
    (d : ℕ) (α p cA CA δ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal p +
      (ENNReal.ofReal (Real.sqrt d)).rpow (-p) *
        exactCubeGlobalScaleConstant d α p cA CA δ) *
    ENNReal.ofReal CA

def exactCubeLowerConstant
    (d : ℕ) (α p cA CA δ : ℝ) : ℝ≥0∞ :=
  (exactCubeReverseConstant d α p cA CA δ)⁻¹

def exactCubeUpperConstant (p cA : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal cA)⁻¹ * (ENNReal.ofReal p)⁻¹

/-- Pure geometry of a corner scale `δ ≤ sqrt(d)/2`. -/
theorem exactCube_structural_radii
    {d : ℕ} {δ : ℝ}
    (hd : 0 < d) (hδ : 0 < δ)
    (h2δ : 2 * δ ≤ Real.sqrt d) :
    0 ≤ exactCubeSubdiametralRadius d δ ∧
    exactCubeSubdiametralRadius d δ < Real.sqrt d ∧
    0 < exactCubeAnchorBallRadius d δ ∧
    0 < exactCubeLambda d δ ∧
    exactCubeLambda d δ < 1 ∧
    0 < exactCubeAnchorScale d δ ∧
    exactCubeAnchorScale d δ < Real.sqrt d := by
  have hR : 0 < Real.sqrt d :=
    Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hRsq : (Real.sqrt d) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hδle : δ ≤ Real.sqrt d / 2 := by linarith
  have hδltR : δ < Real.sqrt d := by linarith
  have hδsq : δ ^ 2 < (d : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt d - δ)]
  have hbase : 0 ≤ (d : ℝ) - δ ^ 2 :=
    sub_nonneg.mpr hδsq.le
  have hρ :
      exactCubeSubdiametralRadius d δ < Real.sqrt d := by
    unfold exactCubeSubdiametralRadius
    exact Real.sqrt_lt_sqrt hbase (by nlinarith)
  have hρ0 : 0 ≤ exactCubeSubdiametralRadius d δ := by
    exact Real.sqrt_nonneg _
  have hε : 0 < exactCubeAnchorBallRadius d δ := by
    unfold exactCubeAnchorBallRadius
    linarith
  have hlam : 0 < exactCubeLambda d δ := by
    unfold exactCubeLambda
    positivity
  have hlam1 : exactCubeLambda d δ < 1 := by
    unfold exactCubeLambda
    rw [div_lt_one (by positivity : 0 < 2 * Real.sqrt d)]
    linarith
  have hscaleEq :
      exactCubeAnchorScale d δ =
        (Real.sqrt d + exactCubeSubdiametralRadius d δ) / 2 := by
    unfold exactCubeAnchorScale exactCubeLambda
    field_simp
  have hscale0 : 0 < exactCubeAnchorScale d δ := by
    rw [hscaleEq]
    positivity
  have hscaleR : exactCubeAnchorScale d δ < Real.sqrt d := by
    rw [hscaleEq]
    linarith
  exact ⟨hρ0, hρ, hε, hlam, hlam1, hscale0, hscaleR⟩

/-- Every structural coefficient used in the exact theorem is positive and finite. -/
theorem exactCube_constants_pos_and_lt_top
    {d : ℕ} {α p cA CA δ : ℝ}
    (hd : 0 < d) (_hα : 0 < α) (hp : 0 < p)
    (hcA : 0 < cA) (hCA : 0 < CA)
    (hδ : 0 < δ) (h2δ : 2 * δ ≤ Real.sqrt d) :
    0 < exactCubeLowerConstant d α p cA CA δ ∧
    exactCubeLowerConstant d α p cA CA δ < ∞ ∧
    0 < exactCubeUpperConstant p cA ∧
    exactCubeUpperConstant p cA < ∞ := by
  have hradii := exactCube_structural_radii hd hδ h2δ
  have hR : 0 < Real.sqrt d :=
    Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hLpos :
      0 < exactCubeAnchorMassLower d α cA δ := by
    unfold exactCubeAnchorMassLower
    exact ENNReal.ofReal_pos.2
      (mul_pos hcA
        (Real.rpow_pos_of_pos hradii.2.2.1 α))
  have hUpos :
      0 < exactCubeTotalMassUpper d α CA := by
    unfold exactCubeTotalMassUpper
    exact ENNReal.ofReal_pos.2
      (mul_pos hCA (Real.rpow_pos_of_pos hR α))
  have hratioPos :
      0 < 4 * exactCubeTotalMassUpper d α CA /
          exactCubeAnchorMassLower d α cA δ :=
    ENNReal.div_pos
      (ENNReal.mul_pos (by norm_num) hUpos.ne').ne'
      ENNReal.ofReal_ne_top
  have hratioFin :
      4 * exactCubeTotalMassUpper d α CA /
          exactCubeAnchorMassLower d α cA δ < ∞ :=
    ENNReal.div_lt_top
      (ENNReal.mul_lt_top (by norm_num)
        ENNReal.ofReal_ne_top.lt_top).ne
      hLpos.ne'
  have hpow :
      (Real.sqrt d) ^ (-p) <
        (exactCubeAnchorScale d δ) ^ (-p) :=
    Real.rpow_lt_rpow_of_neg
      hradii.2.2.2.2.2.1 hradii.2.2.2.2.2.2
      (neg_neg_of_pos hp)
  have htailBase :
      0 < (((exactCubeAnchorScale d δ) ^ (-p) -
          (Real.sqrt d) ^ (-p)) / p) :=
    div_pos (sub_pos.2 hpow) hp
  have htailPos :
      0 < exactCubeTailConstant d p δ := by
    unfold exactCubeTailConstant
    exact ENNReal.inv_pos.2 ENNReal.ofReal_ne_top
  have htailFin :
      exactCubeTailConstant d p δ < ∞ := by
    unfold exactCubeTailConstant
    exact ENNReal.inv_lt_top.mpr
      (ENNReal.ofReal_pos.2 htailBase)
  have hglobalPos :
      0 < exactCubeGlobalScaleConstant d α p cA CA δ := by
    unfold exactCubeGlobalScaleConstant
    exact ENNReal.mul_pos hratioPos.ne' htailPos.ne'
  have hglobalFin :
      exactCubeGlobalScaleConstant d α p cA CA δ < ∞ := by
    unfold exactCubeGlobalScaleConstant
    exact ENNReal.mul_lt_top hratioFin htailFin
  have hRpowPos :
      0 < (ENNReal.ofReal (Real.sqrt d)).rpow (-p) :=
    ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hR)
      ENNReal.ofReal_ne_top
  have hRpowFin :
      (ENNReal.ofReal (Real.sqrt d)).rpow (-p) < ∞ :=
    lt_top_iff_ne_top.mpr
      (ENNReal.rpow_ne_top_of_ne_zero
        (ENNReal.ofReal_ne_zero_iff.2 hR)
        ENNReal.ofReal_ne_top)
  have hsumPos :
      0 < ENNReal.ofReal p +
          (ENNReal.ofReal (Real.sqrt d)).rpow (-p) *
            exactCubeGlobalScaleConstant d α p cA CA δ :=
    (ENNReal.ofReal_pos.2 hp).trans_le le_self_add
  have hsumFin :
      ENNReal.ofReal p +
          (ENNReal.ofReal (Real.sqrt d)).rpow (-p) *
            exactCubeGlobalScaleConstant d α p cA CA δ < ∞ := by
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.ofReal_ne_top.lt_top,
      ENNReal.mul_lt_top hRpowFin hglobalFin⟩
  have hDpos :
      0 < exactCubeReverseConstant d α p cA CA δ := by
    unfold exactCubeReverseConstant
    exact ENNReal.mul_pos hsumPos.ne'
      (ENNReal.ofReal_ne_zero_iff.2 hCA)
  have hDfin :
      exactCubeReverseConstant d α p cA CA δ < ∞ := by
    unfold exactCubeReverseConstant
    exact ENNReal.mul_lt_top hsumFin ENNReal.ofReal_ne_top.lt_top
  have hcpos :
      0 < exactCubeLowerConstant d α p cA CA δ := by
    unfold exactCubeLowerConstant
    exact ENNReal.inv_pos.2 hDfin.ne
  have hcfin :
      exactCubeLowerConstant d α p cA CA δ < ∞ := by
    unfold exactCubeLowerConstant
    exact ENNReal.inv_lt_top.mpr hDpos
  have hCpos :
      0 < exactCubeUpperConstant p cA := by
    unfold exactCubeUpperConstant
    exact ENNReal.mul_pos
      (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
  have hCfin :
      exactCubeUpperConstant p cA < ∞ := by
    unfold exactCubeUpperConstant
    exact ENNReal.mul_lt_top
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.2 hcA))
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.2 hp))
  exact ⟨hcpos, hcfin, hCpos, hCfin⟩

end BesovVerification
