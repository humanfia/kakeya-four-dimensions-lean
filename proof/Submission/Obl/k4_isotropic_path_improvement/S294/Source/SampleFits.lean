-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleFits, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The list and band fits of `sample_at` (session x1088).

* `depth_ge_graphLower`, `graphLower_ge`: `NativeDesign.depth ≥ graphLowerCoeff ≥ 1000`.
* `TmAt_eq_target`: with the fit target below `80 Kg^7`, the capped MK4 target of
  `Source.SampleChoices` is x1095's `mk4MeshTarget`.
* `listLen_le_rpow`: a list target `X ≤ 4 N^(ρ L)` has `listLenOf ≤ m (2δ₀ + ρ + η) + 1` once
  `4 ≤ N^(η L)`.
* `fineAt_lower`: `fineAt ≥ N^(-(gl a))/(2 N^(100 ρc L))` from the graph-mesh floor and
  `KcenAt ≤ N^(ρc L)`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleChoices
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.MK4TargetLower
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.CensusEventual

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

noncomputable section

theorem graphLower_ge {κ₁ d₁ : ℝ} {Ep : ℕ} {precision : ℝ} (hκ : 0 < κ₁) (hd₀ : 0 ≤ d₁)
    (hd₁ : d₁ < 1) (hprec : 1 ≤ precision) :
    1000 ≤ NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision := by
  unfold NativeDesign.graphLowerCoeff
  have h1 : 0 ≤ NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision := by
    unfold NativeDesign.graphTargetCoeff
    have := NativeDesign.floorEndCoeff_pos κ₁ d₁ (Ep := Ep) hprec
    have := NativeDesign.clockCoeff_pos (Ep := Ep) hprec
    positivity
  have hd : 0 < 1 - d₁ := by linarith
  rw [le_div_iff₀ hd]
  nlinarith

theorem depth_ge_graphLower (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) :
    NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision ≤ NativeDesign.depth κ₁ d₁ Ep precision loss := by
  unfold NativeDesign.depth
  set X := 2 + (NativeDesign.rhoPower κ₁ Ep precision : ℝ) +
    (NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss : ℝ) +
    |NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision| +
    |NativeDesign.floorEndCoeff κ₁ d₁ Ep precision|
  have h1 : NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision ≤ X := by
    have := le_abs_self (NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision)
    have h2 : (0 : ℝ) ≤ NativeDesign.rhoPower κ₁ Ep precision := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss := Nat.cast_nonneg _
    have h4 := abs_nonneg (NativeDesign.floorEndCoeff κ₁ d₁ Ep precision)
    linarith
  have hX1 : 1 ≤ X := by
    have h2 : (0 : ℝ) ≤ NativeDesign.rhoPower κ₁ Ep precision := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss := Nat.cast_nonneg _
    have h4 := abs_nonneg (NativeDesign.floorEndCoeff κ₁ d₁ Ep precision)
    have h5 := abs_nonneg (NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision)
    linarith
  have hX4 : X ≤ X ^ 4 := le_self_pow₀ hX1 (by norm_num)
  exact h1.trans (hX4.trans (le_max_right _ _))

/-- The capped MK4 target is x1095's target. -/
theorem TmAt_eq_target {κ Kd N δ₀ L τ ub d₁ θN : ℝ} {m : ℕ}
    (hθ : θN / (80 * KgAt κ Kd N δ₀ L τ ub d₁ m ^ 7) ≤ 1) :
    TmAt κ Kd N δ₀ L τ ub d₁ θN m = mk4MeshTarget θN (KgAt κ Kd N δ₀ L τ ub d₁ m) (κ⁻¹ / 512) := by
  unfold TmAt mk4MeshTarget
  rw [min_eq_left hθ]

/-- **A list length from a power bound of its target.** -/
theorem listLen_le_rpow {m : ℕ} {δ₀ L N X ρ η : ℝ} (hN : 1 < N) (hL : 0 < L) (hδ : 0 ≤ δ₀)
    (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hX : 0 < X) (hXle : X ≤ 4 * N ^ (ρ * L))
    (h4 : 4 ≤ N ^ (η * L)) :
    (listLenOf m δ₀ L N X : ℝ) ≤ m * (2 * δ₀ + ρ + η) + 1 := by
  have hNp : 0 < N := by linarith
  have hlog4 : Real.logb N 4 ≤ η * L := by
    have := Real.logb_le_logb_of_le hN (by norm_num) h4
    rwa [Real.logb_rpow hNp hN.ne'] at this
  have hlogX : Real.logb N X ≤ (η + ρ) * L := by
    have h1 := Real.logb_le_logb_of_le hN hX hXle
    rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos hNp _).ne',
      Real.logb_rpow hNp hN.ne'] at h1
    linarith
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hy : (m : ℝ) * (2 * δ₀ + Real.logb N X / L) ≤ m * (2 * δ₀ + ρ + η) := by
    apply mul_le_mul_of_nonneg_left _ hmR
    have : Real.logb N X / L ≤ ρ + η := by
      rw [div_le_iff₀ hL]; linarith
    linarith
  have hy0 : 0 ≤ (m : ℝ) * (2 * δ₀ + ρ + η) := by positivity
  unfold listLenOf
  calc (⌈(m : ℝ) * (2 * δ₀ + Real.logb N X / L)⌉₊ : ℝ)
      ≤ (⌈(m : ℝ) * (2 * δ₀ + ρ + η)⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hy
    _ ≤ m * (2 * δ₀ + ρ + η) + 1 := (Nat.ceil_lt_add_one hy0).le

/-- **The census fine mesh of the MK4 rows**, from below. -/
theorem fineAt_lower {κ Kd N δ₀ L τ ub d₁ θN ρc g : ℝ} {m : ℕ} (hN : 1 < N)
    (hmesh : N ^ (-g) ≤ Submission.Lib.K4DyadicRowScales.mesh (nmeshAt κ Kd N δ₀ L τ ub d₁ θN m))
    (hKc1 : 1 ≤ KcenAt κ Kd N δ₀ L τ ub m) (hKc : KcenAt κ Kd N δ₀ L τ ub m ≤ N ^ (ρc * L)) :
    N ^ (-(g + 100 * (ρc * L))) / 2 ≤ fineAt κ Kd N δ₀ L τ ub d₁ θN m := by
  have hNp : 0 < N := by linarith
  have hs := (two_pow_stepsOf hKc1).2
  have hK100 : KcenAt κ Kd N δ₀ L τ ub m ^ (100 : ℕ) ≤ N ^ (100 * (ρc * L)) := by
    calc KcenAt κ Kd N δ₀ L τ ub m ^ (100 : ℕ) ≤ (N ^ (ρc * L)) ^ (100 : ℕ) :=
          pow_le_pow_left₀ (by linarith) hKc 100
      _ = N ^ (100 * (ρc * L)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; ring_nf
  have h2s : (2 : ℝ) ^ stepsAt κ Kd N δ₀ L τ ub m ≤ 2 * N ^ (100 * (ρc * L)) := by
    unfold stepsAt; linarith
  have h2s0 : 0 < (2 : ℝ) ^ stepsAt κ Kd N δ₀ L τ ub m := by positivity
  unfold fineAt
  rw [le_div_iff₀ h2s0]
  calc N ^ (-(g + 100 * (ρc * L))) / 2 * (2 : ℝ) ^ stepsAt κ Kd N δ₀ L τ ub m
      ≤ N ^ (-(g + 100 * (ρc * L))) / 2 * (2 * N ^ (100 * (ρc * L))) :=
        mul_le_mul_of_nonneg_left h2s (by positivity)
    _ = N ^ (-g) := by
        rw [show -(g + 100 * (ρc * L)) = -g + -(100 * (ρc * L)) by ring, Real.rpow_add hNp,
          Real.rpow_neg hNp.le (100 * (ρc * L))]
        field_simp
    _ ≤ _ := hmesh

/-- The census geometry at the sample: `24 ≤ Kgeom`, `κ ≤ Kgeom`, `N^(2δ₀L) ≤ Kgeom`. -/
theorem KgeomAt_facts {κ Kd N δ₀ L τ : ℝ} (hκ : 1 ≤ κ) (hN : 1 ≤ N) (hτ : 0 ≤ τ) :
    24 ≤ KgeomAt κ Kd N δ₀ L τ ∧ κ ≤ KgeomAt κ Kd N δ₀ L τ ∧
      N ^ (2 * δ₀ * L) ≤ KgeomAt κ Kd N δ₀ L τ := by
  obtain ⟨h1, h2, h3, h4⟩ := Native.native_pre_geometry_envelope_bounds (source := Kd) hκ hN
    (by linarith : 0 ≤ τ + τ)
  obtain ⟨g1, g2, g3⟩ := geomOf_ge (K := Native.nativePreGeometryEnvelope κ Kd N (τ + τ)) (N := N)
    (δ₀ := δ₀) (L := L)
  unfold KgeomAt
  exact ⟨by linarith, ((le_max_left _ _).trans h3).trans g1, g2⟩

/-- **The root's census list fits in the family.** -/
theorem listA_fit {κ Kd N δ₀ L τ ub d₁ θN ρc gl gain : ℝ} {m nfam : ℕ} (hN : 1 < N) (hL : 0 < L)
    (hκ : 1 ≤ κ) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ₀) (hub : 0 ≤ ub) (hρc : 0 ≤ ρc) (hgl : 0 ≤ gl)
    (hgain : 0 < gain)
    (hKgeom : KgeomAt κ Kd N δ₀ L τ ≤ N ^ (3 * δ₀ * L))
    (hmesh : N ^ (-(gl * (gain * L))) ≤
      Submission.Lib.K4DyadicRowScales.mesh (nmeshAt κ Kd N δ₀ L τ ub d₁ θN m))
    (hKc : KcenAt κ Kd N δ₀ L τ ub m ≤ N ^ (ρc * L)) (h4 : 4 ≤ N ^ (gain * L))
    (hwin : (m : ℝ) * (2 * δ₀ + (3 * δ₀ *
        (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + ub +
        100 * ρc + gl * gain) + gain) + 1 < nfam) :
    listLenOf m δ₀ L N (2 * KgeomAt κ Kd N δ₀ L τ ^ (censusGp FixedSourcePowers.coreRadius
      FixedSourcePowers.jet (stripExpOf (KgeomAt κ Kd N δ₀ L τ) κ N δ₀ L (N ^ (-(ub * L))))
      (rowExpOf FixedSourcePowers.coreRadius) + 10) / fineAt κ Kd N δ₀ L τ ub d₁ θN m) < nfam := by
  have hNp : 0 < N := by linarith
  obtain ⟨hK24, hκK, hNK⟩ := KgeomAt_facts (Kd := Kd) (δ₀ := δ₀) (L := L) hκ hN.le hτ
  set Kgeom := KgeomAt κ Kd N δ₀ L τ
  set F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  have hKc1 : 1 ≤ KcenAt κ Kd N δ₀ L τ ub m := by
    unfold KcenAt; exact (censusK_ge (by linarith) _ _ _ _ _).1
  have hfine := fineAt_lower (θN := θN) (d₁ := d₁) hN hmesh hKc1 hKc
  have hfine0 : 0 < fineAt κ Kd N δ₀ L τ ub d₁ θN m :=
    lt_of_lt_of_le (by positivity) hfine
  have hT := listTarget_le (R := FixedSourcePowers.coreRadius) (J := FixedSourcePowers.jet)
    (ub := ub) hK24 hκ hκK hN.le hNK (by positivity) (by positivity) hfine0
  have hKF : Kgeom ^ censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet ≤
      N ^ (3 * δ₀ * L * F) := by
    calc Kgeom ^ censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet
        ≤ (N ^ (3 * δ₀ * L)) ^ censusFixedPowerOf FixedSourcePowers.coreRadius
            FixedSourcePowers.jet := pow_le_pow_left₀ (by linarith) hKgeom _
      _ = N ^ (3 * δ₀ * L * F) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
  -- `X ≤ 4 N^(R L)`
  have hX : 2 * Kgeom ^ (censusGp FixedSourcePowers.coreRadius FixedSourcePowers.jet
      (stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L)))) (rowExpOf FixedSourcePowers.coreRadius) + 10) /
        fineAt κ Kd N δ₀ L τ ub d₁ θN m ≤
      4 * N ^ ((3 * δ₀ * F + ub + 100 * ρc + gl * gain) * L) := by
    refine hT.trans ?_
    rw [div_le_iff₀ hfine0]
    have hpos : 0 ≤ N ^ ((3 * δ₀ * F + ub + 100 * ρc + gl * gain) * L) := by positivity
    calc 2 * (Kgeom ^ censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet *
          N ^ (ub * L))
        ≤ 2 * (N ^ (3 * δ₀ * L * F) * N ^ (ub * L)) := by gcongr
      _ = 4 * N ^ ((3 * δ₀ * F + ub + 100 * ρc + gl * gain) * L) *
          (N ^ (-(gl * (gain * L) + 100 * (ρc * L))) / 2) := by
          have e : (3 * δ₀ * F + ub + 100 * ρc + gl * gain) * L =
              3 * δ₀ * L * F + ub * L + (gl * (gain * L) + 100 * (ρc * L)) := by ring
          rw [e, Real.rpow_add hNp, Real.rpow_add hNp, Real.rpow_neg hNp.le]
          have : N ^ (gl * (gain * L) + 100 * (ρc * L)) ≠ 0 := (Real.rpow_pos_of_pos hNp _).ne'
          field_simp
          ring
      _ ≤ 4 * N ^ ((3 * δ₀ * F + ub + 100 * ρc + gl * gain) * L) *
          fineAt κ Kd N δ₀ L τ ub d₁ θN m := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hfine
  have hX0 : 0 < 2 * Kgeom ^ (censusGp FixedSourcePowers.coreRadius FixedSourcePowers.jet
      (stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L)))) (rowExpOf FixedSourcePowers.coreRadius) + 10) /
        fineAt κ Kd N δ₀ L τ ub d₁ θN m := by
    have : 0 < Kgeom := by linarith
    positivity
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hlen := listLen_le_rpow (m := m) hN hL hδ (by positivity) hgain.le hX0 hX h4
  have : (listLenOf m δ₀ L N (2 * Kgeom ^ (censusGp FixedSourcePowers.coreRadius
      FixedSourcePowers.jet (stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L))))
      (rowExpOf FixedSourcePowers.coreRadius) + 10) / fineAt κ Kd N δ₀ L τ ub d₁ θN m) : ℝ) <
      nfam := by linarith
  exact_mod_cast this

/-- **The children's census list fits in the family.** -/
theorem listB_fit {κ Kd N δ₀ L τ ub ρε gain εv : ℝ} {m nfam c : ℕ} (hN : 1 < N) (hL : 0 < L)
    (hκ : 1 ≤ κ) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ₀) (hub : 0 ≤ ub) (hρε : 0 ≤ ρε) (hgain : 0 < gain)
    (hKgeom : KgeomAt κ Kd N δ₀ L τ ≤ N ^ (3 * δ₀ * L))
    (hεv : N ^ (-(ρε * L)) / 2 ≤ εv) (h4 : 4 ≤ N ^ (gain * L))
    (hwin : (c : ℝ) + (m : ℝ) * (2 * δ₀ + (3 * δ₀ *
        (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + ub + ρε) +
        gain) + 1 < nfam) :
    c + listLenOf m δ₀ L N (2 * KgeomAt κ Kd N δ₀ L τ ^ (censusGp FixedSourcePowers.coreRadius
      FixedSourcePowers.jet (stripExpOf (KgeomAt κ Kd N δ₀ L τ) κ N δ₀ L (N ^ (-(ub * L))))
      (rowExpOf FixedSourcePowers.coreRadius) + 10) / εv) < nfam := by
  have hNp : 0 < N := by linarith
  obtain ⟨hK24, hκK, hNK⟩ := KgeomAt_facts (Kd := Kd) (δ₀ := δ₀) (L := L) hκ hN.le hτ
  set Kgeom := KgeomAt κ Kd N δ₀ L τ
  set F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  have hεv0 : 0 < εv := lt_of_lt_of_le (by positivity) hεv
  have hT := listTarget_le (R := FixedSourcePowers.coreRadius) (J := FixedSourcePowers.jet)
    (ub := ub) hK24 hκ hκK hN.le hNK (by positivity) (by positivity) hεv0
  have hKF : Kgeom ^ censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet ≤
      N ^ (3 * δ₀ * L * F) := by
    calc Kgeom ^ censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet
        ≤ (N ^ (3 * δ₀ * L)) ^ censusFixedPowerOf FixedSourcePowers.coreRadius
            FixedSourcePowers.jet := pow_le_pow_left₀ (by linarith) hKgeom _
      _ = N ^ (3 * δ₀ * L * F) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
  have hX : 2 * Kgeom ^ (censusGp FixedSourcePowers.coreRadius FixedSourcePowers.jet
      (stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L)))) (rowExpOf FixedSourcePowers.coreRadius) + 10) /
        εv ≤ 4 * N ^ ((3 * δ₀ * F + ub + ρε) * L) := by
    refine hT.trans ?_
    rw [div_le_iff₀ hεv0]
    calc 2 * (Kgeom ^ censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet *
          N ^ (ub * L))
        ≤ 2 * (N ^ (3 * δ₀ * L * F) * N ^ (ub * L)) := by gcongr
      _ = 4 * N ^ ((3 * δ₀ * F + ub + ρε) * L) * (N ^ (-(ρε * L)) / 2) := by
          have e : (3 * δ₀ * F + ub + ρε) * L = 3 * δ₀ * L * F + ub * L + ρε * L := by ring
          rw [e, Real.rpow_add hNp, Real.rpow_add hNp, Real.rpow_neg hNp.le]
          have : N ^ (ρε * L) ≠ 0 := (Real.rpow_pos_of_pos hNp _).ne'
          field_simp
          ring
      _ ≤ 4 * N ^ ((3 * δ₀ * F + ub + ρε) * L) * εv :=
          mul_le_mul_of_nonneg_left hεv (by positivity)
  have hX0 : 0 < 2 * Kgeom ^ (censusGp FixedSourcePowers.coreRadius FixedSourcePowers.jet
      (stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L)))) (rowExpOf FixedSourcePowers.coreRadius) + 10) /
        εv := by
    have : 0 < Kgeom := by linarith
    positivity
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hlen := listLen_le_rpow (m := m) hN hL hδ (by positivity) hgain.le hX0 hX h4
  have : ((c + listLenOf m δ₀ L N (2 * Kgeom ^ (censusGp FixedSourcePowers.coreRadius
      FixedSourcePowers.jet (stripExpOf Kgeom κ N δ₀ L (N ^ (-(ub * L))))
      (rowExpOf FixedSourcePowers.coreRadius) + 10) / εv) : ℕ) : ℝ) < nfam := by
    push_cast; linarith
  exact_mod_cast this

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
