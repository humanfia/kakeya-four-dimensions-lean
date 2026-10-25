import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.Measure

/-!
# Positions and slopes of the synthetic lines

A synthetic line has position `b₀` and slope `β u₃` in its first planar coordinate, with `b₀, u₃`
uniform. At a reference time `τ` its position is `b₀ + τ β u₃`. Three computations on the pair
`(b₀, u₃)` are used: the position is spread with density at most one at every time and slope
(`UU_shear_le`); a position window inside `[β, 1-β]` has exact mass (`UU_shear_eq`); and a
periodic exceptional set of relative positions has proportionally small mass
(`vol_fract_bad_le`). Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set

noncomputable section

/-- The position at time `τ` is spread with density at most one, independently of the slope. -/
theorem UU_shear_le (τ β : ℝ) {C V : Set ℝ} (hC : MeasurableSet C) (hV : MeasurableSet V) :
    (U.prod U) {p : ℝ × ℝ | p.1 + τ * β * p.2 ∈ C ∧ β * p.2 ∈ V} ≤
      volume C * U {u | β * u ∈ V} := by
  have hW : MeasurableSet {u : ℝ | β * u ∈ V} := (measurable_const_mul β) hV
  refine UU_apply_le _ ?_ (volume C) _ ?_ ?_ hW
  · exact ((measurable_fst.add ((measurable_const_mul (τ * β)).comp measurable_snd)) hC).inter
      ((measurable_const_mul β).comp measurable_snd hV)
  · intro u hu
    have : {b : ℝ | (b, u) ∈ {p : ℝ × ℝ | p.1 + τ * β * p.2 ∈ C ∧ β * p.2 ∈ V}} =
        (fun b => b + τ * β * u) ⁻¹' C := by
      ext b; simp [hu.out]
    rw [this]
    calc U ((fun b => b + τ * β * u) ⁻¹' C) ≤ volume ((fun b => b + τ * β * u) ⁻¹' C) :=
          U_le_volume _
      _ = volume C := measure_preimage_add_right _ _ _
  · intro u hu
    ext b
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact fun _ h => hu h

/-- A position window inside `[β, 1-β]` has exact mass, for slopes in `[0, β]` and times in
`[0,1]`. -/
theorem UU_shear_eq (τ β a q : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hβ : 0 ≤ β)
    (ha : β ≤ a) (haq : a + q ≤ 1 - β) :
    (U.prod U) {p : ℝ × ℝ | p.1 + τ * β * p.2 ∈ Ico a (a + q) ∧ p.2 ∈ Icc (0 : ℝ) 1} =
      ENNReal.ofReal q := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 + τ * β * p.2 ∈ Ico a (a + q) ∧
      p.2 ∈ Icc (0 : ℝ) 1} :=
    ((measurable_fst.add ((measurable_const_mul (τ * β)).comp measurable_snd))
      measurableSet_Ico).inter (measurable_snd measurableSet_Icc)
  rw [Measure.prod_apply_symm hmeas]
  have hsec : ∀ u ∈ Icc (0 : ℝ) 1,
      U ((fun b => (b, u)) ⁻¹' {p : ℝ × ℝ | p.1 + τ * β * p.2 ∈ Ico a (a + q) ∧
        p.2 ∈ Icc (0 : ℝ) 1}) = ENNReal.ofReal q := by
    intro u hu
    have hset : (fun b => (b, u)) ⁻¹' {p : ℝ × ℝ | p.1 + τ * β * p.2 ∈ Ico a (a + q) ∧
        p.2 ∈ Icc (0 : ℝ) 1} = Ico (a - τ * β * u) (a + q - τ * β * u) := by
      ext b
      simp only [mem_preimage, mem_ofPred_eq, mem_Ico, hu, and_true]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [hset]
    have hsh : τ * β * u ≤ β := by
      have : τ * u ≤ 1 := by nlinarith [hu.1, hu.2]
      nlinarith [hu.1, hu.2]
    have hsh0 : 0 ≤ τ * β * u := by
      have := hu.1; positivity
    have hsub : Ico (a - τ * β * u) (a + q - τ * β * u) ⊆ Icc 0 1 := by
      intro b hb
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    simp only [U]
    rw [Measure.restrict_apply measurableSet_Ico, inter_eq_left.mpr hsub, Real.volume_Ico]
    congr 1
    ring
  calc ∫⁻ u, U ((fun b => (b, u)) ⁻¹' {p : ℝ × ℝ | p.1 + τ * β * p.2 ∈ Ico a (a + q) ∧
        p.2 ∈ Icc (0 : ℝ) 1}) ∂U
      = ∫⁻ _u, ENNReal.ofReal q ∂U := by
        simp only [U]
        exact setLIntegral_congr_fun measurableSet_Icc hsec
    _ = ENNReal.ofReal q := by simp

/-- Points whose relative position in a grid of mesh `q'` lies within `x₁` above or `x₂` below a
grid point: in a window of `N` meshes they have measure at most `(N + 2)(x₁ + x₂) q'`. -/
theorem vol_fract_bad_le (q' c a : ℝ) (hq' : 0 < q') (N : ℕ) (x₁ x₂ : ℝ) (hx₁ : 0 ≤ x₁)
    (hx₂ : 0 ≤ x₂) :
    volume {b ∈ Ico a (a + N * q') | Int.fract ((b + c) / q') < x₁ ∨
        1 - x₂ ≤ Int.fract ((b + c) / q')} ≤
      ENNReal.ofReal ((N + 2) * ((x₁ + x₂) * q')) := by
  set m₀ : ℤ := ⌊(a + c) / q'⌋ with hm₀
  set F : Finset ℤ := Finset.Icc m₀ (m₀ + N + 1) with hF
  have hsub : {b ∈ Ico a (a + N * q') | Int.fract ((b + c) / q') < x₁ ∨
      1 - x₂ ≤ Int.fract ((b + c) / q')} ⊆
      ⋃ m ∈ F, Ico ((m : ℝ) * q' - c - x₂ * q') ((m : ℝ) * q' - c + x₁ * q') := by
    intro b hb
    obtain ⟨⟨hb1, hb2⟩, hbad⟩ := hb
    set z := (b + c) / q' with hz
    have hzlo : (a + c) / q' ≤ z := by
      rw [hz]; exact div_le_div_of_nonneg_right (by linarith) hq'.le
    have hzhi : z < (a + c) / q' + N := by
      rw [hz, div_add' _ _ _ hq'.ne', div_lt_div_iff_of_pos_right hq']
      linarith
    have hfl1 : m₀ ≤ ⌊z⌋ := Int.floor_mono hzlo
    have hfl2 : ⌊z⌋ ≤ m₀ + N := by
      have : z < (m₀ : ℝ) + 1 + N := by
        have := Int.lt_floor_add_one ((a + c) / q')
        linarith
      have h3 : ⌊z⌋ < m₀ + 1 + N := by
        rw [Int.floor_lt]; push_cast; linarith
      omega
    have hzb : b = z * q' - c := by rw [hz]; field_simp; ring
    simp only [mem_iUnion, mem_Ico, exists_prop, hF, Finset.mem_Icc]
    rcases hbad with h | h
    · refine ⟨⌊z⌋, ⟨hfl1, by omega⟩, ?_, ?_⟩
      · have : (⌊z⌋ : ℝ) ≤ z := Int.floor_le z
        rw [hzb]; nlinarith [hx₂, hq']
      · have : z < ⌊z⌋ + x₁ := by
          have := Int.self_sub_floor z
          rw [← this] at h; linarith
        rw [hzb]; nlinarith
    · refine ⟨⌊z⌋ + 1, ⟨by omega, by omega⟩, ?_, ?_⟩
      · have : (⌊z⌋ : ℝ) + 1 - x₂ ≤ z := by
          have := Int.self_sub_floor z
          rw [← this] at h; linarith
        rw [hzb]; push_cast; nlinarith
      · have : z < ⌊z⌋ + 1 := Int.lt_floor_add_one z
        rw [hzb]; push_cast; nlinarith
  calc volume {b ∈ Ico a (a + N * q') | Int.fract ((b + c) / q') < x₁ ∨
        1 - x₂ ≤ Int.fract ((b + c) / q')}
      ≤ volume (⋃ m ∈ F, Ico ((m : ℝ) * q' - c - x₂ * q') ((m : ℝ) * q' - c + x₁ * q')) :=
        measure_mono hsub
    _ ≤ ∑ m ∈ F, volume (Ico ((m : ℝ) * q' - c - x₂ * q') ((m : ℝ) * q' - c + x₁ * q')) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _m ∈ F, ENNReal.ofReal ((x₁ + x₂) * q') := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Real.volume_Ico]; congr 1; ring
    _ = ENNReal.ofReal ((N + 2) * ((x₁ + x₂) * q')) := by
        rw [Finset.sum_const, hF, Int.card_Icc]
        have h1 : (m₀ + N + 1 + 1 - m₀).toNat = N + 2 := by omega
        rw [h1, nsmul_eq_mul]
        have h2 : ((N + 2 : ℕ) : ENNReal) = ENNReal.ofReal ((N : ℝ) + 2) := by
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl
        rw [h2, ← ENNReal.ofReal_mul (by positivity)]

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
