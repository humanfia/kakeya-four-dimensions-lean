-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.Normalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.Grains

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric

/-- Positive affine changes of coordinates preserve the exact covering constant,
with the smallest scale transformed by the same dilation. -/
theorem Assouad.affine_image {d α C a b : ℝ} {B : Set ℝ}
    (hd : 0 < d) (ha : 0 < a) (h : Assouad d α C B) :
    Assouad (a * d) α C ((fun x => a * x + b) '' B) := by
  intro r R q hdr hrR
  have hr : 0 < r := (mul_pos ha hd).trans_le hdr
  obtain ⟨m, c, hc, hm⟩ := h (r / a) (R / a) ((q - b) / a)
    ((le_div_iff₀ ha).mpr (by nlinarith)) (div_le_div_of_nonneg_right hrR ha.le)
  refine ⟨m, (fun j => a * c j + b), ?_, ?_⟩
  · rintro _ ⟨⟨x, hx, rfl⟩, hxq, hxR⟩
    have hxI : x ∈ Icc ((q - b) / a) ((q - b) / a + R / a) := by
      constructor
      · apply (div_le_iff₀ ha).mpr
        linarith
      · rw [← add_div]
        apply (le_div_iff₀ ha).mpr
        linarith
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc ⟨hx, hxI⟩)
    refine mem_iUnion.mpr ⟨j, ?_⟩
    have hj' : |x - c j| ≤ r / a := by simpa only [mem_closedBall, Real.dist_eq] using hj
    rw [mem_closedBall, Real.dist_eq]
    calc |a * x + b - (a * c j + b)| = a * |x - c j| := by
          rw [show a * x + b - (a * c j + b) = a * (x - c j) by ring,
            abs_mul, abs_of_pos ha]
      _ ≤ r := by simpa only [mul_comm] using (le_div_iff₀ ha).mp hj'
  · have hratio : (R / a) / (r / a) = R / r := by field_simp
    simpa only [hratio] using hm

noncomputable def scaleFirst (a : ℝ) (p : Space) : Space :=
  WithLp.toLp 2 (fun i => if i = 0 then a * p 0 else p i)

/-- The slope rescaling used in normalization has an exact effect on horizontal slices. -/
theorem projectedSlice_scaleFirst (a : ℝ) (f : ℝ → ℝ) (E : Set Space) (z : ℝ) :
    ProjectedSlice (fun t => a * f t) (scaleFirst a '' E) z =
      (fun u => a * u) '' ProjectedSlice f E z := by
  ext u
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, he⟩
    have hu : a * p 0 + (a * f (p 2)) * p 1 = u := by
      simpa [scaleFirst] using congrArg Prod.fst he
    have hz : p 2 = z := by simpa [scaleFirst] using congrArg Prod.snd he
    refine ⟨p 0 + f (p 2) * p 1, ⟨p, hp, ?_⟩, ?_⟩
    · exact Prod.ext rfl hz
    · calc a * (p 0 + f (p 2) * p 1) = a * p 0 + (a * f (p 2)) * p 1 := by ring
        _ = u := hu
  · rintro ⟨v, ⟨p, hp, he⟩, rfl⟩
    have hu : p 0 + f (p 2) * p 1 = v := congrArg Prod.fst he
    have hz : p 2 = z := congrArg Prod.snd he
    refine ⟨scaleFirst a p, ⟨p, hp, rfl⟩, ?_⟩
    apply Prod.ext
    · simp only [scaleFirst, PiLp.toLp_apply, Fin.isValue, ite_true, Fin.reduceEq, ite_false]
      rw [← hu]
      ring
    · simpa [scaleFirst] using hz

theorem Assouad.projectedSlice_scaleFirst {d α C a z : ℝ} {f : ℝ → ℝ} {E : Set Space}
    (hd : 0 < d) (ha : 0 < a) (h : Assouad d α C (ProjectedSlice f E z)) :
    Assouad (a * d) α C (ProjectedSlice (fun t => a * f t) (scaleFirst a '' E) z) := by
  rw [WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.projectedSlice_scaleFirst]
  simpa only [add_zero] using h.affine_image (b := 0) hd ha

/-- The exact analytic normalization required by the frozen conclusion. -/
def NormalizedC2Slope (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ z ∈ Icc (-1 : ℝ) 1,
    |f z| ≤ 1 ∧ |deriv f z| ≤ 1 ∧ |deriv (deriv f) z| ≤ 1

theorem normalizedC2Slope_of_div {M : ℝ} {f : ℝ → ℝ} (hM : 0 < M)
    (hf : ContDiff ℝ 2 f)
    (hbound : ∀ z ∈ Icc (-1 : ℝ) 1,
      |f z| ≤ M ∧ |deriv f z| ≤ M ∧ |deriv (deriv f) z| ≤ M) :
    NormalizedC2Slope (fun z => f z / M) := by
  have hd : deriv (fun z => f z / M) = fun z => deriv f z / M :=
    funext fun _ => deriv_div_const M
  have hdd : deriv (deriv (fun z => f z / M)) = fun z => deriv (deriv f) z / M := by
    rw [hd]
    exact funext fun _ => deriv_div_const M
  refine ⟨hf.div_const M, ?_⟩
  intro z hz
  obtain ⟨h₀, h₁, h₂⟩ := hbound z hz
  rw [hdd, hd]
  simp only [abs_div, abs_of_pos hM]
  exact ⟨(div_le_one hM).mpr h₀, (div_le_one hM).mpr h₁, (div_le_one hM).mpr h₂⟩

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
