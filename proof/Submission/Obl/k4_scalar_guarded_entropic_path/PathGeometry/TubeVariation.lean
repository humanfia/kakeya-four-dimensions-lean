/-
Adapted from this LOT tree, obligation o093, session x0535, commit 05931f40,
Submission/Obl/k4_scalar_critical_path_terminal/TubeVariation.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PacketGraphBounds
import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry

/-! Whole-tube quadratic bounds control variation in normalized time and
transverse position. This reuses the accepted bounded-quadratic variation
theorem, with no coefficient-height loss in the original coordinates. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ActualPacketGraphs

open Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open Submission.Obl.k4_eligibility_sign_description (Quadratic)

noncomputable section

def tubeValue (f : ℝ → ℝ → ℝ) (t₀ q u v a τ z : ℝ) : ℝ :=
  f (t₀ + q * τ) (u + (t₀ + q * τ) * v + a * z)

theorem tubeValue_time_quadratic {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f)
    (t₀ q u v a z : ℝ) : Quadratic (fun τ => tubeValue f t₀ q u v a τ z) := by
  obtain ⟨A, B, C, hc⟩ := hf.line t₀ q (u + t₀ * v + a * z) (q * v)
  refine ⟨C, B, A, ?_⟩
  intro τ
  dsimp [tubeValue]
  rw [show u + (t₀ + q * τ) * v + a * z =
    (u + t₀ * v + a * z) + (q * v) * τ by ring, hc]
  ring

theorem tubeValue_space_quadratic {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f)
    (t₀ q u v a τ : ℝ) : Quadratic (fun s => tubeValue f t₀ q u v a τ (-2 + 4 * s)) := by
  obtain ⟨A, B, C, hc⟩ := hf.line (t₀ + q * τ) 0
    (u + (t₀ + q * τ) * v - 2 * a) (4 * a)
  refine ⟨C, B, A, ?_⟩
  intro s
  dsimp [tubeValue]
  have harg : u + (t₀ + q * τ) * v + a * (-2 + 4 * s) =
      (u + (t₀ + q * τ) * v - 2 * a) + (4 * a) * s := by ring
  simp only [zero_mul, add_zero] at hc
  rw [harg, hc]
  ring

/-- A whole-tube bound has a fixed Lipschitz constant in the tube's
normalized coordinates. Physical dyadic scales do not enter the constant. -/
theorem tubeValue_variation {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f)
    {t₀ q u v a M τ τ' z z' : ℝ}
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z₀ ∈ Icc (-2 : ℝ) 2,
      |tubeValue f t₀ q u v a s z₀| ≤ M)
    (hτ : τ ∈ Icc (0 : ℝ) 1) (hτ' : τ' ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (-2 : ℝ) 2) (hz' : z' ∈ Icc (-2 : ℝ) 2) :
    |tubeValue f t₀ q u v a τ z - tubeValue f t₀ q u v a τ' z'| ≤
      51 * M * (|τ - τ'| + |z - z'|) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound τ hτ z hz)
  have htime := Submission.Obl.k4_horizon_chart_assembly.bounded_quadratic_variation
    (tubeValue_time_quadratic hf t₀ q u v a z)
    (fun s hs => hbound s hs z hz) hτ hτ'
  have hs : (z + 2) / 4 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hz.1, hz.2]
  have hs' : (z' + 2) / 4 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hz'.1, hz'.2]
  have hspace := Submission.Obl.k4_horizon_chart_assembly.bounded_quadratic_variation
    (tubeValue_space_quadratic hf t₀ q u v a τ')
    (fun s hs => hbound τ' hτ' (-2 + 4 * s) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    hs hs'
  have hzid : -2 + 4 * ((z + 2) / 4) = z := by ring
  have hzid' : -2 + 4 * ((z' + 2) / 4) = z' := by ring
  have hdist : |(z + 2) / 4 - (z' + 2) / 4| = |z - z'| / 4 := by
    rw [show (z + 2) / 4 - (z' + 2) / 4 = (z - z') / 4 by ring, abs_div]
    norm_num
  rw [hzid, hzid', hdist] at hspace
  have hspace' : |tubeValue f t₀ q u v a τ' z - tubeValue f t₀ q u v a τ' z'| ≤
      51 * M * |z - z'| := by
    apply hspace.trans
    gcongr
    exact div_le_self (abs_nonneg _) (by norm_num)
  calc
    _ ≤ |tubeValue f t₀ q u v a τ z - tubeValue f t₀ q u v a τ' z| +
        |tubeValue f t₀ q u v a τ' z - tubeValue f t₀ q u v a τ' z'| := abs_sub_le _ _ _
    _ ≤ 51 * M * |τ - τ'| + 51 * M * |z - z'| := add_le_add htime hspace'
    _ = _ := by ring

/-- Return the normalized estimate to the original time and spatial
coordinates. The spatial denominator is the actual fitted width. -/
theorem tube_variation {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f)
    {t₀ q u v a M t s y y' : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hbound : ∀ τ ∈ Icc t₀ (t₀ + q), ∀ z ∈ Icc (-2 : ℝ) 2,
      |f τ (u + τ * v + a * z)| ≤ M)
    (ht : t ∈ Icc t₀ (t₀ + q)) (hs : s ∈ Icc t₀ (t₀ + q))
    (hy : (y - (u + t * v)) / a ∈ Icc (-2 : ℝ) 2)
    (hy' : (y' - (u + s * v)) / a ∈ Icc (-2 : ℝ) 2) :
    |f t y - f s y'| ≤
      51 * M * (|t - s| / q + |(y - y') - v * (t - s)| / a) := by
  have hbound' : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-2 : ℝ) 2,
      |tubeValue f t₀ q u v a τ z| ≤ M := by
    intro τ hτ z hz
    apply hbound _ ⟨?_, ?_⟩ z hz
    · nlinarith [hτ.1]
    · nlinarith [hτ.2]
  have htime (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + q)) :
      (t - t₀) / q ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hq.le
    · apply (div_le_iff₀ hq).mpr
      linarith [ht.2]
  have hdecode (t y : ℝ) :
      tubeValue f t₀ q u v a ((t - t₀) / q) ((y - (u + t * v)) / a) = f t y := by
    unfold tubeValue
    congr 1 <;> field_simp <;> ring
  have h := tubeValue_variation hf hbound' (htime t ht) (htime s hs) hy hy'
  rw [hdecode, hdecode] at h
  have hdistTime : |(t - t₀) / q - (s - t₀) / q| = |t - s| / q := by
    rw [show (t - t₀) / q - (s - t₀) / q = (t - s) / q by ring,
      abs_div, abs_of_pos hq]
  have hdistSpace : |(y - (u + t * v)) / a - (y' - (u + s * v)) / a| =
      |(y - y') - v * (t - s)| / a := by
    rw [show (y - (u + t * v)) / a - (y' - (u + s * v)) / a =
      ((y - y') - v * (t - s)) / a by ring, abs_div, abs_of_pos ha]
  simpa only [hdistTime, hdistSpace] using h

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ActualPacketGraphs
