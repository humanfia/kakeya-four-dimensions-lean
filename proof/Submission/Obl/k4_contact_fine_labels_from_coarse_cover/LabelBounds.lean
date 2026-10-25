-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/LabelBounds.lean
import Mathlib
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.LabelChart
import Submission.Lib.K4QuadraticSheetCore.SheetCore

/-!
# Bounds for the label chart

For a true block with constants `c`, left time `t₀`, length `q` and transverse width `g ≤ K q`,
centred at `Z₀ = c₀ + t₀ c₁`, `Y₀ = c₂ + t₀ c₃ + c₄ Z₀`:

* `label_rate_rigidity`: two trajectories of the block with contact error `ε` and separated
  velocities force `|c₄ - t₀|` and `|c₃ + Z₀|` to be of order `K q / θ`; this is what makes the
  Heisenberg zoom of the whole block bounded (the label's own rate rigidity).
* `chartPoint_core`, `chartPoint_mem_cube`: with `μ = 200 K³ / θ`, every base point of the block
  lies in the unit cube after the chart, with margin `1/8` in the last two coordinates, so that
  points of the block's time interval near a block point also lie in the cube
  (`chartPoint_mem_cube_of_near`).
* `l1dist_chartPoint_le`: the chart costs at most `7 K / q²` in distance.
-/

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Submission.Lib.K4QuadraticSheetCore

open MvPolynomial Set

noncomputable section

/-- The horizontal centre of a label at its left time. -/
def labelZ₀ (t₀ : ℝ) (c : Fin 5 → ℝ) : ℝ := c 0 + t₀ * c 1

/-- The transverse centre of a label at its left time. -/
def labelY₀ (t₀ : ℝ) (c : Fin 5 → ℝ) : ℝ := c 2 + t₀ * c 3 + c 4 * labelZ₀ t₀ c

/-- The contact scaling of the label chart. -/
def labelμ (K θ : ℝ) : ℝ := 200 * K ^ 3 / θ

/-- The label row at the left time combines into the rate defect. -/
theorem label_rate_defect (K q g ε t₀ : ℝ) (c : Fin 5 → ℝ) (b : Fin 6 → ℝ)
    (h1 : |b 0 + t₀ * b 3 - c 0 - t₀ * c 1| ≤ K * q) (h2 : |b 4 - c 3 - c 4 * b 3| ≤ K * g)
    (h3 : |b 4 + b 0| ≤ ε) :
    |-(c 3 + labelZ₀ t₀ c) + (t₀ - c 4) * b 3| ≤ K * g + ε + K * q := by
  have hid : -(c 3 + labelZ₀ t₀ c) + (t₀ - c 4) * b 3 =
      (b 4 - c 3 - c 4 * b 3) - (b 4 + b 0) + (b 0 + t₀ * b 3 - c 0 - t₀ * c 1) := by
    simp only [labelZ₀]; ring
  rw [hid]
  calc _ ≤ |(b 4 - c 3 - c 4 * b 3) - (b 4 + b 0)| + |b 0 + t₀ * b 3 - c 0 - t₀ * c 1| :=
        abs_add_le _ _
    _ ≤ (|b 4 - c 3 - c 4 * b 3| + |b 4 + b 0|) + |b 0 + t₀ * b 3 - c 0 - t₀ * c 1| := by
        gcongr; exact abs_sub _ _
    _ ≤ _ := by linarith

/-- **Rate rigidity of one label.** Two contact trajectories of a label with velocities
`θ`-apart pin `c₄` to `t₀` and `c₃` to `-Z₀`. -/
theorem label_rate_rigidity (K q g ε t₀ θ : ℝ) (c : Fin 5 → ℝ) (b b' : Fin 6 → ℝ)
    (hK : 1 ≤ K) (hθ : 0 < θ)
    (h1 : |b 0 + t₀ * b 3 - c 0 - t₀ * c 1| ≤ K * q) (h2 : |b 4 - c 3 - c 4 * b 3| ≤ K * g)
    (h3 : |b 4 + b 0| ≤ ε)
    (h1' : |b' 0 + t₀ * b' 3 - c 0 - t₀ * c 1| ≤ K * q) (h2' : |b' 4 - c 3 - c 4 * b' 3| ≤ K * g)
    (h3' : |b' 4 + b' 0| ≤ ε)
    (hsep : θ ≤ |b 3 - b' 3|) (hvel : |b 3| ≤ K) :
    |c 4 - t₀| ≤ 2 * (K * g + ε + K * q) / θ ∧
      |c 3 + labelZ₀ t₀ c| ≤ (K * g + ε + K * q) * (1 + 2 * K / θ) := by
  set δ₁ := K * g + ε + K * q with hδ₁
  have e := label_rate_defect K q g ε t₀ c b h1 h2 h3
  have e' := label_rate_defect K q g ε t₀ c b' h1' h2' h3'
  rw [← hδ₁] at e e'
  have hδ₁0 : 0 ≤ δ₁ := le_trans (abs_nonneg _) e
  have hdiff : |(t₀ - c 4) * (b 3 - b' 3)| ≤ 2 * δ₁ := by
    have : (t₀ - c 4) * (b 3 - b' 3) =
        (-(c 3 + labelZ₀ t₀ c) + (t₀ - c 4) * b 3) -
          (-(c 3 + labelZ₀ t₀ c) + (t₀ - c 4) * b' 3) := by ring
    rw [this]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ 2 * δ₁ := by linarith
  have hc4 : |c 4 - t₀| ≤ 2 * δ₁ / θ := by
    rw [le_div_iff₀ hθ, abs_sub_comm]
    rw [abs_mul] at hdiff
    calc |t₀ - c 4| * θ ≤ |t₀ - c 4| * |b 3 - b' 3| :=
          mul_le_mul_of_nonneg_left hsep (abs_nonneg _)
      _ ≤ 2 * δ₁ := hdiff
  refine ⟨hc4, ?_⟩
  have hsplit : c 3 + labelZ₀ t₀ c =
      -(-(c 3 + labelZ₀ t₀ c) + (t₀ - c 4) * b 3) + (t₀ - c 4) * b 3 := by ring
  rw [hsplit]
  have hprod : |(t₀ - c 4) * b 3| ≤ 2 * δ₁ / θ * K := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul hc4 hvel (abs_nonneg _) (by positivity)
  calc _ ≤ |-(-(c 3 + labelZ₀ t₀ c) + (t₀ - c 4) * b 3)| + |(t₀ - c 4) * b 3| := abs_add_le _ _
    _ ≤ δ₁ + 2 * δ₁ / θ * K := by rw [abs_neg]; linarith
    _ = δ₁ * (1 + 2 * K / θ) := by field_simp

/-- The transverse numerator of the zoom along the label box. -/
theorem label_transverse_bound (K q g t₀ : ℝ) (c : Fin 5 → ℝ) (b : Fin 6 → ℝ) (t : ℝ)
    (hK : 0 ≤ K) (hq : 0 ≤ q) (ht : t ∈ Icc t₀ (t₀ + q)) (hc1 : |c 1| ≤ K)
    (hZ : |b 0 + t * b 3 - c 0 - t * c 1| ≤ K * q)
    (hY : |b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| ≤ K * q * g) :
    |(b 1 + t * b 4) - labelY₀ t₀ c + labelZ₀ t₀ c * (t - t₀) -
        t₀ * ((b 0 + t * b 3) - labelZ₀ t₀ c)| ≤
      K * q * g + q * |c 3 + labelZ₀ t₀ c| + 2 * K * q * |c 4 - t₀| := by
  have hZZ : |(b 0 + t * b 3) - labelZ₀ t₀ c| ≤ 2 * K * q := by
    have : (b 0 + t * b 3) - labelZ₀ t₀ c = (b 0 + t * b 3 - c 0 - t * c 1) + (t - t₀) * c 1 := by
      simp only [labelZ₀]; ring
    rw [this]
    have htt : |t - t₀| ≤ q := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    calc _ ≤ |b 0 + t * b 3 - c 0 - t * c 1| + |(t - t₀) * c 1| := abs_add_le _ _
      _ ≤ K * q + q * K := by
          rw [abs_mul]; gcongr
      _ = 2 * K * q := by ring
  have hid : (b 1 + t * b 4) - labelY₀ t₀ c + labelZ₀ t₀ c * (t - t₀) -
        t₀ * ((b 0 + t * b 3) - labelZ₀ t₀ c) =
      (b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)) +
        (t - t₀) * (c 3 + labelZ₀ t₀ c) + (c 4 - t₀) * ((b 0 + t * b 3) - labelZ₀ t₀ c) := by
    simp only [labelY₀]; ring
  rw [hid]
  have htt : |t - t₀| ≤ q := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  calc _ ≤ |b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| +
          |(t - t₀) * (c 3 + labelZ₀ t₀ c)| +
          |(c 4 - t₀) * ((b 0 + t * b 3) - labelZ₀ t₀ c)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K * q * g + q * |c 3 + labelZ₀ t₀ c| + |c 4 - t₀| * (2 * K * q) := by
        rw [abs_mul, abs_mul]
        gcongr
    _ = _ := by ring

/-- Membership in the unit cube, coordinatewise. -/
theorem mem_cube_iff (x : Fin 3 → ℝ) :
    x ∈ Icc (0 : Fin 3 → ℝ) 1 ↔
      (0 ≤ x 0 ∧ x 0 ≤ 1) ∧ (0 ≤ x 1 ∧ x 1 ≤ 1) ∧ (0 ≤ x 2 ∧ x 2 ≤ 1) := by
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨⟨h0 0, h1 0⟩, ⟨h0 1, h1 1⟩, ⟨h0 2, h1 2⟩⟩
  · rintro ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
    · exact a0
    · exact a1
    · exact a2
    · exact b0
    · exact b1
    · exact b2

set_option maxHeartbeats 1000000 in
/-- **The label box lies in the core of the unit cube after the chart.** -/
theorem chartPoint_core (K q g ε θ t₀ : ℝ) (c : Fin 5 → ℝ) (b : Fin 6 → ℝ) (t : ℝ)
    (hK : 1 ≤ K) (hq : 0 < q) (hgq : g ≤ K * q) (hg0 : 0 ≤ g) (hε : 0 ≤ ε) (hεq : ε ≤ q)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hc1 : |c 1| ≤ K)
    (hrate4 : |c 4 - t₀| ≤ 2 * (K * g + ε + K * q) / θ)
    (hrate3 : |c 3 + labelZ₀ t₀ c| ≤ (K * g + ε + K * q) * (1 + 2 * K / θ))
    (ht : t ∈ Icc t₀ (t₀ + q))
    (hZ : |b 0 + t * b 3 - c 0 - t * c 1| ≤ K * q)
    (hY : |b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| ≤ K * q * g) :
    0 ≤ chartPoint t₀ q (labelμ K θ) (labelZ₀ t₀ c) (labelY₀ t₀ c) (basePt b t) 0 ∧
      chartPoint t₀ q (labelμ K θ) (labelZ₀ t₀ c) (labelY₀ t₀ c) (basePt b t) 0 ≤ 1 ∧
      |chartPoint t₀ q (labelμ K θ) (labelZ₀ t₀ c) (labelY₀ t₀ c) (basePt b t) 1 - 1 / 2| ≤
        1 / 4 ∧
      1 / 8 ≤ chartPoint t₀ q (labelμ K θ) (labelZ₀ t₀ c) (labelY₀ t₀ c) (basePt b t) 2 ∧
      chartPoint t₀ q (labelμ K θ) (labelZ₀ t₀ c) (labelY₀ t₀ c) (basePt b t) 2 ≤ 7 / 8 := by
  have hK0 : 0 < K := by linarith
  have hμ : labelμ K θ = 200 * K ^ 3 / θ := rfl
  have hμpos : 0 < labelμ K θ := by rw [hμ]; positivity
  have hKθ : K ≤ K / θ := by rw [le_div_iff₀ hθ]; nlinarith
  have hK3θ : K ^ 3 ≤ K ^ 3 / θ := by rw [le_div_iff₀ hθ]; nlinarith [pow_pos hK0 3]
  have hδ₁ : K * g + ε + K * q ≤ 3 * K ^ 2 * q := by nlinarith
  have hδ₁0 : 0 ≤ K * g + ε + K * q := by positivity
  -- horizontal offset
  have hZZ : |(b 0 + t * b 3) - labelZ₀ t₀ c| ≤ 2 * K * q := by
    have : (b 0 + t * b 3) - labelZ₀ t₀ c = (b 0 + t * b 3 - c 0 - t * c 1) + (t - t₀) * c 1 := by
      simp only [labelZ₀]; ring
    rw [this]
    have htt : |t - t₀| ≤ q := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    calc _ ≤ |b 0 + t * b 3 - c 0 - t * c 1| + |(t - t₀) * c 1| := abs_add_le _ _
      _ ≤ K * q + q * K := by rw [abs_mul]; gcongr
      _ = 2 * K * q := by ring
  -- transverse numerator
  have hnum := label_transverse_bound K q g t₀ c b t hK0.le hq.le ht hc1 hZ hY
  have h3 : q * |c 3 + labelZ₀ t₀ c| ≤ 9 * K ^ 3 * q ^ 2 / θ := by
    have hh : (K * g + ε + K * q) * (1 + 2 * K / θ) ≤ 3 * K ^ 2 * q * (3 * K / θ) := by
      have h1 : 1 + 2 * K / θ ≤ 3 * K / θ := by
        have : 1 ≤ K / θ := le_trans hK (hKθ)
        have e : 3 * K / θ = K / θ + 2 * K / θ := by ring
        linarith
      have h0 : 0 ≤ 1 + 2 * K / θ := by positivity
      calc _ ≤ 3 * K ^ 2 * q * (1 + 2 * K / θ) := mul_le_mul_of_nonneg_right hδ₁ h0
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    calc q * |c 3 + labelZ₀ t₀ c| ≤ q * (3 * K ^ 2 * q * (3 * K / θ)) :=
          mul_le_mul_of_nonneg_left (hrate3.trans hh) hq.le
      _ = 9 * K ^ 3 * q ^ 2 / θ := by field_simp; ring
  have h4 : 2 * K * q * |c 4 - t₀| ≤ 12 * K ^ 3 * q ^ 2 / θ := by
    have hh : 2 * (K * g + ε + K * q) / θ ≤ 6 * K ^ 2 * q / θ := by
      apply div_le_div_of_nonneg_right _ hθ.le; linarith
    calc 2 * K * q * |c 4 - t₀| ≤ 2 * K * q * (6 * K ^ 2 * q / θ) :=
          mul_le_mul_of_nonneg_left (hrate4.trans hh) (by positivity)
      _ = 12 * K ^ 3 * q ^ 2 / θ := by field_simp; ring
  have h5 : K * q * g ≤ K ^ 3 * q ^ 2 / θ := by
    have : K * q * g ≤ K * q * (K * q) := mul_le_mul_of_nonneg_left hgq (by positivity)
    have e : K * q * (K * q) = K ^ 2 * q ^ 2 := by ring
    have hK2 : K ^ 2 * q ^ 2 ≤ K ^ 3 * q ^ 2 / θ := by
      rw [le_div_iff₀ hθ]
      have : K ^ 2 * θ ≤ K ^ 3 := by nlinarith [pow_pos hK0 2]
      nlinarith [sq_nonneg q]
    linarith
  have hnum' : |(b 1 + t * b 4) - labelY₀ t₀ c + labelZ₀ t₀ c * (t - t₀) -
      t₀ * ((b 0 + t * b 3) - labelZ₀ t₀ c)| ≤ q ^ 2 * labelμ K θ / 8 := by
    have : q ^ 2 * labelμ K θ / 8 = 25 * K ^ 3 * q ^ 2 / θ := by rw [hμ]; field_simp; ring
    rw [this]
    have e : 22 * K ^ 3 * q ^ 2 / θ ≤ 25 * K ^ 3 * q ^ 2 / θ := by
      apply div_le_div_of_nonneg_right _ hθ.le; nlinarith [pow_pos hK0 3, sq_nonneg q]
    have e2 : K ^ 3 * q ^ 2 / θ + 9 * K ^ 3 * q ^ 2 / θ + 12 * K ^ 3 * q ^ 2 / θ =
        22 * K ^ 3 * q ^ 2 / θ := by ring
    linarith
  have hZμ : 2 * K * q ≤ q * labelμ K θ / 4 := by
    rw [hμ]
    have : 8 * K ≤ 200 * K ^ 3 / θ := by
      rw [le_div_iff₀ hθ]; nlinarith [pow_pos hK0 3]
    nlinarith
  set μ := labelμ K θ with hμdef
  set Z₀ := labelZ₀ t₀ c with hZ₀def
  set Y₀ := labelY₀ t₀ c with hY₀def
  set num := (b 1 + t * b 4) - Y₀ + Z₀ * (t - t₀) - t₀ * ((b 0 + t * b 3) - Z₀) with hnumdef
  have e0 : chartPoint t₀ q μ Z₀ Y₀ (basePt b t) 0 = (t - t₀) / q := by
    simp [chartPoint, basePt]
  have e1 : chartPoint t₀ q μ Z₀ Y₀ (basePt b t) 1 =
      (b 0 + t * b 3 - Z₀) / (q * μ) + 1 / 2 := by
    simp [chartPoint, basePt]
  have e2 : chartPoint t₀ q μ Z₀ Y₀ (basePt b t) 2 = num / (q ^ 2 * μ) - (t - t₀) / (2 * q) + 3 / 4 := by
    simp only [chartPoint, basePt, hnumdef, Matrix.cons_val]
  have hnn : |num / (q ^ 2 * μ)| ≤ 1 / 8 := by
    rw [abs_div, abs_of_pos (show (0:ℝ) < q ^ 2 * μ by positivity),
      div_le_iff₀ (by positivity)]
    linarith
  have hZn : |(b 0 + t * b 3 - Z₀) / (q * μ)| ≤ 1 / 4 := by
    rw [abs_div, abs_of_pos (show (0:ℝ) < q * μ by positivity), div_le_iff₀ (by positivity)]
    linarith
  have htq0 : 0 ≤ (t - t₀) / (2 * q) := div_nonneg (by linarith [ht.1]) (by positivity)
  have htq1 : (t - t₀) / (2 * q) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith [ht.2]
  have ht0 : 0 ≤ (t - t₀) / q := div_nonneg (by linarith [ht.1]) hq.le
  have ht1 : (t - t₀) / q ≤ 1 := by rw [div_le_one hq]; linarith [ht.2]
  rw [abs_le] at hnn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show 0 ≤ chartPoint t₀ q μ Z₀ Y₀ (basePt b t) 0
    rw [e0]; exact ht0
  · show chartPoint t₀ q μ Z₀ Y₀ (basePt b t) 0 ≤ 1
    rw [e0]; exact ht1
  · show |chartPoint t₀ q μ Z₀ Y₀ (basePt b t) 1 - 1 / 2| ≤ 1 / 4
    rw [e1]
    have : (b 0 + t * b 3 - Z₀) / (q * μ) + 1 / 2 - 1 / 2 = (b 0 + t * b 3 - Z₀) / (q * μ) := by
      ring
    rw [this]; exact hZn
  · show 1 / 8 ≤ chartPoint t₀ q μ Z₀ Y₀ (basePt b t) 2
    rw [e2]; linarith [hnn.1]
  · show chartPoint t₀ q μ Z₀ Y₀ (basePt b t) 2 ≤ 7 / 8
    rw [e2]; linarith [hnn.2]

/-- **The label box lies in the unit cube after the chart.** -/
theorem chartPoint_mem_cube (K q g ε θ t₀ : ℝ) (c : Fin 5 → ℝ) (b : Fin 6 → ℝ) (t : ℝ)
    (hK : 1 ≤ K) (hq : 0 < q) (hgq : g ≤ K * q) (hg0 : 0 ≤ g) (hε : 0 ≤ ε) (hεq : ε ≤ q)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hc1 : |c 1| ≤ K)
    (hrate4 : |c 4 - t₀| ≤ 2 * (K * g + ε + K * q) / θ)
    (hrate3 : |c 3 + labelZ₀ t₀ c| ≤ (K * g + ε + K * q) * (1 + 2 * K / θ))
    (ht : t ∈ Icc t₀ (t₀ + q))
    (hZ : |b 0 + t * b 3 - c 0 - t * c 1| ≤ K * q)
    (hY : |b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| ≤ K * q * g) :
    chartPoint t₀ q (labelμ K θ) (labelZ₀ t₀ c) (labelY₀ t₀ c) (basePt b t) ∈
      Icc (0 : Fin 3 → ℝ) 1 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := chartPoint_core K q g ε θ t₀ c b t hK hq hgq hg0 hε hεq hθ hθ1
    hc1 hrate4 hrate3 ht hZ hY
  rw [abs_le] at h2
  rw [mem_cube_iff]
  exact ⟨⟨h0, h1⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩, ⟨by linarith, by linarith⟩⟩

/-- A point of the block's time interval whose chart is `1/8`-close (in `ℓ¹`) to the chart of a
block point lies in the unit cube. -/
theorem chartPoint_mem_cube_of_near (K q g ε θ t₀ : ℝ) (c : Fin 5 → ℝ) (b : Fin 6 → ℝ) (t : ℝ)
    (hK : 1 ≤ K) (hq : 0 < q) (hgq : g ≤ K * q) (hg0 : 0 ≤ g) (hε : 0 ≤ ε) (hεq : ε ≤ q)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hc1 : |c 1| ≤ K)
    (hrate4 : |c 4 - t₀| ≤ 2 * (K * g + ε + K * q) / θ)
    (hrate3 : |c 3 + labelZ₀ t₀ c| ≤ (K * g + ε + K * q) * (1 + 2 * K / θ))
    (ht : t ∈ Icc t₀ (t₀ + q))
    (hZ : |b 0 + t * b 3 - c 0 - t * c 1| ≤ K * q)
    (hY : |b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| ≤ K * q * g)
    (p : Fin 3 → ℝ) (hp : p 0 ∈ Icc t₀ (t₀ + q))
    (hnear : l1dist (chartPoint t₀ q (labelμ K θ) (labelZ₀ t₀ c) (labelY₀ t₀ c) (basePt b t))
      (chartPoint t₀ q (labelμ K θ) (labelZ₀ t₀ c) (labelY₀ t₀ c) p) ≤ 1 / 8) :
    chartPoint t₀ q (labelμ K θ) (labelZ₀ t₀ c) (labelY₀ t₀ c) p ∈ Icc (0 : Fin 3 → ℝ) 1 := by
  obtain ⟨-, -, h2, h3, h4⟩ := chartPoint_core K q g ε θ t₀ c b t hK hq hgq hg0 hε hεq hθ hθ1
    hc1 hrate4 hrate3 ht hZ hY
  set x := chartPoint t₀ q (labelμ K θ) (labelZ₀ t₀ c) (labelY₀ t₀ c) (basePt b t)
  set y := chartPoint t₀ q (labelμ K θ) (labelZ₀ t₀ c) (labelY₀ t₀ c) p
  have hd1 : |x 1 - y 1| ≤ 1 / 8 := by
    have := abs_nonneg (x 0 - y 0); have := abs_nonneg (x 2 - y 2)
    simp only [l1dist] at hnear; linarith
  have hd2 : |x 2 - y 2| ≤ 1 / 8 := by
    have := abs_nonneg (x 0 - y 0); have := abs_nonneg (x 1 - y 1)
    simp only [l1dist] at hnear; linarith
  have hy0 : y 0 = (p 0 - t₀) / q := by simp [y, chartPoint]
  have hq0 : 0 ≤ (p 0 - t₀) / q := div_nonneg (by linarith [hp.1]) hq.le
  have hq1 : (p 0 - t₀) / q ≤ 1 := by rw [div_le_one hq]; linarith [hp.2]
  rw [abs_le] at h2 hd1 hd2
  rw [mem_cube_iff, hy0]
  exact ⟨⟨hq0, hq1⟩, ⟨by linarith [h2.1, hd1.2], by linarith [h2.2, hd1.1]⟩,
    ⟨by linarith [hd2.2], by linarith [hd2.1]⟩⟩

/-- **Distances in the chart.** The chart costs at most `7 K / q²` in `ℓ¹` distance. -/
theorem l1dist_chartPoint_le (K q μ t₀ Z₀ Y₀ δ : ℝ) (hK : 1 ≤ K) (hq : 0 < q) (hq1 : q ≤ 1)
    (hμ : 1 ≤ μ) (ht₀ : |t₀| ≤ 1) (hZ₀ : |Z₀| ≤ 2 * K) (x y : Fin 3 → ℝ)
    (hxy : ∀ i, |x i - y i| ≤ δ) :
    l1dist (chartPoint t₀ q μ Z₀ Y₀ x) (chartPoint t₀ q μ Z₀ Y₀ y) ≤ 7 * K * δ / q ^ 2 := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (hxy 0)
  have hμ0 : 0 < μ := by linarith
  have h0 := hxy 0; have h1 := hxy 1; have h2 := hxy 2
  simp only [l1dist, chartPoint, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  have e0 : (x 0 - t₀) / q - (y 0 - t₀) / q = (x 0 - y 0) / q := by ring
  have e1 : (x 1 - Z₀) / (q * μ) + 1 / 2 - ((y 1 - Z₀) / (q * μ) + 1 / 2) =
      (x 1 - y 1) / (q * μ) := by ring
  have e2 : (x 2 - Y₀ + Z₀ * (x 0 - t₀) - t₀ * (x 1 - Z₀)) / (q ^ 2 * μ) - (x 0 - t₀) / (2 * q) +
        3 / 4 - ((y 2 - Y₀ + Z₀ * (y 0 - t₀) - t₀ * (y 1 - Z₀)) / (q ^ 2 * μ) -
          (y 0 - t₀) / (2 * q) + 3 / 4) =
      ((x 2 - y 2) + Z₀ * (x 0 - y 0) - t₀ * (x 1 - y 1)) / (q ^ 2 * μ) - (x 0 - y 0) / (2 * q) := by
    ring
  rw [e0, e1, e2]
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have hb0 : |(x 0 - y 0) / q| ≤ δ / q ^ 2 := by
    rw [abs_div, abs_of_pos hq]
    calc |x 0 - y 0| / q ≤ δ / q := div_le_div_of_nonneg_right h0 hq.le
      _ ≤ δ / q ^ 2 := div_le_div_of_nonneg_left hδ (by positivity) hq2
  have hb1 : |(x 1 - y 1) / (q * μ)| ≤ δ / q ^ 2 := by
    rw [abs_div, abs_of_pos (show (0:ℝ) < q * μ by positivity)]
    calc |x 1 - y 1| / (q * μ) ≤ δ / (q * μ) := div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ δ / q ^ 2 := div_le_div_of_nonneg_left hδ (by positivity) (by nlinarith)
  have hnum : |(x 2 - y 2) + Z₀ * (x 0 - y 0) - t₀ * (x 1 - y 1)| ≤ (1 + 2 * K + 1) * δ := by
    calc _ ≤ |(x 2 - y 2) + Z₀ * (x 0 - y 0)| + |t₀ * (x 1 - y 1)| := abs_sub _ _
      _ ≤ |x 2 - y 2| + |Z₀ * (x 0 - y 0)| + |t₀ * (x 1 - y 1)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ δ + 2 * K * δ + 1 * δ := by
          rw [abs_mul, abs_mul]
          gcongr
      _ = (1 + 2 * K + 1) * δ := by ring
  have hb2 : |((x 2 - y 2) + Z₀ * (x 0 - y 0) - t₀ * (x 1 - y 1)) / (q ^ 2 * μ) -
      (x 0 - y 0) / (2 * q)| ≤ (2 + 2 * K) * δ / q ^ 2 + δ / q ^ 2 := by
    calc _ ≤ |((x 2 - y 2) + Z₀ * (x 0 - y 0) - t₀ * (x 1 - y 1)) / (q ^ 2 * μ)| +
          |(x 0 - y 0) / (2 * q)| := abs_sub _ _
      _ ≤ (2 + 2 * K) * δ / q ^ 2 + δ / q ^ 2 := by
          gcongr
          · rw [abs_div, abs_of_pos (show (0:ℝ) < q ^ 2 * μ by positivity)]
            calc _ ≤ (1 + 2 * K + 1) * δ / (q ^ 2 * μ) :=
                  div_le_div_of_nonneg_right hnum (by positivity)
              _ ≤ (1 + 2 * K + 1) * δ / q ^ 2 :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
              _ = _ := by ring
          · rw [abs_div, abs_of_pos (show (0:ℝ) < 2 * q by positivity)]
            calc |x 0 - y 0| / (2 * q) ≤ δ / (2 * q) := div_le_div_of_nonneg_right h0 (by positivity)
              _ ≤ δ / q ^ 2 := div_le_div_of_nonneg_left hδ (by positivity) (by nlinarith)
  have hsum : δ / q ^ 2 + δ / q ^ 2 + ((2 + 2 * K) * δ / q ^ 2 + δ / q ^ 2) ≤ 7 * K * δ / q ^ 2 := by
    rw [← add_div, ← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  linarith

end

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
