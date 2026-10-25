-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/LabelDiameter.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelGood

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory

variable {α : Type*} [MeasurableSpace α] (p : Model α)

theorem I_eq_Icc (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) :
    p.I k s i = Icc ((p.j k s i : ℕ) / (2 : ℝ) ^ p.T k s)
      ((p.j k s i : ℕ) / (2 : ℝ) ^ p.T k s + p.q k s) := by
  rw [I, timeBlock, p.q_eq_inv]
  congr 1
  ring

theorem I_time_distance {k : ℕ} {s : ℝ} {i : Fin (p.n k s)} {t u : ℝ}
    (ht : t ∈ p.I k s i) (hu : u ∈ p.I k s i) : |t - u| ≤ p.q k s := by
  rw [p.I_eq_Icc] at ht hu
  rw [abs_le]
  constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]

/-- A true label has uniformly small base diameter in the original
coordinates, independently of the hidden affine coefficients. -/
theorem label_base_diameter (hp : p.Valid) {k : ℕ} {s : ℝ}
    {i : Fin (p.n k s)} (hs : 0 ≤ s) (hi : p.Label k s i)
    (hBA : p.B k s i ⊆ p.A k s i) {u w : α × ℝ}
    (hu : u ∈ p.B k s i ×ˢ p.I k s i) (hw : w ∈ p.B k s i ×ˢ p.I k s i) :
    ‖p.base k u - p.base k w‖ ≤ 6 * p.K k ^ 2 * p.q k s := by
  have hK : 1 ≤ p.K k := hp.K_ge k
  have hK0 : 0 ≤ p.K k := le_trans zero_le_one hK
  have hq : 0 ≤ p.q k s := (p.q_pos k s).le
  have hsubabs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  have hg : p.g k s ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.N_ge k])
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.ℓ_pos.le) hs
  have htime := p.I_time_distance hu.2 hw.2
  have hc := hi.2.2.2.1
  have hgeo := hi.2.2.2.2.2.1
  obtain ⟨huZ, huY, _⟩ := hgeo u.1 (hBA hu.1) u.2 hu.2
  obtain ⟨hwZ, hwY, _⟩ := hgeo w.1 (hBA hw.1) w.2 hw.2
  have hZ : |p.x k u.1 u.2 1 - p.x k w.1 w.2 1| ≤ 3 * p.K k * p.q k s := by
    calc
      _ = |(p.x k u.1 u.2 1 - p.c k s i 0 - u.2 * p.c k s i 1) -
          (p.x k w.1 w.2 1 - p.c k s i 0 - w.2 * p.c k s i 1) +
            (u.2 - w.2) * p.c k s i 1| := by congr 1; ring
      _ ≤ |p.x k u.1 u.2 1 - p.c k s i 0 - u.2 * p.c k s i 1| +
          |p.x k w.1 w.2 1 - p.c k s i 0 - w.2 * p.c k s i 1| +
            |u.2 - w.2| * |p.c k s i 1| := by
        exact (abs_add_le _ _).trans (add_le_add (hsubabs _ _) (by rw [abs_mul]))
      _ ≤ p.K k * p.q k s + p.K k * p.q k s + p.q k s * p.K k :=
        add_le_add (add_le_add huZ hwZ)
          (mul_le_mul htime (hc 1) (abs_nonneg _) hq)
      _ = _ := by ring
  have hY : |p.x k u.1 u.2 2 - p.x k w.1 w.2 2| ≤
      6 * p.K k ^ 2 * p.q k s := by
    calc
      _ = |(p.x k u.1 u.2 2 - p.c k s i 2 - u.2 * p.c k s i 3 -
            p.c k s i 4 * p.x k u.1 u.2 1) -
          (p.x k w.1 w.2 2 - p.c k s i 2 - w.2 * p.c k s i 3 -
            p.c k s i 4 * p.x k w.1 w.2 1) +
          (u.2 - w.2) * p.c k s i 3 +
          p.c k s i 4 * (p.x k u.1 u.2 1 - p.x k w.1 w.2 1)| := by congr 1; ring
      _ ≤ |p.x k u.1 u.2 2 - p.c k s i 2 - u.2 * p.c k s i 3 -
            p.c k s i 4 * p.x k u.1 u.2 1| +
          |p.x k w.1 w.2 2 - p.c k s i 2 - w.2 * p.c k s i 3 -
            p.c k s i 4 * p.x k w.1 w.2 1| +
          |u.2 - w.2| * |p.c k s i 3| +
          |p.c k s i 4| * |p.x k u.1 u.2 1 - p.x k w.1 w.2 1| := by
        exact (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (hsubabs _ _) (by rw [abs_mul])))
          (by rw [abs_mul]))
      _ ≤ p.K k * p.q k s * p.g k s + p.K k * p.q k s * p.g k s +
          p.q k s * p.K k + p.K k * (3 * p.K k * p.q k s) :=
        add_le_add (add_le_add (add_le_add huY hwY)
          (mul_le_mul htime (hc 3) (abs_nonneg _) hq))
          (mul_le_mul (hc 4) hZ (abs_nonneg _) hK0)
      _ ≤ p.K k * p.q k s + p.K k * p.q k s +
          p.q k s * p.K k + p.K k * (3 * p.K k * p.q k s) := by
        have hgq : p.K k * p.q k s * p.g k s ≤ p.K k * p.q k s := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hg (mul_nonneg hK0 hq)
        exact add_le_add (add_le_add (add_le_add hgq hgq) le_rfl) le_rfl
      _ ≤ _ := by
        have hKq : p.K k * p.q k s ≤ p.K k ^ 2 * p.q k s :=
          mul_le_mul_of_nonneg_right (by nlinarith : p.K k ≤ p.K k ^ 2) hq
        nlinarith
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 6 * p.K k ^ 2 * p.q k s)).mpr
  intro e
  fin_cases e
  · change ‖u.2 - w.2‖ ≤ _
    rw [Real.norm_eq_abs]
    apply htime.trans
    have : 1 ≤ 6 * p.K k ^ 2 := by nlinarith
    nlinarith
  · change ‖p.x k u.1 u.2 1 - p.x k w.1 w.2 1‖ ≤ _
    rw [Real.norm_eq_abs]
    apply hZ.trans
    have : 3 * p.K k ≤ 6 * p.K k ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hq
  · exact hY

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
