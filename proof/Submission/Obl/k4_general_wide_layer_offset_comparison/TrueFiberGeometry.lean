import Submission.Obl.k4_general_wide_layer_offset_comparison.ComparedInterface
import Submission.Obl.k4_general_wide_layer_offset_comparison.DomainCoordinates

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/TrueFiberGeometry.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The center of a true fiber at a specified time depends only on the
original true label and original major bin. -/
def trueFiberPoint (k : ℕ) (r m : ℝ) (Q : Fin (p.n k r))
    (tag : Fin 2 → ℤ) (t : ℝ) : Fin 3 → ℝ :=
  let Z := (tag 1 : ℝ) * p.N k ^ (-m) + t * ((tag 0 : ℝ) * p.N k ^ (-m))
  ![t, Z, p.c k r Q 2 + t * p.c k r Q 3 + p.c k r Q 4 * Z]

theorem trueFiberPoint_mem {k : ℕ} {r m H : ℝ} (hN : 0 < p.N k) (hH : 0 ≤ H)
    (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) {t : ℝ}
    (ht : t ∈ block (p.T k r) (p.j k r Q)) :
    p.trueFiberPoint k r m Q tag t ∈ p.trueFiberBox k r m H Q tag := by
  refine ⟨ht, ?_, ?_⟩
  · simp only [trueFiberPoint, Matrix.cons_val_one, Matrix.cons_val_zero, sub_self, abs_zero]
    positivity
  · change |p.c k r Q 2 + t * p.c k r Q 3 +
        p.c k r Q 4 * ((tag 1 : ℝ) * p.N k ^ (-m) + t * ((tag 0 : ℝ) * p.N k ^ (-m))) -
        p.c k r Q 2 - t * p.c k r Q 3 -
        p.c k r Q 4 * ((tag 1 : ℝ) * p.N k ^ (-m) + t * ((tag 0 : ℝ) * p.N k ^ (-m)))| ≤ _
    have heq : p.c k r Q 2 + t * p.c k r Q 3 +
        p.c k r Q 4 * ((tag 1 : ℝ) * p.N k ^ (-m) + t * ((tag 0 : ℝ) * p.N k ^ (-m))) -
        p.c k r Q 2 - t * p.c k r Q 3 -
        p.c k r Q 4 * ((tag 1 : ℝ) * p.N k ^ (-m) + t * ((tag 0 : ℝ) * p.N k ^ (-m))) = 0 := by ring
    rw [heq, abs_zero]
    positivity

/-- Every point of the whole fiber lies in one affine transverse band.
The bound applies to the physical H-sized fiber without changing H. -/
theorem trueFiberBox_transverse_band {k : ℕ} {r m H K : ℝ}
    (hN : 0 < p.N k) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ)
    (hc : |p.c k r Q 4| ≤ K)
    (hχ : p.N k ^ (-m) ≤ (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
    {z : Fin 3 → ℝ} (hz : z ∈ p.trueFiberBox k r m H Q tag) :
    |z 2 - (p.c k r Q 2 + p.c k r Q 4 * ((tag 1 : ℝ) * p.N k ^ (-m))) -
      z 0 * (p.c k r Q 3 + p.c k r Q 4 * ((tag 0 : ℝ) * p.N k ^ (-m)))| ≤
      H * (1 + K) * ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) := by
  calc
    _ = |(z 2 - p.c k r Q 2 - z 0 * p.c k r Q 3 - p.c k r Q 4 * z 1) +
        p.c k r Q 4 * (z 1 - ((tag 1 : ℝ) * p.N k ^ (-m) +
          z 0 * ((tag 0 : ℝ) * p.N k ^ (-m))))| := by congr 1; ring
    _ ≤ |z 2 - p.c k r Q 2 - z 0 * p.c k r Q 3 - p.c k r Q 4 * z 1| +
        |p.c k r Q 4| * |z 1 - ((tag 1 : ℝ) * p.N k ^ (-m) +
          z 0 * ((tag 0 : ℝ) * p.N k ^ (-m)))| := by
      simpa only [abs_mul] using abs_add_le
        (z 2 - p.c k r Q 2 - z 0 * p.c k r Q 3 - p.c k r Q 4 * z 1)
        (p.c k r Q 4 * (z 1 - ((tag 1 : ℝ) * p.N k ^ (-m) +
          z 0 * ((tag 0 : ℝ) * p.N k ^ (-m)))))
    _ ≤ H * ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) +
        K * (H * p.N k ^ (-m)) :=
      add_le_add hz.2.2 (mul_le_mul hc hz.2.1 (abs_nonneg _) hK)
    _ ≤ H * ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) +
        K * (H * ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))) := by gcongr
    _ = _ := by ring

end Parent

/-- A short affine band has a small diameter in any longer moving chart.
Only the difference of the two velocities enters the estimate. -/
theorem moving_chart_diameter {t t' y y' q h b u v time center speed B V : ℝ}
    (hh : 0 < h) (hb : 0 < b) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (ht : |t - t'| ≤ q)
    (hy : |y - center - t * speed| ≤ B)
    (hy' : |y' - center - t' * speed| ≤ B)
    (hv : |speed - v| ≤ V) :
    |(t - time) / h - (t' - time) / h| +
      |(y - u - t * v) / b - (y' - u - t' * v) / b| ≤
        q / h + (2 * B + q * V) / b := by
  have htime : |(t - time) / h - (t' - time) / h| ≤ q / h := by
    rw [← sub_div, show t - time - (t' - time) = t - t' by ring, abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right ht hh.le
  have hposition : |y - u - t * v - (y' - u - t' * v)| ≤ 2 * B + q * V := by
    calc
      _ = |((y - center - t * speed) - (y' - center - t' * speed)) +
          (t - t') * (speed - v)| := by congr 1; ring
      _ ≤ |y - center - t * speed| + |y' - center - t' * speed| +
          |t - t'| * |speed - v| := by
        exact (abs_add_le _ _).trans
          (add_le_add (by simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (y - center - t * speed) 0 (y' - center - t' * speed)))
            (by rw [abs_mul]))
      _ ≤ B + B + q * V :=
        add_le_add (add_le_add hy hy')
          (mul_le_mul ht hv (abs_nonneg _) ((abs_nonneg _).trans ht))
      _ = _ := by ring
  exact add_le_add htime (by
    rw [← sub_div, abs_div, abs_of_pos hb]
    exact div_le_div_of_nonneg_right hposition hb.le)

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The full physical true fiber is short in the actual long comparison
chart. Its transverse and time scales remain independent. -/
theorem trueFiberBox_chart_diameter {k : ℕ} {r m H h g b time u v : ℝ}
    (hN : 0 < p.N k) (hH : 1 ≤ H) (hK : 0 ≤ p.K k) (hKH : p.K k ≤ H)
    (hh : 0 < h) (hg : 0 < g) (hb : 0 < b) (hmove : h * g = b)
    (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ)
    (hc : |p.c k r Q 4| ≤ p.K k)
    (hχ : p.N k ^ (-m) ≤ (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
    (hv : |p.c k r Q 3 + p.c k r Q 4 * ((tag 0 : ℝ) * p.N k ^ (-m)) - v| ≤
      2 * p.K k * p.N k ^ (-p.ℓ * r) + g)
    {z z' : Fin 3 → ℝ}
    (hz : z ∈ p.trueFiberBox k r m H Q tag)
    (hz' : z' ∈ p.trueFiberBox k r m H Q tag) :
    let q := (2 : ℝ) ^ (-(p.T k r : ℤ))
    let g₀ := p.N k ^ (-p.ℓ * r)
    let x := projectedDomainCoordinates time (32 * h) u v (32 * b) z
    let x' := projectedDomainCoordinates time (32 * h) u v (32 * b) z'
    |x 0 - x' 0| + |x 1 - x' 1| ≤ H ^ 2 * (q * g₀ / b + q * g / b) := by
  dsimp only
  let q := (2 : ℝ) ^ (-(p.T k r : ℤ))
  let g₀ := p.N k ^ (-p.ℓ * r)
  have hq : 0 < q := by dsimp [q]; positivity
  have hg₀ : 0 < g₀ := by dsimp [g₀]; positivity
  have hH0 : 0 ≤ H := by linarith
  have htime : |z 0 - z' 0| ≤ q := by
    have heq : ((((p.j k r Q : ℕ) : ℝ) + 1) / (2 : ℝ) ^ p.T k r) -
        (((p.j k r Q : ℕ) : ℝ) / (2 : ℝ) ^ p.T k r) = q := by
      dsimp [q]
      rw [zpow_neg, zpow_natCast]
      ring
    have ht := hz.1
    have ht' := hz'.1
    change z 0 ∈ Icc _ _ at ht
    change z' 0 ∈ Icc _ _ at ht'
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
  have hband := p.trueFiberBox_transverse_band hN hH0 hK Q tag hc hχ hz
  have hband' := p.trueFiberBox_transverse_band hN hH0 hK Q tag hc hχ hz'
  have hd := moving_chart_diameter (by positivity : 0 < 32 * h)
    (by positivity : 0 < 32 * b)
    (by positivity : 0 ≤ H * (1 + p.K k) * (q * g₀))
    (by positivity : 0 ≤ 2 * p.K k * g₀ + g)
    htime hband hband' hv (u := u) (time := time)
  change |(z 0 - time) / (32 * h) - (z' 0 - time) / (32 * h)| +
    |(z 2 - u - z 0 * v) / (32 * b) - (z' 2 - u - z' 0 * v) / (32 * b)| ≤ _
  apply hd.trans
  have hHsq : 1 ≤ H ^ 2 := one_le_pow₀ hH
  have hpoly : 2 * H * (1 + p.K k) + 2 * p.K k ≤ 6 * H ^ 2 := by
    calc
      _ ≤ 2 * H * (1 + H) + 2 * H := by gcongr
      _ ≤ _ := by nlinarith
  have hnum : 2 * (H * (1 + p.K k) * (q * g₀)) + q * (2 * p.K k * g₀ + g) ≤
      6 * H ^ 2 * (q * g₀) + q * g := by
    nlinarith [mul_le_mul_of_nonneg_right hpoly (mul_nonneg hq.le hg₀.le)]
  have hfirst : q / (32 * h) = q * g / (32 * b) := by
    rw [← hmove]
    field_simp
  calc
    _ ≤ q / (32 * h) + (6 * H ^ 2 * (q * g₀) + q * g) / (32 * b) :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hnum (by positivity))
    _ = (6 * H ^ 2 * (q * g₀) + 2 * (q * g)) / (32 * b) := by rw [hfirst]; ring
    _ ≤ H ^ 2 * (q * g₀ / b + q * g / b) := by
      apply (div_le_iff₀ (by positivity : 0 < 32 * b)).mpr
      have heq : H ^ 2 * (q * g₀ / b + q * g / b) * (32 * b) =
          32 * H ^ 2 * (q * g₀ + q * g) := by field_simp <;> ring
      rw [heq]
      nlinarith [mul_nonneg (sq_nonneg H) (mul_nonneg hq.le hg₀.le),
        mul_le_mul_of_nonneg_right hHsq (mul_nonneg hq.le hg.le)]

end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
