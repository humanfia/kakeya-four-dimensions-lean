import Submission.Obl.k4_scalar_lift_plank.Cells
import Submission.Obl.k4_scalar_coefficient_clustering.Geometry
import Submission.Obl.k4_plank_projected_multiplicity.DirectionPacking

open scoped RealInnerProductSpace

namespace Submission.Obl.k4_paired_full_time_binning

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Record := Fin 4 → ℝ
abbrev Code := Fin 4 → ℤ

def record (u : Plane) (a s : ℝ) : Record := ![u 0, u 1, a, s]

def code (G : ℝ) (x : Record) : Code := fun k => ⌊x k / G⌋

lemma code_record (G : ℝ) (u : Plane) (a s : ℝ) :
    code G (record u a s) = ![⌊u 0 / G⌋, ⌊u 1 / G⌋, ⌊a / G⌋, ⌊s / G⌋] := by
  funext k
  fin_cases k <;> rfl

lemma record_bound {u : Plane} {a s K : ℝ} (hu : ‖u‖ = 1)
    (ha : |a| + |s| ≤ K) (hK : 1 ≤ K) : ∀ k, |record u a s k| ≤ K := by
  intro k
  have hu' (j : Fin 2) : |u j| ≤ K := by
    calc
      |u j| = ‖u j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖u‖ := PiLp.norm_apply_le u j
      _ ≤ K := by simpa [hu] using hK
  fin_cases k
  · exact hu' 0
  · exact hu' 1
  · change |a| ≤ K
    linarith [abs_nonneg s]
  · change |s| ≤ K
    linarith [abs_nonneg a]

/-- Replacing a label by another label in its bin preserves the full affine fit. -/
lemma same_code_fit {G g K : ℝ} (hG : 0 < G) (hgG : g ≤ G) (hK : 2 ≤ K)
    {u u' b v : Plane} {a a' s s' : ℝ}
    (hc : code G (record u a s) = code G (record u' a' s'))
    (hbv : ‖b‖ + ‖v‖ ≤ K)
    (hb : |inner ℝ u b - a| ≤ K * g)
    (hv : |inner ℝ u v - s| ≤ K * g)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |inner ℝ u' (b + t • v) - a' - t * s'| ≤ 6 * K * G := by
  have hd (k : Fin 4) : |record u a s k - record u' a' s' k| ≤ G :=
    Submission.Obl.k4_plank_projected_multiplicity.abs_sub_le_mesh_of_floor_eq hG
      (congrFun hc k)
  have h0 : |u 0 - u' 0| ≤ G := hd 0
  have h1 : |u 1 - u' 1| ≤ G := hd 1
  have ha : |a - a'| ≤ G := hd 2
  have hs : |s - s'| ≤ G := hd 3
  have hn : ‖u - u'‖ ≤ 2 * G := by
    have := Submission.Obl.k4_scalar_coefficient_clustering.plane_norm_le_abs_add (u - u')
    change ‖u - u'‖ ≤ |u 0 - u' 0| + |u 1 - u' 1| at this
    linarith
  have hi (w : Plane) : |inner ℝ (u' - u) w| ≤ 2 * G * ‖w‖ := by
    calc
      _ ≤ ‖u' - u‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ 2 * G * ‖w‖ := by rw [norm_sub_rev]; gcongr
  have hbi : |inner ℝ u' b - a'| ≤ 2 * G * ‖b‖ + K * g + G := by
    calc
      _ = |inner ℝ (u' - u) b + (inner ℝ u b - a) + (a - a')| := by
        congr 1
        rw [inner_sub_left]
        ring
      _ ≤ |inner ℝ (u' - u) b| + |inner ℝ u b - a| + |a - a'| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add (hi b) hb) ha
  have hvi : |inner ℝ u' v - s'| ≤ 2 * G * ‖v‖ + K * g + G := by
    calc
      _ = |inner ℝ (u' - u) v + (inner ℝ u v - s) + (s - s')| := by
        congr 1
        rw [inner_sub_left]
        ring
      _ ≤ |inner ℝ (u' - u) v| + |inner ℝ u v - s| + |s - s'| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add (hi v) hv) hs
  calc
    _ = |(inner ℝ u' b - a') + t * (inner ℝ u' v - s')| := by
      rw [inner_add_right, real_inner_smul_right]
      congr 1
      ring
    _ ≤ |inner ℝ u' b - a'| + |t * (inner ℝ u' v - s')| := abs_add_le _ _
    _ ≤ (2 * G * ‖b‖ + K * g + G) + (2 * G * ‖v‖ + K * g + G) := by
      gcongr
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans
        (by simpa using hvi)
    _ ≤ 6 * K * G := by
      have hKg : K * g ≤ K * G := mul_le_mul_of_nonneg_left hgG (by linarith)
      have hsum : 2 * G * (‖b‖ + ‖v‖) ≤ 2 * G * K :=
        mul_le_mul_of_nonneg_left hbv (by positivity)
      nlinarith

lemma record_neg (u : Plane) (a s : ℝ) :
    record (-u) (-a) (-s) = -record u a s := by
  funext k
  fin_cases k <;> rfl

lemma fit_coefficient_sub {u u' b : Plane} {a a' ε d K : ℝ}
    (hd : ‖u - u'‖ ≤ d) (hbK : ‖b‖ ≤ K)
    (hb : |inner ℝ u b - a| ≤ ε) (hb' : |inner ℝ u' b - a'| ≤ ε)
    (hd0 : 0 ≤ d) : |a - a'| ≤ 2 * ε + d * K := by
  calc
    _ = |-(inner ℝ u b - a) + inner ℝ (u - u') b +
        (inner ℝ u' b - a')| := by rw [inner_sub_left]; congr 1; ring
    _ ≤ |inner ℝ u b - a| + |inner ℝ (u - u') b| + |inner ℝ u' b - a'| := by
      simpa only [abs_neg] using
        (abs_add_le (-(inner ℝ u b - a) + inner ℝ (u - u') b)
          (inner ℝ u' b - a')).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ε + d * K + ε := by
      gcongr
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul hd hbK (norm_nonneg _) hd0)
    _ = _ := by ring

/-- Close projective normals force the full four-coordinate records to be close up to sign. -/
lemma good_records {g H K : ℝ} (hg : 0 < g) (hH : 2 ≤ H) (hHK : 2 * K ≤ H)
    {u u' b v : Plane} {a a' s s' : ℝ}
    (hbv : ‖b‖ + ‖v‖ ≤ K)
    (hb : |inner ℝ u b - a| ≤ K * g) (hv : |inner ℝ u v - s| ≤ K * g)
    (hb' : |inner ℝ u' b - a'| ≤ K * g) (hv' : |inner ℝ u' v - s'| ≤ K * g)
    (hgood : min ‖u - u'‖ ‖u + u'‖ ≤ g * H) :
    (∀ k, |record u a s k - record u' a' s' k| ≤ g * H ^ 2) ∨
    (∀ k, |record u a s k + record u' a' s' k| ≤ g * H ^ 2) := by
  have hK : 0 ≤ K := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hbv
  have hbK : ‖b‖ ≤ K := by linarith [norm_nonneg v]
  have hvK : ‖v‖ ≤ K := by linarith [norm_nonneg b]
  have hscale : 2 * (K * g) + (g * H) * K ≤ g * H ^ 2 := by
    have h1 : 2 * K ≤ K * H := by nlinarith
    have h2 : 2 * (K * H) ≤ H ^ 2 := by nlinarith
    nlinarith
  have hgH : g * H ≤ g * H ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith : H ≤ H ^ 2) hg.le
  have hdir {w : Plane} {c r : ℝ} (hw : ‖u - w‖ ≤ g * H)
      (hwb : |inner ℝ w b - c| ≤ K * g) (hwv : |inner ℝ w v - r| ≤ K * g) :
      ∀ k, |record u a s k - record w c r k| ≤ g * H ^ 2 := by
    have hcoord (j : Fin 2) : |u j - w j| ≤ g * H ^ 2 := by
      have hh := PiLp.norm_apply_le (u - w) j
      change ‖u j - w j‖ ≤ ‖u - w‖ at hh
      have hh' : |u j - w j| ≤ ‖u - w‖ := by
        simpa only [Real.norm_eq_abs] using hh
      exact hh'.trans (hw.trans hgH)
    intro k
    fin_cases k
    · exact hcoord 0
    · exact hcoord 1
    · exact (fit_coefficient_sub hw hbK hb hwb (by positivity)).trans hscale
    · exact (fit_coefficient_sub hw hvK hv hwv (by positivity)).trans hscale
  rcases (min_le_iff.mp hgood) with h | h
  · exact Or.inl (hdir h hb' hv')
  · right
    have hh := hdir (w := -u') (c := -a') (r := -s')
      (by simpa only [sub_neg_eq_add] using h)
      (by simpa only [inner_neg_left, neg_sub_neg, abs_sub_comm] using hb')
      (by simpa only [inner_neg_left, neg_sub_neg, abs_sub_comm] using hv')
    simpa only [record_neg, Pi.neg_apply, sub_neg_eq_add] using hh

end

end Submission.Obl.k4_paired_full_time_binning
