import Mathlib

/- Adapted from this LOT tree, obligation o107, session x0353, commit 96bcaa7b51cc,
   file Submission/Obl/k4_finite_narrowness_path_improvement/ContactBoxes.lean (namespace and imports renamed only). -/

/-! Whole horizontal boxes meeting one reference trajectory fit in one common
contact box of horizontal width H and transverse width H squared. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists

def referenceZ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := p 0 + t * p 2
def referenceY (p : Fin 3 → ℝ) (t : ℝ) : ℝ := p 1 - t * p 0

def horizontalTrueBox (c : Fin 5 → ℝ) (m H K : ℝ) : Set (Fin 3 → ℝ) :=
  {q | |q 0 - m| ≤ H / 2 ∧ |q 1 - c 0 - q 0 * c 1| ≤ K * H ∧
    |q 2 - c 2 - q 0 * c 3 - c 4 * q 1| ≤ K * H ^ 2}

def contactTransverse (m : ℝ) (p q : Fin 3 → ℝ) : ℝ :=
  q 2 - referenceY p (q 0) - m * (q 1 - referenceZ p (q 0))

/-- A contact locates the whole true box, not only its current fitted subset.
No absolute bound on its intercepts or the reference intercepts is needed. -/
theorem horizontalTrueBox_common_contact
    (c : Fin 5 → ℝ) (p q₀ : Fin 3 → ℝ) (m H K D : ℝ)
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hD : D ≤ H ^ 2)
    (hm : |m| ≤ 1) (hc : |c 1| ≤ K) (hv : |p 2| ≤ K)
    (hcenter : |c 3 + c 0 + m * c 1| ≤ K * H) (htilt : |c 4 - m| ≤ K * H)
    (hq₀ : q₀ ∈ horizontalTrueBox c m H K)
    (hcontactZ : |q₀ 1 - referenceZ p (q₀ 0)| ≤ K * D)
    (hcontactY : |q₀ 2 - referenceY p (q₀ 0)| ≤ K * D) :
    ∀ q ∈ horizontalTrueBox c m H K,
      |q 1 - referenceZ p (q 0)| ≤ 8 * K * H ∧
      |contactTransverse m p q| ≤ 32 * K ^ 2 * H ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have hHsq : H ^ 2 ≤ H := by nlinarith
  have hKD : K * D ≤ K * H := mul_le_mul_of_nonneg_left (hD.trans hHsq) hK0
  have hKD2 : K * D ≤ K * H ^ 2 := mul_le_mul_of_nonneg_left hD hK0
  have hZ₀ : |q₀ 1 - (c 0 + q₀ 0 * c 1)| ≤ K * H := by
    convert hq₀.2.1 using 1 <;> congr 1 <;> ring
  have hms : |m - q₀ 0| ≤ H := by
    rw [abs_sub_comm]
    exact hq₀.1.trans (by linarith)
  have hvdiff : |p 2 - c 1| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
  have hmid : |(p 0 + m * p 2) - (c 0 + m * c 1)| ≤ 4 * K * H := by
    calc
      _ = |((referenceZ p (q₀ 0) - q₀ 1) + (q₀ 1 - (c 0 + q₀ 0 * c 1))) +
          (m - q₀ 0) * (p 2 - c 1)| := by unfold referenceZ; congr 1; ring
      _ ≤ (|referenceZ p (q₀ 0) - q₀ 1| + |q₀ 1 - (c 0 + q₀ 0 * c 1)|) +
          |(m - q₀ 0) * (p 2 - c 1)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ K * D + K * H + H * (2 * K) := by
        apply add_le_add
        · exact add_le_add (by simpa only [abs_sub_comm] using hcontactZ) hZ₀
        · rw [abs_mul]
          exact mul_le_mul hms hvdiff (abs_nonneg _) hH.le
      _ ≤ _ := by nlinarith
  have hcoefficient : |c 3 + p 0 + m * p 2| ≤ 5 * K * H := by
    calc
      _ = |(c 3 + c 0 + m * c 1) + ((p 0 + m * p 2) - (c 0 + m * c 1))| := by
        congr 1
        ring
      _ ≤ |c 3 + c 0 + m * c 1| + |(p 0 + m * p 2) - (c 0 + m * c 1)| := abs_add_le _ _
      _ ≤ K * H + 4 * K * H := add_le_add hcenter hmid
      _ = _ := by ring
  have hcontact : |contactTransverse m p q₀| ≤ 2 * K * H ^ 2 := by
    calc
      _ ≤ |q₀ 2 - referenceY p (q₀ 0)| + |m * (q₀ 1 - referenceZ p (q₀ 0))| := abs_sub _ _
      _ ≤ K * D + 1 * (K * D) := add_le_add hcontactY (by
        rw [abs_mul]
        exact mul_le_mul hm hcontactZ (abs_nonneg _) zero_le_one)
      _ ≤ _ := by nlinarith
  intro q hq
  have htime : |q 0 - q₀ 0| ≤ H := by
    apply abs_le.mpr
    have ht := abs_le.mp hq.1
    have hs := abs_le.mp hq₀.1
    constructor <;> linarith
  have hZ : |q 1 - (c 0 + q 0 * c 1)| ≤ K * H := by
    convert hq.2.1 using 1 <;> congr 1 <;> ring
  have hZZ : |q 1 - q₀ 1| ≤ 3 * K * H := by
    calc
      _ = |(q 1 - (c 0 + q 0 * c 1)) + (q 0 - q₀ 0) * c 1 -
          (q₀ 1 - (c 0 + q₀ 0 * c 1))| := by congr 1; ring
      _ ≤ (|q 1 - (c 0 + q 0 * c 1)| + |(q 0 - q₀ 0) * c 1|) +
          |q₀ 1 - (c 0 + q₀ 0 * c 1)| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (K * H + H * K) + K * H := by
        exact add_le_add (add_le_add hZ (by
          rw [abs_mul]
          exact mul_le_mul htime hc (abs_nonneg _) hH.le)) hZ₀
      _ = _ := by ring
  constructor
  · calc
      _ = |(q 1 - q₀ 1) + (q₀ 1 - referenceZ p (q₀ 0)) + (q₀ 0 - q 0) * p 2| := by
        unfold referenceZ
        congr 1
        ring
      _ ≤ (|q 1 - q₀ 1| + |q₀ 1 - referenceZ p (q₀ 0)|) + |(q₀ 0 - q 0) * p 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (3 * K * H + K * D) + H * K := by
        apply add_le_add (add_le_add hZZ hcontactZ)
        rw [abs_mul]
        exact mul_le_mul (by simpa only [abs_sub_comm] using htime) hv (abs_nonneg _) hH.le
      _ ≤ _ := by nlinarith [mul_nonneg hK0 hH.le]
  · have herror : |(q 2 - c 2 - q 0 * c 3 - c 4 * q 1) -
        (q₀ 2 - c 2 - q₀ 0 * c 3 - c 4 * q₀ 1)| ≤ 2 * K * H ^ 2 :=
      (abs_sub _ _).trans (by linarith [hq.2.2, hq₀.2.2])
    have hmove : |(c 3 + p 0 + m * p 2) * (q 0 - q₀ 0)| ≤ 5 * K * H ^ 2 := by
      calc
        _ = |c 3 + p 0 + m * p 2| * |q 0 - q₀ 0| := abs_mul _ _
        _ ≤ (5 * K * H) * H := mul_le_mul hcoefficient htime (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hrotate : |(c 4 - m) * (q 1 - q₀ 1)| ≤ 3 * K ^ 2 * H ^ 2 := by
      calc
        _ = |c 4 - m| * |q 1 - q₀ 1| := abs_mul _ _
        _ ≤ (K * H) * (3 * K * H) := mul_le_mul htilt hZZ (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hdiff : |contactTransverse m p q - contactTransverse m p q₀| ≤
        7 * K * H ^ 2 + 3 * K ^ 2 * H ^ 2 := by
      calc
        _ = |((q 2 - c 2 - q 0 * c 3 - c 4 * q 1) -
              (q₀ 2 - c 2 - q₀ 0 * c 3 - c 4 * q₀ 1)) +
            (c 3 + p 0 + m * p 2) * (q 0 - q₀ 0) + (c 4 - m) * (q 1 - q₀ 1)| := by
          unfold contactTransverse referenceY referenceZ
          congr 1
          ring
        _ ≤ (2 * K * H ^ 2 + 5 * K * H ^ 2) + 3 * K ^ 2 * H ^ 2 := (abs_add_le _ _).trans
          (add_le_add ((abs_add_le _ _).trans (add_le_add herror hmove)) hrotate)
        _ = _ := by ring
    have hKK : K * H ^ 2 ≤ K ^ 2 * H ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith : K ≤ K ^ 2) (sq_nonneg H)
    have htri := abs_add_le (contactTransverse m p q - contactTransverse m p q₀)
      (contactTransverse m p q₀)
    rw [sub_add_cancel] at htri
    exact htri.trans (by nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg H)])

end Submission.Obl.k4_critical_derivative_evaluation_lists
