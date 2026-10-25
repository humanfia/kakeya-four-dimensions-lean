import Submission.Obl.k4_horizontal_three_traversal_spreading.Approximation
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.FiniteCriticalSelection

namespace Submission.Obl.k4_horizontal_three_traversal_spreading

open Set MeasureTheory Finset
open Discretize Inherited
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

noncomputable section
namespace Law

variable {α : Type} [MeasurableSpace α] (D : Law α)

theorem floor_eq_close {a b h : ℝ} (hh : 0 < h) (hab : ⌊a / h⌋ = ⌊b / h⌋) :
    |a - b| ≤ h := by
  have ha := abs_sub_floor_center (x := a) hh
  have hb := abs_sub_floor_center (x := b) hh
  rw [← hab] at hb
  have ht := abs_sub_le a (((⌊a / h⌋ : ℝ) + 1 / 2) * h) b
  have hb' : |((⌊a / h⌋ : ℝ) + 1 / 2) * h - b| ≤ h / 2 := by
    simpa only [abs_sub_comm] using hb
  linarith

/-- Representatives of the same rounded arm obey the horizontal traversal
law up to five fine-mesh units. -/
theorem traverse_error (hD : D.Valid) {p q : α × ℝ} (hp : p ∈ D.G) (hq : q ∈ D.G)
    (hcode : D.code p.1 = D.code q.1) (c : ℝ)
    (hvc : |D.vel p.1 - c| ≤ D.h / 2) (hwc : |D.vel q.1 - c| ≤ D.h / 2) :
    ∀ i : Fin 2, |D.x q.1 q.2 i.succ - horizontalTraverse c p.2 q.2
      ![D.x p.1 p.2 1, D.x p.1 p.2 2] i| ≤ 5 * D.h := by
  have hh : 0 ≤ D.h := hD.h_pos.le
  have ht := (hD.geometry p hp).1
  have hu := (hD.geometry q hq).1
  have ht1 : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hu1 : |q.2| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
  have hut : |q.2 - p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1, ht.2], by linarith [hu.2, ht.1]⟩
  have hZ : |D.Z0 q.1 - D.Z0 p.1| ≤ D.h :=
    floor_eq_close hD.h_pos (congrFun hcode.symm 0)
  have hY : |D.Y0 q.1 - D.Y0 p.1| ≤ D.h :=
    floor_eq_close hD.h_pos (congrFun hcode.symm 1)
  have hxp : D.x p.1 p.2 1 = D.Z0 p.1 + D.vel p.1 * p.2 := by
    simpa only [Z0, sub_zero] using (hD.geometry p hp).2.2.2 0 (by norm_num) p.2 ht |>.1
  have hxq : D.x q.1 q.2 1 = D.Z0 q.1 + D.vel q.1 * q.2 := by
    simpa only [Z0, sub_zero] using (hD.geometry q hq).2.2.2 0 (by norm_num) q.2 hu |>.1
  have hep : |D.x p.1 p.2 2 - (D.Y0 p.1 - D.Z0 p.1 * p.2)| ≤ D.h :=
    D.exact_line_close hD hp 2
  have heq : |D.x q.1 q.2 2 - (D.Y0 q.1 - D.Z0 q.1 * q.2)| ≤ D.h :=
    D.exact_line_close hD hq 2
  have hpt : |(D.vel p.1 - c) * p.2| ≤ D.h / 2 := by
    rw [abs_mul]
    exact (mul_le_mul hvc ht1 (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hqu : |(D.vel q.1 - c) * q.2| ≤ D.h / 2 := by
    rw [abs_mul]
    exact (mul_le_mul hwc hu1 (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hZu : |(D.Z0 q.1 - D.Z0 p.1) * q.2| ≤ D.h := by
    rw [abs_mul]
    exact (mul_le_mul hZ hu1 (abs_nonneg _) hD.h_pos.le).trans_eq (mul_one _)
  have hctl : |(c - D.vel p.1) * p.2 * (q.2 - p.2)| ≤ D.h / 2 := by
    rw [abs_mul, abs_mul, abs_sub_comm c]
    exact (mul_le_mul (mul_le_mul hvc ht1 (abs_nonneg _) (by positivity)) hut
      (abs_nonneg _) (by positivity)).trans_eq (by ring)
  intro i
  fin_cases i
  · change |D.x q.1 q.2 1 - (D.x p.1 p.2 1 + c * (q.2 - p.2))| ≤ _
    rw [hxp, hxq]
    rw [show D.Z0 q.1 + D.vel q.1 * q.2 - (D.Z0 p.1 + D.vel p.1 * p.2 + c * (q.2 - p.2)) =
      (D.Z0 q.1 - D.Z0 p.1) + (D.vel q.1 - c) * q.2 - (D.vel p.1 - c) * p.2 by ring]
    have ha := abs_sub ((D.Z0 q.1 - D.Z0 p.1) + (D.vel q.1 - c) * q.2)
      ((D.vel p.1 - c) * p.2)
    have hb := abs_add_le (D.Z0 q.1 - D.Z0 p.1) ((D.vel q.1 - c) * q.2)
    linarith [hD.h_pos]
  · change |D.x q.1 q.2 2 - (D.x p.1 p.2 2 +
      (-D.x p.1 p.2 1 + p.2 * c) * (q.2 - p.2))| ≤ _
    rw [hxp]
    let A := D.x q.1 q.2 2 - (D.Y0 q.1 - D.Z0 q.1 * q.2)
    let B := D.x p.1 p.2 2 - (D.Y0 p.1 - D.Z0 p.1 * p.2)
    let C := D.Y0 q.1 - D.Y0 p.1
    let E := (D.Z0 q.1 - D.Z0 p.1) * q.2
    let H := (c - D.vel p.1) * p.2 * (q.2 - p.2)
    have hid : D.x q.1 q.2 2 - (D.x p.1 p.2 2 +
        (-(D.Z0 p.1 + D.vel p.1 * p.2) + p.2 * c) * (q.2 - p.2)) =
        A - B + C - E - H := by dsimp [A, B, C, E, H]; ring
    rw [hid]
    have h1 := abs_sub (A - B + C - E) H
    have h2 := abs_sub (A - B + C) E
    have h3 := abs_add_le (A - B) C
    have h4 := abs_sub A B
    change |A| ≤ D.h at heq
    change |B| ≤ D.h at hep
    change |C| ≤ D.h at hY
    change |E| ≤ D.h at hZu
    change |H| ≤ D.h / 2 at hctl
    linarith [hD.h_pos]

def timeInterval {T : ℕ} (t : Fin T) : Set ℝ :=
  Ico ((t.val : ℝ) / T) (((t.val : ℝ) + 1) / T)

theorem center_time {T : ℕ} (hT : 0 < T) (t : Fin T) : center t ∈ Icc (0 : ℝ) 1 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have ht : (t.val : ℝ) + 1 ≤ T := by exact_mod_cast t.isLt
  constructor
  · exact div_nonneg (by positivity) hT'.le
  · rw [center, div_le_one hT']; linarith

theorem timeInterval_volume {T : ℕ} (hT : 0 < T) (t : Fin T) :
    volume (timeInterval t) = ENNReal.ofReal (1 / T) := by
  rw [timeInterval, Real.volume_Ico]
  congr 1
  ring

theorem timeInterval_unit {T : ℕ} (hT : 0 < T) (t : Fin T) :
    timeInterval t ⊆ Icc (0 : ℝ) 1 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have ht : (t.val : ℝ) + 1 ≤ T := by exact_mod_cast t.isLt
  intro s hs
  exact ⟨(div_nonneg (Nat.cast_nonneg _) hT'.le).trans hs.1,
    hs.2.le.trans ((div_le_one hT').mpr ht)⟩

theorem timeInterval_disjoint {T : ℕ} (hT : 0 < T) :
    Pairwise (fun t u : Fin T => Disjoint (timeInterval t) (timeInterval u)) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  intro t u hne
  rw [Set.disjoint_left]
  intro s ht hu
  have htu : (t.val : ℝ) < (u.val : ℝ) + 1 := by
    exact (div_lt_div_iff_of_pos_right hT').mp (ht.1.trans_lt hu.2)
  have hut : (u.val : ℝ) < (t.val : ℝ) + 1 := by
    exact (div_lt_div_iff_of_pos_right hT').mp (hu.1.trans_lt ht.2)
  have htu' : t.val < u.val + 1 := by exact_mod_cast htu
  have hut' : u.val < t.val + 1 := by exact_mod_cast hut
  exact hne (Fin.ext (by omega))

theorem timeInterval_near {T : ℕ} (hT : 0 < T) (t : Fin T) (s : ℝ)
    (hs : s ∈ timeInterval t) : |s - center t| ≤ 1 / T := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hd : (0 : ℝ) ≤ 1 / T := by positivity
  have heq1 : ((t.val : ℝ) + 1) / T = center t + (1 / T) / 2 := by dsimp [center]; ring
  have heq0 : (t.val : ℝ) / T = center t - (1 / T) / 2 := by dsimp [center]; ring
  rw [timeInterval, Set.mem_Ico, heq0, heq1] at hs
  rw [abs_le]
  constructor <;> linarith

/-- All finite geometric hypotheses follow from actual representatives. -/
def finiteGeometry (hD : D.Valid) {n T : ℕ} (hT : 0 < T) (hM : 0 < D.mass n)
    {K : ℝ} (hBK : D.B + D.h ≤ K) :
    FiniteHorizontalGeometry (D.switch n T) D.velocity center K (5 * D.h) D.h (1 / T) where
  point := D.point hD
  point_time e he := by
    obtain ⟨p, hp, hg, hpt⟩ := D.point_spec hD (D.switch_pos_weight hM he)
    rw [hpt, (hD.geometry p hg.1).2.2.1 p.2 (hD.geometry p hg.1).1 |>.1]
    exact (hD.geometry p hg.1).1
  point_horizontal e he := by
    obtain ⟨p, hp, hg, hpt⟩ := D.point_spec hD (D.switch_pos_weight hM he)
    rw [hpt]
    exact ((hD.geometry p hg.1).2.2.1 p.2 (hD.geometry p hg.1).1 |>.2 1).trans
      (by linarith [hD.h_pos])
  center_time := center_time hT
  control_bound z := (Finset.mem_filter.mp z.property).2.trans hBK
  time_near e he := by
    obtain ⟨p, hp, hg, hpt⟩ := D.point_spec hD (D.switch_pos_weight hM he)
    rw [hpt, (hD.geometry p hg.1).2.2.1 p.2 (hD.geometry p hg.1).1 |>.1]
    exact timeInterval_near hT e.2.2 p.2 (time_code_mem hT hp.2.2)
  refresh_close e er he her hf := by
    obtain ⟨p, hp, hg, hpt⟩ := D.point_spec hD (D.switch_pos_weight hM he)
    obtain ⟨q, hq, hqg, hqt⟩ := D.point_spec hD (D.switch_pos_weight hM her)
    rw [hpt, hqt]
    exact (hD.state_geometry p hg.1 q hqg.1
      (hp.1.trans ((congrArg (fun k : Fin n × ℤ => k.1.val) hf).trans hq.1.symm))).2
  traverse_close er e' her he' harm := by
    obtain ⟨p, hp, hg, hpt⟩ := D.point_spec hD (D.switch_pos_weight hM her)
    obtain ⟨q, hq, hqg, hqt⟩ := D.point_spec hD (D.switch_pos_weight hM he')
    have ha : er.2.1 = e'.2.1 := congrArg (fun k : D.armSet × Unit => k.1) harm
    have hc : D.code p.1 = D.code q.1 := hp.2.1.trans ((congrArg Subtype.val ha).trans hq.2.1.symm)
    have hvc : |D.vel p.1 - D.velocity (D.palOf er.2.1)| ≤ D.h / 2 := by
      rw [velocity, ← D.pre_palette hp]
      exact abs_sub_floor_center hD.h_pos
    have hwc : |D.vel q.1 - D.velocity (D.palOf er.2.1)| ≤ D.h / 2 := by
      rw [ha, velocity, ← D.pre_palette hq]
      exact abs_sub_floor_center hD.h_pos
    rw [hpt, hqt, (hD.geometry p hg.1).2.2.1 p.2 (hD.geometry p hg.1).1 |>.1,
      (hD.geometry q hqg.1).2.2.1 q.2 (hD.geometry q hqg.1).1 |>.1]
    exact D.traverse_error hD hg.1 hqg.1 hc _ hvc hwc

def pointCell (hD : D.Valid) {n T : ℕ} (e : D.Event n T) : Fin 3 → ℤ :=
  cellIdx D.ω (D.point hD e)

theorem point_support (hD : D.Valid) {n T : ℕ} {e : D.Event n T}
    (he : 0 < D.weight e) : (D.binOf e.2.1, D.pointCell hD e) ∈ D.F := by
  obtain ⟨p, hp, hg, hpt⟩ := D.point_spec hD he
  rw [pointCell, hpt, ← D.pre_bin hp]
  exact hg.2.2

theorem point_spatial (hD : D.Valid) {n T : ℕ} (e : D.Event n T) (i : Fin 3) :
    |D.point hD e i - cellCenter D.ω (D.pointCell hD e) i| ≤ D.ω / 2 :=
  abs_sub_floor_center hD.ω_pos

end Law
end
end Submission.Obl.k4_horizontal_three_traversal_spreading
