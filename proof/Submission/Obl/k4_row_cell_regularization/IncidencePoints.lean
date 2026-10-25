import Submission.Obl.k4_row_cell_regularization.MeasureCells
import Submission.Obl.k4_scalar_lift_plank.Cells
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

/-!
# The finite point cells and velocity bins of the incidences

`incPoints` is the finite set of four-dimensional point cells (position cell and row bin) that
good incidences can occupy, `incBins` the finite set of their velocity bins.  We bound their
sizes, show that good incidences land in them, bound the cell centers, and show that the
projection of a point cell along the velocity of its trajectory stays within `O(L)` mesh units
of a value depending only on the trajectory.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

set_option linter.unusedSectionVars false

namespace Submission.Obl.k4_row_cell_regularization

-- Adapted from this LOT tree, o072, session x0247, IncidencePoints.lean,
-- commits b33e4e7 and 0040823.

/-- Integer ranges of the four cell coordinates. -/
noncomputable def cellRanges (h E L : ℝ) : Fin 4 → Finset ℤ :=
  ![Finset.Icc 0 ⌊1 / h⌋, Finset.Icc ⌊-L / h⌋ ⌊L / h⌋, Finset.Icc ⌊-L / E⌋ ⌊L / E⌋,
    Finset.Icc ⌊-L / E⌋ ⌊L / E⌋]

/-- The finite set of point cells. -/
noncomputable def incPoints (h E L : ℝ) (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)) :
    Finset Point :=
  (Fintype.piFinset (cellRanges h E L)).filter (fun c => ![c 2, c 3] ∈ F ![c 0, c 1])

/-- The finite set of velocity bins. -/
noncomputable def incBins (h L : ℝ) : Finset ℤ := Finset.Icc ⌊-L / h⌋ ⌊L / h⌋

theorem card_Icc_le_real (a b : ℤ) {X : ℝ} (hX : 0 ≤ X) (hab : (b : ℝ) + 1 - a ≤ X) :
    ((Finset.Icc a b).card : ℝ) ≤ X := by
  rw [Int.card_Icc]
  have h1 : (((b + 1 - a).toNat : ℤ) : ℝ) = max ((b : ℝ) + 1 - a) 0 := by
    rw [Int.toNat_eq_max]
    push_cast
    rfl
  rw [show (((b + 1 - a).toNat : ℕ) : ℝ) = (((b + 1 - a).toNat : ℤ) : ℝ) by norm_cast, h1]
  exact max_le hab hX

theorem floor_sym_range_card {L h : ℝ} (hh : 0 < h) (hL : 0 ≤ L) :
    ((Finset.Icc ⌊-L / h⌋ ⌊L / h⌋).card : ℝ) ≤ 2 * L / h + 2 := by
  apply card_Icc_le_real _ _ (by positivity)
  have h1 := Int.floor_le (L / h)
  have h2 := Int.lt_floor_add_one (-L / h)
  have h3 : -L / h = -(L / h) := by ring
  have h4 : 2 * L / h = L / h + L / h := by ring
  linarith

theorem incBins_card {h L : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hL : 1 ≤ L) :
    ((incBins h L).card : ℝ) ≤ 4 * L / h := by
  refine (floor_sym_range_card hh (by linarith)).trans ?_
  have : 2 ≤ 2 * L / h := by
    rw [le_div_iff₀ hh]; nlinarith
  have : 4 * L / h = 2 * L / h + 2 * L / h := by ring
  linarith

theorem mem_incPoints {h E L : ℝ} {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)} {c : Point} :
    c ∈ incPoints h E L F ↔
      (0 ≤ c 0 ∧ c 0 ≤ ⌊1 / h⌋) ∧ (⌊-L / h⌋ ≤ c 1 ∧ c 1 ≤ ⌊L / h⌋) ∧
      (⌊-L / E⌋ ≤ c 2 ∧ c 2 ≤ ⌊L / E⌋) ∧ (⌊-L / E⌋ ≤ c 3 ∧ c 3 ≤ ⌊L / E⌋) ∧
      ![c 2, c 3] ∈ F ![c 0, c 1] := by
  simp only [incPoints, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hr, hF⟩
    have h0 : c 0 ∈ Finset.Icc 0 ⌊1 / h⌋ := hr 0
    have h1 : c 1 ∈ Finset.Icc ⌊-L / h⌋ ⌊L / h⌋ := hr 1
    have h2 : c 2 ∈ Finset.Icc ⌊-L / E⌋ ⌊L / E⌋ := hr 2
    have h3 : c 3 ∈ Finset.Icc ⌊-L / E⌋ ⌊L / E⌋ := hr 3
    rw [Finset.mem_Icc] at h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3, hF⟩
  · rintro ⟨h0, h1, h2, h3, hF⟩
    refine ⟨fun j => ?_, hF⟩
    fin_cases j
    · show c 0 ∈ Finset.Icc 0 ⌊1 / h⌋
      exact Finset.mem_Icc.mpr h0
    · show c 1 ∈ Finset.Icc ⌊-L / h⌋ ⌊L / h⌋
      exact Finset.mem_Icc.mpr h1
    · show c 2 ∈ Finset.Icc ⌊-L / E⌋ ⌊L / E⌋
      exact Finset.mem_Icc.mpr h2
    · show c 3 ∈ Finset.Icc ⌊-L / E⌋ ⌊L / E⌋
      exact Finset.mem_Icc.mpr h3

/-- The position fiber of the point cells injects into the row bins `F q`. -/
theorem incPoints_fiber_card {h E L : ℝ} {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)}
    (q : Fin 2 → ℤ) :
    ((incPoints h E L F).filter (fun c => ![c 0, c 1] = q)).card ≤ (F q).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun c => ![c 2, c 3])
  · intro c hc
    simp only [Finset.coe_filter, mem_ofPred_eq] at hc
    obtain ⟨hc, hq⟩ := hc
    have := (mem_incPoints.mp hc).2.2.2.2
    rw [hq] at this
    exact this
  · intro c hc c' hc' heq
    simp only [Finset.coe_filter, mem_ofPred_eq] at hc hc'
    have hq := hc.2.trans hc'.2.symm
    funext j
    fin_cases j
    · exact congrFun hq 0
    · exact congrFun hq 1
    · exact congrFun heq 0
    · exact congrFun heq 1

theorem incPoints_card {h E L : ℝ} {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)}
    (hh : 0 < h) (hh1 : h ≤ 1) (hL : 1 ≤ L) (hF : ∀ q, ((F q).card : ℝ) ≤ L) :
    ((incPoints h E L F).card : ℝ) ≤ 8 * L ^ 2 / h ^ 2 := by
  classical
  set Q : Finset (Fin 2 → ℤ) :=
    Fintype.piFinset ![Finset.Icc 0 ⌊1 / h⌋, Finset.Icc ⌊-L / h⌋ ⌊L / h⌋]
  have hmaps : Set.MapsTo (fun c : Point => ![c 0, c 1]) (incPoints h E L F) Q := by
    intro c hc
    have hc' := mem_incPoints.mp hc
    simp only [Q, Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Finset.mem_Icc]
      exact hc'.1
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Finset.mem_Icc]
      exact hc'.2.1
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hQ : (Q.card : ℝ) ≤ (2 / h) * (4 * L / h) := by
    simp only [Q, Fintype.card_piFinset, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    apply mul_le_mul _ _ (Nat.cast_nonneg _) (by positivity)
    · apply card_Icc_le_real _ _ (by positivity)
      have := Int.floor_le (1 / h)
      have : 1 ≤ 1 / h := by rw [le_div_iff₀ hh]; linarith
      have : 2 / h = 1 / h + 1 / h := by ring
      push_cast
      linarith
    · refine (floor_sym_range_card hh (by linarith)).trans ?_
      have : 2 ≤ 2 * L / h := by
        rw [le_div_iff₀ hh]; nlinarith
      have : 4 * L / h = 2 * L / h + 2 * L / h := by ring
      linarith
  calc ((incPoints h E L F).card : ℝ)
      = ∑ q ∈ Q, (((incPoints h E L F).filter (fun c => ![c 0, c 1] = q)).card : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ ∑ _q ∈ Q, L := by
        apply Finset.sum_le_sum
        intro q _
        exact (Nat.cast_le.mpr (incPoints_fiber_card q)).trans (hF q)
    _ = Q.card * L := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 / h) * (4 * L / h) * L := mul_le_mul_of_nonneg_right hQ (by linarith)
    _ = 8 * L ^ 2 / h ^ 2 := by field_simp; ring

/-- Centers of point cells are bounded. -/
theorem incPoints_center {h E L : ℝ} {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)}
    (hh : 0 < h) (hh1 : h ≤ 1) (hhE : h ≤ E) (hL : 0 ≤ L) {c : Point}
    (hc : c ∈ incPoints h E L F) (j : Fin 4) : |h * (c j : ℝ)| ≤ L + 1 := by
  have hE : 0 < E := lt_of_lt_of_le hh hhE
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩, ⟨h3, h3'⟩, -⟩ := mem_incPoints.mp hc
  -- a coordinate between `⌊-M⌋` and `⌊M⌋` is within `M + 1` of zero
  have key : ∀ (M s : ℝ) (k : ℤ), 0 < s → ⌊-M / s⌋ ≤ k → k ≤ ⌊M / s⌋ →
      |h * (k : ℝ)| ≤ h * (M / s) + h := by
    intro M s k hs hlo hhi
    have a1 : (k : ℝ) ≤ M / s := (Int.cast_le.mpr hhi).trans (Int.floor_le _)
    have a2 : -M / s < (k : ℝ) + 1 := by
      have := Int.lt_floor_add_one (-M / s)
      have : ((⌊-M / s⌋ : ℤ) : ℝ) ≤ k := Int.cast_le.mpr hlo
      linarith
    have : -M / s = -(M / s) := by ring
    rw [this] at a2
    rw [abs_le]
    constructor <;> nlinarith
  have hLE : h * (L / E) ≤ L := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ hE]
    nlinarith
  have hLh : h * (L / h) = L := by field_simp
  fin_cases j
  · show |h * (c 0 : ℝ)| ≤ L + 1
    have a1 : (c 0 : ℝ) ≤ 1 / h := (Int.cast_le.mpr h0').trans (Int.floor_le _)
    have a0 : (0 : ℝ) ≤ c 0 := by exact_mod_cast h0
    rw [abs_le]
    have : h * (c 0 : ℝ) ≤ 1 := by
      calc h * (c 0 : ℝ) ≤ h * (1 / h) := mul_le_mul_of_nonneg_left a1 hh.le
        _ = 1 := by field_simp
    have : 0 ≤ h * (c 0 : ℝ) := mul_nonneg hh.le a0
    constructor <;> linarith
  · show |h * (c 1 : ℝ)| ≤ L + 1
    have := key L h (c 1) hh h1 h1'
    rw [hLh] at this
    linarith
  · show |h * (c 2 : ℝ)| ≤ L + 1
    have := key L E (c 2) hE h2 h2'
    linarith
  · show |h * (c 3 : ℝ)| ≤ L + 1
    have := key L E (c 3) hE h3 h3'
    linarith

/-- The velocity represented by a bin. -/
def binVel (h : ℝ) (d : ℤ) : ℝ := (d : ℝ) * h

theorem floor_div_bounds {s : ℝ} (hs : 0 < s) (x : ℝ) :
    s * (⌊x / s⌋ : ℝ) ≤ x ∧ x < s * (⌊x / s⌋ : ℝ) + s := by
  have h1 := Int.floor_le (x / s)
  have h2 := Int.lt_floor_add_one (x / s)
  constructor
  · calc s * (⌊x / s⌋ : ℝ) ≤ s * (x / s) := mul_le_mul_of_nonneg_left h1 hs.le
      _ = x := by field_simp
  · calc x = s * (x / s) := by field_simp
      _ < s * ((⌊x / s⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left h2 hs
      _ = s * (⌊x / s⌋ : ℝ) + s := by ring

theorem real_floor_error (x : ℝ) : |x - (⌊x⌋ : ℝ)| ≤ 1 := by
  simpa only [abs_sub_comm] using
    Submission.Obl.k4_scalar_lift_plank.abs_floor_sub x

section Good

variable {α : Type} [MeasurableSpace α] {h E L : ℝ} {b v H : α → ℝ} {T : α × ℝ → Fin 2 → ℝ}
  {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)} {p : α × ℝ}

theorem goodSet_time (hp : p ∈ goodSet h E L b v H T F) : 0 ≤ p.2 ∧ p.2 ≤ 1 := hp.1

theorem goodSet_row (hp : p ∈ goodSet h E L b v H T F) (j : Fin 2) : |T p j| ≤ L := hp.2.1 j

theorem goodSet_bins (hp : p ∈ goodSet h E L b v H T F) :
    (fun j => ⌊T p j / E⌋) ∈ F (posCell h b v p) := hp.2.2.1

theorem goodSet_eval (hp : p ∈ goodSet h E L b v H T F) :
    |T p 0 + v p.1 * T p 1 - H p.1| ≤ L * E := hp.2.2.2

theorem goodSet_pos (htraj : ∀ l, |b l| + |v l| ≤ L) (hp : p ∈ goodSet h E L b v H T F) :
    |b p.1 + p.2 * v p.1| ≤ L := by
  obtain ⟨ht0, ht1⟩ := goodSet_time hp
  calc |b p.1 + p.2 * v p.1| ≤ |b p.1| + |p.2 * v p.1| := abs_add_le _ _
    _ = |b p.1| + |p.2| * |v p.1| := by rw [abs_mul]
    _ ≤ |b p.1| + 1 * |v p.1| := by
        gcongr
        rw [abs_le]; constructor <;> linarith
    _ ≤ L := by rw [one_mul]; exact htraj _

theorem floor_mem_sym_range {M s x : ℝ} (hs : 0 < s) (hx : |x| ≤ M) :
    ⌊-M / s⌋ ≤ ⌊x / s⌋ ∧ ⌊x / s⌋ ≤ ⌊M / s⌋ := by
  rw [abs_le] at hx
  exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right hx.1 hs.le),
    Int.floor_le_floor (div_le_div_of_nonneg_right hx.2 hs.le)⟩

theorem incCell_mem_incPoints (hh : 0 < h) (hhE : h ≤ E) (htraj : ∀ l, |b l| + |v l| ≤ L)
    (hp : p ∈ goodSet h E L b v H T F) : incCell h E b v T p ∈ incPoints h E L F := by
  have hE : 0 < E := lt_of_lt_of_le hh hhE
  obtain ⟨ht0, ht1⟩ := goodSet_time hp
  rw [mem_incPoints, incCell_zero, incCell_one, incCell_two, incCell_three]
  refine ⟨⟨Int.floor_nonneg.mpr (div_nonneg ht0 hh.le),
      Int.floor_le_floor (div_le_div_of_nonneg_right ht1 hh.le)⟩,
    floor_mem_sym_range hh (goodSet_pos htraj hp),
    floor_mem_sym_range hE (goodSet_row hp 0), floor_mem_sym_range hE (goodSet_row hp 1), ?_⟩
  have hF := goodSet_bins hp
  rw [posCell_eq] at hF
  convert hF using 1
  funext j
  fin_cases j <;> rfl

theorem incBin_mem_incBins (hh : 0 < h) (htraj : ∀ l, |b l| + |v l| ≤ L) (p : α × ℝ) :
    incBin h v p ∈ incBins h L := by
  have hv : |v p.1| ≤ L := le_trans (le_add_of_nonneg_left (abs_nonneg _)) (htraj p.1)
  exact Finset.mem_Icc.mpr (floor_mem_sym_range hh hv)

theorem abs_binVel_incBin_le (hh : 0 < h) (hh1 : h ≤ 1) (htraj : ∀ l, |b l| + |v l| ≤ L)
    (p : α × ℝ) : |binVel h (incBin h v p)| ≤ L + 1 := by
  have hv : |v p.1| ≤ L := le_trans (le_add_of_nonneg_left (abs_nonneg _)) (htraj p.1)
  obtain ⟨h1, h2⟩ := floor_div_bounds hh (v p.1)
  have e : binVel h (incBin h v p) = h * (⌊v p.1 / h⌋ : ℝ) := by
    simp only [binVel, incBin]; ring
  rw [e, abs_le]
  rw [abs_le] at hv
  constructor <;> linarith

theorem incCell_pos_error_zero (hh : 0 < h) (p : α × ℝ) :
    |p.2 - h * (incCell h E b v T p 0 : ℝ)| ≤ h :=
  Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hh _

theorem incCell_pos_error_one (hh : 0 < h) (p : α × ℝ) :
    |(b p.1 + p.2 * v p.1) - h * (incCell h E b v T p 1 : ℝ)| ≤ h :=
  Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hh _

theorem incCell_row_error (hh : 0 < h) (hhE : h ≤ E) (p : α × ℝ) (j : Fin 2) :
    |(h / E) * T p j - h * (⌊T p j / E⌋ : ℝ)| ≤ h := by
  have hE : 0 < E := lt_of_lt_of_le hh hhE
  have e : (h / E) * T p j - h * (⌊T p j / E⌋ : ℝ) = h * (T p j / E - (⌊T p j / E⌋ : ℝ)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hh]
  calc h * |T p j / E - (⌊T p j / E⌋ : ℝ)| ≤ h * 1 :=
        mul_le_mul_of_nonneg_left (real_floor_error _) hh.le
    _ = h := mul_one h

/-- Along its own velocity bin, the first projection of a point cell is within `L + 3` mesh
units of the trajectory intercept. -/
theorem traj_proj_fst (hh : 0 < h) (hh1 : h ≤ 1) (htraj : ∀ l, |b l| + |v l| ≤ L)
    (hp : p ∈ goodSet h E L b v H T F) :
    |(pointProjection (binVel h (incBin h v p)) (incCell h E b v T p)).1 - b p.1 / h| ≤
      L + 3 := by
  obtain ⟨ht0, ht1⟩ := goodSet_time hp
  have hu := abs_binVel_incBin_le hh hh1 htraj p
  set t := p.2
  set B := b p.1
  set V := v p.1
  set d : ℤ := ⌊V / h⌋ with hd
  have hdef : pointProjection (binVel h (incBin h v p)) (incCell h E b v T p) =
      ((⌊(B + t * V) / h⌋ : ℝ) - (d : ℝ) * h * (⌊t / h⌋ : ℝ),
        (⌊T p 0 / E⌋ : ℝ) + (d : ℝ) * h * (⌊T p 1 / E⌋ : ℝ)) := rfl
  rw [hdef]
  simp only
  have hu' : |(d : ℝ) * h| ≤ L + 1 := hu
  obtain ⟨hV1, hV2⟩ := floor_div_bounds hh V
  have e1 : |(⌊(B + t * V) / h⌋ : ℝ) - (B + t * V) / h| ≤ 1 := by
    rw [abs_sub_comm]; exact real_floor_error _
  have e2 : |t / h - (⌊t / h⌋ : ℝ)| ≤ 1 := real_floor_error _
  have e3 : |t * ((V - (d : ℝ) * h) / h)| ≤ 1 := by
    have a1 : 0 ≤ (V - (d : ℝ) * h) / h := div_nonneg (by linarith) hh.le
    have a2 : (V - (d : ℝ) * h) / h ≤ 1 := by
      rw [div_le_one hh]; linarith
    rw [abs_of_nonneg (mul_nonneg ht0 a1)]
    calc t * ((V - (d : ℝ) * h) / h) ≤ 1 * 1 := mul_le_mul ht1 a2 a1 zero_le_one
      _ = 1 := one_mul 1
  have e4 : |(d : ℝ) * h * (t / h - (⌊t / h⌋ : ℝ))| ≤ L + 1 := by
    rw [abs_mul]
    calc |(d : ℝ) * h| * |t / h - (⌊t / h⌋ : ℝ)| ≤ (L + 1) * 1 :=
          mul_le_mul hu' e2 (abs_nonneg _) (by linarith [abs_nonneg ((d : ℝ) * h)])
      _ = L + 1 := mul_one _
  have iden : (⌊(B + t * V) / h⌋ : ℝ) - (d : ℝ) * h * (⌊t / h⌋ : ℝ) - B / h =
      ((⌊(B + t * V) / h⌋ : ℝ) - (B + t * V) / h) + t * ((V - (d : ℝ) * h) / h) +
        (d : ℝ) * h * (t / h - (⌊t / h⌋ : ℝ)) := by
    field_simp
    ring
  rw [iden]
  calc _ ≤ |(⌊(B + t * V) / h⌋ : ℝ) - (B + t * V) / h| + |t * ((V - (d : ℝ) * h) / h)| +
        |(d : ℝ) * h * (t / h - (⌊t / h⌋ : ℝ))| := abs_add_three _ _ _
    _ ≤ 1 + 1 + (L + 1) := by gcongr
    _ = L + 3 := by ring

/-- Along its own velocity bin, the second projection of a point cell is within `3L + 2`
mesh units of the trajectory evaluation. -/
theorem traj_proj_snd (hh : 0 < h) (hh1 : h ≤ 1) (hhE : h ≤ E)
    (htraj : ∀ l, |b l| + |v l| ≤ L) (hp : p ∈ goodSet h E L b v H T F) :
    |(pointProjection (binVel h (incBin h v p)) (incCell h E b v T p)).2 - H p.1 / E| ≤
      3 * L + 2 := by
  have hE : 0 < E := lt_of_lt_of_le hh hhE
  have hu := abs_binVel_incBin_le hh hh1 htraj p
  have hT1 := goodSet_row hp 1
  have hev := goodSet_eval hp
  set V := v p.1
  set d : ℤ := ⌊V / h⌋ with hd
  have hdef : pointProjection (binVel h (incBin h v p)) (incCell h E b v T p) =
      ((⌊(b p.1 + p.2 * V) / h⌋ : ℝ) - (d : ℝ) * h * (⌊p.2 / h⌋ : ℝ),
        (⌊T p 0 / E⌋ : ℝ) + (d : ℝ) * h * (⌊T p 1 / E⌋ : ℝ)) := rfl
  rw [hdef]
  simp only
  have hu' : |(d : ℝ) * h| ≤ L + 1 := hu
  obtain ⟨hV1, hV2⟩ := floor_div_bounds hh V
  have e1 : |(⌊T p 0 / E⌋ : ℝ) - T p 0 / E| ≤ 1 := by
    rw [abs_sub_comm]; exact real_floor_error _
  have e2 : |(d : ℝ) * h * ((⌊T p 1 / E⌋ : ℝ) - T p 1 / E)| ≤ L + 1 := by
    rw [abs_mul]
    have : |(⌊T p 1 / E⌋ : ℝ) - T p 1 / E| ≤ 1 := by
      rw [abs_sub_comm]; exact real_floor_error _
    calc |(d : ℝ) * h| * |(⌊T p 1 / E⌋ : ℝ) - T p 1 / E| ≤ (L + 1) * 1 :=
          mul_le_mul hu' this (abs_nonneg _) (by linarith [abs_nonneg ((d : ℝ) * h)])
      _ = L + 1 := mul_one _
  have e3 : |((d : ℝ) * h - V) * (T p 1 / E)| ≤ L := by
    rw [abs_mul, abs_div, abs_of_pos hE]
    have a1 : |(d : ℝ) * h - V| ≤ h := by
      rw [abs_le]; constructor <;> linarith
    calc |(d : ℝ) * h - V| * (|T p 1| / E) ≤ h * (L / E) := by
          apply mul_le_mul a1 _ (by positivity) hh.le
          exact div_le_div_of_nonneg_right hT1 hE.le
      _ = (h / E) * L := by ring
      _ ≤ 1 * L := by
          apply mul_le_mul_of_nonneg_right _ (le_trans (abs_nonneg _) hT1)
          rw [div_le_one hE]; exact hhE
      _ = L := one_mul L
  have e4 : |(T p 0 + V * T p 1 - H p.1) / E| ≤ L := by
    rw [abs_div, abs_of_pos hE, div_le_iff₀ hE]
    exact hev
  have iden : (⌊T p 0 / E⌋ : ℝ) + (d : ℝ) * h * (⌊T p 1 / E⌋ : ℝ) - H p.1 / E =
      ((⌊T p 0 / E⌋ : ℝ) - T p 0 / E) + (d : ℝ) * h * ((⌊T p 1 / E⌋ : ℝ) - T p 1 / E) +
        ((d : ℝ) * h - V) * (T p 1 / E) + (T p 0 + V * T p 1 - H p.1) / E := by
    field_simp
    ring
  rw [iden]
  calc _ ≤ |(⌊T p 0 / E⌋ : ℝ) - T p 0 / E| +
        |(d : ℝ) * h * ((⌊T p 1 / E⌋ : ℝ) - T p 1 / E)| +
        |((d : ℝ) * h - V) * (T p 1 / E)| + |(T p 0 + V * T p 1 - H p.1) / E| := by
        have := abs_add_three ((⌊T p 0 / E⌋ : ℝ) - T p 0 / E)
          ((d : ℝ) * h * ((⌊T p 1 / E⌋ : ℝ) - T p 1 / E)) (((d : ℝ) * h - V) * (T p 1 / E))
        have := abs_add_le ((⌊T p 0 / E⌋ : ℝ) - T p 0 / E +
          (d : ℝ) * h * ((⌊T p 1 / E⌋ : ℝ) - T p 1 / E) + ((d : ℝ) * h - V) * (T p 1 / E))
          ((T p 0 + V * T p 1 - H p.1) / E)
        linarith
    _ ≤ 1 + (L + 1) + L + L := by gcongr
    _ = 3 * L + 2 := by ring

end Good

end Submission.Obl.k4_row_cell_regularization
