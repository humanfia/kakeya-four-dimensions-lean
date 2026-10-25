-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.WindowLens.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LensDescent

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- Crossing times for a pair in a fixed closed window. -/
def windowCrossings {n : ℕ} (g : Fin n → ℝ → ℝ) (l u : ℝ) (i j : Fin n) : Set ℝ :=
  {t | t ∈ Icc l u ∧ g i t = g j t}

/-- A pair has a lens when it has two distinct crossings in the window. -/
def HasWindowLens {n : ℕ} (g : Fin n → ℝ → ℝ) (l u : ℝ) (i j : Fin n) : Prop :=
  ∃ a ∈ Icc l u, ∃ b ∈ Icc l u, a < b ∧ g i a = g j a ∧ g i b = g j b

/-- The canonical lens width is the diameter of the crossing set. It is
zero for a pair with fewer than two crossings. -/
noncomputable def windowLensWidth {n : ℕ} (g : Fin n → ℝ → ℝ) (l u : ℝ) (i j : Fin n) : ℝ :=
  Metric.diam (windowCrossings g l u i j)

theorem windowCrossings_symm {n : ℕ} (g : Fin n → ℝ → ℝ) (l u : ℝ) (i j : Fin n) :
    windowCrossings g l u i j = windowCrossings g l u j i := by
  ext t
  simp only [windowCrossings, mem_ofPred_eq, eq_comm]

theorem hasWindowLens_symm {n : ℕ} (g : Fin n → ℝ → ℝ) (l u : ℝ) (i j : Fin n) :
    HasWindowLens g l u i j ↔ HasWindowLens g l u j i := by
  simp only [HasWindowLens, eq_comm]

theorem windowLensWidth_symm {n : ℕ} (g : Fin n → ℝ → ℝ) (l u : ℝ) (i j : Fin n) :
    windowLensWidth g l u i j = windowLensWidth g l u j i := by
  unfold windowLensWidth
  rw [windowCrossings_symm g l u i j]

theorem windowLensWidth_nonneg {n : ℕ} (g : Fin n → ℝ → ℝ) (l u : ℝ) (i j : Fin n) :
    0 ≤ windowLensWidth g l u i j := Metric.diam_nonneg

theorem windowLensWidth_le {n : ℕ} (g : Fin n → ℝ → ℝ) {l u : ℝ}
    (hlu : l ≤ u) (i j : Fin n) : windowLensWidth g l u i j ≤ u - l := by
  unfold windowLensWidth
  calc
    Metric.diam (windowCrossings g l u i j) ≤ Metric.diam (Icc l u) :=
      Metric.diam_mono (fun _ ht => ht.1) (Metric.isBounded_Icc l u)
    _ = u - l := Real.diam_Icc hlu

/-- Any two crossings give the exact canonical width in a short window. -/
theorem windowLensWidth_eq_of_crossings {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {l u a b : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hab : a < b)
    (hdist : 0 < dist (q i) (q j))
    (heqa : g i a = g j a) (heqb : g i b = g j b) :
    windowLensWidth g l u i j = b - a := by
  have heq : windowCrossings g l u i j = {a, b} := by
    ext t
    constructor
    · intro ht
      have h := crossing_eq_one_of_two hg hjet i j hl hu hshort ha hb ht.1 hab
        (v := 0) (by rw [abs_zero]; positivity)
        (sub_eq_zero.mpr heqa) (sub_eq_zero.mpr heqb) (sub_eq_zero.mpr ht.2)
      simpa only [mem_insert_iff, mem_singleton_iff] using h
    · rintro (rfl | rfl)
      · exact ⟨ha, heqa⟩
      · exact ⟨hb, heqb⟩
  rw [windowLensWidth, heq, Metric.diam_pair, Real.dist_eq,
    abs_sub_comm, abs_of_pos (sub_pos.mpr hab)]

/-- The canonical width is positive for every lens of a separated pair. -/
theorem windowLensWidth_pos {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {l u : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (hdist : 0 < dist (q i) (q j)) (h : HasWindowLens g l u i j) :
    0 < windowLensWidth g l u i j := by
  obtain ⟨a, ha, b, hb, hab, heqa, heqb⟩ := h
  rw [windowLensWidth_eq_of_crossings hg hjet i j hl hu hshort ha hb hab hdist heqa heqb]
  exact sub_pos.mpr hab

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
