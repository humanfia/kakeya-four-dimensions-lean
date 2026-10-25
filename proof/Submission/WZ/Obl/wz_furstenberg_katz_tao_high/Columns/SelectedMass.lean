-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.SelectedMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0720 Columns/SelectedMass.lean (758215d).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.AngularMass

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
open WangZahlLot.Obl.wz_tower_balanced_refinement
open scoped BigOperators Classical

/-- Passing to selected whole classes does not require balancing again.
The cap bound controls the conversion from retained labels to incidences. -/
theorem selected_label_mass_le_incidence {D J : Finset (E2 × E2)} {P : Finset E2}
    {cls : E2 × E2 → E2 × E2} {R V : ℝ} (hV : 0 ≤ V)
    (hDP : ∀ q ∈ D, q.1 ∈ P) (hJ : ∀ j ∈ J, ‖j.2‖ = 1)
    (hgeo : ∀ q ∈ D, dist q.2 (cls q).2 < R ∨ dist q.2 (-(cls q).2) < R)
    (hcap : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter fun e => dist e u ≤ R).card : ℝ) ≤ V) :
    ((D.filter fun q => cls q ∈ J).card : ℝ) ≤
      2 * V * ∑ j ∈ J, ((pinsOf D cls j).card : ℝ) := by
  let S := D.filter fun q => cls q ∈ J
  have hSD : S ⊆ D := Finset.filter_subset _ _
  have hbush (p : E2) : bushOf S p ⊆ bushOf D p :=
    fun e he => mem_bushOf.mpr (hSD (mem_bushOf.mp he))
  have hcap' : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf S p).filter fun e => dist e u ≤ R).card : ℝ) ≤ V := by
    intro p hp u hu
    exact (Nat.cast_le.mpr (Finset.card_le_card
      (Finset.monotone_filter_left _ (hbush p)))).trans (hcap p hp u hu)
  have hmass := label_mass_le_class_incidence (D := S) (J := J) (cls := cls)
    (fun q hq => hDP q (hSD hq)) (fun q hq => (Finset.mem_filter.mp hq).2)
    hJ (fun q hq => hgeo q (hSD hq)) hcap'
  apply hmass.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * V)
  apply Finset.sum_le_sum
  intro j hj
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  obtain ⟨e, he, hec⟩ := mem_pinsOf.mp hp
  exact mem_pinsOf.mpr ⟨e, hSD he, hec⟩

/-- Retaining a fraction of the labels in whole coarse classes retains the
predicted total incidence, measured by a fixed reference angular profile. -/
theorem coarse_selected_incidence_lower {R K lam : ℝ} (hR : 0 < R) (hK : 0 < K)
    (hlam : 0 ≤ lam) {D J : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hJ : ∀ j ∈ J, ‖j.2‖ = 1)
    (hgeo : ∀ q ∈ D, dist q.2 (cls q).2 < 2 * R ∨ dist q.2 (-(cls q).2) < 2 * R)
    (hbal : Balanced D Prod.fst K)
    (harc : Balanced D (fun q => (q.1, arcOf R q.2)) K)
    (p₀ : E2) (hne : (bushOf D p₀).Nonempty)
    (hkeep : lam * (D.card : ℝ) ≤ (D.filter fun q => cls q ∈ J).card) :
    lam * (D.image Prod.fst).card * ((bushOf D p₀).image (arcOf R)).card ≤
      72 * K ^ 2 * ∑ j ∈ J, ((pinsOf D cls j).card : ℝ) := by
  let n : ℝ := (bushOf D p₀).card
  let A : ℝ := ((bushOf D p₀).image (arcOf R)).card
  let P := D.image Prod.fst
  let I : ℝ := ∑ j ∈ J, ((pinsOf D cls j).card : ℝ)
  let L : ℝ := (D.filter fun q => cls q ∈ J).card
  have hn : 0 < n := Nat.cast_pos.mpr hne.card_pos
  have hA : 0 < A := Nat.cast_pos.mpr (hne.image _).card_pos
  have hp₀ : p₀ ∈ P := by
    obtain ⟨e, he⟩ := hne
    exact Finset.mem_image.mpr ⟨(p₀, e), mem_bushOf.mp he, rfl⟩
  have hDP : ∀ q ∈ D, q.1 ∈ P := fun q hq => Finset.mem_image_of_mem _ hq
  have hlower : n * P.card ≤ K * (D.card : ℝ) := by
    rw [card_eq_sum_bushOf hDP, Finset.mul_sum]
    calc
      n * P.card = ∑ _p ∈ P, n := by simp [mul_comm]
      _ ≤ ∑ p ∈ P, K * ((bushOf D p).card : ℝ) :=
        Finset.sum_le_sum fun p hp => bush_le_of_balanced hbal hp₀ hp
  let V := 36 * K * n / A
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hcap : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter fun e => dist e u ≤ 2 * R).card : ℝ) ≤ V := by
    intro p hp u hu
    have hh := bush_ball_global D hR (by positivity : 0 < 2 * R) hK.le harc p₀ p u
    have heq : (2 * (2 * R) / R + 2) ^ 2 = 36 := by field_simp; ring
    rw [heq] at hh
    dsimp [V]
    rw [le_div_iff₀ hA]
    nlinarith only [hh]
  have hupper := selected_label_mass_le_incidence hV hDP hJ hgeo hcap
  change L ≤ 2 * V * I at hupper
  have hupper' : L * A ≤ 72 * K * n * I := by
    have hh := mul_le_mul_of_nonneg_right hupper hA.le
    have heq : 2 * V * I * A = 72 * K * n * I := by dsimp [V]; field_simp; ring
    rwa [heq] at hh
  apply (mul_le_mul_iff_right₀ hn).mp
  calc
    n * (lam * P.card * A) = (n * P.card) * (lam * A) := by ring
    _ ≤ (K * D.card) * (lam * A) :=
      mul_le_mul_of_nonneg_right hlower (mul_nonneg hlam hA.le)
    _ = K * (lam * D.card) * A := by ring
    _ ≤ K * L * A := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkeep hK.le) hA.le
    _ = K * (L * A) := by ring
    _ ≤ K * (72 * K * n * I) := mul_le_mul_of_nonneg_left hupper' hK.le
    _ = n * (72 * K ^ 2 * I) := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
