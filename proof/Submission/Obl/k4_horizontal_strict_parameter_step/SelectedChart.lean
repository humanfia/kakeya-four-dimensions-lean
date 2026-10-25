import Submission.Obl.k4_horizontal_strict_parameter_step.SelectedRowDefinitions
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeScalarSupport
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeCountMesh
import Submission.Obl.k4_critical_derivative_evaluation_lists.GeoNativeGroupGeometry

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Lib.K4FullTimeLayers

noncomputable section

private theorem grid_abs_sub_le {x D : ℝ} {j : ℤ} (hD : 0 < D)
    (hj : ⌊x / D⌋ = j) : |x - (j : ℝ) * D| ≤ D := by
  have hh := Int.floor_eq_iff.mp hj
  rw [le_div_iff₀ hD, div_lt_iff₀ hD] at hh
  exact abs_le.mpr ⟨by linarith, by nlinarith [hh.2]⟩

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

/-- The trajectory assignment stays whole; row selection and all subsequent
preparations occur in the labeled spacetime event. -/
def selectedChart
    (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (E : Fin c.m → Set (α × ℝ)) (h : Fin c.m) : RawChart α where
  A := c.AH h
  q := c.group h
  h := c.hH h
  F := c.selectedF choice h
  E := E h

/-- On a later selected event, the original true child list supplies the
scalar support for the actual time-only row. The finite list is constructed
from occurring child labels and all floors remain original. -/
theorem selectedChart_support_at_child {r τ : ℝ}
    (parent : cfg.AssignmentLevel k s) (child : cfg.AssignmentLevel k r)
    (L : NativeAffineTable cfg k r)
    (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (E : Fin c.m → Set (α × ℝ)) (h : Fin c.m)
    (hE : ∀ p ∈ E h, p ∈ c.support.event ∧ p.1 ∈ c.AH h ∧
      ∃ i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧
        choice h (cfg.j k s i) = some i)
    (hcover : ∀ p ∈ E h, ∃ i, p.1 ∈ cfg.B k r i ∧
      p.2 ∈ Data.I (cfg.T k r) (cfg.j k r i))
    (hunique : ∀ p ∈ E h, ∀ j j' : Fin (2 ^ cfg.T k r),
      p.2 ∈ Data.I (cfg.T k r) j → p.2 ∈ Data.I (cfg.T k r) j' → j = j')
    (hnest : ∀ i : Fin (cfg.n k r), ∃ j : Fin (cfg.n k s),
      cfg.A k r i ⊆ cfg.A k s j ∧
      Data.I (cfg.T k r) (cfg.j k r i) ⊆ Data.I (cfg.T k s) (cfg.j k s j))
    (hν : IsProbabilityMeasure (cfg.ν k)) (hN : 2 ≤ cfg.N k) (hK : 3 ≤ cfg.K k)
    (hℓ : cfg.ℓ = cfg.κ) (hκ : 0 ≤ cfg.κ) (hκ1 : 2 * cfg.κ ≤ 1)
    (hr : 0 ≤ r) (hsr : s ≤ r) (ha : c.a = cfg.N k ^ (-s))
    (hM : c.M = 8 * cfg.K k ^ 4)
    (hdom : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (hlarge : 69120 * cfg.K k ^ 8 ≤ cfg.N k)
    (hDq : c.D ≤ cfg.timeLength k r ^ 2)
    (hcap : ∀ u ∈ ({s, r} : Set ℝ), ∀ (Q : Fin 3 → ℤ) (j : ℤ),
      cfg.μ k {ω | cfg.z k (cfg.N k) (r + 2) ω = Q ∧
        ⌊(cfg.x k ω.1 ω.2) 3 / cfg.N k ^ (-u)⌋ = j} ≤
          ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * (r + 2) - cfg.d * u)))
    (hcontactBudget : 16 * cfg.K k ^ 4 * cfg.N k ^ (-cfg.e₀) ≤ cfg.N k ^ (-r))
    (hroom : 14155776 * cfg.K k ^ 10 * c.D ≤
      (cfg.N k ^ (-r) / cfg.N k ^ (-s)) * cfg.timeLength k r ^ 2) :
    ∃ Γ : Finset ℤ,
      (Γ.card : ℝ) ≤ 811008 * cfg.K k ^ 12 *
        (cfg.N k ^ (-r) / cfg.N k ^ (-s)) ^ (-cfg.d) ∧
      ∀ l, (l, τ) ∈ E h →
        ⌊FirstJet.scal
          ((c.selectedChart choice E h).y (cfg.b k) (cfg.N k ^ (-s)) c.D)
          ((c.selectedChart choice E h).β (cfg.b k) (cfg.N k ^ (-s)) c.D)
          ((c.selectedChart choice E h).γ (cfg.b k) (cfg.N k ^ (-s)) c.D)
          (c.selectedF choice h) l τ / (cfg.N k ^ (-r) / cfg.N k ^ (-s))⌋ ∈ Γ := by
  classical
  have hNp : 0 < cfg.N k := by linarith
  have hN1 : 1 ≤ cfg.N k := by linarith
  have hK1 : 1 ≤ cfg.K k := by linarith
  have hK₂ : 5 ≤ cfg.K k ^ 2 := by nlinarith
  have ha₀ : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hNp _
  have hχ : 0 < cfg.N k ^ (-cfg.e₀) := Real.rpow_pos_of_pos hNp _
  by_cases hnonempty : ∃ l, (l, τ) ∈ E h
  · obtain ⟨l₀, hl₀⟩ := hnonempty
    obtain ⟨hp₀, hAH₀, i₀, hBi₀, ht₀, hchoice₀⟩ := hE (l₀, τ) hl₀
    have ht : τ ∈ Icc (0 : ℝ) 1 := c.support.unit (l₀, τ) hp₀
    let v := cfg.N k ^ (-cfg.e₀) * (c.group h 0 : ℝ)
    let p₀ := (c.group h 1 : ℝ) * c.D
    let q₀ := (c.group h 2 : ℝ) * c.D
    have hcoords (l : α) (hl : (l, τ) ∈ E h) :
        l ∈ c.AH h ∧ |cfg.b k l 0 - p₀| ≤ c.D ∧ |cfg.b k l 1 - q₀| ≤ c.D := by
      have hh := hE (l, τ) hl
      have hg := (c.layer.2.2.1 h).1 l hh.2.1
      exact ⟨hh.2.1, grid_abs_sub_le c.D_pos hg.2.1, grid_abs_sub_le c.D_pos hg.2.2⟩
    have hvel (l : α) (hl : (l, τ) ∈ E h) :
        |cfg.b k l 3 - v| ≤ cfg.N k ^ (-cfg.e₀) := by
      have hg := (c.layer.2.2.1 h).1 l (hE (l, τ) hl).2.1
      simpa only [v, mul_comm] using grid_abs_sub_le hχ hg.1
    have hdef (l : α) (hl : (l, τ) ∈ E h) :
        |cfg.b k l 4 + cfg.b k l 0| ≤ cfg.N k ^ (-cfg.e₀) :=
      c.support.contact (l, τ) (hE (l, τ) hl).1
    have hpbound : |p₀| ≤ 3 * cfg.K k := by
      calc
        |p₀| ≤ |cfg.b k l₀ 0| + |cfg.b k l₀ 0 - p₀| := by
          have hh := abs_sub_le p₀ (cfg.b k l₀ 0) 0
          simp only [sub_zero] at hh
          rw [abs_sub_comm] at hh
          linarith
        _ ≤ 2 * cfg.K k + c.D :=
          add_le_add (c.support.coefficients (l₀, τ) hp₀ 0) (hcoords l₀ hl₀).2.1
        _ ≤ _ := by linarith [c.D_one]
    have hvbound : |v| ≤ cfg.K k ^ 2 := by
      have hv₀ : |v| ≤ 2 * cfg.K k + cfg.N k ^ (-cfg.e₀) := by
        have hh := abs_sub_le v (cfg.b k l₀ 3) 0
        simp only [sub_zero] at hh
        rw [abs_sub_comm] at hh
        linarith [c.support.coefficients (l₀, τ) hp₀ 3, hvel l₀ hl₀]
      have hχ1 := c.velocity_width.trans c.D_one
      nlinarith
    have hparent (l : α) (hl : (l, τ) ∈ E h) :
        l ∈ cfg.B k s i₀ ∧ τ ∈ Data.I (cfg.T k s) (cfg.j k s i₀) := by
      obtain ⟨_, _, i, hBi, hti, hchi⟩ := hE (l, τ) hl
      have hj := c.support.unique_block (l₀, τ) hp₀ _ _ hti ht₀
      rw [hj] at hchi
      have hi : i = i₀ := Option.some.inj (hchi.symm.trans hchoice₀)
      simpa only [hi] using And.intro hBi hti
    let S : Finset (Fin (cfg.n k r)) := Finset.univ.filter fun i =>
      ∃ l, (l, τ) ∈ E h ∧ l ∈ cfg.B k r i ∧ τ ∈ Data.I (cfg.T k r) (cfg.j k r i)
    have hS (i : Fin (cfg.n k r)) (hi : i ∈ S) :
        ∃ l, (l, τ) ∈ E h ∧ l ∈ cfg.B k r i ∧ τ ∈ Data.I (cfg.T k r) (cfg.j k r i) :=
      (Finset.mem_filter.mp hi).2
    obtain ⟨i₁, hBi₁, hti₁⟩ := hcover (l₀, τ) hl₀
    let J := cfg.j k r i₁
    have hblock (i : Fin (cfg.n k r)) (hi : i ∈ S) : cfg.j k r i = J := by
      obtain ⟨l, hl, hBi, hti⟩ := hS i hi
      exact hunique (l₀, τ) hl₀ _ _ hti hti₁
    have hnested (i : Fin (cfg.n k r)) (hi : i ∈ S) :
        cfg.A k r i ⊆ cfg.A k s i₀ ∧
        Data.I (cfg.T k r) (cfg.j k r i) ⊆ Data.I (cfg.T k s) (cfg.j k s i₀) := by
      obtain ⟨l, hl, hBi, hti⟩ := hS i hi
      obtain ⟨j, hA, hI⟩ := hnest i
      have hjblock := c.support.unique_block (l₀, τ) hp₀ _ _ (hI hti) ht₀
      have hj : j = i₀ := by
        by_contra hne
        exact Set.disjoint_left.mp (parent.disjoint j i₀ hne hjblock)
          (hA (child.fitted_subset i hBi)) (parent.fitted_subset i₀ (hparent l hl).1)
      simpa only [hj] using And.intro hA hI
    have hcontacts (i : Fin (cfg.n k r)) (hi : i ∈ S) :
        ∃ z ∈ cfg.originalTrueBox k r i,
          |z 1 - referenceZ ![p₀, q₀, v] (z 0)| ≤ cfg.K k ^ 2 * c.D ∧
          |z 2 - referenceY ![p₀, q₀, v] (z 0)| ≤ cfg.K k ^ 2 * c.D := by
      obtain ⟨l, hl, hBi, hti⟩ := hS i hi
      have hb := hcoords l hl
      have hrec := native_group_mem_contact_rectangle (cfg.b k l) ![p₀, q₀, v]
        0 2 c.D τ c.D_pos.le (by norm_num) ht
        (by rw [sub_zero, show (2 : ℝ) / 2 = 1 by norm_num, abs_of_nonneg ht.1]; exact ht.2)
        hb.2.1 hb.2.2 ((hvel l hl).trans c.velocity_width) ((hdef l hl).trans c.velocity_width)
      have hr := (mem_contactOuterBox_iff 0 2 (2 * c.D) (5 * c.D)
        ![p₀, q₀, v] (nativeHorizontalLine (cfg.b k l) τ)).mp hrec
      refine ⟨cfg.originalBasePoint k (l, τ), cfg.original_witness_mem_trueBox child i
        (l, τ) ⟨hBi, hti⟩, ?_, ?_⟩
      · exact hr.2.1.trans (mul_le_mul_of_nonneg_right (by linarith : 2 ≤ cfg.K k ^ 2) c.D_pos.le)
      · have hy : |(cfg.originalBasePoint k (l, τ)) 2 -
            referenceY ![p₀, q₀, v] ((cfg.originalBasePoint k (l, τ)) 0)| ≤ 5 * c.D := by
          simpa [contactTransverse, nativeHorizontalLine, NativeModel.originalBasePoint, Data.x]
            using hr.2.2
        exact hy.trans (mul_le_mul_of_nonneg_right hK₂ c.D_pos.le)
    let P : NativeAffineTable cfg k s := {
      entry := c.L
      slopes := by simpa only [hM] using c.slopes
      fit := by simpa only [ha] using c.true_fit }
    have hm : |(((J : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k r| ≤ 1 := by
      have hh := cfg.original_timeCenter_mem_unit (k := k) (s := r) i₁
      have hh' : 0 ≤ (((J : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k r ∧
          (((J : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k r ≤ 1 := hh
      rw [abs_of_nonneg hh'.1]
      exact hh'.2
    obtain ⟨hm₀, hm₁, hm₂, hmfit⟩ := cfg.original_count_mesh_resolves child hN hK1
      hℓ hκ hκ1 hr hlarge hpbound hvbound hm
    have hresolve : cfg.N k ^ (-(r + 2)) * ∑ e : Fin 3, |P.entry i₀ e.succ| ≤
        cfg.N k ^ (-s) := by
      have hsum : (∑ e : Fin 3, |P.entry i₀ e.succ|) ≤ 24 * cfg.K k ^ 4 := by
        calc
          _ ≤ ∑ _e : Fin 3, 8 * cfg.K k ^ 4 := Finset.sum_le_sum (fun e _ => P.slopes i₀ e)
          _ = _ := by simp; ring
      calc
        _ ≤ cfg.N k ^ (-(r + 2)) * (24 * cfg.K k ^ 4) :=
          mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hNp.le _)
        _ = 24 * cfg.K k ^ 4 * cfg.N k ^ (-(r + 2)) := mul_comm _ _
        _ ≤ cfg.N k ^ (-r) := hmfit
        _ ≤ cfg.N k ^ (-s) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    apply cfg.nested_original_scalar_support parent child P L (c.selectedChart choice E h)
      i₀ S J hν hN hK1 hℓ hκ hκ1 hr hsr hdom hlarge c.D_pos hDq ht hblock
      (fun i hi => (hnested i hi).1) (fun i hi => (hnested i hi).2) hvbound hcontacts
      hm₀ hm₁ (by simpa only [p₀, selectedChart, neg_mul] using hm₂) hresolve hcap
    · change c.selectedF choice h τ = _
      rw [c.selectedF_eq choice (l₀, τ) hp₀ h i₀ ht₀ hchoice₀]
      simp only [nativePhysical, affinePredictor, ha, P, selectedChart, v]
    · exact hcoords
    · exact hvel
    · exact hdef
    · intro l hl
      obtain ⟨i, hBi, hti⟩ := hcover (l, τ) hl
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, l, hl, hBi, hti⟩, hBi, hti⟩
    · exact hcontactBudget
    · exact hroom
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · intro l hl
      exact (hnonempty ⟨l, hl⟩).elim

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
