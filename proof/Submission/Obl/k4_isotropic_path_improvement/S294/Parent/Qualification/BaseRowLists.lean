-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.BaseRowLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/BaseRowLists.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ShearedSupport
import Submission.Lib.K4IncidenceWitnesses

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set

noncomputable section

/-- A finite cover by pieces on which the actual row has diameter at
most one mesh gives an actual row-code list. Neither absolute row size
nor the total number of original physical states is charged. -/
theorem row_list_of_piece_diameters {Ω I : Type*}
    (E : Set Ω) (G : Ω → Fin 3 → ℝ) (pieces : Finset I) (piece : I → Set Ω)
    {p : ℝ} (hp : 0 < p)
    (hcover : ∀ x∈E, ∃ i∈pieces, x∈piece i)
    (hdiam : ∀ i∈pieces, ∀ x∈E, x∈piece i → ∀ y∈E, y∈piece i → ‖G x-G y‖ ≤ p) :
    ∃ F : Finset (Fin 3 → ℤ), (F.card:ℝ) ≤ (pieces.card:ℝ)*9^3 ∧
      ∀ x∈E, (fun j => ⌊G x j/p⌋)∈F := by
  classical
  let codes (i : I) : Set (Fin 3 → ℤ) :=
    {q | ∃ x∈E, x∈piece i ∧ (fun j => ⌊G x j/p⌋)=q}
  have hcount (i : I) (hi : i∈pieces) (F : Finset (Fin 3 → ℤ))
      (hF : (F : Set (Fin 3 → ℤ)) ⊆ codes i) : (F.card:ℝ) ≤ 9^3 := by
    have hh := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter
      F (R:=3) (by norm_num) (by
        intro q hq q' hq' j
        obtain ⟨x,hx,hxi,hxq⟩ := hF hq
        obtain ⟨y,hy,hyi,hyq⟩ := hF hq'
        have hdiff : |G x j-G y j| ≤ p :=
          (norm_le_pi_norm (G x-G y) j).trans (hdiam i hi x hx hxi y hy hyi)
        have hfloor := ShearedSupport.floor_distance hp hdiff
        have hfloor' : |(⌊G x j/p⌋:ℝ)-(⌊G y j/p⌋:ℝ)| ≤ 3 := by
          simpa only [div_self hp.ne',show (1:ℝ)+2=3 by norm_num] using hfloor
        rw [←congrFun hxq j,←congrFun hyq j]
        exact hfloor')
    simpa only [Fintype.card_fin,show 2*(3:ℝ)+3=9 by norm_num] using hh
  have hfinite (i : I) (hi : i∈pieces) : (codes i).Finite :=
    Submission.Obl.k4_scalar_initial_true_horizon.finite_of_uniform_finset_card_bound
      (codes i) (9^3) (hcount i hi)
  have hex (i : pieces) : ∃ F : Finset (Fin 3 → ℤ), (F.card:ℝ) ≤ 9^3 ∧
      ∀ x∈E, x∈piece i → (fun j => ⌊G x j/p⌋)∈F := by
    refine ⟨(hfinite i i.property).toFinset,?_,?_⟩
    · exact hcount i i.property _ (by simp only [Set.Finite.coe_toFinset]; exact subset_rfl)
    · intro x hx hxi
      exact (hfinite i i.property).mem_toFinset.mpr ⟨x,hx,hxi,rfl⟩
  choose lists hcard hknown using hex
  let F := Finset.univ.biUnion lists
  refine ⟨F,?_,?_⟩
  · calc
      (F.card:ℝ) ≤ ∑ i : pieces, ((lists i).card:ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s:=Finset.univ) (t:=lists)
      _ ≤ ∑ _i : pieces, (9:ℝ)^3 := Finset.sum_le_sum (fun i _ => hcard i)
      _ = (pieces.card:ℝ)*9^3 := by simp
  · intro x hx
    obtain ⟨i,hi,hxi⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨⟨i,hi⟩,Finset.mem_univ _,hknown ⟨i,hi⟩ x hx hxi⟩

/-- Actual height-pair estimates on finitely many old core pieces turn a
physical field comparison into a BASE-ONLY row list. Exact clock ratios
can be kept in `heightError`, `baseDiameter` and `L` by the caller. -/
theorem base_row_list_of_height_pieces {Ω I : Type*}
    (E : Set Ω) (base : Ω → Fin 3 → ℝ) (height : Ω → ℝ) (G : Ω → Fin 3 → ℝ)
    (pieces : Finset I) (piece : I → Set Ω)
    {baseDiameter heightError slope L ρ p : ℝ}
    (hbaseDiameter : 0 ≤ baseDiameter) (hheightError : 0 ≤ heightError)
    (hslope : 0 ≤ slope) (hL : 0 ≤ L) (hp : 0 < p)
    (hcover : ∀ x∈E, ∃ i∈pieces, x∈piece i)
    (hbase : ∀ x∈E, ∀ y∈E, ‖base x-base y‖ ≤ baseDiameter)
    (hheight : ∀ i∈pieces, ∀ x∈E, x∈piece i → ∀ y∈E, y∈piece i →
      |height x-height y| ≤ heightError+slope*‖base x-base y‖)
    (hphysical : ∀ x∈E, ∀ y∈E,
      ‖G x-G y‖ ≤ L*(‖(Fin.snoc (base x) (height x) : Fin 4 → ℝ)-
        Fin.snoc (base y) (height y)‖+ρ))
    (hsmall : L*((1+slope)*baseDiameter+heightError+ρ) ≤ p) :
    ∃ F : Finset (Fin 3 → ℤ), (F.card:ℝ) ≤ (pieces.card:ℝ)*9^3 ∧
      ∀ x∈E, (fun j => ⌊G x j/p⌋)∈F := by
  apply row_list_of_piece_diameters E G pieces piece hp hcover
  intro i hi x hx hxi y hy hyi
  let D := (1+slope)*baseDiameter+heightError
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbaseD : baseDiameter ≤ D := by
    dsimp only [D]
    nlinarith only [mul_nonneg hslope hbaseDiameter,hheightError]
  have hheightD : |height x-height y| ≤ D := by
    apply (hheight i hi x hx hxi y hy hyi).trans
    calc
      _ ≤ heightError+slope*baseDiameter :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hbase x hx y hy) hslope)
      _ ≤ D := by dsimp only [D]; linarith only [hbaseDiameter]
  have hpoint : ‖(Fin.snoc (base x) (height x) : Fin 4 → ℝ)-Fin.snoc (base y) (height y)‖ ≤ D := by
    apply (pi_norm_le_iff_of_nonneg hD).mpr
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [Pi.sub_apply,Fin.snoc_last,Real.norm_eq_abs] using hheightD
    · have hh := ((norm_le_pi_norm (base x-base y) k).trans (hbase x hx y hy)).trans hbaseD
      simpa only [Pi.sub_apply,Fin.snoc_castSucc] using hh
  exact (hphysical x hx y hy).trans
    ((mul_le_mul_of_nonneg_left (add_le_add hpoint le_rfl) hL).trans hsmall)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
