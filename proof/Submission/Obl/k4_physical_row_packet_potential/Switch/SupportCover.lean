-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/SupportCover.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). The switching target cover from a finite occupied-cell census
in the form of the frozen support clause (`gridCode`, `occupied` of
`Submission.Lib.K4ParentSignalPreparation.Census`): each occupied cell gives one
box of base half-width `p/2` and height half-width `θ w/2`, the height being
`θ` times the counted signal.
-/
import Submission.Lib.K4ParentSignalPreparation.Census
import Submission.Lib.K4PolynomialNorming.NormingCoordinates

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Lib.K4PolynomialNorming

/-- Centers of the census boxes, height first. -/
noncomputable def censusCenter (p w θ : ℝ) (k : (Fin 3 → ℤ) × ℤ) : Fin 4 → ℝ :=
  Fin.cons (θ * w * ((k.2 : ℝ) + 1 / 2)) (fun i => p * ((k.1 i : ℝ) + 1 / 2))

/-- Half-widths of the census boxes, height first. -/
noncomputable def censusWidth (p w θ : ℝ) : Fin 4 → ℝ :=
  Fin.cons (θ * w / 2) (fun _ => p / 2)

theorem floor_cell_center_dist {x m : ℝ} (hm : 0 < m) :
    |x - m * ((⌊x / m⌋ : ℝ) + 1 / 2)| ≤ m / 2 := by
  have hlo := Int.floor_le (x / m)
  have hhi := Int.lt_floor_add_one (x / m)
  have h1 : m * (⌊x / m⌋ : ℝ) ≤ x := by
    have := mul_le_mul_of_nonneg_left hlo hm.le
    rwa [mul_div_cancel₀ _ hm.ne'] at this
  have h2 : x < m * ((⌊x / m⌋ : ℝ) + 1) := by
    have := mul_lt_mul_of_pos_left hhi hm
    rwa [mul_div_cancel₀ _ hm.ne'] at this
  rw [abs_le]
  constructor <;> nlinarith

/-- Every counted event lies in the box of its own occupied cell. -/
theorem census_box_cover {Ω : Type*} (E : Set Ω) (z : Ω → Fin 3 → ℝ) (X : Ω → ℝ)
    {p w θ : ℝ} (hp : 0 < p) (hw : 0 < w) (hθ : 0 < θ)
    (hfin : (occupied E z X p w).Finite) :
    ∀ y ∈ {y : (Fin 3 → ℝ) × ℝ | ∃ x ∈ E, y = (z x, θ * X x)},
      ∃ k ∈ hfin.toFinset, ∀ j,
        |(splitHeadCoordinates 3).symm y j - censusCenter p w θ k j| ≤ censusWidth p w θ j := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨gridCode z X p w x, hfin.mem_toFinset.mpr ⟨x, hx, rfl⟩, fun j => ?_⟩
  rw [splitHeadCoordinates_symm_apply]
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero, censusCenter, censusWidth, gridCode]
    have hθw : 0 < θ * w := mul_pos hθ hw
    have h := floor_cell_center_dist (x := θ * X x) hθw
    have hfl : ⌊θ * X x / (θ * w)⌋ = ⌊X x / w⌋ := by
      congr 1
      field_simp
    rw [hfl] at h
    exact h
  · simp only [Fin.cons_succ, censusCenter, censusWidth, gridCode]
    exact floor_cell_center_dist hp

theorem card_census_boxes {Ω : Type*} (E : Set Ω) (z : Ω → Fin 3 → ℝ) (X : Ω → ℝ) {p w : ℝ}
    (hfin : (occupied E z X p w).Finite) :
    (hfin.toFinset.card : ℝ) = ((occupied E z X p w).ncard : ℝ) := by
  rw [Set.ncard_eq_toFinset_card _ hfin]

end Submission.Obl.k4_physical_row_packet_potential.Switch
