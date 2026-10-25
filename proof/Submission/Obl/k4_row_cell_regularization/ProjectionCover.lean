import Submission.Obl.k4_row_cell_regularization.IncidencePoints

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace Submission.Obl.k4_row_cell_regularization

/-- The unrounded two-coordinate projection, as a vector. -/
def projectionVec (u : ℝ) (p : Point) : Fin 2 → ℝ :=
  ![(pointProjection u p).1, (pointProjection u p).2]

noncomputable def roundedCode (u : ℝ) (p : Point) : Fin 2 → ℤ :=
  fun j => ⌊projectionVec u p j⌋

variable {α : Type} [MeasurableSpace α]

/-- The long trajectories used to freeze all projection covers before direction selection. -/
def longGood (h E L : ℝ) (b v H : α → ℝ) (T : α × ℝ → Fin 2 → ℝ)
    (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)) : Set (α × ℝ) :=
  longSet (goodSet h E L b v H T F) (1 / (2 * L ^ 2))

/-- Cells occurring on a long trajectory with a prescribed velocity bin. -/
noncomputable def occupiedCells (h E L : ℝ) (b v H : α → ℝ)
    (T : α × ℝ → Fin 2 → ℝ) (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)) (d : ℤ) :
    Finset Point :=
  (incPoints h E L F).filter fun p => ∃ x ∈ longGood h E L b v H T F,
    incCell h E b v T x = p ∧ incBin h v x = d

section

variable {h E L : ℝ} {b v H : α → ℝ} {T : α × ℝ → Fin 2 → ℝ}
    {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)}

theorem trajectory_projection_error (hh : 0 < h) (hh1 : h ≤ 1) (hhE : h ≤ E)
    (hL : 1 ≤ L) (htraj : ∀ l, |b l| + |v l| ≤ L)
    {x : α × ℝ} (hx : x ∈ goodSet h E L b v H T F) (j : Fin 2) :
    |projectionVec (binVel h (incBin h v x)) (incCell h E b v T x) j -
      (![b x.1 / h, H x.1 / E] : Fin 2 → ℝ) j| ≤ 4 * L + 4 := by
  fin_cases j
  · exact (traj_proj_fst hh hh1 htraj hx).trans (by linarith)
  · exact (traj_proj_snd hh hh1 hhE htraj hx).trans (by linarith)

/-- All cells on the same good trajectory are near its occurring rounded projections. -/
theorem trajectory_projection_near (hh : 0 < h) (hh1 : h ≤ 1) (hhE : h ≤ E)
    (hL : 1 ≤ L) (htraj : ∀ l, |b l| + |v l| ≤ L)
    {x y : α × ℝ} (hx : x ∈ goodSet h E L b v H T F)
    (hy : y ∈ goodSet h E L b v H T F) (hxy : y.1 = x.1) (j : Fin 2) :
    |projectionVec (binVel h (incBin h v x)) (incCell h E b v T y) j -
      (roundedCode (binVel h (incBin h v x)) (incCell h E b v T x) j : ℝ)| ≤
      8 * L + 9 := by
  have hbin : incBin h v y = incBin h v x := by simp only [incBin, hxy]
  have hy' := trajectory_projection_error hh hh1 hhE hL htraj hy j
  rw [hbin, hxy] at hy'
  have hx' := trajectory_projection_error hh hh1 hhE hL htraj hx j
  have hf := real_floor_error
    (projectionVec (binVel h (incBin h v x)) (incCell h E b v T x) j)
  have ht := abs_sub_le
    (projectionVec (binVel h (incBin h v x)) (incCell h E b v T y) j)
    ((![b x.1 / h, H x.1 / E] : Fin 2 → ℝ) j)
    (projectionVec (binVel h (incBin h v x)) (incCell h E b v T x) j)
  have hr := abs_sub_le
    (projectionVec (binVel h (incBin h v x)) (incCell h E b v T y) j)
    (projectionVec (binVel h (incBin h v x)) (incCell h E b v T x) j)
    (roundedCode (binVel h (incBin h v x)) (incCell h E b v T x) j : ℝ)
  rw [abs_sub_comm ((![b x.1 / h, H x.1 / E] : Fin 2 → ℝ) j)] at ht
  change |_ - (⌊_⌋ : ℝ)| ≤ _ at hf
  dsimp only [roundedCode] at hr ⊢
  linarith

end

variable {ν : Measure α} {μ : Measure (α × ℝ)} {b v H : α → ℝ}
    {T : α × ℝ → Fin 2 → ℝ} {π : Measure ℝ} {E : ℝ}
    {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)} {h L S : ℝ}

/-- The original long time fibers give a fixed cover, inherited by every later restriction. -/
theorem IncHyp.occupied_projection_card (hyp : IncHyp ν μ b v H T π E F h L S) (d : ℤ) :
    (((occupiedCells h E L b v H T F d).image (roundedProjection (binVel h d))).card : ℝ) ≤
      2 ^ 18 * L ^ 6 / h := by
  classical
  let P := incPoints h E L F
  let Q := occupiedCells h E L b v H T F d
  let u := binVel h d
  let C := Q.image (roundedCode u)
  let W : (Fin 2 → ℤ) → Finset Point := fun c => P.filter fun p =>
    ∀ j : Fin 2, |projectionVec u p j - (c j : ℝ)| ≤ 8 * L + 9
  have hW : ∀ c ∈ C, W c ⊆ P := fun _ _ => Finset.filter_subset _ _
  have hlarge : ∀ c ∈ C, (1 / (2 * L ^ 2)) / h ≤ ((W c).card : ℝ) := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    change p ∈ (incPoints h E L F).filter _ at hp
    obtain ⟨_, x, hx, hcell, hbin⟩ := Finset.mem_filter.mp hp
    have hgood : x ∈ goodSet h E L b v H T F := hx.1
    have hlen : ENNReal.ofReal (1 / (2 * L ^ 2)) ≤
        volume (Prod.mk x.1 ⁻¹' goodSet h E L b v H T F) := hx.2
    apply Submission.Lib.K4IncidenceWitnesses.time_labels_card_lower
      (W (roundedCode u p)) (fun q => q 0)
      (Prod.mk x.1 ⁻¹' goodSet h E L b v H T F) hyp.h_pos _ hlen
    intro t ht
    let y : α × ℝ := (x.1, t)
    have hy : y ∈ goodSet h E L b v H T F := ht
    refine ⟨incCell h E b v T y, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact incCell_mem_incPoints hyp.h_pos hyp.h_le_E hyp.traj_bound hy
    · intro j
      rw [← hcell]
      have hn := trajectory_projection_near hyp.h_pos hyp.h_lt_one.le hyp.h_le_E
        hyp.one_le_L hyp.traj_bound hgood hy rfl j
      rw [hbin] at hn
      exact hn
  have hnear : ∀ c ∈ C, ∀ p ∈ W c, ∀ j,
      |projectionVec u p j - (c j : ℝ)| ≤ 8 * L + 9 := by
    intro c _ p hp
    exact (Finset.mem_filter.mp hp).2
  have hbound := Submission.Lib.K4IncidenceWitnesses.projection_cover_of_witnesses
    P C W (projectionVec u) (by linarith [hyp.one_le_L] : 0 ≤ 8 * L + 9) hW hlarge hnear
  simp only [Fintype.card_fin] at hbound
  have hL : 0 < L := lt_of_lt_of_le one_pos hyp.one_le_L
  have hh := hyp.h_pos
  have hratio : 0 < (1 / (2 * L ^ 2)) / h := by positivity
  have hC : (C.card : ℝ) ≤ 16 * L ^ 4 * (32 * L + 39) ^ 2 / h := by
    apply (mul_le_mul_iff_left₀ hratio).mp
    calc
      _ ≤ (P.card : ℝ) * (4 * (8 * L + 9) + 3) ^ 2 := by
        exact hbound
      _ ≤ (8 * L ^ 2 / h ^ 2) * (4 * (8 * L + 9) + 3) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (incPoints_card hyp.h_pos hyp.h_lt_one.le hyp.one_le_L hyp.bins_card)
          (sq_nonneg _)
      _ = (16 * L ^ 4 * (32 * L + 39) ^ 2 / h) * ((1 / (2 * L ^ 2)) / h) := by
        field_simp
        ring
  have hupper : (C.card : ℝ) ≤ 2 ^ 18 * L ^ 6 / h := by
    have hsq : (32 * L + 39) ^ 2 ≤ (71 * L) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith [hyp.one_le_L]
    calc
      _ ≤ 16 * L ^ 4 * (32 * L + 39) ^ 2 / h := hC
      _ ≤ 16 * L ^ 4 * (71 * L) ^ 2 / h := by gcongr
      _ = 80656 * L ^ 6 / h := by ring
      _ ≤ 2 ^ 18 * L ^ 6 / h := by gcongr; norm_num
  let e : (ℤ × ℤ) → Fin 2 → ℤ := fun q => ![q.1, q.2]
  have he : Function.Injective e := by
    intro q q' hq
    exact Prod.ext (congrFun hq 0) (congrFun hq 1)
  have hCeq : C = (Q.image (roundedProjection u)).image e := by
    rw [Finset.image_image]
    change Q.image (roundedCode u) = Q.image (e ∘ roundedProjection u)
    congr 1
    funext p j
    fin_cases j <;> rfl
  have hcard : C.card = (Q.image (roundedProjection u)).card := by
    rw [hCeq, Finset.card_image_of_injective _ he]
  rw [hcard] at hupper
  exact hupper

end Submission.Obl.k4_row_cell_regularization
