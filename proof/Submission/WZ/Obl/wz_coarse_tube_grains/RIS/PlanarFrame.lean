-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PlanarFrame.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CoarseFrame
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.TubeNormal
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorBox

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open LeanEval.Analysis.WangZahlKakeya Set Metric

/-- Slab containment bounds the normal component of a unit segment's axis. -/
theorem tube_direction_of_slab {δ r t : ℝ} {x v u : V} (hδ : 0 < δ)
    (hslab : T δ x v ⊆ {p | |inner ℝ u p - t| ≤ r}) : |inner ℝ u v| ≤ 2 * r := by
  have hx : x ∈ T δ x v := self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))
  have hxv : x + v ∈ T δ x v := self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v))
  have h := abs_sub (inner ℝ u (x + v) - t) (inner ℝ u x - t)
  have he : (inner ℝ u (x + v) - t) - (inner ℝ u x - t) = inner ℝ u v := by
    rw [inner_add_right]
    ring
  rw [he] at h
  have hhx : |inner ℝ u x - t| ≤ r := hslab hx
  have hhxv : |inner ℝ u (x + v) - t| ≤ r := hslab hxv
  linarith

/-- Normal direction bounds for a nonempty coarse fiber determine a common
frame. Only the occupied set Q is constrained. -/
theorem exists_coarse_frame_from_normals {δ ρ τ : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hτρ : 2 * τ ≤ ρ) (hρ100 : ρ ≤ 1 / 100)
    {x v : Fin n → V} {y w u : V} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (Q : Set (Fin n)) (hQ : Q.Nonempty)
    (hv : ∀ i ∈ Q, ‖v i‖ = 1)
    (hcover : ∀ i ∈ Q, T δ (x i) (v i) ⊆ T ρ y w)
    (hnormal : ∀ i ∈ Q, |inner ℝ u (v i)| ≤ τ) :
    ∃ e : V ≃ₗᵢ[ℝ] V, (∀ p, e p 0 = inner ℝ u p) ∧
      (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2 ∧
      ∀ i ∈ Q, 1 / 2 ≤ |e (v i) 2| ∧ |e (v i) 0| ≤ τ ∧ |e (v i) 1| ≤ 8 * ρ := by
  classical
  obtain ⟨i₀, hi₀⟩ := hQ
  have hτ : 0 ≤ τ := (abs_nonneg _).trans (hnormal i₀ hi₀)
  obtain ⟨z, hz, hzu, hzv⟩ := BrushPlanarity.unit_perpendicular_near (hv i₀ hi₀) hu
    (q := τ) (by linarith) (by rw [real_inner_comm]; exact hnormal i₀ hi₀)
  obtain ⟨b, hb1, hb2⟩ := Factor.exists_frame hu hz (by rw [real_inner_comm]; exact hzu)
  let b' : OrthonormalBasis (Fin 3) ℝ V := b.reindex (Equiv.swap 0 1)
  have hb'0 : b' 0 = u := by simp [b', OrthonormalBasis.reindex_apply, hb1]
  have hb'2 : b' 2 = z := by
    simp [b', OrthonormalBasis.reindex_apply,
      show (Equiv.swap (0 : Fin 3) 1) 2 = 2 by decide, hb2]
  let e := b'.repr
  have he0 (p : V) : e p 0 = inner ℝ u p := by
    change b'.repr p 0 = _
    rw [b'.repr_apply_apply, hb'0]
  have hez1 : e z 1 = 0 := by
    change b'.repr z 1 = _
    rw [b'.repr_apply_apply, ← hb'2]
    exact b'.orthonormal.2 (by decide)
  have hbase1 : |e (v i₀) 1| ≤ 2 * τ := by
    have hdist : ‖v i₀ - z‖ ≤ 2 * τ := by
      rw [norm_sub_rev]
      linarith
    have h := (abs_rotated_coord_le e (v i₀ - z) 1).trans hdist
    simpa only [map_sub, PiLp.sub_apply, hez1, sub_zero] using h
  have hw1 : |e w 1| ≤ 6 * ρ := covered_coarse_coordinate_bound hδ (by linarith)
    (hv i₀ hi₀) hw e 1 (hcover i₀ hi₀) (hbase1.trans hτρ)
  have hcoarse : (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2 :=
    coarse_axis_frame_bound hδ hρ (by linarith) (hv i₀ hi₀) hw e (hcover i₀ hi₀)
      (by rw [he0]; linarith [hnormal i₀ hi₀]) (hbase1.trans hτρ)
  refine ⟨e, he0, hcoarse, ?_⟩
  intro i hi
  have h0 : |e (v i) 0| ≤ τ := by rw [he0]; exact hnormal i hi
  have h1 : |e (v i) 1| ≤ 8 * ρ := by
    have h := covered_fine_coordinate_bound hδ e 1 (hcover i hi) hw1
    linarith
  refine ⟨?_, h0, h1⟩
  have h0' : |e (v i) 0| ≤ ρ := by linarith
  have h0sq := (sq_le_sq₀ (abs_nonneg _) hρ.le).mpr h0'
  have h1sq := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 8 * ρ)).mpr h1
  have hρsq := pow_le_pow_left₀ hρ.le hρ100 2
  have hsum := EuclideanSpace.real_norm_sq_eq (e (v i))
  rw [e.norm_map, hv i hi, Fin.sum_univ_three] at hsum
  simp only [sq_abs] at h0sq h1sq
  have h2 : (e (v i) 2) ^ 2 = |e (v i) 2| ^ 2 := (sq_abs _).symm
  nlinarith [abs_nonneg (e (v i) 2)]

/-- A nonempty family of unit tubes in one thin slab and one coarse tube has
a common frame adapted to both. Only the occupied set Q is constrained. -/
theorem exists_planar_coarse_frame {δ ρ t : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδρ : 8 * δ ≤ ρ) (hρ100 : ρ ≤ 1 / 100)
    {x v : Fin n → V} {y w u : V} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (Q : Set (Fin n)) (hQ : Q.Nonempty)
    (hv : ∀ i ∈ Q, ‖v i‖ = 1)
    (hcover : ∀ i ∈ Q, T δ (x i) (v i) ⊆ T ρ y w)
    (hslab : ∀ i ∈ Q, T δ (x i) (v i) ⊆ {p | |inner ℝ u p - t| ≤ 2 * δ}) :
    ∃ e : V ≃ₗᵢ[ℝ] V, (∀ p, e p 0 = inner ℝ u p) ∧
      (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2 ∧
      ∀ i ∈ Q, 1 / 2 ≤ |e (v i) 2| ∧ |e (v i) 0| ≤ 4 * δ ∧ |e (v i) 1| ≤ 8 * ρ := by
  have hρ : 0 < ρ := by linarith
  apply exists_coarse_frame_from_normals hδ hρ (by linarith) hρ100 hu hw Q hQ hv hcover
  intro i hi
  have h := tube_direction_of_slab hδ (hslab i hi)
  linarith

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
