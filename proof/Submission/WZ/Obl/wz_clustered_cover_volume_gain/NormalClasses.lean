-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.NormalClasses.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Classes

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

/-- A projective angular cap of radius `B*θ` can be covered at scale `θ/8`
using a number of classes independent of `θ`. Both possible signs are encoded. -/
theorem projective_cluster_cover {n B : ℕ} (hn : 0 < n) (hB : 1 ≤ B)
    {θ : ℝ} (hθ : 0 < θ) (v : Fin n → V) (v₀ : V)
    (hcap : ∀ i, pd (v i) v₀ ≤ B * θ) :
    ∃ K : ℕ, K = (128 * B + 1) ^ 4 ∧ ∃ ref : Fin K → Fin n,
      ∀ i, ∃ k, ‖v i - v (ref k)‖ ≤ θ / 8 := by
  classical
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  let good : Fin n → Prop := fun i => ‖v i - v₀‖ ≤ B * θ
  let base : Fin n → V := fun i => if good i then v₀ else -v₀
  have hb : ∀ i, ‖v i - base i‖ ≤ B * θ := by
    intro i
    by_cases hi : good i
    · simpa only [base, if_pos hi] using hi
    · have hh : ‖v i + v₀‖ ≤ B * θ :=
        (min_le_iff.mp (hcap i)).resolve_left hi
      simpa only [base, if_neg hi, sub_neg_eq_add] using hh
  let p : Fin n → Fin 4 → ℝ := fun i =>
    ![(v i - base i) 0 / θ, (v i - base i) 1 / θ, (v i - base i) 2 / θ,
      if good i then 0 else 1]
  have hcoord (i : Fin n) (j : Fin 3) : |(v i - base i) j / θ| ≤ B := by
    rw [abs_div, abs_of_pos hθ]
    apply (div_le_iff₀ hθ).mpr
    have hh : |(v i - base i) j| ≤ ‖v i - base i‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v i - base i) j
    exact hh.trans (hb i)
  have hp : ∀ i j, |p i j| ≤ (64 * B : ℕ) * (1 / 64 : ℝ) := by
    have he : ((64 * B : ℕ) : ℝ) * (1 / 64 : ℝ) = B := by push_cast; ring
    rw [he]
    intro i j
    fin_cases j
    · exact hcoord i 0
    · exact hcoord i 1
    · exact hcoord i 2
    · dsimp [p]
      split_ifs <;> simp only [abs_zero, abs_one] <;> linarith
  obtain ⟨K, hK, ref, hcover⟩ := finite_grid_representatives hn p (by norm_num : (0 : ℝ) < 1 / 64) hp
  refine ⟨K, ?_, ref, ?_⟩
  · rw [hK]
    congr 1
    ring
  intro i
  obtain ⟨k, hk⟩ := hcover i
  refine ⟨k, ?_⟩
  have he : base i = base (ref k) := by
    have hh := hk 3
    by_cases hi : good i <;> by_cases hj : good (ref k)
    · simp only [base, if_pos hi, if_pos hj]
    · norm_num [p, hi, hj] at hh
    · norm_num [p, hi, hj] at hh
    · simp only [base, if_neg hi, if_neg hj]
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  change |(v i - base i) 0 / θ - (v (ref k) - base (ref k)) 0 / θ| < 1 / 64 at h0
  change |(v i - base i) 1 / θ - (v (ref k) - base (ref k)) 1 / θ| < 1 / 64 at h1
  change |(v i - base i) 2 / θ - (v (ref k) - base (ref k)) 2 / θ| < 1 / 64 at h2
  rw [← he] at h0 h1 h2
  have h0' := scaled_coord_difference hθ (LinearIsometryEquiv.refl ℝ V) (v i) (v (ref k)) (base i) 0 h0
  have h1' := scaled_coord_difference hθ (LinearIsometryEquiv.refl ℝ V) (v i) (v (ref k)) (base i) 1 h1
  have h2' := scaled_coord_difference hθ (LinearIsometryEquiv.refl ℝ V) (v i) (v (ref k)) (base i) 2 h2
  have hh := norm_le_coord_sum (v i - v (ref k))
  change |(v i - v (ref k)) 0| ≤ (1 / 64 : ℝ) * θ at h0'
  change |(v i - v (ref k)) 1| ≤ (1 / 64 : ℝ) * θ at h1'
  change |(v i - v (ref k)) 2| ≤ (1 / 64 : ℝ) * θ at h2'
  linarith

/-- Angular selection inside a cap has a constant mass loss depending only on
the cap's relative radius, with no power of the absolute angular scale. -/
theorem clustered_normal_pigeonhole {n B : ℕ} (hn : 0 < n) (hB : 1 ≤ B)
    {θ : ℝ} (hθ : 0 < θ) (v : Fin n → V) (v₀ : V) (H : Fin n → Set V)
    (A : Set V) (hcover : A ⊆ ⋃ i, H i)
    (hcap : ∀ i, pd (v i) v₀ ≤ B * θ) :
    ∃ F : Finset (Fin n),
      (∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ≤ θ / 4) ∧
      μ A ≤ (((128 * B + 1) ^ 4 : ℕ) : ENNReal) * μ (A ∩ ⋃ i ∈ F, H i) := by
  classical
  obtain ⟨K, hK, ref, hnet⟩ := projective_cluster_cover hn hB hθ v v₀ hcap
  have hKpos : 0 < K := by rw [hK]; positivity
  letI : Nonempty (Fin K) := ⟨⟨0, hKpos⟩⟩
  let F : Fin K → Finset (Fin n) := fun k => Finset.univ.filter (fun i => ‖v i - v (ref k)‖ ≤ θ / 8)
  let Y : Fin K → Set V := fun k => A ∩ ⋃ i ∈ F k, H i
  have hcovered : A ⊆ ⋃ k ∈ (Finset.univ : Finset (Fin K)), Y k := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hp)
    obtain ⟨k, hk⟩ := hnet i
    exact mem_iUnion₂.mpr ⟨k, Finset.mem_univ _, hp,
      mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, hi⟩⟩
  obtain ⟨k, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun k : Fin K => μ (Y k)) Finset.univ_nonempty
  refine ⟨F k, ?_, ?_⟩
  · intro i hi j hj
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := (Finset.mem_filter.mp hj).2
    have he : v i - v j = (v i - v (ref k)) - (v j - v (ref k)) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  · calc
      μ A ≤ ∑ j : Fin K, μ (Y j) := (measure_mono hcovered).trans (measure_biUnion_finset_le _ _)
      _ ≤ ∑ _j : Fin K, μ (Y k) := Finset.sum_le_sum fun j hj => hmax j hj
      _ = (((128 * B + 1) ^ 4 : ℕ) : ENNReal) * μ (A ∩ ⋃ i ∈ F k, H i) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hK, Y]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
