-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.GrainRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.GrainFamily
import Submission.WZ.Obl.wz_broad_grains_initialization.DirectionClass
import Submission.WZ.Obl.wz_broad_grains_initialization.EndpointTrim
import Submission.WZ.Obl.wz_broad_grains_initialization.CubeBudget
import Submission.WZ.Obl.wz_broad_grains_initialization.SparseCells
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (bodyCount half_mass_after_loss)
open scoped Classical

def grainMassConstant : ℝ := (2002 : ℝ) ^ 6 * 64000

lemma grainMassConstant_pos : 0 < grainMassConstant := by norm_num [grainMassConstant]

lemma rescale_mass_le {a b : ℝ} (hb : 0 < b) {M N : ENNReal}
    (h : ENNReal.ofReal a * M ≤ ENNReal.ofReal b * N) :
    ENNReal.ofReal (a / b) * M ≤ N := by
  calc
    _ = ENNReal.ofReal (1 / b) * (ENNReal.ofReal a * M) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring
    _ ≤ ENNReal.ofReal (1 / b) * (ENNReal.ofReal b * N) := mul_le_mul' le_rfl h
    _ = N := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hb.ne',
        ENNReal.ofReal_one, one_mul]

/-- The elementary grain construction with its two explicit deletion
budgets. All cuts after the direction selection are common point cuts. -/
theorem grain_refinement_of_budgets {n : ℕ} (hn : 0 < n) {δ h lam q : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100000) (hlam : 0 < lam) (hq : 0 < q)
    (htrim : 64000000000000 * δ ≤ lam)
    (hsparse : 4 * grainMassConstant * 2073600000 * δ ^ h ≤ q * lam)
    (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Space) 1)
    (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i)))
    (hdensity : ENNReal.ofReal (lam * n * δ ^ 2) ≤ ∑ i, volume (Y i))
    (hcut : ∀ V : Fin n → Set Space, (∀ i, MeasurableSet (V i)) →
      ∃ (G : Set Space) (m : ℝ), MeasurableSet G ∧ 0 < m ∧
        ENNReal.ofReal q * (∑ i, volume (V i)) ≤ ∑ i, volume (V i ∩ G) ∧
        ∀ p ∈ ⋃ i, V i ∩ G, bodyCount (fun i => V i ∩ G) p ∈ Set.Icc m (2 * m)) :
    ∃ W : Fin n → Set Space,
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i) ∧
      ENNReal.ofReal (q / (4 * grainMassConstant)) * (∑ i, volume (Y i)) ≤
        ∑ i, volume (W i) ∧
      (∀ p ∈ ⋃ i, W i, bodyCount Y p ≤ (2 * (2002 : ℝ) ^ 3) * bodyCount W p) ∧
      Nonempty (UnitGrainFamily δ h x v W (100 * δ)) := by
  classical
  have hC := grainMassConstant_pos
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  let b : ℝ := 5 * δ
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hcsmall : 20 * b ≤ 1 / 1000 := by dsimp [b]; linarith
  have hδb : δ ≤ b / 5 := by dsimp [b]; linarith
  have hfinite (V : Fin n → Set Space) (hV : ∀ i, V i ⊆ Y i) :
      (∑ i, volume (V i)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono ((hV i).trans ((hYT i).trans (hball i))))
  obtain ⟨T, hT, hTloss, hTcount⟩ := trim_tube_endpoints x v Y hYm (show 0 ≤ 20 * b by positivity)
  have hTbudget : ENNReal.ofReal (32000000 * n * (20 * b) ^ 3) ≤
      (1 / 2 : ENNReal) * ∑ i, volume (Y i) := by
    calc
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * (lam * n * δ ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_le_mul_of_nonneg_right htrim (show 0 ≤ (n : ℝ) * δ ^ 2 by positivity)
        dsimp [b]
        nlinarith only [hh]
      _ = (1 / 2 : ENNReal) * ENNReal.ofReal (lam * n * δ ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num), hhalf]
      _ ≤ _ := mul_le_mul' le_rfl hdensity
  have hTmass := half_mass_after_loss (hfinite Y (fun _ => subset_rfl)) hTloss hTbudget
  obtain ⟨e, A, hA, hAmass, hAcount⟩ := aligned_shading_class hn v hv T (fun i => (hT i).1)
  obtain ⟨G, _, hGcolor, hSmass⟩ := spatial_cube_refinement hb hb1 e A (fun i => (hA i).1)
    (fun i => (hA i).2.1.trans ((hT i).2.1.trans ((hYT i).trans (hball i))))
  let S : Fin n → Set Space := fun i => A i ∩ ⋃ j ∈ G, cubeCell b e j
  have hSm (i : Fin n) : MeasurableSet (S i) :=
    (hA i).1.inter (MeasurableSet.biUnion G.finite_toSet.countable fun j _ => cubeCell_measurable b e j)
  have hTS : (1 / 2 : ENNReal) * (∑ i, volume (Y i)) ≤
      ENNReal.ofReal grainMassConstant * ∑ i, volume (S i) := by
    calc
      _ ≤ ∑ i, volume (T i) := hTmass
      _ ≤ ENNReal.ofReal ((2002 : ℝ) ^ 6) * ∑ i, volume (A i) := hAmass
      _ ≤ ENNReal.ofReal ((2002 : ℝ) ^ 6) * (64000 * ∑ i, volume (S i)) :=
        mul_le_mul' le_rfl hSmass
      _ = _ := by rw [← mul_assoc]; norm_num [grainMassConstant, ENNReal.ofReal_mul]
  have hSret : ENNReal.ofReal (1 / (2 * grainMassConstant)) *
      (∑ i, volume (Y i)) ≤ ∑ i, volume (S i) := by
    have hh := rescale_mass_le grainMassConstant_pos (a := (1 / 2 : ℝ)) (by
      simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hTS)
    convert hh using 1 <;> congr 2 <;> ring
  obtain ⟨Q, m, hQ, hm, hVmass, hVlevel⟩ := hcut S hSm
  let V : Fin n → Set Space := fun i => S i ∩ Q
  have hVm (i : Fin n) : MeasurableSet (V i) := (hSm i).inter hQ
  have hVY (i : Fin n) : V i ⊆ Y i :=
    inter_subset_left.trans (inter_subset_left.trans ((hA i).2.1.trans (hT i).2.1))
  have hVret : ENNReal.ofReal (q / (2 * grainMassConstant)) *
      (∑ i, volume (Y i)) ≤ ∑ i, volume (V i) := by
    calc
      _ = ENNReal.ofReal q * (ENNReal.ofReal (1 / (2 * grainMassConstant)) *
          ∑ i, volume (Y i)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hq.le]
        congr 2
        ring
      _ ≤ ENNReal.ofReal q * ∑ i, volume (S i) := mul_le_mul' le_rfl hSret
      _ ≤ _ := hVmass
  have hbudget : (∑ i, (((G.filter fun j => (V i ∩ cubeCell b e j).Nonempty).card : ℝ) *
      (20 * b) ^ 3)) ≤ 82944000 * n * b ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, (82944000 * b ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        apply cube_cell_tube_budget (δ := δ) hb hb1 (by dsimp [b]; linarith) e (x i) (v i) (hv i)
        intro j hj
        obtain ⟨p, hpV, hpC⟩ := (Finset.mem_filter.mp hj).2
        exact ⟨p, hYT i (hVY i hpV), hpC⟩
      _ = _ := by simp; ring
  obtain ⟨F, hFG, hFdense, hWloss⟩ := discard_sparse_cells G (cubeCell b e) V
    (fun _ => inter_subset_left.trans inter_subset_right)
    (Real.rpow_nonneg hδ.le h) (show 0 ≤ (20 * b) ^ 3 by positivity) hbudget
  let W : Fin n → Set Space := fun i => V i ∩ ⋃ j ∈ F, cubeCell b e j
  have hWm (i : Fin n) : MeasurableSet (W i) :=
    (hVm i).inter (MeasurableSet.biUnion F.finite_toSet.countable fun j _ => cubeCell_measurable b e j)
  have hWbudget : ENNReal.ofReal (δ ^ h * (82944000 * n * b ^ 2)) ≤
      (1 / 2 : ENNReal) * ∑ i, volume (V i) := by
    calc
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * (q / (2 * grainMassConstant)) * (lam * n * δ ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_le_mul_of_nonneg_right hsparse (show 0 ≤ (n : ℝ) * δ ^ 2 by positivity)
        have hC := grainMassConstant_pos
        dsimp [b]
        apply (mul_le_mul_iff_of_pos_right (show 0 < 4 * grainMassConstant by positivity)).mp
        convert hh using 1 <;> field_simp <;> ring
      _ = (1 / 2 : ENNReal) * (ENNReal.ofReal (q / (2 * grainMassConstant)) *
          ENNReal.ofReal (lam * n * δ ^ 2)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), hhalf, mul_assoc]
      _ ≤ (1 / 2 : ENNReal) * (ENNReal.ofReal (q / (2 * grainMassConstant)) *
          ∑ i, volume (Y i)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hdensity)
      _ ≤ _ := mul_le_mul' le_rfl hVret
  have hWmass := half_mass_after_loss (hfinite V hVY) hWloss hWbudget
  have hWret : ENNReal.ofReal (q / (4 * grainMassConstant)) *
      (∑ i, volume (Y i)) ≤ ∑ i, volume (W i) := by
    calc
      _ = (1 / 2 : ENNReal) * (ENNReal.ofReal (q / (2 * grainMassConstant)) *
          ∑ i, volume (Y i)) := by
        rw [← mul_assoc, ← hhalf, ← ENNReal.ofReal_mul (by norm_num)]
        congr 2
        ring
      _ ≤ (1 / 2 : ENNReal) * ∑ i, volume (V i) := mul_le_mul' le_rfl hVret
      _ ≤ _ := hWmass
  have hWcount (p : Space) (hp : p ∈ ⋃ i, W i) : bodyCount W p = bodyCount A p := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    change bodyCount (fun i => V i ∩ ⋃ j ∈ F, cubeCell b e j) p = _
    rw [body_count_cut, if_pos hi.2]
    change bodyCount (fun i => S i ∩ Q) p = _
    rw [body_count_cut, if_pos hi.1.2]
    change bodyCount (fun i => A i ∩ ⋃ j ∈ G, cubeCell b e j) p = _
    rw [body_count_cut, if_pos hi.1.1.2]
  refine ⟨W, fun i => ⟨hWm i, inter_subset_left.trans (hVY i)⟩, hWret, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    have hpA : p ∈ A i := hi.1.1.1
    have hcT := hTcount p (Set.mem_iUnion.mpr ⟨i, (hA i).2.1 hpA⟩)
    have hcA := hAcount p (Set.mem_iUnion.mpr ⟨i, hpA⟩)
    rw [hWcount p (Set.mem_iUnion.mpr ⟨i, hi⟩)]
    nlinarith only [hcT, hcA]
  · have hh := unit_grain_family_of_cells hδ hb hcsmall hδb x v W e F hv hball hWm
      (fun i => inter_subset_left.trans ((hVY i).trans (hYT i)))
      (fun i hi => (hA i).2.2 (hi.mono (fun _ hp => hp.1.1.1)))
      (fun i p hp => (hT i).2.2 p ((hA i).2.1 hp.1.1.1))
      (fun j hj k hk => hGcolor j (hFG hj) k (hFG hk)) (fun _ => inter_subset_right)
      (fun j hj => (hFdense j hj).trans (measure_mono (by
        intro p hp
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp.1
        exact ⟨Set.mem_iUnion.mpr ⟨i, hi, Set.mem_iUnion₂.mpr ⟨j, hj, hp.2⟩⟩, hp.2⟩)))
      (by
        intro p hp
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
        have hh := hVlevel p (Set.mem_iUnion.mpr ⟨i, hi.1⟩)
        change bodyCount (fun i => V i ∩ ⋃ j ∈ F, cubeCell b e j) p ∈ _
        rw [body_count_cut, if_pos hi.2]
        exact hh)
    simpa only [b, show 20 * (5 * δ) = 100 * δ by ring] using hh

end WangZahlLot.Obl.wz_broad_grains_initialization
