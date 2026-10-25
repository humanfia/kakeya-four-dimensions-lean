-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_restricted_uniform_improvement.Refinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_restricted_uniform_improvement.Estimates
import Submission.WZ.Obl.wz_direction_density_transfer

namespace WangZahlLot.Obl.wz_restricted_uniform_improvement

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_endpoint_bootstrap

/-- A threshold extraction retaining a controlled number of indices. -/
theorem threshold_extraction {ι : Type*} [Fintype ι] (f : ι → ℝ) (a B : ℝ)
    (ha : 0 ≤ a) (hupper : ∀ i, f i ≤ B)
    (haverage : (Fintype.card ι : ℝ) * a ≤ ∑ i, f i) :
    ∃ F : Finset ι, (∀ i ∈ F, a / 2 ≤ f i) ∧
      (Fintype.card ι : ℝ) * a ≤ 2 * (F.card : ℝ) * B := by
  classical
  let F : Finset ι := Finset.univ.filter fun i => a / 2 ≤ f i
  have hpoint : ∀ i, f i ≤ (if i ∈ F then B else 0) + a / 2 := by
    intro i
    by_cases hi : i ∈ F
    · rw [ite_eq_left hi]
      linarith [hupper i]
    · rw [ite_eq_right hi]
      have hnot : ¬a / 2 ≤ f i := by simpa [F] using hi
      linarith
  have hsum : ∑ i, f i ≤ (F.card : ℝ) * B + (Fintype.card ι : ℝ) * (a / 2) := by
    calc
      _ ≤ ∑ i, ((if i ∈ F then B else 0) + a / 2) := Finset.sum_le_sum fun i _ => hpoint i
      _ = _ := by simp [Finset.sum_add_distrib]
  refine ⟨F, fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
  linarith

/-- A uniform upper bound for unit-tube volume in the scale range of the problem. -/
theorem tube_volume_upper {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x v : Space) (hv : ‖v‖ = 1) :
    volume (tube δ x v) ≤ ENNReal.ofReal (384 * δ ^ 2) := by
  have hseg : (fun t : ℝ => x + t • v) '' Icc 0 1 = segment ℝ x (x + v) := by
    rw [segment_eq_image']
    simp
  have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper x v hv
    (T := Icc 0 1) Subset.rfl (r := δ) (A := 1) hδ zero_le_one
    (by intro s hs t ht; rw [Real.dist_eq, abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
  rw [hseg] at h
  apply h.trans (ENNReal.ofReal_le_ofReal _)
  exact mul_le_mul_of_nonneg_right (by linarith : 128 * (2 * 1 + δ) ≤ 384) (sq_nonneg δ)

/-- The positive-density hypotheses allow a refinement with uniform density
on every retained tube. The statement retains the absolute constants explicitly. -/
theorem extract_uniform_density {δ η : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : Admissible δ η x v Y) :
    ∃ F : Finset (Fin n), F.Nonempty ∧
      (n : ℝ) * δ ^ η ≤ 768 * (F.card : ℝ) ∧
      ∀ i ∈ F, ENNReal.ofReal (δ ^ η * δ ^ 2 / 2) ≤ volume (Y i) := by
  classical
  have hupper : ∀ i, volume (Y i) ≤ ENNReal.ofReal (384 * δ ^ 2) :=
    fun i => (measure_mono (hA.2.2.2.2.2.1 i)).trans
      (tube_volume_upper hδ hδ1 (x i) (v i) (hA.2.1 i))
  have hfin : ∀ i, volume (Y i) ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper i)
  have hupperR : ∀ i, (volume (Y i)).toReal ≤ 384 * δ ^ 2 :=
    fun i => ENNReal.toReal_le_of_le_ofReal (by positivity) (hupper i)
  have hsumfin : ∑ i, volume (Y i) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => hfin i)
  have hsumR : (n : ℝ) * (δ ^ η * δ ^ 2) ≤ ∑ i, (volume (Y i)).toReal := by
    have h := ENNReal.toReal_mono hsumfin hA.2.2.2.2.2.2
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_sum (fun i _ => hfin i)] at h
    convert h using 1; ring
  obtain ⟨F, hF, hcard⟩ := threshold_extraction (fun i => (volume (Y i)).toReal)
    (δ ^ η * δ ^ 2) (384 * δ ^ 2) (by positivity) hupperR (by simpa using hsumR)
  have hcard' : (n : ℝ) * δ ^ η ≤ 768 * (F.card : ℝ) := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp
    have hh : (n : ℝ) * (δ ^ η * δ ^ 2) ≤ 2 * (F.card : ℝ) * (384 * δ ^ 2) := by
      simpa only [Fintype.card_fin] using hcard
    nlinarith only [hh]
  have hFpos : 0 < (F.card : ℝ) := by
    have hpos : 0 < (n : ℝ) * δ ^ η := mul_pos (Nat.cast_pos.mpr hA.1) (Real.rpow_pos_of_pos hδ _)
    nlinarith
  refine ⟨F, Finset.card_pos.mp (Nat.cast_pos.mp hFpos), hcard', ?_⟩
  intro i hi
  exact (ENNReal.ofReal_le_ofReal (hF i hi)).trans_eq (ENNReal.ofReal_toReal (hfin i))

/-- Reindex the selected tubes by a finite ordinal without introducing duplicates. -/
theorem extract_uniform_density_fin {δ η : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : Admissible δ η x v Y) :
    ∃ k : ℕ, 0 < k ∧ ∃ f : Fin k ↪ Fin n,
      (n : ℝ) * δ ^ η ≤ 768 * (k : ℝ) ∧
      ∀ j, ENNReal.ofReal (δ ^ η * δ ^ 2 / 2) ≤ volume (Y (f j)) := by
  classical
  obtain ⟨F, hF, hcard, hdense⟩ := extract_uniform_density hδ hδ1 hA
  let e : F ≃ Fin F.card := Fintype.equivFinOfCardEq (by simp)
  let f : Fin F.card ↪ Fin n :=
    ⟨fun j => (e.symm j).val, fun _ _ h => e.symm.injective (Subtype.ext h)⟩
  exact ⟨F.card, Finset.card_pos.mpr hF, f, hcard,
    fun j => hdense (f j) (e.symm j).property⟩

/-- Contained-tube counts cannot increase after passage to a subfamily. -/
theorem subfamily_count {n k : ℕ} (f : Fin k ↪ Fin n) (P : Fin n → Prop) :
    (Set.ncard {j | P (f j)}) ≤ Set.ncard {i | P i} := by
  calc
    _ = (f '' {j | P (f j)}).ncard := (Set.ncard_image_of_injective _ f.injective).symm
    _ ≤ _ := Set.ncard_le_ncard (by rintro _ ⟨j, hj, rfl⟩; exact hj)

theorem katz_subfamily {δ m : ℝ} {n k : ℕ} {x v : Fin n → Space}
    (f : Fin k ↪ Fin n) (hK : Katz δ m x v) : Katz δ m (x ∘ f) (v ∘ f) := by
  intro W hW
  apply le_trans (ENNReal.ofReal_le_ofReal _) (hK W hW)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
  exact_mod_cast subfamily_count f (fun i => tube δ (x i) (v i) ⊆ W)

/-- The only slab-count loss on restriction is the ratio of cardinalities. -/
theorem frostman_subfamily {δ l l' : ℝ} {n k : ℕ} {x v : Fin n → Space}
    (f : Fin k ↪ Fin n) (hcard : l * (n : ℝ) ≤ l' * (k : ℝ))
    (hF : Frostman δ l x v) : Frostman δ l' (x ∘ f) (v ∘ f) := by
  intro u t r hu hr
  apply le_trans (ENNReal.ofReal_le_ofReal _) ((hF u t r hu hr).trans _)
  · exact_mod_cast subfamily_count f (fun i => tube δ (x i) (v i) ⊆
      ball (0 : Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r})
  · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hcard) _

theorem dense_of_individual {δ η : ℝ} {k : ℕ} {Y : Fin k → Set Space}
    (hδ : 0 ≤ δ) (h : ∀ j, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y j)) :
    WangZahlLot.Obl.wz_endpoint_bootstrap.Dense δ η Y := by
  calc
    ENNReal.ofReal (δ ^ η * (k : ℝ) * δ ^ 2) =
        ∑ j : Fin k, ENNReal.ofReal (δ ^ η * δ ^ 2) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      congr 1
      ring
    _ ≤ _ := Finset.sum_le_sum fun j _ => h j

theorem admissible_subfamily {δ η η' : ℝ} {n k : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space} (f : Fin k ↪ Fin n)
    (hk : 0 < k) (hA : Admissible δ η x v Y)
    (hden : WangZahlLot.Obl.wz_endpoint_bootstrap.Dense δ η' (Y ∘ f)) :
    Admissible δ η' (x ∘ f) (v ∘ f) (Y ∘ f) := by
  rcases hA with ⟨_, hv, hb, hd, hm, hY, _⟩
  exact ⟨hk, fun j => hv (f j), fun j => hb (f j),
    fun i j hij => hd (f i) (f j) (f.injective.ne hij),
    fun j => hm (f j), fun j => hY (f j), hden⟩

theorem subfamily_union_subset {n k : ℕ} (f : Fin k → Fin n)
    (Y : Fin n → Set Space) : (⋃ j, Y (f j)) ⊆ ⋃ i, Y i :=
  iUnion_subset fun j => subset_iUnion Y (f j)

end WangZahlLot.Obl.wz_restricted_uniform_improvement
