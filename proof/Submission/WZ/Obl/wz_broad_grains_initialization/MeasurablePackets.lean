-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.MeasurablePackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.AngularMax
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open wz_measurable_angular_selection (pd)
open wz_clustered_cover_volume_gain (bodyCount)

/-- Measurable packets at a common angular scale, with lower cardinalities
relative to the original shading. -/
def PacketRefinement {n : ℕ} (β δ θ : ℝ) (v : Fin n → Space)
    (Y Z : Fin n → Set Space) (P : Space → Finset (Finset (Fin n)))
    (a : Space → Finset (Fin n) → Fin n) : Prop :=
  (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (∀ W, MeasurableSet {p | W ∈ P p}) ∧
      (∀ W j, MeasurableSet {p | a p W = j}) ∧
      (∀ p, (P p : Set (Finset (Fin n))).Pairwise Disjoint ∧
        ((P p).biUnion id : Set (Fin n)) = {i | p ∈ Z i} ∧
        ∀ W ∈ P p, W.Nonempty ∧
          (∀ i ∈ W, pd (v i) (v (a p W)) ≤ 2 * θ) ∧
          (({i | p ∈ Y i}.ncard : ℝ) / 2) * (θ) ^ β ≤ W.card ∧
          ∀ u r, δ ≤ r →
            ((W.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤
              2 * (r / θ) ^ β * (W.card : ℝ))

/-- Select one common angular scale while retaining a logarithmic fraction of
incidence mass. At each point the incidences are partitioned into large broad
packets, and every choice has measurable fibres. -/
theorem measurable_angular_packets {n : ℕ} (hn : 0 < n)
    (v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (Y : Fin n → Set Space) (hY : ∀ i, MeasurableSet (Y i))
    {β δ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hδ : 0 < δ) {K : ℕ}
    (hK2 : (1 / 2 : ℝ) ^ K < 2 * δ) :
    ∃ (k : Fin (K + 1)) (Z : Fin n → Set Space)
      (P : Space → Finset (Finset (Fin n))) (a : Space → Finset (Fin n) → Fin n),
      PacketRefinement β δ ((1 / 2 : ℝ) ^ (k : ℕ)) v Y Z P a ∧
      ENNReal.ofReal (1 / (2 * ((K : ℝ) + 1))) * ∑ i, volume (Y i) ≤
        ∑ i, volume (Z i) := by
  classical
  choose packets hgood hsub hdis hcount using
    fun S : Finset (Fin n) => partial_angular_partition v hv hβ hβ1 hδ hK2
      ((S.card : ℝ) / 2) (by positivity) S
  have hlabels : ∀ S W, ∃ k : Fin (K + 1), ∃ j : Fin n,
      W ∈ packets S →
      (∀ i ∈ W, pd (v i) (v j) ≤ 2 * (1 / 2 : ℝ) ^ (k : ℕ)) ∧
      ((S.card : ℝ) / 2) * ((1 / 2 : ℝ) ^ (k : ℕ)) ^ β ≤ W.card ∧
      ∀ u r, δ ≤ r →
        ((W.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤
          2 * (r / (1 / 2 : ℝ) ^ (k : ℕ)) ^ β * (W.card : ℝ) := by
    intro S W
    by_cases hW : W ∈ packets S
    · obtain ⟨_, k, hk, j, hc, hs, hr⟩ := hgood S W hW
      exact ⟨⟨k, Nat.lt_succ_of_le hk⟩, j, fun _ => ⟨hc, hs, hr⟩⟩
    · exact ⟨0, ⟨0, hn⟩, fun hh => (hW hh).elim⟩
  choose label center hlabel using hlabels
  let pattern : Space → Finset (Fin n) := fun p => Finset.univ.filter (fun i => p ∈ Y i)
  have hpattern (p : Space) (i : Fin n) : i ∈ pattern p ↔ p ∈ Y i := by simp [pattern]
  let group : Fin (K + 1) → Finset (Fin n) → Finset (Finset (Fin n)) :=
    fun k S => (packets S).filter (fun W => label S W = k)
  let Z : Fin (K + 1) → Fin n → Set Space :=
    fun k i => {p | i ∈ (group k (pattern p)).biUnion id}
  let U : Fin n → Set Space := fun i => {p | i ∈ (packets (pattern p)).biUnion id}
  have hZm (k : Fin (K + 1)) (i : Fin n) : MeasurableSet (Z k i) :=
    wz_measurable_angular_selection.measurableSet_pattern hY pattern hpattern
      (fun S => i ∈ (group k S).biUnion id)
  have hUm (i : Fin n) : MeasurableSet (U i) :=
    wz_measurable_angular_selection.measurableSet_pattern hY pattern hpattern
      (fun S => i ∈ (packets S).biUnion id)
  have hZsub (k : Fin (K + 1)) (i : Fin n) : Z k i ⊆ Y i := by
    intro p hp
    obtain ⟨W, hW, hi⟩ := Finset.mem_biUnion.mp hp
    exact (hpattern p i).mp (hsub (pattern p) W (Finset.mem_filter.mp hW).1 hi)
  have hCY (p : Space) : bodyCount Y p = ((pattern p).card : ℝ) := by
    simp [bodyCount, pattern, Set.ncard_eq_toFinset_card']
  have hCU (p : Space) : bodyCount U p = ((packets (pattern p)).biUnion id).card := by
    have he : {i | p ∈ U i} = ((packets (pattern p)).biUnion id : Set (Fin n)) := by
      ext i
      rfl
    simp only [bodyCount, he, Set.ncard_coe_finset]
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) * ∑ i, volume (Y i) ≤ ∑ i, volume (U i) := by
    apply wz_clustered_cover_volume_gain.body_mass_le_of_count hY hUm (by norm_num)
    intro p
    rw [hCY, hCU]
    have hh := hcount (pattern p)
    linarith
  have hcover (i : Fin n) : U i ⊆ ⋃ k, Z k i := by
    intro p hp
    obtain ⟨W, hW, hi⟩ := Finset.mem_biUnion.mp hp
    refine Set.mem_iUnion.mpr ⟨label (pattern p) W, ?_⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨W, Finset.mem_filter.mpr ⟨hW, rfl⟩, hi⟩
  have hsum : ENNReal.ofReal (1 / 2 : ℝ) * ∑ i, volume (Y i) ≤
      ∑ k, ∑ i, volume (Z k i) := by
    apply hhalf.trans
    calc
      ∑ i, volume (U i) ≤ ∑ i, ∑ k, volume (Z k i) := by
        apply Finset.sum_le_sum
        intro i _
        exact (measure_mono (hcover i)).trans (by
          simpa only [tsum_fintype] using (measure_iUnion_le (fun k => Z k i)))
      _ = _ := Finset.sum_comm
  obtain ⟨k, _, hkmax⟩ := Finset.exists_max_image Finset.univ
    (fun k : Fin (K + 1) => ∑ i, volume (Z k i)) (Finset.univ_nonempty)
  have hmassbound : ENNReal.ofReal (1 / 2 : ℝ) * ∑ i, volume (Y i) ≤
      ENNReal.ofReal ((K : ℝ) + 1) * ∑ i, volume (Z k i) := by
    apply hsum.trans
    calc
      ∑ l, ∑ i, volume (Z l i) ≤ ∑ _ : Fin (K + 1), ∑ i, volume (Z k i) :=
        Finset.sum_le_sum (fun l hl => hkmax l hl)
      _ = _ := by simp [nsmul_eq_mul, ENNReal.ofReal_add]
  have hscale : ENNReal.ofReal (1 / (2 * ((K : ℝ) + 1))) * ∑ i, volume (Y i) ≤
      ∑ i, volume (Z k i) := by
    have hKpos : 0 < (K : ℝ) + 1 := by positivity
    calc
      _ = ENNReal.ofReal (1 / ((K : ℝ) + 1)) *
          (ENNReal.ofReal (1 / 2 : ℝ) * ∑ i, volume (Y i)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
      _ ≤ ENNReal.ofReal (1 / ((K : ℝ) + 1)) *
          (ENNReal.ofReal ((K : ℝ) + 1) * ∑ i, volume (Z k i)) :=
        mul_le_mul_right hmassbound _
      _ = ∑ i, volume (Z k i) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hKpos.ne']
        simp
  refine ⟨k, Z k, fun p => group k (pattern p), fun p => center (pattern p),
    ?_, hscale⟩
  refine ⟨fun i => ⟨hZm k i, hZsub k i⟩, ?_, ?_, ?_⟩
  · intro W
    exact wz_measurable_angular_selection.measurableSet_pattern hY pattern hpattern
      (fun S => W ∈ group k S)
  · intro W j
    exact wz_measurable_angular_selection.measurableSet_pattern hY pattern hpattern
      (fun S => center S W = j)
  · intro p
    refine ⟨(hdis (pattern p)).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)), ?_, ?_⟩
    · ext i
      simp [Z]
    · intro W hW
      obtain ⟨hWP, hWk⟩ := Finset.mem_filter.mp hW
      obtain ⟨hc, hs, hr⟩ := hlabel (pattern p) W hWP
      rw [hWk] at hc hs hr
      refine ⟨(hgood (pattern p) W hWP).1, hc, ?_, hr⟩
      simpa only [← hCY p, bodyCount] using hs

end WangZahlLot.Obl.wz_broad_grains_initialization
