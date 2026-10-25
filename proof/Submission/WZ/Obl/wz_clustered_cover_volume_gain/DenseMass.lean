-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.DenseMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyDensity

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (Space BodySlabCount)

lemma select_large_masses {n : ℕ} (Y : Fin n → Set Space) {w D t : ℝ}
    (hn : 0 < n) (hw : 0 < w) (hD : 0 < D) (ht : 0 ≤ t) (htD : 2 * t ≤ D)
    (hupper : ∀ i, volume (Y i) ≤ ENNReal.ofReal (384 * w))
    (hmass : ENNReal.ofReal (D * n * w) ≤ ∑ i, volume (Y i)) :
    ∃ (k : ℕ) (f : Fin k → Fin n), Function.Injective f ∧ 0 < k ∧
      D * n / 768 ≤ (k : ℝ) ∧
      ∀ i, ENNReal.ofReal (t * w) ≤ volume (Y (f i)) := by
  classical
  have hfin : ∀ i, volume (Y i) ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper i)
  let a := fun i => (volume (Y i)).toReal
  have ha (i : Fin n) : a i ≤ 384 * w := ENNReal.toReal_le_of_le_ofReal (by positivity) (hupper i)
  have hmassR : (D / 384) * n * (384 * w) ≤ ∑ i, a i := by
    have hh := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hfin i)) hmass
    rw [ENNReal.toReal_sum (fun i _ => hfin i), ENNReal.toReal_ofReal (by positivity)] at hh
    convert hh using 1 <;> ring
  have hcount := dense_entries_card a (by positivity : 0 < 384 * w)
    (show 0 ≤ t / 384 by positivity) (by linarith : 2 * (t / 384) ≤ D / 384) ha hmassR
  let S : Finset (Fin n) := {i | t * w ≤ a i}.toFinset
  have he : (t / 384) * (384 * w) = t * w := by ring
  rw [he] at hcount
  have hcard : D * n / 768 ≤ (S.card : ℝ) := by
    convert hcount using 1
    · ring
    · simp [S, ncard_eq_toFinset_card']
  let f : Fin S.card → Fin n := fun i => (S.equivFin.symm i).val
  refine ⟨S.card, f, Subtype.val_injective.comp S.equivFin.symm.injective,
    Nat.cast_pos.mp ((show 0 < D * n / 768 by positivity).trans_le hcard), hcard, ?_⟩
  intro i
  apply (ENNReal.ofReal_le_iff_le_toReal (hfin (f i))).mpr
  simpa only [S, Set.mem_toFinset, Set.mem_ofPred_eq, f, a] using (S.equivFin.symm i).property

lemma body_slab_count_restrict {n k : ℕ} {U : Fin n → Set Space} {l : ℝ}
    (hk : 0 < k) (hF : BodySlabCount U l) (f : Fin k → Fin n) (hf : Function.Injective f) :
    BodySlabCount (U ∘ f) (l * n / k) := by
  intro ν s r hν hr
  have hcard : ({i : Fin k | U (f i) ⊆ {p | |inner ℝ ν p - s| ≤ r}}.ncard : ℝ) ≤
      {i : Fin n | U i ⊆ {p | |inner ℝ ν p - s| ≤ r}}.ncard := by
    apply Nat.cast_le.mpr
    exact Set.ncard_le_ncard_of_injOn f (fun _ hi => hi) hf.injOn
  apply (ENNReal.ofReal_le_ofReal hcard).trans
  convert hF ν s r hν hr using 1
  congr 1
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  field_simp

lemma subfamily_slab_factor {σ l n k : ℝ} (hl : 0 < l) (hn : 0 < n) (hk : 0 < k) :
    (l * n / k) ^ (-σ) * k ^ (1 - σ) = l ^ (-σ) * n ^ (-σ) * k := by
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
