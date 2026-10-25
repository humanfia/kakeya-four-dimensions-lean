-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.PrismCapsTransport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.PrismSelectionCaps
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.MergeScale
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.LowOverlap

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap
  (PrismData mergePieces mergePieces_ncard mergePieces_measure fair_prism_cuts valid_cut)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (bodyCount bodyCount_inter)

/-- A common cut preserves normalized caps if it retains the required fraction
of the incidence mass in each column. -/
theorem caps_of_prism_cut {n : ℕ} (D : PrismData n) (C : Fin D.L → Set V)
    {d h h' ρ c : ℝ} {q : ENNReal} (hd : 0 < d)
    (hbudget : O (d^h') ≤ q * O (d^h)) (hcap : D.HasCaps d h ρ c)
    (hretain : ∀ j, q * ∑ i, volume (D.W i j) ≤ ∑ i, volume (D.W i j ∩ C j)) :
    (D.cut C).HasCaps d h' ρ c := by
  classical
  obtain ⟨m, hm, hcount, havg⟩ := hcap
  refine ⟨m, hm, ?_, ?_⟩
  · intro j p
    change Fin D.L at j
    change bodyCount (fun i => D.W i j ∩ C j) p ≤ m j
    rw [bodyCount_inter]
    split_ifs
    · exact hcount j p
    · exact (hm j).le
  · intro j
    change Fin D.L at j
    change O (d^h'*m j) * volume (P D.a (ρ*c) c (D.z j) (D.e j)) ≤ _
    calc
      _ = O (d^h') * (O (m j) * volume (P D.a (ρ*c) c (D.z j) (D.e j))) := by
        rw [O, ENNReal.ofReal_mul (Real.rpow_nonneg hd.le h'), mul_assoc]
      _ ≤ (q * O (d^h)) * (O (m j) * volume (P D.a (ρ*c) c (D.z j) (D.e j))) :=
        mul_le_mul' hbudget le_rfl
      _ = q * (O (d^h*m j) * volume (P D.a (ρ*c) c (D.z j) (D.e j))) := by
        rw [O, ENNReal.ofReal_mul (Real.rpow_nonneg hd.le h)]
        ring
      _ ≤ q * ∑ i, volume (D.W i j) := mul_le_mul' le_rfl (havg j)
      _ ≤ _ := hretain j

/-- Caps add when columns are merged. The same prism-volume budget used for
ordinary density pays for normalized incidence density, independently of the
number of old columns assigned to a new one. -/
theorem caps_of_prism_merge {n K : ℕ} (D : PrismData n)
    {d h h' ρ ρ' c c' a' : ℝ} (hd : 0 < d)
    (f : Fin D.L → Fin K) (hf : Function.Surjective f)
    (z' : Fin K → V) (e' : Fin K → V ≃ₗᵢ[ℝ] V) (γ' : Fin K → Fin D.N)
    (hWm : ∀ i j, MeasurableSet (D.W i j))
    (hdisj : ∀ i j j', j ≠ j' → Disjoint (D.W i j) (D.W i j'))
    (hcap : D.HasCaps d h ρ c)
    (hbudget : ∀ k j, f j = k →
      O (d^h') * volume (P a' (ρ'*c') c' (z' k) (e' k)) ≤
        O (d^h) * volume (P D.a (ρ*c) c (D.z j) (D.e j))) :
    (D.mergeScale ρ' f a' z' e' γ').HasCaps d h' ρ' c' := by
  classical
  obtain ⟨m, hm, hcount, havg⟩ := hcap
  let M : Fin K → ℝ := fun k => ∑ j, if f j = k then m j else 0
  have hterm (k : Fin K) (j : Fin D.L) : 0 ≤ if f j = k then m j else 0 := by
    split_ifs
    · exact (hm j).le
    · exact le_rfl
  have hM (k : Fin K) : 0 < M k := by
    obtain ⟨j, hj⟩ := hf k
    have hh := Finset.single_le_sum (fun j _ => hterm k j) (Finset.mem_univ j)
    exact (hm j).trans_le (by simpa only [hj, ite_true] using hh)
  refine ⟨M, hM, ?_, ?_⟩
  · intro k p
    change Fin K at k
    change bodyCount (fun i => mergePieces f D.W i k) p ≤ M k
    have hn := mergePieces_ncard f D.W hdisj p k (fun _ => True)
    simp only [and_true] at hn
    dsimp only [bodyCount, M]
    rw [hn]
    push_cast
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact hcount j p
    · exact le_rfl
  · intro k
    change Fin K at k
    change O (d^h'*M k) * volume (P a' (ρ'*c') c' (z' k) (e' k)) ≤
      ∑ i, volume (mergePieces f D.W i k)
    calc
      _ = ∑ j, if f j = k then
          O (m j) * (O (d^h') * volume (P a' (ρ'*c') c' (z' k) (e' k))) else 0 := by
        rw [O, ENNReal.ofReal_mul (Real.rpow_nonneg hd.le h')]
        dsimp only [M]
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hterm k j),
          Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs
        · ring
        · simp
      _ ≤ ∑ j, if f j = k then ∑ i, volume (D.W i j) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs with hj
        · calc
            _ ≤ O (m j) * (O (d^h) * volume (P D.a (ρ*c) c (D.z j) (D.e j))) :=
              mul_le_mul' le_rfl (hbudget k j hj)
            _ = O (d^h*m j) * volume (P D.a (ρ*c) c (D.z j) (D.e j)) := by
              rw [O, ENNReal.ofReal_mul (Real.rpow_nonneg hd.le h)]
              ring
            _ ≤ _ := havg j
        · exact le_rfl
      _ = _ := by
        simp_rw [mergePieces_measure volume f D.W hWm hdisj]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp

/-- Fair disjointification retains normalized caps as well as stage-two data. -/
theorem capped_stage_two_of_bounded_overlap {ω ζ d h h' ρ c : ℝ} {n m : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hm : 0 < m) (hd : 0 < d) (hd1 : d ≤ 1) (hhh : h ≤ h')
    (hbudget : O (d^h') ≤ (m : ENNReal)⁻¹ * O (d^h))
    (hYI : ∀ i, Y i ⊆ I) (H : D.Valid ω ζ d h ρ c x v Y 1)
    (hcap : D.HasCaps d h ρ c)
    (hcount : ∀ p k, {j | D.γ j = k ∧ p ∈ ⋃ i, D.W i j}.ncard ≤ m) :
    ∃ D' : PrismData n, D'.Valid ω ζ d h' ρ c x v Y 2 ∧ D'.HasCaps d h' ρ c := by
  classical
  have hW := H.2.2.2.2.1
  obtain ⟨C, hCm, hdisj, hvol, hunion⟩ := fair_prism_cuts hm D.W D.γ
    (fun i j => (hW i j).1)
    (fun i j => ((hW i j).2.1.trans inter_subset_left).trans (hYI i)) hcount
  have Hcut : (D.cut C).Valid ω ζ d h' ρ c x v Y 1 := by
    apply valid_cut D hd hd1 hhh H C hCm
    · calc
        _ ≤ ((m : ENNReal)⁻¹ * O (d^h)) * ∑ i, volume (Y i) := mul_le_mul' hbudget le_rfl
        _ ≤ (m : ENNReal)⁻¹ * ∑ i, ∑ j, volume (D.W i j) := by
          rw [mul_assoc]
          exact mul_le_mul' le_rfl H.2.2.2.2.2.1
        _ = _ := by simp only [hvol, Finset.mul_sum]
    · intro j
      calc
        _ ≤ ((m : ENNReal)⁻¹ * O (d^h)) * volume (P D.a (ρ*c) c (D.z j) (D.e j)) :=
          mul_le_mul' hbudget le_rfl
        _ ≤ (m : ENNReal)⁻¹ * volume (⋃ i, D.W i j) := by
          rw [mul_assoc]
          exact mul_le_mul' le_rfl (H.2.2.2.2.2.2.1 j)
        _ = _ := (hunion j).symm
  have Hcapcut : (D.cut C).HasCaps d h' ρ c := caps_of_prism_cut D C hd hbudget hcap
    (fun j => by simp only [hvol, Finset.mul_sum]; exact le_rfl)
  refine ⟨D.cut C, ?_, Hcapcut⟩
  rcases Hcut with ⟨ha, hab, hbc, hc, hW', hmass, hdense, hcross, hbroad, hX, hw, hcover, _⟩
  refine ⟨ha, hab, hbc, hc, hW', hmass, hdense, hcross, hbroad, hX, hw,
    fun _ => hcover (by decide), ?_⟩
  intro _ j j' hne hγ
  exact (hdisj j j' hne hγ).mono (iUnion_subset fun _ => inter_subset_right)
    (iUnion_subset fun _ => inter_subset_right)

end WangZahlLot.Obl.wz_broad_grains_improvement
