-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.BrushSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.StemSelection
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.StemBrush
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Extraction
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry

/-! A populated old grain and the many fine tubes meeting its shaded stem. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

lemma exists_massful_tube {n : ℕ} (hn : 0 < n) (W : Fin n → Set V)
    (hfin : ∀ i, volume (W i) ≠ ∞) {t : ℝ}
    (hmass : O ((n : ℝ)*t) ≤ ∑ i, volume (W i)) :
    ∃ i, O t ≤ volume (W i) := by
  classical
  have hreal : (n : ℝ)*t ≤ ∑ i, volume.real (W i) := by
    have hh := (ENNReal.ofReal_le_iff_le_toReal
      (ENNReal.sum_ne_top.mpr (fun i _ => hfin i))).mp hmass
    simpa only [ENNReal.toReal_sum (fun i _ => hfin i), Measure.real] using hh
  obtain ⟨i, hi⟩ := weighted_scale_selection hn Finset.univ (fun i : Fin n => i)
    (fun i => volume.real (W i))
  simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton] at hi
  refine ⟨i, (ENNReal.ofReal_le_iff_le_toReal (hfin i)).mpr ?_⟩
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  exact (mul_le_mul_iff_right₀ hnR).mp (hreal.trans hi)

/-- Both a long shaded stem and the radius-sized exceptional case supply a
large collection of tubes crossing one old grain. -/
theorem exists_populated_crossed_grain {n N J : ℕ} {d a b c lam m r ρ ω ζ h : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hc : 0 < c) (hc1 : c ≤ 1)
    (hab : a ≤ b) (hbc : b ≤ c) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hm : 0 < m) (hdr : d ≤ r) (hrρ : r ≤ ρ) (hρ1 : ρ ≤ 1)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (S : Finset (Fin n)) (W : Fin n → Set V) (f : Fin n → Fin N)
    (hWm : ∀ i, MeasurableSet (W i)) (hWT : ∀ i, W i ⊆ T d (x i) (v i))
    (hWI : ∀ i, W i ⊆ ball (0 : V) 1)
    (hWS : ∀ i, (W i).Nonempty → i ∈ S)
    (hmass : O (lam*(n : ℝ)*d^2) ≤ ∑ i, volume (W i))
    (hBr : Broad ω ζ d h ρ n N v S W f)
    (hsmallcap : d^(-h)*(r/ρ)^(ω*ζ/100) ≤ 1/2)
    (hlevel : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
      m ≤ ({i | i ∈ S ∧ f i = k ∧ p ∈ W i}.ncard : ℝ))
    (z : Fin J → V) (e : Fin J → V ≃ₗᵢ[ℝ] V) (G : Fin J → Set V)
    (γ : Fin J → Fin N) (hGP : ∀ j, G j ⊆ P a b c (z j) (e j))
    (hcover : ∀ i p, p ∈ W i → ∃ j, f i = γ j ∧ p ∈ G j)
    (hcross : ∀ i j, f i = γ j → (W i ∩ G j).Nonempty →
      W i ∩ P a b c (z j) (e j) ⊆ G j ∧ Crosses d a b c (x i) (v i) (z j) (e j)) :
    ∃ (j : Fin J) (H : Finset (Fin n)), H.Nonempty ∧
      lam*m*c*r ≤ 10000000000*d*(H.card : ℝ) ∧
      ∀ i ∈ H, i ∈ S ∧ f i = γ j ∧ (W i ∩ G j).Nonempty ∧
        Crosses d a b c (x i) (v i) (z j) (e j) := by
  classical
  have hr : 0 < r := hd.trans_le hdr
  have hWfin (i) : volume (W i) ≠ ∞ := measure_ne_top_of_subset (hWI i) measure_ball_lt_top.ne
  obtain ⟨i₀, hi₀⟩ := exists_massful_tube hn W hWfin (t := lam*d^2) (by
    convert hmass using 1 <;> congr 1 <;> ring)
  have hW0 : volume (W i₀) ≠ 0 := ne_of_gt
    ((ENNReal.ofReal_pos.mpr (by positivity)).trans_le hi₀)
  have hiS : i₀ ∈ S := hWS i₀ (nonempty_of_measure_ne_zero hW0)
  by_cases hshort : d ≤ lam*c/1000000000
  · let I := {j : Fin J // f i₀ = γ j ∧ (W i₀ ∩ G j).Nonempty}
    have hIcover : ∀ p ∈ W i₀, ∃ j : I, p ∈ P a b c (z j) (e j) ∧
        Crosses d a b c (x i₀) (v i₀) (z j) (e j) := by
      intro p hp
      obtain ⟨j, hji, hpG⟩ := hcover i₀ p hp
      let j' : I := ⟨j, hji, ⟨p, hp, hpG⟩⟩
      exact ⟨j', hGP j hpG, (hcross i₀ j hji j'.property.2).2⟩
    obtain ⟨j, hj⟩ := exists_stem_grain hd hc hc1 hlam
      (by nlinarith) hshort hab hbc (hv i₀) (hWm i₀) (hWT i₀) (hWI i₀) hi₀
      (fun j : I => z j) (fun j : I => e j) hIcover
    let E := W i₀ ∩ P a b c (z j) (e j)
    have hEP : E ⊆ G j := (hcross i₀ j j.property.1 j.property.2).1
    have hEfin : volume E ≠ ∞ := measure_ne_top_of_subset inter_subset_left (hWfin i₀)
    have ha : 0 ≤ a := by
      obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hW0
      obtain ⟨j, _, hpG⟩ := hcover i₀ p hp
      have hh := (hGP j hpG).1
      linarith [abs_nonneg (e j (p-z j) 0)]
    have hEm : MeasurableSet E := (hWm i₀).inter
      (wz_clustered_cover_volume_gain.frozen_prism_compact ha hab hbc (z j) (e j)).measurableSet
    obtain ⟨H, hH, hHmass⟩ := broad_stem_brush_count hd hρ1 hm.le hv hWm hWT hBr
      (f i₀) (x i₀) (v i₀) (hv i₀) hEm (inter_subset_left.trans (hWT i₀)) hdr hrρ hsmallcap
      (fun p hp => hlevel _ _ ⟨i₀, hiS, rfl, hp.1⟩)
    have hcount : lam*m*c*r ≤ 10000000000*d*(H.ncard : ℝ) := by
      have hmass' : O ((m/2)*(lam*c*d^2/10000)) ≤
          O ((H.ncard : ℝ)*(4096*d^3/r)) := by
        calc
          _ = O (m/2) * O (lam*c*d^2/10000) := ENNReal.ofReal_mul (by positivity)
          _ ≤ O (m/2) * volume E := mul_le_mul_right hj _
          _ ≤ _ := hHmass
      have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (H.ncard : ℝ)*(4096*d^3/r))).mp hmass'
      have hrealr := mul_le_mul_of_nonneg_right hreal hr.le
      have heq : ((H.ncard : ℝ)*(4096*d^3/r))*r = (H.ncard : ℝ)*4096*d^3 := by field_simp
      rw [heq] at hrealr
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp
      nlinarith [mul_nonneg (show 0 ≤ d^3 by positivity) (Nat.cast_nonneg H.ncard)]
    have hHpos : 0 < (H.ncard : ℝ) := by
      by_contra hh
      have hnon : (H.ncard : ℝ) = 0 := le_antisymm (not_lt.mp hh) (Nat.cast_nonneg _)
      rw [hnon, mul_zero] at hcount
      exact (not_le.mpr (by positivity : 0 < lam*m*c*r)) hcount
    refine ⟨j, H.toFinset, ?_, by simpa only [Set.ncard_eq_toFinset_card'] using hcount, ?_⟩
    · exact Set.toFinset_nonempty.mpr (Set.nonempty_iff_ne_empty.mpr (fun he => by simp [he] at hHpos))
    · intro i hi
      have hiH := hH i (Set.mem_toFinset.mp hi)
      have hmeet : (W i ∩ G j).Nonempty := by
        obtain ⟨p, hpE, hpW⟩ := hiH.2.2.2
        exact ⟨p, hpW, hEP hpE⟩
      have hfi : f i = γ j := hiH.2.1.trans j.property.1
      exact ⟨hiH.1, hfi, hmeet, (hcross i j hfi hmeet).2⟩
  · obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hW0
    obtain ⟨j, hji, hpG⟩ := hcover i₀ p hp
    let H : Finset (Fin n) := ({i : Fin n | i ∈ S ∧ f i = γ j ∧ p ∈ W i} : Set (Fin n)).toFinset
    have hcard : m ≤ (H.card : ℝ) := by
      simpa only [H, Set.ncard_eq_toFinset_card'] using hlevel (γ j) p ⟨i₀, hiS, hji, hp⟩
    have hcard0 : 0 < (H.card : ℝ) := hm.trans_le hcard
    refine ⟨j, H, Finset.card_pos.mp (Nat.cast_pos.mp hcard0), ?_, ?_⟩
    · have hcr : lam*c*r ≤ 1000000000*d := by
        have hr1 := hrρ.trans hρ1
        have hh : lam*c < 1000000000*d := by linarith [lt_of_not_ge hshort]
        nlinarith [mul_pos hlam hc]
      have hh := mul_le_mul_of_nonneg_right hcr hm.le
      have hh' := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 1000000000*d by positivity)
      nlinarith [mul_nonneg hd.le (Nat.cast_nonneg H.card)]
    · intro i hi
      have hi' : i ∈ S ∧ f i = γ j ∧ p ∈ W i := by simpa only [H, Set.mem_toFinset, Set.mem_setOf_eq] using hi
      have hmeet : (W i ∩ G j).Nonempty := ⟨p, hi'.2.2, hpG⟩
      exact ⟨hi'.1, hi'.2.1, hmeet, (hcross i j hi'.2.1 hmeet).2⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
