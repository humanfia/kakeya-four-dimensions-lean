-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/CriticalJitter.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/CriticalJitter.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.CriticalEndpoint
import Submission.Obl.k4_matching_abstract_switching_mixture.Covers

/-! Stability of critical endpoints under jitter of the three time coordinates. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

open Set MeasureTheory
open scoped ENNReal

/-- Jittering the three times by delta moves the critical endpoint by at most
20*K^2*delta. The transverse starting position need not be bounded. -/
theorem critical_endpoint_time_perturbation
    (c q : Fin 3 → ℝ) (K δ s s' : ℝ) (t t' : Fin 2 → ℝ)
    (hK : 1 ≤ K) (hδ : 0 ≤ δ) (hc : ∀ i, |c i| ≤ K)
    (hq0 : |q 0| ≤ K) (hq1 : |q 1| ≤ K)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (_hs' : s' ∈ Set.Icc (0 : ℝ) 1)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (ht' : ∀ i, t' i ∈ Set.Icc (0 : ℝ) 1)
    (hss : |s - s'| ≤ δ) (htt : ∀ i, |t i - t' i| ≤ δ) :
    ∀ i : Fin 3, |criticalEndpoint c q (s, t) i - criticalEndpoint c q (s', t') i| ≤
      20 * K ^ 2 * δ := by
  have hK0 : 0 ≤ K := by linarith
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hKsq : 1 ≤ K ^ 2 := by nlinarith
  have hKD : K * δ ≤ K ^ 2 * δ := mul_le_mul_of_nonneg_right hK2 hδ
  have hD : δ ≤ K ^ 2 * δ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKsq hδ
  have hg1 : |c 1 - c 0| ≤ 2 * K := (abs_sub _ _).trans (by linarith [hc 1, hc 0])
  have hg2 : |c 2 - c 1| ≤ 2 * K := (abs_sub _ _).trans (by linarith [hc 2, hc 1])
  have hq : |-q 1 + q 0 * c 0| ≤ 2 * K ^ 2 := by
    calc
      _ ≤ |q 1| + |q 0| * |c 0| := by simpa only [abs_neg, abs_mul] using abs_add_le (-q 1) (q 0 * c 0)
      _ ≤ K + K * K := add_le_add hq1 (mul_le_mul hq0 (hc 0) (abs_nonneg _) hK0)
      _ ≤ _ := by nlinarith
  have hprod (i : Fin 2) :
      |t i * (s - t i) - t' i * (s' - t' i)| ≤ 3 * δ := by
    have hst : |s - t i| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1, (ht i).2], by linarith [hs.2, (ht i).1]⟩
    have ht1 : |t' i| ≤ 1 := abs_le.mpr ⟨by linarith [(ht' i).1], (ht' i).2⟩
    have hdiff : |(s - s') - (t i - t' i)| ≤ 2 * δ :=
      (abs_sub _ _).trans (by linarith [htt i])
    calc
      _ = |(t i - t' i) * (s - t i) + t' i * ((s - s') - (t i - t' i))| := by congr 1; ring
      _ ≤ |(t i - t' i) * (s - t i)| + |t' i * ((s - s') - (t i - t' i))| := abs_add_le _ _
      _ ≤ δ * 1 + 1 * (2 * δ) := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul (htt i) hst (abs_nonneg _) hδ)
          (mul_le_mul ht1 hdiff (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  have hZ : |criticalSpatialEndpoint c q s t 0 - criticalSpatialEndpoint c q s' t' 0| ≤
      5 * K * δ := by
    have heq : criticalSpatialEndpoint c q s t 0 - criticalSpatialEndpoint c q s' t' 0 =
        c 2 * (s - s') - (c 1 - c 0) * (t 0 - t' 0) -
          (c 2 - c 1) * (t 1 - t' 1) := by simp [criticalSpatialEndpoint]; ring
    rw [heq]
    calc
      _ ≤ |c 2 * (s - s') - (c 1 - c 0) * (t 0 - t' 0)| +
          |(c 2 - c 1) * (t 1 - t' 1)| := abs_sub _ _
      _ ≤ |c 2 * (s - s')| + |(c 1 - c 0) * (t 0 - t' 0)| +
          |(c 2 - c 1) * (t 1 - t' 1)| := by
        gcongr
        exact abs_sub _ _
      _ ≤ K * δ + (2 * K) * δ + (2 * K) * δ := by
        simp only [abs_mul]
        exact add_le_add
          (add_le_add (mul_le_mul (hc 2) hss (abs_nonneg _) hK0)
            (mul_le_mul hg1 (htt 0) (abs_nonneg _) (by positivity)))
          (mul_le_mul hg2 (htt 1) (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hY : |criticalSpatialEndpoint c q s t 1 - criticalSpatialEndpoint c q s' t' 1| ≤
      2 * K ^ 2 * δ + 12 * K * δ := by
    have heq : criticalSpatialEndpoint c q s t 1 - criticalSpatialEndpoint c q s' t' 1 =
        (-q 1 + q 0 * c 0) * (s - s') +
          (c 1 - c 0) * (t 0 * (s - t 0) - t' 0 * (s' - t' 0)) +
          (c 2 - c 1) * (t 1 * (s - t 1) - t' 1 * (s' - t' 1)) := by
      simp [criticalSpatialEndpoint]
      ring
    rw [heq]
    calc
      _ ≤ |(-q 1 + q 0 * c 0) * (s - s') +
            (c 1 - c 0) * (t 0 * (s - t 0) - t' 0 * (s' - t' 0))| +
          |(c 2 - c 1) * (t 1 * (s - t 1) - t' 1 * (s' - t' 1))| := abs_add_le _ _
      _ ≤ |(-q 1 + q 0 * c 0) * (s - s')| +
          |(c 1 - c 0) * (t 0 * (s - t 0) - t' 0 * (s' - t' 0))| +
          |(c 2 - c 1) * (t 1 * (s - t 1) - t' 1 * (s' - t' 1))| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (2 * K ^ 2) * δ + (2 * K) * (3 * δ) + (2 * K) * (3 * δ) := by
        simp only [abs_mul]
        exact add_le_add
          (add_le_add (mul_le_mul hq hss (abs_nonneg _) (by positivity))
            (mul_le_mul hg1 (hprod 0) (abs_nonneg _) (by positivity)))
          (mul_le_mul hg2 (hprod 1) (abs_nonneg _) (by positivity))
      _ = _ := by ring
  intro i
  fin_cases i
  · change |s - s'| ≤ _
    nlinarith
  · change |criticalSpatialEndpoint c q s t 0 - criticalSpatialEndpoint c q s' t' 0| ≤ _
    nlinarith
  · change |criticalSpatialEndpoint c q s t 1 - criticalSpatialEndpoint c q s' t' 1| ≤ _
    nlinarith


/-- A finite family of disjoint time boxes landing in one base cell has the
expected cubic count. The estimate reuses the accepted count-to-volume bridge. -/
theorem critical_endpoint_time_box_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (Tc : Type*) [DecidableEq Tc]
      (I : Tc → Set ℝ) (center : Tc → ℝ),
      (∀ a, MeasurableSet (I a)) →
      Pairwise (fun a b => Disjoint (I a) (I b)) →
      ∀ (d δ K r : ℝ), 0 < d → 0 ≤ δ → 2 ≤ K → 0 ≤ r →
      (∀ a, volume (I a) = ENNReal.ofReal d) →
      (∀ a, I a ⊆ Set.Icc (0 : ℝ) 1) →
      (∀ a, center a ∈ Set.Icc (0 : ℝ) 1) →
      (∀ a s, s ∈ I a → |s - center a| ≤ δ) →
      (2 * K)⁻¹ + 2 * δ ≤ K⁻¹ → 20 * K ^ 2 * δ ≤ r →
      ∀ (c q u : Fin 3 → ℝ), (∀ i, |c i| ≤ K) →
      (∀ i : Fin 2, K⁻¹ ≤ |c i.succ - c i.castSucc|) →
      |q 0| ≤ K → |q 1| ≤ K →
      ∀ Q : Finset (Fin 3 → Tc),
      (∀ a ∈ Q, K⁻¹ ≤ |center (a 1) - center (a 0)| ∧
        ∀ i, |criticalEndpoint c q
          (center (a 2), fun j : Fin 2 => center (a j.castSucc)) i - u i| ≤ r) →
      (Q.card : ℝ) * d ^ 3 ≤ C * K ^ 24 * r ^ 3 := by
  obtain ⟨C, hC, hcap⟩ := critical_endpoint_cell_bound
  refine ⟨C * (2 : ℝ) ^ 27, by positivity, ?_⟩
  intro Tc _ I center hIm hId d δ K r hd hδ hK hr hIv hIunit hcenter hnear hmargin herror
    c q u hc hgap hq0 hq1 Q hQ
  let E : Set (ℝ × (Fin 2 → ℝ)) := {p |
    p.1 ∈ Set.Icc (0 : ℝ) 1 ∧
    p.2 ∈ Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 (2 * K)⁻¹ ∧
    ∀ i, |criticalEndpoint c q p i - u i| ≤ 2 * r}
  have hKpos : 0 < K := by linarith
  have hinv : (2 * K)⁻¹ ≤ K⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hKpos (by linarith : K ≤ 2 * K)
  have hsub (a : Fin 3 → Tc) (ha : a ∈ Q) :
      Submission.Obl.k4_matching_abstract_switching_mixture.tupleBox I a ⊆ E := by
    intro p hp
    have hs : p.1 ∈ I (a 2) := hp.1
    have ht (i : Fin 2) : p.2 i ∈ I (a i.castSucc) := Set.mem_pi.mp hp.2 i (Set.mem_univ i)
    have hactual : ∀ i : Fin 2, p.2 i ∈ Set.Icc (0 : ℝ) 1 :=
      fun i => hIunit _ (ht i)
    have hsep : (2 * K)⁻¹ ≤ |p.2 1 - p.2 0| :=
      Submission.Obl.k4_matching_abstract_switching_mixture.separated_of_near
        (hnear _ _ (ht 1)) (hnear _ _ (ht 0)) (hQ a ha).1 hmargin
    have hnorm : ‖p.2‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
      intro i
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(hactual i).1], (hactual i).2⟩
    have hregular : p.2 ∈
        Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 (2 * K)⁻¹ := by
      refine ⟨hnorm, ?_⟩
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hsep
      · change (2 * K)⁻¹ ≤ |p.2 0 - p.2 1|
        rw [abs_sub_comm]
        exact hsep
      · exact (hij rfl).elim
    have hpert := critical_endpoint_time_perturbation c q K δ p.1 (center (a 2)) p.2
      (fun j : Fin 2 => center (a j.castSucc)) (by linarith) hδ hc hq0 hq1
      (hIunit _ hs) (hcenter _) hactual (fun i => hcenter _) (hnear _ _ hs)
      (fun i => hnear _ _ (ht i))
    refine ⟨hIunit _ hs, hregular, ?_⟩
    intro i
    calc
      _ ≤ |criticalEndpoint c q p i - criticalEndpoint c q
            (center (a 2), fun j : Fin 2 => center (a j.castSucc)) i| +
          |criticalEndpoint c q
            (center (a 2), fun j : Fin 2 => center (a j.castSucc)) i - u i| := by
        have h := abs_add_le
          (criticalEndpoint c q p i - criticalEndpoint c q
            (center (a 2), fun j : Fin 2 => center (a j.castSucc)) i)
          (criticalEndpoint c q
            (center (a 2), fun j : Fin 2 => center (a j.castSucc)) i - u i)
        simpa only [sub_add_sub_cancel] using h
      _ ≤ _ := by linarith [(hQ a ha).2 i, hpert i]
  have hcount := Submission.Obl.k4_matching_abstract_switching_mixture.tupleBox_count_volume_le
    I hIm hId hd hIv Q E hsub
  have hvol : volume E ≤ ENNReal.ofReal (C * (2 * K) ^ 24 * (2 * r) ^ 3) := by
    exact hcap (2 * K) (by linarith) c (fun i => (hc i).trans (by linarith))
      (fun i => hinv.trans (hgap i)) q u (2 * r) (by positivity)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcount.trans hvol)
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hreal
  convert hreal using 1 <;> ring

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
