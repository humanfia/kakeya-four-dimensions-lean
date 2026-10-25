-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.Merge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.MergeBasics

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, Merge.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O q P T ι)

def PrismData.merge {n K : ℕ} (D : PrismData n) (f : Fin D.L → Fin K)
    (a' : ℝ) (z' : Fin K → V) (e' : Fin K → V ≃ₗᵢ[ℝ] V)
    (γ' : Fin K → Fin D.N) : PrismData n where
  a := a'
  s := D.s
  L := K
  N := D.N
  z := z'
  e := e'
  W := mergePieces f D.W
  y := D.y
  w := D.w
  γ := γ'

/-- Once geometric merging has supplied containing prisms with long-face
crossings, the incidence conditions pass to the new family without a mass
loss. The only density cost is the increase of each containing prism's volume. -/
theorem valid_merge {ω ζ δ h h' ρ c c' a' : ℝ} {n K : ℕ}
    (D : PrismData n) (x v : Fin n → V) (Y : Fin n → Set V)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h')
    (H : D.Valid ω ζ δ h ρ c x v Y 1)
    (f : Fin D.L → Fin K) (z' : Fin K → V) (e' : Fin K → V ≃ₗᵢ[ℝ] V)
    (γ' : Fin K → Fin D.N) (hγ : ∀ j, γ' (f j) = D.γ j)
    (ha' : δ ≤ a') (hab' : a' ≤ ρ * c') (hbc' : ρ * c' ≤ c') (hc' : c' ≤ 1)
    (hcontain : ∀ j, P D.a (ρ * c) c (D.z j) (D.e j) ⊆
      P a' (ρ * c') c' (z' (f j)) (e' (f j)))
    (hdensity : ∀ k, ∃ j, f j = k ∧
      O (δ ^ h') * volume (P a' (ρ * c') c' (z' k) (e' k)) ≤
        O (δ ^ h) * volume (P D.a (ρ * c) c (D.z j) (D.e j)))
    (hcross' : ∀ i j, (D.W i j).Nonempty →
      (∀ p ∈ T δ (x i) (v i) ∩ frontier (P a' (ρ * c') c' (z' (f j)) (e' (f j))),
        |ι (e' (f j) (p - z' (f j))) 2| = c' / 2) ∧
      ∀ t ∈ ({-c'/2,c'/2} : Set ℝ), ∃ p ∈
        T δ (x i) (v i) ∩ P a' (ρ * c') c' (z' (f j)) (e' (f j)),
        ι (e' (f j) (p - z' (f j))) 2 = t)
    (hcover' : ∀ k, P a' (ρ * c') c' (z' k) (e' k) ⊆
      T ρ (D.y (γ' k)) (D.w (γ' k)) ∧
      ι (e' k (D.w (γ' k))) 0 ^ 2 + ι (e' k (D.w (γ' k))) 1 ^ 2 ≤ (10 * ρ) ^ 2) :
    (D.merge f a' z' e' γ').Valid ω ζ δ h' ρ c' x v Y 1 := by
  classical
  rcases H with ⟨ha, hab, hbc, hc, hW, hmass, hdense, hcross, hbroad, hX, hw, hcover, _⟩
  have hdisj := fun i j j' hne => (hW i j).2.2 j' hne
  have hmeas := fun i j => (hW i j).1
  have hp := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhh)
  have hn := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hhh)
  dsimp only [PrismData.Valid, PrismData.merge]
  refine ⟨ha', hab', hbc', hc', ?_, ?_, ?_, ?_, ?_, hX, hw, ?_, by norm_num⟩
  · intro i k
    refine ⟨mergePieces_measurable f D.W hmeas i k, ?_,
      fun k' hne => mergePieces_disjoint f D.W hdisj i k k' hne⟩
    intro p hp
    obtain ⟨j, hj, hpj⟩ := (mem_mergePieces f D.W i k p).mp hp
    refine ⟨((hW i j).2.1 hpj).1, ?_⟩
    simpa only [hj] using hcontain j ((hW i j).2.1 hpj).2
  · rw [mergePieces_total_measure volume f D.W hmeas hdisj]
    exact (mul_le_mul' hp le_rfl).trans hmass
  · intro k
    obtain ⟨j, hj, hv⟩ := hdensity k
    apply hv.trans ((hdense j).trans (measure_mono ?_))
    rintro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨i, (mem_mergePieces f D.W i k p).mpr ⟨j, hj, hi⟩⟩
  · intro i k hnon
    obtain ⟨p, hp⟩ := hnon
    obtain ⟨j, hj, hpj⟩ := (mem_mergePieces f D.W i k p).mp hp
    have hjnon : (D.W i j).Nonempty := ⟨p, hpj⟩
    refine ⟨?_, ?_⟩
    · simpa only [PrismData.merge, ← hγ j, hj] using (hcross i j hjnon).1
    · simpa only [PrismData.merge, hj] using hcross' i j hjnon
  · intro k p u r hu hdr hrρ
    have hc0 : 0 < c := hδ.trans_le (ha.trans (hab.trans hbc))
    have hρ0 : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
      (by intro h; linarith [h.2]) |>.1
    apply mergePieces_count_bound f D.W hdisj p k
      (fun i => min ‖v i - u‖ ‖v i + u‖ ≤ r)
    intro j
    exact (hbroad j p u r hu hdr hrρ).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hn
          (Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ0.le) _))
        (Nat.cast_nonneg _))
  · intro _
    exact ⟨(hcover (by norm_num)).1, hcover'⟩

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
