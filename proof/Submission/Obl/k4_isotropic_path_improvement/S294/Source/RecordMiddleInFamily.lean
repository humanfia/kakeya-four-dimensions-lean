-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordMiddleInFamily, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordMiddleLevel

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- A middle level as a literal index of the registered consecutive
core depths i+j. The family can stop before the full history depth. -/
theorem exists_middle_level_in_consecutive_family
    {m : ℕ} {s : ℕ → ℝ} (hm : 0 < m) (hs : ∀ j, s j=((j:ℝ)+1)/m)
    (i stop nfam : ℕ) (hnfam : 0 < nfam) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hwindow : X+Y+1/(m:ℝ) ≤ s stop-s i)
    (hfamily : X+1/(m:ℝ) ≤ s (i+nfam-1)-s i) :
    ∃ j : Fin nfam, i+j.val ≤ stop ∧
      X ≤ s (i+j.val)-s i ∧ Y ≤ s stop-s (i+j.val) := by
  let familyEnd := i+nfam-1
  have hmax : 0 ≤ max Y (s stop-s familyEnd) := hY.trans (le_max_left _ _)
  have hsep : X+max Y (s stop-s familyEnd)+1/(m:ℝ) ≤ s stop-s i := by
    by_cases h : Y ≤ s stop-s familyEnd
    · rw [max_eq_right h]
      linarith only [hfamily]
    · rw [max_eq_left (le_of_not_ge h)]
      exact hwindow
  obtain ⟨mid,himid,hmidstop,hleft,hright⟩ := exists_middle_level hm hs hX hmax hsep
  have hcapScalar : s mid ≤ s familyEnd := by
    have hh := (le_max_right Y (s stop-s familyEnd)).trans hright
    linarith only [hh]
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  rw [hs mid,hs familyEnd] at hcapScalar
  have hcapCast := (div_le_div_iff_of_pos_right hmR).mp hcapScalar
  have hcap : mid ≤ familyEnd := by
    have hh : (mid:ℝ) ≤ (familyEnd:ℝ) := by linarith only [hcapCast]
    exact_mod_cast hh
  let j : Fin nfam := ⟨mid-i,by dsimp only [familyEnd] at hcap; omega⟩
  have hj : i+j.val=mid := by dsimp only [j]; omega
  refine ⟨j,?_,?_,?_⟩
  · simpa only [hj] using hmidstop
  · simpa only [hj] using hleft
  · simpa only [hj] using (le_max_left Y (s stop-s familyEnd)).trans hright

/-- The genuine record midpoint belongs to the exact core depth
family, and supplies all four normalized record-geometry margins.
The left-room premise preserves any prescribed final deep gap. -/
theorem exists_record_middle_in_consecutive_family
    {m : ℕ} {s : ℕ → ℝ} (hm : 0 < m) (hs : ∀ j, s j=((j:ℝ)+1)/m)
    (R J qcore i stop nfam : ℕ) (hnfam : 0 < nfam)
    {κ₁ δ₀ gamma margin baseAccuracy hiddenAccuracy : ℝ}
    (hκ : 0 < κ₁) (hδ : 0 ≤ δ₀) (hgamma : 0 ≤ gamma)
    (hmargin : 0 ≤ margin) (hhidden : 0 ≤ hiddenAccuracy)
    (hbase : margin+3*gamma+2*δ₀+baseAccuracy ≤ κ₁*(s stop-s i))
    (hwindow : (hiddenAccuracy+8*gamma+2*δ₀+margin)+
      (hiddenAccuracy+(((qcore+7)*J+R+13:ℕ):ℝ)*gamma+2*δ₀+margin)/κ₁+
        1/(m:ℝ) ≤ s stop-s i)
    (hfamily : (hiddenAccuracy+8*gamma+2*δ₀+margin)+1/(m:ℝ) ≤
      s (i+nfam-1)-s i) :
    ∃ j : Fin nfam, i+j.val ≤ stop ∧
      margin+3*gamma+(κ₁*(s i-s stop)+2*δ₀) ≤ -baseAccuracy ∧
      margin+((R+5:ℕ):ℝ)*gamma+(κ₁*(s (i+j.val)-s stop)+2*δ₀) ≤ 0 ∧
      margin+8*gamma-(s (i+j.val)-s i-2*δ₀) ≤ -hiddenAccuracy ∧
      margin+(((qcore+7)*J+R+13:ℕ):ℝ)*gamma+
        (κ₁*(s (i+j.val)-s stop)+2*δ₀) ≤ -hiddenAccuracy := by
  let power : ℝ := ((qcore+7)*J+R+13:ℕ)
  let X := hiddenAccuracy+8*gamma+2*δ₀+margin
  let Y := (hiddenAccuracy+power*gamma+2*δ₀+margin)/κ₁
  have hp : 0 ≤ power := Nat.cast_nonneg _
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  obtain ⟨j,hstop,hleft,hright⟩ := exists_middle_level_in_consecutive_family
    hm hs i stop nfam hnfam hX hY hwindow hfamily
  have hYK : Y*κ₁=hiddenAccuracy+power*gamma+2*δ₀+margin := by
    dsimp only [Y]
    field_simp
  have hclock : margin+power*gamma+(κ₁*(s (i+j.val)-s stop)+2*δ₀) ≤ -hiddenAccuracy := by
    have hh := mul_le_mul_of_nonneg_left hright hκ.le
    linarith only [hh,hYK]
  have hcore : margin+((R+5:ℕ):ℝ)*gamma+(κ₁*(s (i+j.val)-s stop)+2*δ₀) ≤ 0 := by
    have hpR : ((R+5:ℕ):ℝ) ≤ power := by
      dsimp only [power]
      exact_mod_cast (show R+5 ≤ (qcore+7)*J+R+13 by omega)
    have hh := mul_le_mul_of_nonneg_right hpR hgamma
    linarith only [hclock,hh,hhidden]
  refine ⟨j,hstop,?_,hcore,?_,hclock⟩
  · linarith only [hbase]
  · dsimp only [X] at hleft
    linarith only [hleft]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
