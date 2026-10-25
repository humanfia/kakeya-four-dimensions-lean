-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordMiddleLevel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.LevelRatios
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordGeometryPowers

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- Choose a genuine grid level for the original record source. The
left gap pays its height accuracy; the right clock gap pays the core
jet and deep-radius powers. This level precedes all actual path data. -/
theorem exists_record_middle_level
    {m : ℕ} {s : ℕ → ℝ} (hm : 0 < m) (hs : ∀ i, s i=((i:ℝ)+1)/m)
    (R J qcore i stop : ℕ)
    {κ₁ δ₀ gamma margin baseAccuracy hiddenAccuracy : ℝ}
    (hκ : 0 < κ₁) (hδ : 0 ≤ δ₀) (hgamma : 0 ≤ gamma)
    (hmargin : 0 ≤ margin) (hhidden : 0 ≤ hiddenAccuracy)
    (hbase : margin+3*gamma+2*δ₀+baseAccuracy ≤ κ₁*(s stop-s i))
    (hsep : (hiddenAccuracy+8*gamma+2*δ₀+margin)+
      (hiddenAccuracy+(((qcore+7)*J+R+13:ℕ):ℝ)*gamma+2*δ₀+margin)/κ₁+
        1/(m:ℝ) ≤ s stop-s i) :
    ∃ mid : ℕ, i ≤ mid ∧ mid ≤ stop ∧
      margin+3*gamma+(κ₁*(s i-s stop)+2*δ₀) ≤ -baseAccuracy ∧
      margin+((R+5:ℕ):ℝ)*gamma+(κ₁*(s mid-s stop)+2*δ₀) ≤ 0 ∧
      margin+8*gamma-(s mid-s i-2*δ₀) ≤ -hiddenAccuracy ∧
      margin+(((qcore+7)*J+R+13:ℕ):ℝ)*gamma+
        (κ₁*(s mid-s stop)+2*δ₀) ≤ -hiddenAccuracy := by
  let power : ℝ := ((qcore+7)*J+R+13:ℕ)
  let X := hiddenAccuracy+8*gamma+2*δ₀+margin
  let Y := (hiddenAccuracy+power*gamma+2*δ₀+margin)/κ₁
  have hpower : 0 ≤ power := Nat.cast_nonneg _
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  obtain ⟨mid,himid,hmidstop,hleft,hright⟩ := exists_middle_level hm hs hX hY hsep
  have hYK : Y*κ₁=hiddenAccuracy+power*gamma+2*δ₀+margin := by
    dsimp only [Y]
    field_simp
  have hclock : margin+power*gamma+(κ₁*(s mid-s stop)+2*δ₀) ≤ -hiddenAccuracy := by
    have hh := mul_le_mul_of_nonneg_left hright hκ.le
    linarith only [hh,hYK]
  have hcore : margin+((R+5:ℕ):ℝ)*gamma+(κ₁*(s mid-s stop)+2*δ₀) ≤ 0 := by
    have hpowerR : ((R+5:ℕ):ℝ) ≤ power := by
      dsimp only [power]
      exact_mod_cast (show R+5 ≤ (qcore+7)*J+R+13 by omega)
    have hh := mul_le_mul_of_nonneg_right hpowerR hgamma
    linarith only [hclock,hh,hhidden]
  refine ⟨mid,himid,hmidstop,?_,hcore,?_,hclock⟩
  · linarith only [hbase]
  · dsimp only [X] at hleft
    linarith only [hleft]

/-- Multiplying the normalized level margins by the problem's length
gives the literal four power budgets used by RecordGeometry. -/
theorem record_geometry_budgets_of_normalized_margins
    {N G gamma margin baseAccuracy hiddenAccuracy κ₁ δ₀ L si smid sstop : ℝ}
    (R J qcore : ℕ) (hN : 1 ≤ N) (hG0 : 0 ≤ G) (hL : 0 ≤ L)
    (hG : G ≤ N^(gamma*L)) (hconstant : 24 ≤ N^(margin*L))
    (hbase : margin+3*gamma+(κ₁*(si-sstop)+2*δ₀) ≤ -baseAccuracy)
    (hcore : margin+((R+5:ℕ):ℝ)*gamma+(κ₁*(smid-sstop)+2*δ₀) ≤ 0)
    (hdepth : margin+8*gamma-(smid-si-2*δ₀) ≤ -hiddenAccuracy)
    (hclock : margin+(((qcore+7)*J+R+13:ℕ):ℝ)*gamma+
      (κ₁*(smid-sstop)+2*δ₀) ≤ -hiddenAccuracy) :
    G^3*N^((κ₁*(si-sstop)+2*δ₀)*L) ≤ N^(-baseAccuracy*L) ∧
    12*G^(R+5)*N^((κ₁*(smid-sstop)+2*δ₀)*L) ≤ 1 ∧
    8*G^8*N^(-((smid-si-2*δ₀)*L)) ≤ N^(-hiddenAccuracy*L) ∧
    24*G^((qcore+7)*J+R+13)*N^((κ₁*(smid-sstop)+2*δ₀)*L) ≤ N^(-hiddenAccuracy*L) := by
  apply record_geometry_budgets_of_exponent_margins R J qcore hN hG0 hG hconstant
  · nlinarith only [mul_le_mul_of_nonneg_right hbase hL]
  · nlinarith only [mul_le_mul_of_nonneg_right hcore hL]
  · nlinarith only [mul_le_mul_of_nonneg_right hdepth hL]
  · nlinarith only [mul_le_mul_of_nonneg_right hclock hL]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
