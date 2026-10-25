-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordGeometry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalDeepPowerGeometry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RelativeWindowScales

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)

noncomputable section

/-- Uniform actual ancestor-record geometry from scalar level budgets.
The record envelope K stays separate from the frame envelope G: G may
pay the fixed grid error N^(2delta0 L), while only K^12 is charged to the
late front fraction. No absolute ancestor depth enters the budgets. -/
theorem original_record_geometry_of_level_budgets
    {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    {K G baseRef hiddenRef : ℝ} (hK : 2304 ≤ K) (hKG : K ≤ G)
    (hmax : max p.κ (d.K k) ≤ K) (hgeometry : d.N k^(2*δ₀*d.L) ≤ G)
    (R J qcore i mid stop : ℕ) (hi : i < m) (hmid : mid < m) (hstop : stop < m)
    (hhidden : hiddenRef ≤ 1)
    (hbaseBudget : G^3*d.N k^((κ₁*(s i-s stop)+2*δ₀)*d.L) ≤ baseRef)
    (hcoreBudget : 12*G^(R+5)*d.N k^((κ₁*(s mid-s stop)+2*δ₀)*d.L) ≤ 1)
    (hheightDepth : 8*G^8*d.N k^(-((s mid-s i-2*δ₀)*d.L)) ≤ hiddenRef)
    (hheightClock : 24*G^((qcore+7)*J+R+13)*
      d.N k^((κ₁*(s mid-s stop)+2*δ₀)*d.L) ≤ hiddenRef) :
    δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r i) ∧
    (∀ root : Fin p.C, p.lev root=i → ∀ deep : Fin p.C, p.lev deep=stop →
      p.unshearedDeepRadius root deep ≤ baseRef) ∧
    (∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K^R)⁻¹/12) ∧
    ∀ root : Fin p.C, p.lev root=i →
      ∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev root)))*
        (2*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev root))))+
          ((K^(qcore+7))^J*(p.κ+K^14*(K^6)⁻¹))*
            (6*K^R*p.deepBaseRadius (d.N k) d.L δ₀ fine deep)) ≤ hiddenRef := by
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hKp : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hG : 2304 ≤ G := hK.trans hKG
  have hGp : 0 < G := by linarith
  have hG1 : 1 ≤ G := by linarith
  have hκ0 : 0 ≤ p.κ := zero_le_one.trans hp.1
  have hmaxG : max p.κ (d.K k) ≤ G := hmax.trans hKG
  let clockMid := d.N k^((κ₁*(s mid-s stop)+2*δ₀)*d.L)
  let depth := d.N k^(-((s mid-s i-2*δ₀)*d.L))
  have hdepth0 : 0 ≤ depth := Real.rpow_nonneg hNp.le _
  have hG8 : 1 ≤ G^8 := one_le_pow₀ hG1
  have hδ : δ (d.N k) (p.r mid)/δ (d.N k) (p.r i) ≤ 2*depth :=
    (hp.relative_parent_width_bounds hN i mid hi hmid).2
  have hdepth1 : 2*depth ≤ 1 := by
    have hh : 2*depth ≤ 8*G^8*depth := by nlinarith
    exact hh.trans (hheightDepth.trans hhidden)
  have hwidth : δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r i) := by
    have hp0 : 0 < δ (d.N k) (p.r i) := by unfold δ; positivity
    exact (div_le_one hp0).mp (hδ.trans hdepth1)
  have hdeepBound (fine deep : Fin p.C) (hf : p.lev fine=mid) (hdp : p.lev deep=stop) :
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ G^5*clockMid := by
    have hclock : (2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev deep) ≤ clockMid := by
      simpa only [hf,hdp,clockMid] using hp.original_clock_ratio_upper hNp mid stop hmid hstop
    exact (original_deep_base_radius_le_power hd hp hG hmaxG hgeometry fine deep).trans
      (mul_le_mul_of_nonneg_left hclock (by positivity))
  have hK8 : K^14*(K^6)⁻¹=K^8 := by
    simpa using (pow_sub₀ K hKp.ne' (by norm_num : (6:ℕ)≤14)).symm
  have hK8G : K^8 ≤ G^8 := pow_le_pow_left₀ hKp.le hKG 8
  have hKRG : K^R ≤ G^R := pow_le_pow_left₀ hKp.le hKG R
  refine ⟨hwidth,?_,?_,?_⟩
  · intro root hr deep hdp
    have hclock : (2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T (p.lev deep) ≤
        d.N k^((κ₁*(s i-s stop)+2*δ₀)*d.L) := by
      simpa only [hr,hdp] using hp.original_clock_ratio_upper hNp i stop hi hstop
    exact (original_unsheared_deep_radius_le_power hd hp hG hmaxG root deep).trans
      ((mul_le_mul_of_nonneg_left hclock (by positivity)).trans hbaseBudget)
  · intro fine deep hf hdp
    rw [←one_div]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<12)).mpr
    apply (le_div_iff₀ (pow_pos hKp R)).mpr
    calc
      _ ≤ (G^5*clockMid)*12*G^R := by
        gcongr
        · exact hdeepBound fine deep hf hdp
      _ = 12*G^(R+5)*clockMid := by rw [pow_add]; ring
      _ ≤ 1 := hcoreBudget
  · intro root hr fine deep hf hdp
    have hrootδ : δ (d.N k) (p.r (p.lev root))≠0 := by unfold δ; positivity
    rw [div_self hrootδ,one_mul,hK8]
    have hratio : δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev root)) ≤ 2*depth := by
      simpa only [hr] using hδ
    have hratio0 : 0 ≤ δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev root)) := by
      unfold δ
      positivity
    have hdeep0 : 0 ≤ p.deepBaseRadius (d.N k) d.L δ₀ fine deep := by
      unfold PathData.deepBaseRadius
      positivity
    have hadd : 2*(K^8*(δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev root)))) ≤
        4*G^8*depth := by
      calc
        _ ≤ 2*(G^8*(2*depth)) := by gcongr
        _ = _ := by ring
    have hcoeff : p.κ+K^8 ≤ 2*G^8 := by
      have hκG : p.κ ≤ G := (le_max_left _ _).trans hmaxG
      have hGle : G ≤ G^8 := by simpa only [pow_one] using pow_le_pow_right₀ hG1 (by norm_num : (1:ℕ)≤8)
      linarith
    have hpower : (K^(qcore+7))^J ≤ G^((qcore+7)*J) := by
      rw [←pow_mul]
      exact pow_le_pow_left₀ hKp.le hKG _
    have htail : ((K^(qcore+7))^J*(p.κ+K^8))*
        (6*K^R*p.deepBaseRadius (d.N k) d.L δ₀ fine deep) ≤
        12*G^((qcore+7)*J+R+13)*clockMid := by
      calc
        _ ≤ (G^((qcore+7)*J)*(2*G^8))*(6*G^R*(G^5*clockMid)) :=
          mul_le_mul
            (mul_le_mul hpower hcoeff (by positivity) (by positivity))
            (mul_le_mul (mul_le_mul_of_nonneg_left hKRG (by norm_num))
              (hdeepBound fine deep hf hdp) hdeep0 (by positivity))
            (by positivity) (by positivity)
        _ = _ := by simp only [pow_add]; ring
    linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
