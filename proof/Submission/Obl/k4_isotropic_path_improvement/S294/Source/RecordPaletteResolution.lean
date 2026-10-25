-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordPaletteResolution, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Stages
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.InternalEntropyBudget
import Submission.Obl.k4_clean_cover_graph_atlas

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- An explicit lower power for the literal final velocity-palette
mesh. The estimate uses the dyadic thicknesses themselves and keeps
the only rounding factor two visible. -/
theorem pvOf_lower_power
    {N L rA rB precision loss gain : ℝ} (Ep TA TB : ℕ) (hN : 0 < N) :
    N^(-((rB-rA)+(Ep:ℝ)*(precision*gain*L)+
      (2*(Ep:ℝ)+2)*(loss*gain*L/((Ep:ℝ)+1))))/2 ≤
      pvOf Ep precision loss gain N L rA rB TA TB := by
  let kexp := loss*gain*L/((Ep:ℝ)+1)
  let pgl := precision*gain*L
  let target := (rB-rA)+(Ep:ℝ)*pgl+(2*(Ep:ℝ)+2)*kexp
  have hδA : 0 < O204.Split.δ N rA := O204.Tangent.δ_pos N rA
  have hδB : 0 < O204.Split.δ N rB := O204.Tangent.δ_pos N rB
  have hδUpper := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN rA).2
  have hδLower := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN rB).1
  have ha : N^(rA-rB)/2 ≤ aRelOf N rA rB := by
    unfold aRelOf
    rw [le_div_iff₀ hδA]
    calc
      _ ≤ N^(rA-rB)/2*(2*N^(-rA)) :=
        mul_le_mul_of_nonneg_left hδUpper (by positivity)
      _ = N^(-rB) := by
        rw [Real.rpow_sub hN]
        simp only [Real.rpow_neg hN.le]
        field_simp
      _ ≤ _ := hδLower
  have hh0 : 0 < hRelOf TA TB := by unfold hRelOf; positivity
  have hh1 : hRelOf TA TB ≤ 1 := by
    unfold hRelOf
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hah : N^(rA-rB)/2 ≤ aRelOf N rA rB/hRelOf TA TB := by
    apply ha.trans
    rw [le_div_iff₀ hh0]
    exact mul_le_of_le_one_right (by unfold aRelOf; positivity) hh1
  have hz := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN pgl).1
  have hzPower : N^(-((Ep:ℝ)*pgl)) ≤ zetaOf precision gain N L^Ep := by
    calc
      _ = (N^(-pgl))^Ep := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hz Ep
  have hKpowers (n : ℕ) : KOf Ep loss gain N L^n=N^((n:ℝ)*kexp) := by
    unfold KOf
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    congr 1
    dsimp only [kexp]
    ring
  have hnormalize : N^(rA-rB)/2*N^(-((Ep:ℝ)*pgl))/N^((Ep:ℝ)*kexp)/
      N^(((Ep+2:ℕ):ℝ)*kexp)=N^(-target)/2 := by
    simp only [div_eq_mul_inv]
    rw [←Real.rpow_neg hN.le,←Real.rpow_neg hN.le]
    have htarget : -target=(rA-rB)+(-((Ep:ℝ)*pgl))+(-((Ep:ℝ)*kexp))+
        (-(((Ep+2:ℕ):ℝ)*kexp)) := by dsimp only [target]; push_cast; ring
    rw [htarget,Real.rpow_add hN,Real.rpow_add hN,Real.rpow_add hN]
    ring
  change N^(-target)/2 ≤ _
  unfold pvOf thetaOf
  rw [hKpowers,hKpowers,←hnormalize]
  have hah0 : 0 ≤ aRelOf N rA rB/hRelOf TA TB := by unfold aRelOf; positivity
  gcongr

/-- A positive exponent margin resolves the front's fine palette at
the final packet palette width. -/
theorem fine_palette_le_pvOf_of_margin
    {N L rA rB precision loss gain fineExponent margin : ℝ}
    (Ep TA TB : ℕ) (hN : 1 ≤ N) (hconstant : 2 ≤ N^margin)
    (hmargin : (rB-rA)+(Ep:ℝ)*(precision*gain*L)+
      (2*(Ep:ℝ)+2)*(loss*gain*L/((Ep:ℝ)+1))+margin ≤ fineExponent) :
    N^(-fineExponent) ≤ pvOf Ep precision loss gain N L rA rB TA TB := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  apply le_trans _ (pvOf_lower_power Ep TA TB hNp)
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ N^(-fineExponent)*N^margin :=
      mul_le_mul_of_nonneg_left hconstant (Real.rpow_nonneg hNp.le _)
    _ = N^(margin-fineExponent) := by rw [←Real.rpow_add hNp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The chosen child offset, including both integer roundings and the
two path depth errors, lies within a fixed fraction of the palette
depth. This comparison holds before the sample or path is chosen. -/
theorem childOffset_depth_bound
    {κ₁ precision gain δ₀ L : ℝ} {Ep m : ℕ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hprecision : 1 ≤ precision)
    (hgain : 0 < gain) (hδ : δ₀ ≤ gain/100) (hL : 0 ≤ L)
    (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ)) :
    (((childOffset κ₁ Ep precision gain m:ℕ):ℝ)/(m:ℝ)+2*δ₀)*L ≤
      2*(((Ep:ℝ)+1)*precision+3)*gain*L/κ₁ := by
  let Y := ((Ep:ℝ)+1)*precision+2
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hceil := (Nat.ceil_lt_add_one
    (by positivity : (0:ℝ) ≤ 2*Y*gain*m/κ₁)).le
  have hchild : ((childOffset κ₁ Ep precision gain m:ℕ):ℝ) ≤ 2*Y*gain*m/κ₁+2 := by
    unfold childOffset
    simp only [Nat.cast_add,Nat.cast_one]
    dsimp only [Y] at hceil
    linarith only [hceil]
  have hratio : ((childOffset κ₁ Ep precision gain m:ℕ):ℝ)/(m:ℝ) ≤
      2*Y*gain/κ₁+2/(m:ℝ) := by
    rw [div_le_iff₀ hmR]
    have heq : (2*Y*gain/κ₁+2/(m:ℝ))*(m:ℝ)=2*Y*gain*m/κ₁+2 := by field_simp
    rw [heq]
    exact hchild
  have hstep : 2/(m:ℝ) ≤ gain/4 := by
    rw [div_le_div_iff₀ hmR (by norm_num : (0:ℝ)<4)]
    linarith only [hgm]
  have herror : 2/(m:ℝ)+2*δ₀ ≤ 2*gain/κ₁ := by
    have hgainκ : gain*κ₁ ≤ gain := mul_le_of_le_one_right hgain.le hκ1
    have hgκ : gain ≤ gain/κ₁ := by rw [le_div_iff₀ hκ]; exact hgainκ
    calc
      _ ≤ gain/4+2*(gain/100) := by linarith only [hstep,hδ]
      _ ≤ 2*gain := by linarith only [hgain]
      _ ≤ 2*(gain/κ₁) := mul_le_mul_of_nonneg_left hgκ (by norm_num)
      _ = _ := by ring
  have hnormalized : ((childOffset κ₁ Ep precision gain m:ℕ):ℝ)/(m:ℝ)+2*δ₀ ≤
      2*(((Ep:ℝ)+1)*precision+3)*gain/κ₁ := by
    calc
      _ ≤ 2*Y*gain/κ₁+2*gain/κ₁ := by linarith only [hratio,herror]
      _ = _ := by dsimp only [Y]; ring
  have hh := mul_le_mul_of_nonneg_right hnormalized hL
  simpa only [div_mul_eq_mul_div] using hh

/-- The actual front palette exponent pays the literal final palette
width with a full gain*L margin, uniformly in the tuning depth. -/
theorem front_palette_exponent_margin
    (tune : Tuning) {κ₁ d₁ precision loss gain L δ₀ rA rB : ℝ} {Ep : ℕ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hprecision : 1 ≤ precision)
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hgain : 0 < gain) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ₀)
    (hdepth : rB-rA ≤ 2*(((Ep:ℝ)+1)*precision+3)*gain*L/κ₁) :
    (rB-rA)+(Ep:ℝ)*(precision*gain*L)+
      (2*(Ep:ℝ)+2)*(loss*gain*L/((Ep:ℝ)+1))+gain*L ≤
        ueOf tune κ₁ d₁ Ep precision loss gain δ₀ L := by
  let X := ((Ep:ℝ)+1)*precision+3
  let u := gain*L/κ₁
  let D := tune.depth κ₁ d₁ Ep precision loss
  have hEp : 0 ≤ (Ep:ℝ) := Nat.cast_nonneg Ep
  have hXp : 0 < X := by dsimp only [X]; positivity
  have hD : 1 ≤ D := tune.one_le_depth _ _ _ _ _
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hgL : 0 ≤ gain*L := mul_nonneg hgain.le hL
  have hgainU : gain*L ≤ u := by
    dsimp only [u]
    rw [le_div_iff₀ hκ]
    exact mul_le_of_le_one_right hgL hκ1
  have hprecU : (Ep:ℝ)*(precision*gain*L) ≤ (Ep:ℝ)*precision*u := by
    have hh := mul_le_mul_of_nonneg_left hgainU (by positivity : (0:ℝ) ≤ (Ep:ℝ)*precision)
    nlinarith only [hh]
  have hlossU : loss*gain*L ≤ u := by
    have hh : loss*(gain*L) ≤ gain*L := mul_le_of_le_one_left hgL hloss1
    nlinarith only [hh,hgainU]
  have hthree : (Ep:ℝ)*precision+3 ≤ 2*X := by dsimp only [X]; nlinarith only [hEp,hprecision]
  have htarget : (rB-rA)+(Ep:ℝ)*(precision*gain*L)+2*(loss*gain*L)+gain*L ≤ 4*X*u := by
    have hdepth' : rB-rA ≤ 2*X*u := by
      simpa only [X,u,div_eq_mul_inv,mul_assoc] using hdepth
    have hh := mul_le_mul_of_nonneg_right hthree hu
    nlinarith only [hdepth',hprecU,hlossU,hgainU,hh]
  have hpower : (2*(Ep:ℝ)+2)*(loss*gain*L/((Ep:ℝ)+1))=2*(loss*gain*L) := by
    have hE : 0 < (Ep:ℝ)+1 := by positivity
    field_simp
  rw [hpower]
  apply htarget.trans
  have hpal : paletteExpOf tune κ₁ d₁ Ep precision loss gain L=4*X*D*u := by
    dsimp only [paletteExpOf,X,D,u]
    ring
  rw [ueOf,hpal]
  have hh := mul_le_mul_of_nonneg_left hD (by positivity : (0:ℝ) ≤ 4*X*u)
  nlinarith only [hh,mul_nonneg hδ hL]

/-- The front's actual fine palette is resolved at the final child's
pvOf. Only the literal uniform grid and the two path depth errors are
needed; the child rounding is handled internally. -/
theorem fine_palette_le_pvOf_at_childOffset
    (tune : Tuning) {N κ₁ d₁ precision loss gain L δ₀ rA rB : ℝ}
    {Ep m i : ℕ} (TA TB : ℕ) (s : ℕ → ℝ)
    (hN : 1 ≤ N) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hprecision : 1 ≤ precision)
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hgain : 0 < gain) (hL : 0 ≤ L)
    (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ gain/100) (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ))
    (hs : ∀ j, s j=((j:ℝ)+1)/m)
    (hra : |rA-s i*L| ≤ δ₀*L)
    (hrb : |rB-s (i+childOffset κ₁ Ep precision gain m)*L| ≤ δ₀*L)
    (hconstant : 2 ≤ N^(gain*L)) :
    N^(-ueOf tune κ₁ d₁ Ep precision loss gain δ₀ L) ≤
      pvOf Ep precision loss gain N L rA rB TA TB := by
  have hgap : s (i+childOffset κ₁ Ep precision gain m)-s i=
      ((childOffset κ₁ Ep precision gain m:ℕ):ℝ)/(m:ℝ) := by
    rw [hs,hs]
    push_cast
    ring
  have herrors : rB-rA ≤
      (s (i+childOffset κ₁ Ep precision gain m)-s i+2*δ₀)*L := by
    have h1 := (abs_le.mp hra).1
    have h2 := (abs_le.mp hrb).2
    nlinarith only [h1,h2]
  rw [hgap] at herrors
  have hdepth := herrors.trans (childOffset_depth_bound hκ hκ1 hprecision hgain hδ hL hm hgm)
  exact fine_palette_le_pvOf_of_margin Ep TA TB hN hconstant
    (front_palette_exponent_margin tune hκ hκ1 hprecision hloss hloss1 hgain hL hδ0 hdepth)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
