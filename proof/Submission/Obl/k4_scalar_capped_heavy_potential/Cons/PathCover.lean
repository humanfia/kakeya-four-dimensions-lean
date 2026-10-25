import Submission.Obl.k4_scalar_capped_heavy_potential.Core.SwitchEndpointRecovery
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Geometry
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.RoundedPalette
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.CellCurl

/-!
# One actual switched path covers its simulated endpoint

Five incidences `e 0, …, e 4` of a block, joined by four shared-state switches,
each line obeying the field relation throughout the block: the simulated
polynomial endpoint (rescaled by `lam`, with rounded velocities) lies in the
enlarged base cell of the actual endpoint, and the simulated height is close to
the center of its hidden-coordinate bin.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching
open Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching

theorem ubase_div_affine {z₀ : Fin 2 → ℝ} {h lam : ℝ} (hh : h ≠ 0) (hlam : lam ≠ 0)
    (l : ℕ × (Fin 5 → ℝ)) (t t' : ℝ) (d : Fin 2) :
    ubase z₀ h l t' d / lam =
      ubase z₀ h l t d / lam + ((![1, l.2 1] : Fin 2 → ℝ) d) * ((t' - t) / (h * lam)) := by
  rw [ubase_affine hh l t t' d]
  field_simp

theorem switch_base_bound {z₀ : Fin 2 → ℝ} {h lam H δs : ℝ} (hh : 0 < h) (hlam : 0 < lam)
    (ω : (ℕ × (Fin 5 → ℝ)) × ℝ) (l' : ℕ × (Fin 5 → ℝ)) (hrel : switchRel H δs ω l')
    (hbd : ∀ i, |l'.2 i| ≤ H) (ht : |ω.2| ≤ 1) (d : Fin 2) :
    |ubase z₀ h l' ω.2 d / lam - ubase z₀ h ω.1 ω.2 d / lam| ≤ (H + 1) * δs / (h * lam) := by
  have hy := (hrel hbd ht).1
  have hnn : 0 ≤ (H + 1) * δs := (abs_nonneg _).trans hy
  fin_cases d
  · simp only [ubase, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, sub_self, abs_zero]
    positivity
  · simp only [ubase, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    have hid : (yL l' ω.2 - z₀ 1) / h / lam - (yL ω.1 ω.2 - z₀ 1) / h / lam =
        (yL l' ω.2 - yL ω.1 ω.2) / (h * lam) := by field_simp; ring
    rw [hid, abs_div, abs_of_pos (mul_pos hh hlam)]
    exact div_le_div_of_nonneg_right hy (mul_pos hh hlam).le

theorem switch_height_bound {h H δs : ℝ} (hh : 0 < h)
    (ω : (ℕ × (Fin 5 → ℝ)) × ℝ) (l' : ℕ × (Fin 5 → ℝ)) (hrel : switchRel H δs ω l')
    (hbd : ∀ i, |l'.2 i| ≤ H) (ht : |ω.2| ≤ 1) :
    |xL l' ω.2 / h - xL ω.1 ω.2 / h| ≤ (4 * H + 1) * δs / h := by
  have hx := (hrel hbd ht).2
  rw [← sub_div, abs_div, abs_of_pos hh]
  exact div_le_div_of_nonneg_right hx hh.le

/-- **Path cover.** The deterministic core of the success event. -/
theorem exists_path_cover_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (z₀ : Fin 2 → ℝ)
      (t₀ h lam H δs δv εT ξ w₁ K : ℝ) (e : Fin 5 → (ℕ × (Fin 5 → ℝ)) × ℝ)
      (q : Fin 2 → ℤ) (m : ℤ),
      (∀ i, (𝒯 i).totalDegree ≤ D) → (∀ i b, |(𝒯 i).coeff b| ≤ H) →
      0 < h → 1 ≤ lam → 0 ≤ H → 0 < δs → 0 < δv → 0 ≤ εT → 0 < ξ → 0 < w₁ →
      2 * H ≤ lam → lam ^ (D + 1) * (((D + 1) ^ 2 : ℕ) * H) ≤ K → H ≤ K →
      4 * max ((H + 1) * δs / (h * lam)) ((4 * H + 1) * δs / h) + 4 * (δv / 2) ≤ 1 / 2 →
      (∀ k, (e k).2 ∈ Icc t₀ (t₀ + h)) → (∀ t ∈ Icc t₀ (t₀ + h), |t| ≤ 1) →
      (∀ k, ∀ i, |(e k).1.2 i| ≤ H) →
      (∀ k, ∀ t ∈ Icc t₀ (t₀ + h), ∀ i, |ubase z₀ h (e k).1 t i| ≤ H) →
      (∀ k, ∀ t ∈ Icc t₀ (t₀ + h), |(e k).1.2 3 + 2 * t * (e k).1.2 4 -
        ∑ i : Fin 2, eval (ubase z₀ h (e k).1 t) (𝒯 i) * (![1, (e k).1.2 1] : Fin 2 → ℝ) i| ≤ εT) →
      (∀ j : Fin 4, switchRel H δs (e j.castSucc) (e j.succ).1) →
      (fun i => ⌊ubase z₀ h (e 4).1 (e 4).2 i / ξ⌋) = q →
      ⌊xL (e 4).1 (e 4).2 / w₁⌋ = m →
      let b := max ((H + 1) * δs / (h * lam)) ((4 * H + 1) * δs / h)
      let x : Fin 2 → ℝ := fun d => ubase z₀ h (e 0).1 (e 0).2 d / lam
      let v : Fin 4 → ℝ := fun j => vround δv ((e j.succ).1.2 1)
      let δ : Fin 4 → ℝ := fun j => ((e j.succ).2 - (e j.castSucc).2) / (h * lam)
      δ ∈ Icc (-1 : Fin 4 → ℝ) 1 ∧ x ∈ halfBox ∧ (∀ j, |v j| ≤ H + δv) ∧
        switchedBaseEndpoint x v δ ∈
          Icc (fun d => ((q d : ℝ) + 1 / 2) * (ξ / lam) - (ξ / (2 * lam) + (4 * b + 4 * (δv / 2))))
            (fun d => ((q d : ℝ) + 1 / 2) * (ξ / lam) + (ξ / (2 * lam) + (4 * b + 4 * (δv / 2)))) ∧
        |xL (e 0).1 (e 0).2 / h +
            eval δ (brokenHeight (scaleField lam (𝒯 0)) (scaleField lam (𝒯 1)) x v) -
            ((m : ℝ) + 1 / 2) * w₁ / h| ≤
          w₁ / (2 * h) + (4 * (lam * εT + (1 + K) * (2 * C * K) * (4 * b + 4 * (δv / 2)) +
            K * (δv / 2)) + 3 * b) + b := by
  obtain ⟨C, hC, hcov⟩ := exists_actual_endpoint_cover_constant D
  refine ⟨C, hC, ?_⟩
  intro 𝒯 z₀ t₀ h lam H δs δv εT ξ w₁ K e q m h𝒯deg h𝒯coeff hh hlam1 hH hδs hδv hεT hξ hw₁
    hlamH hKfield hKH hsmall heI hI1 hbd hu hfield hrel hq hm
  intro b x v δ
  have hlam : 0 < lam := by linarith
  have hhlam : 0 < h * lam := mul_pos hh hlam
  have hb : 0 ≤ b := le_max_of_le_right (by positivity)
  have hbY : (H + 1) * δs / (h * lam) ≤ b := le_max_left _ _
  have hbX : (4 * H + 1) * δs / h ≤ b := le_max_right _ _
  have htime (k : Fin 5) : |(e k).2| ≤ 1 := hI1 _ (heI k)
  -- increments
  have hδj (j : Fin 4) : |δ j| ≤ 1 := by
    have h1 := heI j.succ
    have h2 := heI j.castSucc
    have hd : |(e j.succ).2 - (e j.castSucc).2| ≤ h := by
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    change |((e j.succ).2 - (e j.castSucc).2) / (h * lam)| ≤ 1
    rw [abs_div, abs_of_pos hhlam, div_le_one hhlam]
    nlinarith
  have hδbox : δ ∈ Icc (-1 : Fin 4 → ℝ) 1 :=
    ⟨fun j => by have := (abs_le.mp (hδj j)).1; simpa using this,
      fun j => by have := (abs_le.mp (hδj j)).2; simpa using this⟩
  -- the start lies in the half box
  have hxhalf : x ∈ halfBox := by
    have hb0 := hu 0 _ (heI 0)
    constructor <;> intro d <;> simp only [x]
    · have h1 := (abs_le.mp (hb0 d)).1
      rw [le_div_iff₀ hlam]
      nlinarith
    · have h1 := (abs_le.mp (hb0 d)).2
      rw [div_le_iff₀ hlam]
      nlinarith
  have hv (j : Fin 4) : |v j| ≤ H + δv :=
    (abs_vround_le hδv _).trans (by linarith [hbd j.succ 1])
  refine ⟨hδbox, hxhalf, hv, ?_⟩
  -- leg data
  let w : Fin 4 → ℝ := fun j => (e j.succ).1.2 1
  let z : Fin 4 → Fin 2 → ℝ := fun j d => ubase z₀ h (e j.succ).1 (e j.castSucc).2 d / lam
  let S : Fin 4 → Polynomial ℝ := fun j => legHeight (e j.succ).1 (e j.castSucc).2 (h * lam) h
  let center : Fin 2 → ℝ := fun d => ((q d : ℝ) + 1 / 2) * (ξ / lam)
  -- leg endpoint identity
  have hleg (j : Fin 4) (t : ℝ) (d : Fin 2) :
      ubase z₀ h (e j.succ).1 t d / lam =
        z j d + ((![1, w j] : Fin 2 → ℝ) d) * ((t - (e j.castSucc).2) / (h * lam)) :=
    ubase_div_affine hh.ne' hlam.ne' _ _ _ d
  have hlegend (j : Fin 4) (d : Fin 2) :
      z j d + ((![1, w j] : Fin 2 → ℝ) d) * δ j = ubase z₀ h (e j.succ).1 (e j.succ).2 d / lam :=
    (hleg j _ d).symm
  -- field bound on the unit box
  have hnorm : ∀ u ∈ Icc (-1 : Fin 2 → ℝ) 1,
      |eval u (scaleField lam (𝒯 0))| ≤ K ∧ |eval u (scaleField lam (𝒯 1))| ≤ K := by
    intro u hu'
    exact ⟨(scaleField_eval_le hlam1 _ (h𝒯deg 0) hH (h𝒯coeff 0) u hu').trans hKfield,
      (scaleField_eval_le hlam1 _ (h𝒯deg 1) hH (h𝒯coeff 1) u hu').trans hKfield⟩
  -- start
  have hstart (d : Fin 2) : |z 0 d - x d| ≤ b := by
    have h := switch_base_bound (z₀ := z₀) hh hlam (e 0) (e 1).1 (hrel 0) (hbd 1) (htime 0) d
    exact h.trans hbY
  -- consecutive legs
  have hbase (j : Fin 3) (d : Fin 2) :
      |z j.succ d - (z j.castSucc d + ((![1, w j.castSucc] : Fin 2 → ℝ) d) * δ j.castSucc)| ≤ b := by
    rw [hlegend j.castSucc d]
    have hidx : (j.castSucc : Fin 4).succ = (j.succ : Fin 4).castSucc := by
      ext; simp
    have h := switch_base_bound (z₀ := z₀) hh hlam (e (j.succ : Fin 4).castSucc)
      (e (j.succ : Fin 4).succ).1 (hrel j.succ) (hbd _) (htime _) d
    simp only [z]
    rw [hidx]
    exact h.trans hbY
  -- heights
  have hswitch (j : Fin 3) :
      |(S j.succ).eval 0 - (S j.castSucc).eval (δ j.castSucc)| ≤ b := by
    simp only [S, legHeight_eval, mul_zero, add_zero]
    have hidx : (j.castSucc : Fin 4).succ = (j.succ : Fin 4).castSucc := by
      ext; simp
    have ht : (e (j.castSucc : Fin 4).castSucc).2 + h * lam * δ j.castSucc =
        (e (j.castSucc : Fin 4).succ).2 := by
      simp only [δ]
      field_simp
      ring
    rw [ht, hidx]
    exact (switch_height_bound hh (e (j.succ : Fin 4).castSucc) (e (j.succ : Fin 4).succ).1
      (hrel j.succ) (hbd _) (htime _)).trans hbX
  have hheightStart : |(S 0).eval 0 - xL (e 0).1 (e 0).2 / h| ≤ b := by
    simp only [S, legHeight_eval, mul_zero, add_zero]
    exact (switch_height_bound hh (e 0) (e 1).1 (hrel 0) (hbd 1) (htime 0)).trans hbX
  -- the endpoint cell
  have hphysical (d : Fin 2) :
      |z 3 d + ((![1, w 3] : Fin 2 → ℝ) d) * δ 3 - center d| ≤ ξ / (2 * lam) := by
    rw [hlegend 3 d]
    have hcell : ⌊ubase z₀ h (e 4).1 (e 4).2 d / ξ⌋ = q d := congrFun hq d
    rw [Int.floor_eq_iff] at hcell
    have h1 := hcell.1
    have h2 := hcell.2
    rw [le_div_iff₀ hξ] at h1
    rw [div_lt_iff₀ hξ] at h2
    simp only [center]
    have hid : ubase z₀ h (e (3 : Fin 4).succ).1 (e (3 : Fin 4).succ).2 d / lam -
        ((q d : ℝ) + 1 / 2) * (ξ / lam) =
        (ubase z₀ h (e 4).1 (e 4).2 d - ((q d : ℝ) + 1 / 2) * ξ) / lam := by
      have : ((3 : Fin 4).succ : Fin 5) = 4 := rfl
      rw [this]
      field_simp
    rw [hid, abs_div, abs_of_pos hlam, show ξ / (2 * lam) = (ξ / 2) / lam by ring]
    apply div_le_div_of_nonneg_right _ hlam.le
    rw [abs_le]
    constructor <;> linarith
  have hheight : |(S 3).eval (δ 3) - ((m : ℝ) + 1 / 2) * w₁ / h| ≤ w₁ / (2 * h) := by
    simp only [S, legHeight_eval, show ((3 : Fin 4).succ : Fin 5) = 4 from rfl]
    have ht : (e (3 : Fin 4).castSucc).2 + h * lam * δ 3 = (e 4).2 := by
      simp only [δ]
      field_simp
      ring_nf
      rfl
    rw [ht]
    have hcell : ⌊xL (e 4).1 (e 4).2 / w₁⌋ = m := hm
    rw [Int.floor_eq_iff] at hcell
    have h1 := hcell.1
    have h2 := hcell.2
    rw [le_div_iff₀ hw₁] at h1
    rw [div_lt_iff₀ hw₁] at h2
    have hnum : |xL (e 4).1 (e 4).2 - ((m : ℝ) + 1 / 2) * w₁| ≤ w₁ / 2 := by
      rw [abs_le]; constructor <;> linarith
    have hid : xL (e 4).1 (e 4).2 / h - ((m : ℝ) + 1 / 2) * w₁ / h =
        (xL (e 4).1 (e 4).2 - ((m : ℝ) + 1 / 2) * w₁) / h := by ring
    rw [hid, abs_div, abs_of_pos hh, show w₁ / (2 * h) = (w₁ / 2) / h by ring]
    exact div_le_div_of_nonneg_right hnum hh.le
  -- along each leg
  have hpath : ∀ j, ∀ s ∈ uIcc (0 : ℝ) (δ j),
      (fun d => z j d + ((![1, w j] : Fin 2 → ℝ) d) * s) ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
      (fun d => eval (Sum.elim δ (fun _ : Unit => s)) (legPoint x v j d)) ∈
        Icc (-1 : Fin 2 → ℝ) 1 ∧
      |(S j).derivative.eval s -
        (eval (fun d => z j d + ((![1, w j] : Fin 2 → ℝ) d) * s) (scaleField lam (𝒯 0)) +
          w j * eval (fun d => z j d + ((![1, w j] : Fin 2 → ℝ) d) * s)
            (scaleField lam (𝒯 1)))| ≤ lam * εT := by
    intro j s hs
    set t := (e j.castSucc).2 + h * lam * s with ht
    have hδdef : h * lam * δ j = (e j.succ).2 - (e j.castSucc).2 := by
      simp only [δ]; field_simp
    have htI : t ∈ Icc t₀ (t₀ + h) := by
      have h1 := heI j.succ
      have h2 := heI j.castSucc
      rcases Set.mem_uIcc.mp hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · have hm1 : 0 ≤ h * lam * s := mul_nonneg hhlam.le hs1
        have hm2 : h * lam * s ≤ h * lam * δ j := mul_le_mul_of_nonneg_left hs2 hhlam.le
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      · have hm1 : h * lam * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hhlam.le hs2
        have hm2 : h * lam * δ j ≤ h * lam * s := mul_le_mul_of_nonneg_left hs1 hhlam.le
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hsabs : |s| ≤ 1 := by
      rcases Set.mem_uIcc.mp hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · rw [abs_le]; constructor <;> linarith [(abs_le.mp (hδj j)).2]
      · rw [abs_le]; constructor <;> linarith [(abs_le.mp (hδj j)).1]
    have hpos : (fun d => z j d + ((![1, w j] : Fin 2 → ℝ) d) * s) =
        fun d => ubase z₀ h (e j.succ).1 t d / lam := by
      funext d
      rw [hleg j t d]
      congr 2
      rw [ht]
      field_simp
      ring
    have hhalfpos : (fun d => ubase z₀ h (e j.succ).1 t d / lam) ∈ halfBox := by
      have hb0 := hu j.succ t htI
      constructor <;> intro d
      · have h1 := (abs_le.mp (hb0 d)).1
        show -(1 / 2 : ℝ) ≤ ubase z₀ h (e j.succ).1 t d / lam
        rw [le_div_iff₀ hlam]
        nlinarith
      · have h1 := (abs_le.mp (hb0 d)).2
        show ubase z₀ h (e j.succ).1 t d / lam ≤ 1 / 2
        rw [div_le_iff₀ hlam]
        nlinarith
    refine ⟨?_, ?_, ?_⟩
    · rw [hpos]; exact halfBox_subset hhalfpos
    · have hvw : ∀ i, |w i - v i| ≤ δv / 2 := fun i => by
        rw [abs_sub_comm]; exact abs_vround_sub_le hδv _
      constructor <;> intro d
      · have herr := switched_base_error x v w δ z b (δv / 2) 1 hb (by positivity) hδj hvw
          hstart hbase j d s hsabs
        have hact := congrFun hpos d
        have hhd := hhalfpos.1 d
        simp only at hact hhd
        rw [abs_le] at herr
        simp only [Pi.neg_apply, Pi.one_apply]
        linarith
      · have herr := switched_base_error x v w δ z b (δv / 2) 1 hb (by positivity) hδj hvw
          hstart hbase j d s hsabs
        have hact := congrFun hpos d
        have hhd := hhalfpos.2 d
        simp only at hact hhd
        rw [abs_le] at herr
        simp only [Pi.one_apply]
        linarith
    · rw [hpos]
      simp only [S, legHeight_derivative_eval, eval_scaleField]
      have hscale : (fun i => lam * (ubase z₀ h (e j.succ).1 t i / lam)) =
          ubase z₀ h (e j.succ).1 t := by
        funext i; field_simp
      rw [hscale]
      have hf := hfield j.succ t htI
      rw [Fin.sum_univ_two] at hf
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at hf
      have hid : h * lam * ((e j.succ).1.2 3 + 2 * ((e j.castSucc).2 + h * lam * s) *
          (e j.succ).1.2 4) / h - (lam * eval (ubase z₀ h (e j.succ).1 t) (𝒯 0) +
            w j * (lam * eval (ubase z₀ h (e j.succ).1 t) (𝒯 1))) =
          lam * ((e j.succ).1.2 3 + 2 * t * (e j.succ).1.2 4 -
            (eval (ubase z₀ h (e j.succ).1 t) (𝒯 0) +
              eval (ubase z₀ h (e j.succ).1 t) (𝒯 1) * (e j.succ).1.2 1)) := by
        simp only [w, ht]
        field_simp
      rw [hid, abs_mul, abs_of_pos hlam]
      exact mul_le_mul_of_nonneg_left hf hlam.le
  have hwK (j : Fin 4) : |w j| ≤ K := (hbd j.succ 1).trans hKH
  have hwv (j : Fin 4) : |w j - v j| ≤ δv / 2 := by
    rw [abs_sub_comm]; exact abs_vround_sub_le hδv _
  have hK0 : 0 ≤ K := hH.trans hKH
  have hres := hcov (scaleField lam (𝒯 0)) (scaleField lam (𝒯 1))
    (scaleField_degree lam _ (h𝒯deg 0)) (scaleField_degree lam _ (h𝒯deg 1))
    x center v w δ z S K b (δv / 2) (lam * εT) (ξ / (2 * lam)) (w₁ / (2 * h))
    (xL (e 0).1 (e 0).2 / h) (((m : ℝ) + 1 / 2) * w₁ / h) hK0 hb (by positivity)
    (mul_nonneg hlam.le hεT) hδj hwK hwv hnorm hstart hbase hpath hswitch hheightStart
    hphysical hheight
  exact hres

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
