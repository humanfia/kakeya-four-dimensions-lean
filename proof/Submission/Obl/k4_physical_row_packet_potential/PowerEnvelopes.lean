import Submission.Obl.k4_physical_row_packet_potential.PowerBounds
import Submission.Obl.k4_physical_row_packet_potential.Switch.PacketFinal

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.PowerBudget

open Switch.PacketSwitching

private theorem c0 (x : ℝ) (hx : 0 ≤ x) : Bound (fun _ => x) := Bound.const x hx

/-- The switching pencil has a polynomially bounded inverse radius. -/
theorem bound_inv_pencilRadius (Kf : ℝ → ℝ) (hf : Bound Kf)
    (hf2 : ∀ K : ℝ, 2 ≤ K → 2 ≤ Kf K) : Bound (fun K => (pencilRadius (Kf K))⁻¹) := by
  have h := ((c0 8 (by norm_num)).mul (hf.add (c0 1 (by norm_num)))).mul (hf.pow 100)
  apply h.mono
  intro K hK
  have hk : 0 < Kf K := by linarith [hf2 K hK]
  refine ⟨by unfold pencilRadius; positivity, le_of_eq ?_⟩
  simp only [pencilRadius, inv_div, Real.rpow_neg hk.le 100, Real.rpow_natCast,
    div_inv_eq_mul]
  norm_num

theorem bound_fieldRadius (Kf : ℝ → ℝ) (hf : Bound Kf) : Bound (fun K => fieldRadius (Kf K)) :=
  ((c0 2 (by norm_num)).mul hf).add
    ((c0 7 (by norm_num)).mul ((c0 2 (by norm_num)).add hf))

theorem bound_fieldBound (D : ℕ) (Kf AT : ℝ → ℝ) (hf : Bound Kf) (hAT : Bound AT) :
    Bound (fun K => fieldBound D (Kf K) (AT K)) :=
  (((c0 ((D + 1 : ℕ) : ℝ) (by positivity)).mul
    (((c0 1 (by norm_num)).max ((c0 3 (by norm_num)).mul (bound_fieldRadius Kf hf))).pow D)).mul hAT)

theorem bound_fieldLip (D : ℕ) (Kf AT : ℝ → ℝ) (hf : Bound Kf) (hAT : Bound AT) :
    Bound (fun K => fieldLip D (Kf K) (AT K)) :=
  (c0 3 (by norm_num)).mul (((c0 ((D + 1 : ℕ) : ℝ) (by positivity)).mul
    (((c0 1 (by norm_num)).max ((c0 3 (by norm_num)).mul (bound_fieldRadius Kf hf))).pow D)).mul
      ((c0 D (by positivity)).mul hAT))

theorem bound_curlWeight (D : ℕ) (Kf : ℝ → ℝ) (hf : Bound Kf) :
    Bound (fun K => curlWeight D (2 * Kf K) (Kf K)) :=
  ((((c0 9 (by norm_num)).mul ((c0 ((D + 1 : ℕ) : ℝ) (by positivity)).pow 2)).mul
    (((c0 1 (by norm_num)).max
      ((c0 3 (by norm_num)).mul ((c0 2 (by norm_num)).mul hf))).pow D)).mul hf)

/-- All constants in the census smallness budget are polynomial costs. -/
theorem bound_censusConstant (D cNorm cCurl : ℕ) (Kf Kr : ℝ → ℝ)
    (hf : Bound Kf) (hr : Bound Kr) :
    Bound (fun K => censusConstant D cNorm cCurl (Kf K) (Kr K) (2 * Kf K) (Kf K) 1) := by
  let hΛ := (c0 8 (by norm_num)).mul ((((c0 48 (by norm_num)).mul hf).mul hr).pow 6)
  exact (((((hΛ.mul ((c0 9216 (by norm_num)).mul (c0 ((D : ℝ) + 2) (by positivity)))).mul hf).mul
    (((c0 1 (by norm_num)).max (hf.add (c0 1 (by norm_num)))).pow 4)).mul (hΛ.pow cNorm)).mul
      ((c0 2 (by norm_num)).mul (((bound_curlWeight D Kf hf).mul
        (((c0 8 (by norm_num)).mul (hf.pow 5)).pow cCurl)).add (c0 1 (by norm_num)))))

/-- The height census scale has a fixed power lower bound before any
physical packet or accuracy is chosen. -/
theorem lower_censusHeight (D cNorm cCurl : ℕ) (d : ℝ) (hd : d < 1)
    (Kf Kr : ℝ → ℝ) (hf : Bound Kf) (hr : Bound Kr)
    (hf2 : ∀ K : ℝ, 2 ≤ K → 2 ≤ Kf K) (hr1 : ∀ K : ℝ, 2 ≤ K → 1 ≤ Kr K) :
    Lower (fun K ζ => censusHeight D cNorm cCurl (Kf K) (Kr K) ζ d) := by
  apply exists_height_power
    (fun K => censusConstant D cNorm cCurl (Kf K) (Kr K) (2 * Kf K) (Kf K) 1)
    (fun K => pencilRadius (Kf K))
    (bound_censusConstant D cNorm cCurl Kf Kr hf hr) (bound_inv_pencilRadius Kf hf hf2)
  · intro K hK
    have hk : 0 < Kf K := by linarith [hf2 K hK]
    have hkr : 0 < Kr K := by linarith [hr1 K hK]
    unfold censusConstant curlWeight
    positivity
  · intro K hK
    have hk : 0 < Kf K := by linarith [hf2 K hK]
    unfold pencilRadius
    positivity
  · exact hd

/-- One precision exponent makes all three frozen switching widths large
enough for the same physical error. The exponent depends only on fixed
polynomial envelopes for the constants and the inverse long-line duration. -/
theorem exists_packet_resolution_power (D cNorm cCurl : ℕ) (d : ℝ) (hd : d < 1)
    (Kf Kr AT Itime : ℝ → ℝ) (hf : Bound Kf) (hr : Bound Kr)
    (hAT : Bound AT) (hI : Bound Itime)
    (hf2 : ∀ K : ℝ, 2 ≤ K → 2 ≤ Kf K)
    (hr1 : ∀ K : ℝ, 2 ≤ K → 1 ≤ Kr K)
    (hIpos : ∀ K : ℝ, 2 ≤ K → 0 < Itime K) :
    ∃ E : ℕ, ∀ K ζ a h : ℝ, 2 ≤ K → 0 < ζ → ζ ≤ 1 → 0 < a → 0 < h → a ≤ K * h →
      (a / h) * (ζ ^ E / K ^ E) ≤
        packetEpsBound D cNorm cCurl (Kf K) (Kr K) a h ζ d (AT K) ∧
      (a / h) * (ζ ^ E / K ^ E) ≤
        binWidth D cNorm cCurl (Kf K) (Kr K) a h ζ d (AT K) ∧
      (a / h) * (ζ ^ E / K ^ E) ≤
        packetErrBound D cNorm cCurl (Kf K) (Kr K) a h ζ d (1 / Itime K) := by
  let wc : ℝ → ℝ → ℝ := fun K ζ => censusHeight D cNorm cCurl (Kf K) (Kr K) ζ d
  let remez : ℝ → ℝ := fun K => (8 * ((D : ℝ) + 2) * Itime K) ^ (D + 1)
  have hremez : Bound remez :=
    (((c0 8 (by norm_num)).mul (c0 ((D : ℝ) + 2) (by positivity))).mul hI).pow (D + 1)
  have hrad : Lower (fun K _ => pencilRadius (Kf K)) :=
    Lower.of_inv_bound _ (bound_inv_pencilRadius Kf hf hf2) (by
      intro K hK
      have hk : 0 < Kf K := by linarith [hf2 K hK]
      unfold pencilRadius
      positivity)
  have hwc : Lower wc := lower_censusHeight D cNorm cCurl d hd Kf Kr hf hr hf2 hr1
  let e1 : ℝ → ℝ := fun K => Kf K ^ 100 * (24 * (1 + Kf K))
  let e2 : ℝ → ℝ := fun K => 2400 * Kf K
  let e3 : ℝ → ℝ := fun K => 2520 * (Kf K + 1) * (fieldLip D (Kf K) (AT K) + 1) * (1 + Kf K)
  let e4 : ℝ → ℝ := fun K => 60 * K
  let b2 : ℝ → ℝ := fun K => 48 * Kf K ^ 100
  let b3 : ℝ → ℝ := fun K => 90 * (fieldBound D (Kf K) (AT K) + 1)
  let b4 : ℝ → ℝ := fun K => 1260 * (Kf K + 1) * (fieldLip D (Kf K) (AT K) + 1)
  let r1 : ℝ → ℝ := fun K => 2 * remez K
  let r2 : ℝ → ℝ := fun K => 60 * (384 * Kf K * ((D : ℝ) + 2)) ^ (D + 1) * remez K
  have he1 : Bound e1 := (hf.pow 100).mul ((c0 24 (by norm_num)).mul ((c0 1 (by norm_num)).add hf))
  have he2 : Bound e2 := (c0 2400 (by norm_num)).mul hf
  have he3 : Bound e3 := (((c0 2520 (by norm_num)).mul (hf.add (c0 1 (by norm_num)))).mul
    ((bound_fieldLip D Kf AT hf hAT).add (c0 1 (by norm_num)))).mul ((c0 1 (by norm_num)).add hf)
  have he4 : Bound e4 := (c0 60 (by norm_num)).mul Bound.id
  have hb2 : Bound b2 := (c0 48 (by norm_num)).mul (hf.pow 100)
  have hb3 : Bound b3 := (c0 90 (by norm_num)).mul ((bound_fieldBound D Kf AT hf hAT).add (c0 1 (by norm_num)))
  have hb4 : Bound b4 := ((c0 1260 (by norm_num)).mul (hf.add (c0 1 (by norm_num)))).mul
    ((bound_fieldLip D Kf AT hf hAT).add (c0 1 (by norm_num)))
  have hr1' : Bound r1 := (c0 2 (by norm_num)).mul hremez
  have hr2 : Bound r2 := ((c0 60 (by norm_num)).mul
    ((((c0 384 (by norm_num)).mul hf).mul (c0 ((D : ℝ) + 2) (by positivity))).pow (D + 1))).mul hremez
  have hpos (K : ℝ) (hK : 2 ≤ K) :
      0 < e1 K ∧ 0 < e2 K ∧ 0 < e3 K ∧ 0 < e4 K ∧
      0 < b2 K ∧ 0 < b3 K ∧ 0 < b4 K ∧ 0 < r1 K ∧ 0 < r2 K := by
    have hk : 0 < K := by linarith
    have hkf : 0 < Kf K := by linarith [hf2 K hK]
    have hAt0 : 0 ≤ AT K := by obtain ⟨_, hb⟩ := hAT; exact (hb K hK).1
    have hIt := hIpos K hK
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [e1, e2, e3, e4, b2, b3, b4, r1, r2, remez, fieldLip, fieldBound, fieldRadius] <;>
      positivity
  let epsC : ℝ → ℝ → ℝ := fun K ζ => min (1 / K) (min (wc K ζ / e1 K)
    (min (wc K ζ / e2 K) (min (wc K ζ / e3 K) (wc K ζ / e4 K))))
  let binC : ℝ → ℝ → ℝ := fun K ζ => min (pencilRadius (Kf K) / K)
    (min (wc K ζ / b2 K) (min (wc K ζ / b3 K) (wc K ζ / b4 K)))
  let errC : ℝ → ℝ → ℝ := fun K ζ => min (ζ / r1 K) (wc K ζ / r2 K)
  have heps : Lower epsC :=
    (Lower.one.div_cost _ Bound.id (by intros; linarith)).min
      ((hwc.div_cost e1 he1 (fun K hK => (hpos K hK).1)).min
        ((hwc.div_cost e2 he2 (fun K hK => (hpos K hK).2.1)).min
          ((hwc.div_cost e3 he3 (fun K hK => (hpos K hK).2.2.1)).min
            (hwc.div_cost e4 he4 (fun K hK => (hpos K hK).2.2.2.1)))))
  have hbin : Lower binC :=
    (hrad.div_cost _ Bound.id (by intros; linarith)).min
      ((hwc.div_cost b2 hb2 (fun K hK => (hpos K hK).2.2.2.2.1)).min
        ((hwc.div_cost b3 hb3 (fun K hK => (hpos K hK).2.2.2.2.2.1)).min
          (hwc.div_cost b4 hb4 (fun K hK => (hpos K hK).2.2.2.2.2.2.1))))
  have herr : Lower errC :=
    (Lower.accuracy.div_cost r1 hr1' (fun K hK => (hpos K hK).2.2.2.2.2.2.2.1)).min
      (hwc.div_cost r2 hr2 (fun K hK => (hpos K hK).2.2.2.2.2.2.2.2))
  obtain ⟨E, hE⟩ := heps.min (hbin.min herr)
  refine ⟨E, ?_⟩
  intro K ζ a h hK hζ hζ1 ha hh haK
  have hK0 : 0 < K := by linarith
  have hR : a / h ≤ K := (div_le_iff₀ hh).mpr haK
  have hR0 : 0 ≤ a / h := by positivity
  have hkf : 0 < Kf K := by linarith [hf2 K hK]
  have hAt0 : 0 ≤ AT K := by obtain ⟨_, hb⟩ := hAT; exact (hb K hK).1
  have hIt := hIpos K hK
  have hkr : 0 < Kr K := by linarith [hr1 K hK]
  obtain ⟨hqeps, hqbin, hqerr⟩ : ζ ^ E / K ^ E ≤ epsC K ζ ∧
      ζ ^ E / K ^ E ≤ binC K ζ ∧ ζ ^ E / K ^ E ≤ errC K ζ := by
    simpa only [le_min_iff] using hE K ζ hK hζ hζ1
  obtain ⟨he0, he1', he2', he3', he4'⟩ : ζ ^ E / K ^ E ≤ 1 / K ∧
      ζ ^ E / K ^ E ≤ wc K ζ / e1 K ∧ ζ ^ E / K ^ E ≤ wc K ζ / e2 K ∧
      ζ ^ E / K ^ E ≤ wc K ζ / e3 K ∧ ζ ^ E / K ^ E ≤ wc K ζ / e4 K := by
    simpa only [epsC, le_min_iff] using hqeps
  obtain ⟨hb1', hb2', hb3', hb4'⟩ : ζ ^ E / K ^ E ≤ pencilRadius (Kf K) / K ∧
      ζ ^ E / K ^ E ≤ wc K ζ / b2 K ∧ ζ ^ E / K ^ E ≤ wc K ζ / b3 K ∧
      ζ ^ E / K ^ E ≤ wc K ζ / b4 K := by
    simpa only [binC, le_min_iff] using hqbin
  obtain ⟨hr1'', hr2'⟩ : ζ ^ E / K ^ E ≤ ζ / r1 K ∧ ζ ^ E / K ^ E ≤ wc K ζ / r2 K := by
    simpa only [errC, le_min_iff] using hqerr
  have hmul {v : ℝ} (hv : ζ ^ E / K ^ E ≤ v) :
      (a / h) * (ζ ^ E / K ^ E) ≤ (a / h) * v := mul_le_mul_of_nonneg_left hv hR0
  have hwc0 : 0 ≤ wc K ζ := by
    obtain ⟨n, hn⟩ := hwc
    exact (show (0 : ℝ) ≤ ζ ^ n / K ^ n by positivity).trans (hn K ζ hK hζ hζ1)
  refine ⟨?_, ?_, ?_⟩
  · unfold packetEpsBound
    refine le_min ((hmul he0).trans ?_) (le_min ?_ (le_min ?_ (le_min ?_ ?_)))
    · exact (mul_le_mul_of_nonneg_right hR (by positivity)).trans_eq (by field_simp)
    · apply (hmul he1').trans_eq
      dsimp only [e1, wc, censusBase]
      field_simp <;> ring
    · apply (hmul he2').trans_eq
      dsimp only [e2, wc]
      ring
    · apply (hmul he3').trans_eq
      dsimp only [e3, wc]
      ring
    · apply (hmul he4').trans
      dsimp only [e4]
      calc
        _ = (a / h / K) * (wc K ζ / 60) := by ring
        _ ≤ 1 * (wc K ζ / 60) := mul_le_mul_of_nonneg_right
          ((div_le_one hK0).mpr hR) (by positivity)
        _ = _ := by simp only [one_mul, wc]
  · unfold binWidth
    refine le_min ((hmul hb1').trans ?_) (le_min ?_ (le_min ?_ ?_))
    · calc
        _ = (a / h / K) * pencilRadius (Kf K) := by ring
        _ ≤ 1 * pencilRadius (Kf K) := mul_le_mul_of_nonneg_right
          ((div_le_one hK0).mpr hR) (by unfold pencilRadius; positivity)
        _ = _ := one_mul _
    · apply (hmul hb2').trans_eq
      dsimp only [b2, wc, censusBase]
      field_simp <;> ring
    · apply (hmul hb3').trans_eq
      dsimp only [b3, wc]
      ring
    · apply (hmul hb4').trans_eq
      dsimp only [b4, wc]
      ring
  · unfold packetErrBound
    refine le_min ((hmul hr1'').trans_eq ?_) ((hmul hr2').trans_eq ?_)
    · dsimp only [r1, remez]
      field_simp <;> ring
    · dsimp only [r2, remez, wc]
      field_simp <;> ring

end Submission.Obl.k4_physical_row_packet_potential.PowerBudget
