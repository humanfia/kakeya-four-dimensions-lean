import Mathlib

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap

open Set

/-- The strict rate update in Section 9. -/
noncomputable def improvedRate (c α u : ℝ) : ℝ := u / (1 + α * (u - c))

theorem improvedRate_mem {c α u : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hαc : α * c < 1) (hu : c < u) (hu1 : u ≤ 1) :
    c < improvedRate c α u ∧ improvedRate c α u < u ∧ improvedRate c α u ≤ 1 := by
  have hu0 : 0 < u := hc.trans hu
  have hden : 0 < 1 + α * (u - c) := by positivity
  have hden1 : 1 < 1 + α * (u - c) := by nlinarith
  have hlo : c < improvedRate c α u := by
    rw [improvedRate, lt_div_iff₀ hden]
    nlinarith
  have hhi : improvedRate c α u < u := by
    rw [improvedRate, div_lt_iff₀ hden]
    nlinarith
  exact ⟨hlo, hhi, hhi.le.trans hu1⟩

/-- A uniform strict step reaches every interior target after finitely many uses.
The predicate can retain a fixed buffer and any other data chosen before the rate. -/
theorem bootstrap_all_strict_rates {c α : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hα : 0 < α) (hαc : α * c < 1) (G : ℝ → Prop)
    (hbase : G 1)
    (hup : ∀ u v, c < u → u ≤ v → v ≤ 1 → G u → G v)
    (hstep : ∀ u, c < u → u ≤ 1 → G u → G (improvedRate c α u)) :
    ∀ v, c < v → v ≤ 1 → G v := by
  let S : Set ℝ := {u | c < u ∧ u ≤ 1 ∧ G u}
  have hS : S.Nonempty := ⟨1, hc1, le_rfl, hbase⟩
  have hbelow : BddBelow S := ⟨c, fun u hu => hu.1.le⟩
  have hcle : c ≤ sInf S := le_csInf hS (fun u hu => hu.1.le)
  have htle1 : sInf S ≤ 1 := csInf_le hbelow ⟨hc1, le_rfl, hbase⟩
  have hinf : sInf S = c := by
    by_contra hne
    have hlt : c < sInf S := lt_of_le_of_ne hcle (Ne.symm hne)
    have htpos : 0 < sInf S := hc.trans hlt
    have hδ : 0 < α * sInf S * (sInf S - c) := by positivity
    obtain ⟨u, huS, hul⟩ := exists_lt_of_csInf_lt hS (by linarith :
      sInf S < sInf S + α * sInf S * (sInf S - c))
    have htu : sInf S ≤ u := csInf_le hbelow huS
    have hmem := improvedRate_mem hc hα hαc huS.1 huS.2.1
    have himem : improvedRate c α u ∈ S := ⟨hmem.1, hmem.2.2, hstep u huS.1 huS.2.1 huS.2.2⟩
    have hile := csInf_le hbelow himem
    have hden : 0 < 1 + α * (u - c) := by
      nlinarith [mul_pos hα (sub_pos.mpr huS.1)]
    have hsmall : improvedRate c α u < sInf S := by
      rw [improvedRate, div_lt_iff₀ hden]
      nlinarith [mul_nonneg (show 0 ≤ α * sInf S by positivity) (sub_nonneg.mpr htu)]
    exact (not_lt_of_ge hile) hsmall
  intro v hcv hv1
  obtain ⟨u, huS, huv⟩ := exists_lt_of_csInf_lt hS (by simpa only [hinf] using hcv)
  exact hup u v huS.1 huv.le hv1 huS.2.2

/-- If the analytic step permits every smaller positive gain, the last step can be
truncated to land on the desired rate exactly; no regridding of the parameter squares is needed. -/
theorem bootstrap_all_strict_rates_of_partial_steps {c α : ℝ} (hc : 0 < c)
    (hc1 : c < 1) (hα : 0 < α) (hαc : α * c < 1) (G : ℝ → Prop)
    (hbase : G 1)
    (hstep : ∀ u θ, c < u → u ≤ 1 → 0 < θ → θ ≤ α * (u - c) → G u →
      G (u / (1 + θ))) : ∀ v, c < v → v ≤ 1 → G v := by
  let P : ℝ → Prop := fun u => ∀ v, u ≤ v → v ≤ 1 → G v
  have hPbase : P 1 := by
    intro v hv hv1
    have : v = 1 := le_antisymm hv1 hv
    simpa only [this] using hbase
  have hPup : ∀ u v, c < u → u ≤ v → v ≤ 1 → P u → P v := by
    intro u v hcu huv hv1 hPu w hvw hw1
    exact hPu w (huv.trans hvw) hw1
  have hPstep : ∀ u, c < u → u ≤ 1 → P u → P (improvedRate c α u) := by
    intro u hcu hu1 hPu v huv hv1
    by_cases huv' : u ≤ v
    · exact hPu v huv' hv1
    have hvu : v < u := lt_of_not_ge huv'
    have hmem := improvedRate_mem hc hα hαc hcu hu1
    have hcv : c < v := hmem.1.trans_le huv
    have hv0 : 0 < v := hc.trans hcv
    have hu0 : 0 < u := hc.trans hcu
    let θ := u / v - 1
    have hθ : 0 < θ := by
      dsimp [θ]
      have := (lt_div_iff₀ hv0).mpr (show 1 * v < u by simpa using hvu)
      linarith
    have hden : 0 < 1 + α * (u - c) := by positivity
    have hθle : θ ≤ α * (u - c) := by
      have hmul : u ≤ v * (1 + α * (u - c)) :=
        (div_le_iff₀ hden).mp huv
      dsimp [θ]
      have hdiv : u / v ≤ 1 + α * (u - c) :=
        (div_le_iff₀ hv0).mpr (by simpa only [mul_comm v] using hmul)
      linarith
    have heq : u / (1 + θ) = v := by
      dsimp [θ]
      field_simp
      simpa only [add_sub_cancel] using div_self hu0.ne'
    simpa only [heq] using hstep u θ hcu hu1 hθ hθle (hPu u le_rfl hu1)
  intro v hcv hv1
  exact bootstrap_all_strict_rates hc hc1 hα hαc P hPbase hPup hPstep v hcv hv1 v le_rfl hv1

/-- The numerical constants of the paper satisfy the hypotheses of the iteration lemma. -/
theorem bootstrap_all_strict_rates_kakeya {d κ : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hκ : 0 < κ) (hκ1 : 2 * κ < 1) (G : ℝ → Prop)
    (hbase : G 1)
    (hup : ∀ u v, 2 * κ < u → u ≤ v → v ≤ 1 → G u → G v)
    (hstep : ∀ u, 2 * κ < u → u ≤ 1 → G u →
      G (u / (1 + (1 - d) * (u - 2 * κ) / 10000))) :
    ∀ v, 2 * κ < v → v ≤ 1 → G v := by
  apply bootstrap_all_strict_rates (c := 2 * κ) (α := (1 - d) / 10000)
    (by positivity) hκ1 (by positivity) (by nlinarith) G hbase hup
  intro u hu hu1 hGu
  convert hstep u hu hu1 hGu using 1 <;> dsimp [improvedRate] <;> congr 2 <;> ring

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap
